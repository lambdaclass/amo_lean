/*
 * Isolated Goldilocks Fold Microbenchmark: 4 reduction variants
 * Measures ONLY the product reduction x mod p (where p = 2^64 - 2^32 + 1),
 * without butterfly sum/diff or loop overhead.
 * B39-4: Calibration data for Goldilocks InstructionProfile model.
 *
 * Variants:
 *   A) fold_mul:      hi*c + lo (128-bit multiply by c=2^32-1)
 *   B) fold_shiftsub:  (hi<<32) - hi + lo (shift-subtract, 128-bit intermediates)
 *   C) fold_halves:   halves decomposition (all uint64_t, no 128-bit overflow)
 *   D) NEON Karatsuba: 3 × vmull_u32 (2-lane, for SIMD butterfly)
 *
 * Template: bench_redc_isolated.c (B35-2, 126 LOC)
 * Reference: TRZK_goldigraphs_idea.md §Fase 0.5
 */
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>

#define GOLDI_P 0xFFFFFFFF00000001ULL
#define GOLDI_C 0xFFFFFFFFULL  /* 2^32 - 1 */

/* ══════ Variant A: Solinas fold with 128-bit multiply ══════
   fold(x) = hi * c + lo, where c = 2^32-1.
   Simple but hi*c needs __uint128_t (hi can be up to 2^64). */
static inline uint64_t fold_mul(unsigned __int128 x) {
    uint64_t hi = (uint64_t)(x >> 64), lo = (uint64_t)x;
    unsigned __int128 result = (unsigned __int128)hi * GOLDI_C + lo;
    /* Single fold: result < 2^96. Need second fold or conditional sub. */
    uint64_t hi2 = (uint64_t)(result >> 64), lo2 = (uint64_t)result;
    uint64_t r = (unsigned __int128)hi2 * GOLDI_C + lo2;
    return r >= GOLDI_P ? r - GOLDI_P : r;
}

/* ══════ Variant B: Shift-subtract fold (no multiply, 128-bit) ══════
   fold(x) = (hi<<32) - hi + lo ≡ hi*(2^32-1) + lo.
   Avoids multiply but needs 128-bit shifts. */
static inline uint64_t fold_shiftsub(unsigned __int128 x) {
    uint64_t hi = (uint64_t)(x >> 64), lo = (uint64_t)x;
    unsigned __int128 result = ((unsigned __int128)hi << 32) - hi + lo;
    uint64_t hi2 = (uint64_t)(result >> 64), lo2 = (uint64_t)result;
    uint64_t r = ((unsigned __int128)hi2 << 32) - hi2 + lo2;
    return r >= GOLDI_P ? r - GOLDI_P : r;
}

/* ══════ Variant C: Fold with halves (all uint64_t, no overflow) ══════
   Decomposes hi into hh (top 32) and hl (bottom 32).
   x mod p ≡ (lo - hh) + hl*(2^32-1).
   This is the variant used by lowerGoldilocksProductReduce (Stmt path). */
static inline uint64_t fold_halves(unsigned __int128 x) {
    uint64_t hi = (uint64_t)(x >> 64), lo = (uint64_t)x;
    uint64_t hh = hi >> 32, hl = hi & 0xFFFFFFFF;
    /* t0 = lo - hh (with borrow handling) */
    uint64_t t0;
    int borrow = __builtin_sub_overflow(lo, hh, &t0);
    if (borrow) t0 -= GOLDI_C;  /* 2^64 + lo - hh - (2^32-1) = p + lo - hh */
    /* t1 = hl * (2^32-1): hl < 2^32 so t1 < 2^64 */
    uint64_t t1 = hl * GOLDI_C;
    /* r = t0 + t1 (with carry handling) */
    uint64_t r;
    int carry = __builtin_add_overflow(t0, t1, &r);
    if (carry || r >= GOLDI_P) r -= GOLDI_P;
    return r;
}

/* ══════ Variant D: NEON 2-lane Karatsuba (3 × vmull_u32) ══════
   Goldilocks multiply: a*b mod p using Karatsuba with φ=2^32.
   a = a0 + a1·φ, b = b0 + b1·φ (32-bit halves).
   p0 = a0·b0, p2 = a1·b1, p1 = (a0+a1)·(b0+b1)
   result = p0 - p2 + (p1 - p0)·φ (mod p, using φ²≡φ-1). */
static inline uint64x2_t goldi_mul_neon(uint64x2_t a, uint64x2_t b) {
    /* Split into 32-bit halves */
    uint32x2_t a0 = vmovn_u64(a);           /* low 32 bits */
    uint32x2_t a1 = vshrn_n_u64(a, 32);     /* high 32 bits */
    uint32x2_t b0 = vmovn_u64(b);
    uint32x2_t b1 = vshrn_n_u64(b, 32);
    /* 3 widening multiplies (Karatsuba) */
    uint64x2_t p0 = vmull_u32(a0, b0);      /* a0·b0 */
    uint64x2_t p2 = vmull_u32(a1, b1);      /* a1·b1 */
    uint32x2_t a01 = vadd_u32(a0, a1);
    uint32x2_t b01 = vadd_u32(b0, b1);
    uint64x2_t p1 = vmull_u32(a01, b01);    /* (a0+a1)·(b0+b1) */
    /* Recombine: result = p0 + (p1 - p0 - p2)·φ - p2·(φ²-φ+1-1)
       Since φ²≡φ-1 (mod p): result ≡ p0 - p2 + (p1 - p0)·φ (mod p)
       This needs scalar reduction — just measure the NEON multiply part. */
    /* For benchmarking: return p0 XOR p1 XOR p2 to prevent dead-code elimination */
    return veorq_u64(veorq_u64(p0, p1), p2);
}

static double elapsed_ns(struct timespec *t0, struct timespec *t1) {
    return (t1->tv_sec - t0->tv_sec) * 1e9 + (t1->tv_nsec - t0->tv_nsec);
}

int main(void) {
    const int N = 10000000;
    /* Setup: deterministic inputs in [0, p) */
    uint64_t a_val = 0x123456789ABCULL;
    uint64_t b_val = 0xFEDCBA987654ULL;
    unsigned __int128 product = (unsigned __int128)a_val * b_val;
    struct timespec t0, t1;
    volatile uint64_t sink;

    /* ── Warmup ── */
    for (int i = 0; i < 1000; i++) {
        sink = fold_halves(product);
        product = (unsigned __int128)sink * b_val;
    }
    product = (unsigned __int128)a_val * b_val; /* reset */

    /* ── Benchmark fold_mul ── */
    unsigned __int128 prod = product;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        sink = fold_mul(prod);
        prod = (unsigned __int128)sink * b_val;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double mul_ns = elapsed_ns(&t0, &t1);

    /* ── Benchmark fold_shiftsub ── */
    prod = product;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        sink = fold_shiftsub(prod);
        prod = (unsigned __int128)sink * b_val;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double shiftsub_ns = elapsed_ns(&t0, &t1);

    /* ── Benchmark fold_halves ── */
    prod = product;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        sink = fold_halves(prod);
        prod = (unsigned __int128)sink * b_val;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double halves_ns = elapsed_ns(&t0, &t1);

    /* ── Benchmark NEON Karatsuba ── */
    uint64_t __attribute__((aligned(16))) neon_a[2] = {a_val, a_val + 1};
    uint64_t __attribute__((aligned(16))) neon_b[2] = {b_val, b_val + 1};
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        uint64x2_t va = vld1q_u64(neon_a);
        uint64x2_t vb = vld1q_u64(neon_b);
        uint64x2_t vr = goldi_mul_neon(va, vb);
        vst1q_u64(neon_a, vr);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    sink = neon_a[0];
    double neon_ns = elapsed_ns(&t0, &t1);

    (void)sink;
    printf("# Goldilocks Isolated Fold Microbenchmark (N=%d)\n", N);
    printf("#\n");
    printf("# Variant          ns/call   ns/elem\n");
    printf("fold_mul:        %8.2f  %8.2f\n", mul_ns/N, mul_ns/N);
    printf("fold_shiftsub:   %8.2f  %8.2f\n", shiftsub_ns/N, shiftsub_ns/N);
    printf("fold_halves:     %8.2f  %8.2f\n", halves_ns/N, halves_ns/N);
    printf("neon_karatsuba:  %8.2f  %8.2f  (2 lanes)\n", neon_ns/N, neon_ns/(N*2));
    printf("#\n");
    printf("# Ratios vs fold_halves (baseline):\n");
    printf("fold_mul/halves:      %.2fx\n", mul_ns / halves_ns);
    printf("fold_shiftsub/halves: %.2fx\n", shiftsub_ns / halves_ns);
    printf("neon_karat/halves:    %.2fx\n", neon_ns / halves_ns);
    printf("#\n");
    printf("# CSV: variant,ns_call,ns_elem\n");
    printf("# fold_mul,%.2f,%.2f\n", mul_ns/N, mul_ns/N);
    printf("# fold_shiftsub,%.2f,%.2f\n", shiftsub_ns/N, shiftsub_ns/N);
    printf("# fold_halves,%.2f,%.2f\n", halves_ns/N, halves_ns/N);
    printf("# neon_karatsuba,%.2f,%.2f\n", neon_ns/N, neon_ns/(N*2));
    return 0;
}
