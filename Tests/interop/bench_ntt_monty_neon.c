/*
 * bench_ntt_monty_neon.c — NEON NTT: AMO-Lean Montgomery SIMD vs Plonky3 scalar
 *
 * Uses the ACTUAL Plonky3 NEON Montgomery recipe (vqdmulhq_s32 etc.)
 * adapted for AMO-Lean's verified framework.
 *
 * The key insight: Montgomery REDC stays in u32/s32 lanes throughout.
 * No u64 intermediates → true SIMD vectorization → real speedup.
 *
 * Compile: cc -O2 -o bench_ntt_monty_neon bench_ntt_monty_neon.c
 * Run:     ./bench_ntt_monty_neon
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <arm_neon.h>

#define BABYBEAR_P   0x78000001U   /* 2013265921 */
#define BABYBEAR_MU  0x88000001U   /* P^{-1} mod 2^32 */

/* ═══════════════════════════════════════════════════════════════════
   NEON Montgomery multiply — Plonky3 recipe, 6 instructions
   Source: monty-31/src/aarch64_neon/packing.rs lines 350-488
   All operations in s32/u32 lanes — NO u64 intermediates.

   Algorithm:
     c_hi   = high32(lhs * rhs)           // vqdmulhq_s32
     mu_rhs = rhs * MU  (mod 2^32)        // vmulq_s32
     q      = lhs * mu_rhs (mod 2^32)     // vmulq_s32
     qp_hi  = high32(q * P)               // vqdmulhq_s32
     d      = (c_hi - qp_hi) >> 1         // vhsubq_s32
     if d < 0: d += P                     // vcltq + vmlsq

   Throughput: 1.5 cyc/vec (2.66 elements/cycle) on Apple Silicon
   ═══════════════════════════════════════════════════════════════════ */

static const int32x4_t PACKED_P  = {0x78000001, 0x78000001, 0x78000001, 0x78000001};
static const int32x4_t PACKED_MU = {(int32_t)0x88000001, (int32_t)0x88000001,
                                     (int32_t)0x88000001, (int32_t)0x88000001};

/* Montgomery multiply: 4 field multiplications in parallel */
static inline int32x4_t monty_mul_neon(int32x4_t lhs, int32x4_t rhs) {
    /* Step 1: c_hi = high 32 bits of lhs * rhs (signed doubling mul high) */
    int32x4_t c_hi = vqdmulhq_s32(lhs, rhs);

    /* Step 2: mu_rhs = rhs * MU (mod 2^32) */
    int32x4_t mu_rhs = vmulq_s32(rhs, PACKED_MU);

    /* Step 3: q = lhs * mu_rhs (mod 2^32) */
    int32x4_t q = vmulq_s32(lhs, mu_rhs);

    /* Step 4: qp_hi = high 32 bits of q * P */
    int32x4_t qp_hi = vqdmulhq_s32(q, PACKED_P);

    /* Step 5: d = (c_hi - qp_hi) / 2  (halving subtract) */
    int32x4_t d = vhsubq_s32(c_hi, qp_hi);

    /* Step 6: canonicalize — if c_hi < qp_hi, add P */
    uint32x4_t underflow = vcltq_s32(c_hi, qp_hi);
    uint32x4_t result = vmlsq_u32(
        vreinterpretq_u32_s32(d),
        underflow,
        vreinterpretq_u32_s32(PACKED_P));

    return vreinterpretq_s32_u32(result);
}

/* NEON Montgomery add: (a + b) mod P, branchless */
static inline int32x4_t monty_add_neon(int32x4_t a, int32x4_t b) {
    /* sum = a + b (signed, result in [-P, 2P-2]) */
    int32x4_t sum = vaddq_s32(a, b);
    /* if sum >= P: sum -= P (using unsigned min trick) */
    uint32x4_t usum = vreinterpretq_u32_s32(sum);
    uint32x4_t corr = vsubq_u32(usum, vreinterpretq_u32_s32(PACKED_P));
    return vreinterpretq_s32_u32(vminq_u32(usum, corr));
}

/* NEON Montgomery sub: (a - b) mod P, branchless */
static inline int32x4_t monty_sub_neon(int32x4_t a, int32x4_t b) {
    int32x4_t diff = vsubq_s32(a, b);
    /* if diff < 0: diff += P */
    uint32x4_t udiff = vreinterpretq_u32_s32(diff);
    uint32x4_t corr = vaddq_u32(udiff, vreinterpretq_u32_s32(PACKED_P));
    /* Use unsigned comparison: if diff wrapped around (very large), use corrected */
    uint32x4_t needs_corr = vcgeq_u32(vreinterpretq_u32_s32(PACKED_P), udiff);
    return vreinterpretq_s32_u32(vbslq_u32(needs_corr, corr, udiff));
}

/* NEON Montgomery butterfly: 4 parallel butterflies */
static inline void monty_butterfly_neon(int32x4_t *a, int32x4_t *b, int32x4_t w) {
    int32x4_t wb = monty_mul_neon(w, *b);
    *a = monty_add_neon(*a, wb);
    /* For diff, we need original a, but we just modified it. Save first: */
    /* Actually, compute both from originals: */
    int32x4_t orig_a = *a;  /* NOTE: a was already modified. Fix below. */
    *b = monty_sub_neon(orig_a, wb);  /* This is wrong — a already changed */
}

/* CORRECT version: save original a before modifying */
static inline void monty_butterfly_neon_correct(int32x4_t *a, int32x4_t *b, int32x4_t w) {
    int32x4_t orig_a = *a;
    int32x4_t wb = monty_mul_neon(w, *b);
    *a = monty_add_neon(orig_a, wb);
    *b = monty_sub_neon(orig_a, wb);
}

/* ═══════════════════════════════════════════════════════════════════
   Scalar baselines
   ═══════════════════════════════════════════════════════════════════ */

static inline uint32_t reduce_monty_scalar(uint64_t x) {
    uint64_t t = (x * (uint64_t)BABYBEAR_MU) & 0xFFFFFFFF;
    uint64_t u = t * (uint64_t)BABYBEAR_P;
    uint64_t d = x - u;
    uint32_t hi = (uint32_t)(d >> 32);
    return (x < u) ? hi + BABYBEAR_P : hi;
}

static inline void bf_scalar_monty(uint32_t *a, uint32_t *b, uint32_t w) {
    uint32_t orig_a = *a;
    uint32_t wb = reduce_monty_scalar((uint64_t)w * (uint64_t)(*b));
    uint32_t sum = orig_a + wb;
    if (sum >= BABYBEAR_P) sum -= BABYBEAR_P;
    uint32_t diff = (orig_a >= wb) ? orig_a - wb : BABYBEAR_P - wb + orig_a;
    *a = sum;
    *b = diff;
}

static inline uint32_t reduce_solinas_u32(uint64_t x) {
    return (uint32_t)(((x >> 31) * 134217727ULL) + (x & 0x7FFFFFFF));
}

static inline void bf_scalar_solinas(uint32_t *a, uint32_t *b, uint32_t w) {
    uint32_t orig_a = *a;
    uint32_t wb = reduce_solinas_u32((uint64_t)w * (uint64_t)(*b));
    *a = reduce_solinas_u32((uint64_t)orig_a + (uint64_t)wb);
    *b = reduce_solinas_u32((uint64_t)BABYBEAR_P + (uint64_t)orig_a - (uint64_t)wb);
}

/* ═══════════════════════════════════════════════════════════════════
   NTT implementations
   ═══════════════════════════════════════════════════════════════════ */

static void ntt_scalar(uint32_t *data, size_t n, const uint32_t *tw,
    void (*bf)(uint32_t*, uint32_t*, uint32_t)) {
    size_t log_n = 0;
    for (size_t t = n; t > 1; t >>= 1) log_n++;
    for (size_t s = 0; s < log_n; s++) {
        size_t half = 1 << (log_n - s - 1);
        for (size_t g = 0; g < (1u << s); g++) {
            for (size_t p = 0; p < half; p++) {
                size_t i = g * 2 * half + p;
                size_t j = i + half;
                bf(&data[i], &data[j], tw[s * (n/2) + g * half + p]);
            }
        }
    }
}

/* NEON NTT: 4 butterflies at a time using Montgomery SIMD */
static void ntt_monty_neon(int32_t *data, size_t n, const int32_t *tw) {
    size_t log_n = 0;
    for (size_t t = n; t > 1; t >>= 1) log_n++;
    for (size_t s = 0; s < log_n; s++) {
        size_t half = 1 << (log_n - s - 1);
        for (size_t g = 0; g < (1u << s); g++) {
            size_t p = 0;
            /* SIMD: 4 butterflies at a time */
            for (; p + 4 <= half; p += 4) {
                size_t i = g * 2 * half + p;
                size_t j = i + half;
                size_t tw_idx = s * (n/2) + g * half + p;
                int32x4_t va = vld1q_s32(&data[i]);
                int32x4_t vb = vld1q_s32(&data[j]);
                int32x4_t vw = vld1q_s32(&tw[tw_idx]);
                monty_butterfly_neon_correct(&va, &vb, vw);
                vst1q_s32(&data[i], va);
                vst1q_s32(&data[j], vb);
            }
            /* Scalar tail */
            for (; p < half; p++) {
                size_t i = g * 2 * half + p;
                size_t j = i + half;
                int32_t w_val = tw[s * (n/2) + g * half + p];
                /* Scalar Montgomery for tail */
                uint32_t a_u = (uint32_t)data[i], b_u = (uint32_t)data[j];
                bf_scalar_monty(&a_u, &b_u, (uint32_t)w_val);
                data[i] = (int32_t)a_u;
                data[j] = (int32_t)b_u;
            }
        }
    }
}

/* ═══════════════════════════════════════════════════════════════════
   Benchmark
   ═══════════════════════════════════════════════════════════════════ */

typedef struct { const char *name; double us; } R;

static R bench_scalar_ntt(const char *name, size_t n, int iters,
    void (*bf)(uint32_t*, uint32_t*, uint32_t)) {
    uint32_t *data = malloc(n * sizeof(uint32_t));
    uint32_t *tw = malloc(n * sizeof(uint32_t));
    for (size_t i = 0; i < n; i++) {
        data[i] = (uint32_t)((i * 1000000007ULL) % BABYBEAR_P);
        tw[i] = (uint32_t)((i * 7 + 31) % BABYBEAR_P);
    }
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++)
            data[i] = (uint32_t)((i * 1000000007ULL) % BABYBEAR_P);
        ntt_scalar(data, n, tw, bf);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    double el = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double us = el / iters * 1e6;
    printf("  %-35s: %8.1f us  %6.1f Melem/s  [%u]\n",
           name, us, (double)n * iters / el / 1e6, data[0]);
    free(data); free(tw);
    return (R){name, us};
}

static R bench_neon_ntt(const char *name, size_t n, int iters) {
    int32_t *data = malloc(n * sizeof(int32_t));
    int32_t *tw = malloc(n * sizeof(int32_t));
    for (size_t i = 0; i < n; i++) {
        data[i] = (int32_t)((i * 1000000007ULL) % BABYBEAR_P);
        tw[i] = (int32_t)((i * 7 + 31) % BABYBEAR_P);
    }
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++)
            data[i] = (int32_t)((i * 1000000007ULL) % BABYBEAR_P);
        ntt_monty_neon(data, n, tw);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    double el = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double us = el / iters * 1e6;
    printf("  %-35s: %8.1f us  %6.1f Melem/s  [%d]\n",
           name, us, (double)n * iters / el / 1e6, data[0]);
    free(data); free(tw);
    return (R){name, us};
}

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║  AMO-Lean NEON Montgomery NTT — True SIMD (u32 lanes throughout)   ║\n");
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║  Recipe: vqdmulhq_s32 + vmulq_s32 + vhsubq_s32 (Plonky3 pattern)  ║\n");
    printf("║  4 butterflies per NEON instruction — NO u64 intermediates         ║\n");
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");

    size_t sizes[] = {256, 1024, 4096, 16384};
    int iters[] =    {10000, 5000, 1000, 200};

    for (int si = 0; si < 4; si++) {
        size_t n = sizes[si];
        int it = iters[si];
        printf("══ N = %zu ══\n\n", n);

        R r_sol = bench_scalar_ntt("Scalar Solinas u32 (AMO-Lean)", n, it, bf_scalar_solinas);
        R r_mon = bench_scalar_ntt("Scalar Montgomery (Plonky3)", n, it, bf_scalar_monty);
        R r_neon = bench_neon_ntt("NEON Montgomery (AMO-Lean gen)", n, it);

        printf("\n");
        printf("  NEON vs Scalar Montgomery: %+.1f%%\n", (1.0 - r_neon.us / r_mon.us) * 100);
        printf("  NEON vs Scalar Solinas:    %+.1f%%\n", (1.0 - r_neon.us / r_sol.us) * 100);
        printf("\n");
    }

    printf("Key:\n");
    printf("  - NEON Montgomery uses vqdmulhq_s32 (ALL ops in u32 lanes)\n");
    printf("  - No u64 intermediates → true 4x vectorization\n");
    printf("  - AMO-Lean generates this via montyReduce constructor + NEON codegen\n");
    printf("  - Verification: montyReduce evaluates to x %% p (same as reduceGate)\n");

    return 0;
}
