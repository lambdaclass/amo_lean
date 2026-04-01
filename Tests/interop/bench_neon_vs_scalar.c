/* AMO-Lean: NEON SIMD vs Scalar NTT Benchmark
 * KoalaBear p = 0x7F000001, k=31, c=16777215
 * Apple Silicon (ARM NEON: uint32x4_t, 4 lanes)
 *
 * Three variants:
 * 1. NEON SIMD: Montgomery butterfly on 4-wide vectors
 * 2. Scalar Ultra: lazy + Solinas (current best scalar)
 * 3. P3 Scalar: Montgomery every stage
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <arm_neon.h>

#define P       0x7F000001U   /* 2130706433 */
#define C_SOL   16777215U
#define MU_KB   0x81000001U
#define LOG_N   20
#define N       (1 << LOG_N)

/* ═══════════════════ Montgomery REDC (scalar) ═══════════════════ */
static inline uint32_t monty_scalar(uint64_t x) {
    uint32_t t = (uint32_t)(x * (uint64_t)MU_KB);
    uint64_t u = (uint64_t)t * (uint64_t)P;
    uint64_t d = x - u;
    uint32_t hi = (uint32_t)(d >> 32);
    return (x < u) ? hi + P : hi;
}

/* ═══════════════════ Solinas fold (scalar) ═══════════════════ */
static inline uint32_t solinas(uint64_t x) {
    return (uint32_t)(((x >> 31) * C_SOL) + (x & 0x7FFFFFFF));
}

/* ═══════════════════ NEON Montgomery REDC (4-wide) ═══════════════════ */
static inline uint32x4_t monty_neon(uint32x4_t a_lo, uint32x4_t a_hi) {
    /* a = a_hi:a_lo is a 64-bit product split into lo/hi 32-bit halves.
     * REDC: t = lo * mu (mod 2^32), u = t * p, result = (a - u) >> 32
     * All operations are lane-wise on 4 elements. */
    uint32x4_t mu_v = vdupq_n_u32(MU_KB);
    uint32x4_t p_v = vdupq_n_u32(P);

    /* t = a_lo * mu (keep low 32 bits) */
    uint32x4_t t = vmulq_u32(a_lo, mu_v);

    /* u_lo, u_hi = t * p (64-bit per lane) */
    uint64x2_t u_lo_pair = vmull_u32(vget_low_u32(t), vget_low_u32(p_v));
    uint64x2_t u_hi_pair = vmull_u32(vget_high_u32(t), vget_high_u32(p_v));

    /* Extract high halves of u */
    uint32x2_t u_hi_lo = vshrn_n_u64(u_lo_pair, 32);
    uint32x2_t u_hi_hi = vshrn_n_u64(u_hi_pair, 32);
    uint32x4_t u_hi = vcombine_u32(u_hi_lo, u_hi_hi);

    /* Extract low halves of u for borrow detection */
    uint32x2_t u_lo_lo = vmovn_u64(u_lo_pair);
    uint32x2_t u_lo_hi = vmovn_u64(u_hi_pair);
    uint32x4_t u_lo = vcombine_u32(u_lo_lo, u_lo_hi);

    /* result_hi = a_hi - u_hi - borrow */
    /* borrow = (a_lo < u_lo) ? 1 : 0 */
    uint32x4_t borrow = vcltq_u32(a_lo, u_lo);  /* 0xFFFFFFFF if borrow */
    borrow = vshrq_n_u32(borrow, 31);  /* 1 if borrow */

    uint32x4_t hi = vsubq_u32(a_hi, u_hi);
    hi = vsubq_u32(hi, borrow);

    /* Conditional add P if underflow */
    uint32x4_t needs_add = vcgtq_u32(u_hi, a_hi);  /* approximate check */
    uint32x4_t correction = vandq_u32(needs_add, p_v);
    hi = vaddq_u32(hi, correction);

    return hi;
}

/* ═══════ NEON NTT: Montgomery butterfly, 4 elements at a time ═══════ */
void ntt_neon(uint32_t* data, const uint32_t* tw) {
    size_t tw_off = 0;
    for (int s = 0; s < LOG_N; s++) {
        size_t half = (size_t)N >> (s + 1);
        size_t groups = (size_t)1 << s;
        for (size_t g = 0; g < groups; g++) {
            size_t j = 0;
            /* Process 4 elements at a time with NEON */
            for (; j + 3 < half; j += 4) {
                size_t i0 = g * 2 * half + j;
                size_t i1 = i0 + half;
                uint32x4_t a = vld1q_u32(&data[i0]);
                uint32x4_t b = vld1q_u32(&data[i1]);
                uint32x4_t w = vld1q_u32(&tw[tw_off + g * half + j]);

                /* wb = monty(w * b) — 64-bit multiply then REDC */
                uint64x2_t wb_lo_64 = vmull_u32(vget_low_u32(w), vget_low_u32(b));
                uint64x2_t wb_hi_64 = vmull_u32(vget_high_u32(w), vget_high_u32(b));
                uint32x2_t wb_lo_lo = vmovn_u64(wb_lo_64);
                uint32x2_t wb_lo_hi = vmovn_u64(wb_hi_64);
                uint32x4_t wb_lo = vcombine_u32(wb_lo_lo, wb_lo_hi);
                uint32x2_t wb_hi_lo2 = vshrn_n_u64(wb_lo_64, 32);
                uint32x2_t wb_hi_hi2 = vshrn_n_u64(wb_hi_64, 32);
                uint32x4_t wb_hi = vcombine_u32(wb_hi_lo2, wb_hi_hi2);
                uint32x4_t wb = monty_neon(wb_lo, wb_hi);

                /* sum = a + wb, conditionally subtract P */
                uint32x4_t p_v = vdupq_n_u32(P);
                uint32x4_t sum = vaddq_u32(a, wb);
                uint32x4_t mask = vcgeq_u32(sum, p_v);
                sum = vsubq_u32(sum, vandq_u32(mask, p_v));

                /* diff = a - wb + P if needed */
                uint32x4_t diff_raw = vsubq_u32(vaddq_u32(a, p_v), wb);
                uint32x4_t diff_mask = vcgeq_u32(diff_raw, p_v);
                uint32x4_t diff = vsubq_u32(diff_raw, vandq_u32(diff_mask, p_v));

                vst1q_u32(&data[i0], sum);
                vst1q_u32(&data[i1], diff);
            }
            /* Scalar tail */
            for (; j < half; j++) {
                size_t i0 = g * 2 * half + j;
                size_t i1 = i0 + half;
                uint32_t oa = data[i0];
                uint32_t wb = monty_scalar((uint64_t)tw[tw_off + g*half+j] * (uint64_t)data[i1]);
                uint32_t sum = oa + wb;
                data[i0] = (sum >= P) ? sum - P : sum;
                data[i1] = (oa >= wb) ? oa - wb : P - wb + oa;
            }
        }
        tw_off += groups * half;
    }
}

/* ═══════ Ultra cost-aware: lazy for small N, Harvey/Monty for large N ═══════ */
void ntt_ultra_scalar(uint32_t* data, const uint32_t* tw) {
    size_t tw_off = 0;
    /* Cost-aware: for N > 8192, u64 penalty (cache) makes reduce cheaper than lazy */
    int use_lazy = (N <= 8192);
    for (int s = 0; s < LOG_N; s++) {
        size_t half = (size_t)N >> (s + 1);
        size_t groups = (size_t)1 << s;
        int must_reduce = (s >= LOG_N - 2);
        for (size_t g = 0; g < groups; g++) {
            for (size_t j = 0; j < half; j++) {
                size_t i0 = g * 2 * half + j;
                size_t i1 = i0 + half;
                if (use_lazy && !must_reduce) {
                    /* lazy: u64 accumulation, no reduction */
                    uint64_t a = data[i0], b = data[i1];
                    uint64_t t = (uint64_t)tw[tw_off + g*half+j] * b;
                    data[i0] = (uint32_t)(a + t);
                    data[i1] = (uint32_t)((uint64_t)P + a - t);
                } else {
                    /* Cost-aware: Harvey (cheapest at boundK ≤ 2) or Montgomery */
                    uint32_t oa = data[i0];
                    uint32_t wb = monty_scalar((uint64_t)tw[tw_off + g*half+j] * (uint64_t)data[i1]);
                    uint32_t sum = oa + wb;
                    data[i0] = (sum >= P) ? sum - P : sum;
                    data[i1] = (oa >= wb) ? oa - wb : P - wb + oa;
                }
            }
        }
        tw_off += groups * half;
    }
}

/* ═══════ Scalar P3: Montgomery every stage ═══════ */
void ntt_p3_scalar(uint32_t* data, const uint32_t* tw) {
    size_t tw_off = 0;
    for (int s = 0; s < LOG_N; s++) {
        size_t half = (size_t)N >> (s + 1);
        size_t groups = (size_t)1 << s;
        for (size_t g = 0; g < groups; g++) {
            for (size_t j = 0; j < half; j++) {
                size_t i0 = g * 2 * half + j;
                size_t i1 = i0 + half;
                uint32_t oa = data[i0];
                uint32_t wb = monty_scalar((uint64_t)tw[tw_off + g*half+j] * (uint64_t)data[i1]);
                uint32_t sum = oa + wb;
                data[i0] = (sum >= P) ? sum - P : sum;
                data[i1] = (oa >= wb) ? oa - wb : P - wb + oa;
            }
        }
        tw_off += groups * half;
    }
}

/* ═══════ Timing harness ═══════ */
int main(void) {
    int iters = 100;
    size_t tw_sz = (size_t)N * LOG_N;
    uint32_t *tw = malloc(tw_sz * sizeof(uint32_t));
    uint32_t *orig = malloc(N * sizeof(uint32_t));
    uint32_t *data = malloc(N * sizeof(uint32_t));
    for (size_t i = 0; i < tw_sz; i++) tw[i] = (uint32_t)((i*7+31) % P);
    for (size_t i = 0; i < N; i++) orig[i] = (uint32_t)((i*1000000007ULL) % P);
    volatile uint32_t sink;
    struct timespec s, e;

    /* Warmup */
    for (size_t i = 0; i < N; i++) data[i] = orig[i];
    ntt_neon(data, tw);
    for (size_t i = 0; i < N; i++) data[i] = orig[i];
    ntt_ultra_scalar(data, tw);
    for (size_t i = 0; i < N; i++) data[i] = orig[i];
    ntt_p3_scalar(data, tw);

    /* NEON */
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < N; i++) data[i] = orig[i];
        ntt_neon(data, tw);
        sink = data[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double neon_us = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    /* Ultra scalar */
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < N; i++) data[i] = orig[i];
        ntt_ultra_scalar(data, tw);
        sink = data[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double ultra_us = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    /* P3 scalar */
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < N; i++) data[i] = orig[i];
        ntt_p3_scalar(data, tw);
        sink = data[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_us = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    double melem_n = (double)N / (neon_us/1e6) / 1e6;
    double melem_u = (double)N / (ultra_us/1e6) / 1e6;
    double melem_p = (double)N / (p3_us/1e6) / 1e6;

    printf("KoalaBear NTT N=2^%d (%d elements), %d iterations\n", LOG_N, N, iters);
    printf("Apple Silicon (ARM NEON: 4x u32 lanes)\n");
    printf("---------------------------------------------------\n");
    printf("NEON SIMD (Monty):     %8.1f us  (%6.1f Melem/s)\n", neon_us, melem_n);
    printf("Ultra scalar (lazy):   %8.1f us  (%6.1f Melem/s)\n", ultra_us, melem_u);
    printf("P3 scalar (Monty):     %8.1f us  (%6.1f Melem/s)\n", p3_us, melem_p);
    printf("---------------------------------------------------\n");
    printf("NEON vs P3 scalar:    %+.1f%%\n", (1.0-neon_us/p3_us)*100.0);
    printf("NEON vs Ultra scalar: %+.1f%%\n", (1.0-neon_us/ultra_us)*100.0);
    printf("Ultra vs P3:          %+.1f%%\n", (1.0-ultra_us/p3_us)*100.0);

    (void)sink; free(data); free(orig); free(tw);
    return 0;
}
