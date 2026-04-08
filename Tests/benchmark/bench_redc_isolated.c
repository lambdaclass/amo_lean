/*
 * Isolated REDC Microbenchmark: vmull widening vs sqdmulh Montgomery
 * Measures ONLY the REDC product reduction, without butterfly sum/diff or loop overhead.
 * B35-2: Calibration data for InstructionProfile model.
 */
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>

#define P 2013265921U
#define MU 0x88000001U

/* ══════════ REDC vmull widening (current, 2-lane) ══════════ */
static inline int32x4_t redc_vmull(int32x4_t b, int32x4_t tw,
    uint32x4_t p_vec, uint32x4_t mu_vec) {
    uint32x2_t b_lo = vget_low_u32(vreinterpretq_u32_s32(b));
    uint32x2_t b_hi = vget_high_u32(vreinterpretq_u32_s32(b));
    uint32x2_t w_lo = vget_low_u32(vreinterpretq_u32_s32(tw));
    uint32x2_t w_hi = vget_high_u32(vreinterpretq_u32_s32(tw));
    uint64x2_t prod_lo = vmull_u32(w_lo, b_lo);
    uint64x2_t prod_hi = vmull_u32(w_hi, b_hi);
    uint32x2_t tl_lo = vmovn_u64(prod_lo);
    uint32x2_t tl_hi = vmovn_u64(prod_hi);
    uint32x2_t mu_lo_v = vget_low_u32(mu_vec);
    uint32x2_t mu_hi_v = vget_high_u32(mu_vec);
    uint32x2_t m_lo = vmul_u32(tl_lo, mu_lo_v);
    uint32x2_t m_hi = vmul_u32(tl_hi, mu_hi_v);
    uint32x2_t p_lo = vget_low_u32(p_vec);
    uint32x2_t p_hi = vget_high_u32(p_vec);
    uint64x2_t u_lo = vmull_u32(m_lo, p_lo);
    uint64x2_t u_hi = vmull_u32(m_hi, p_hi);
    int64x2_t d_lo = vsubq_s64(vreinterpretq_s64_u64(prod_lo), vreinterpretq_s64_u64(u_lo));
    int64x2_t d_hi = vsubq_s64(vreinterpretq_s64_u64(prod_hi), vreinterpretq_s64_u64(u_hi));
    int32x2_t q_lo = vshrn_n_s64(d_lo, 32);
    int32x2_t q_hi = vshrn_n_s64(d_hi, 32);
    int32x4_t q = vcombine_s32(q_lo, q_hi);
    uint64x2_t lt_lo = vcltq_u64(prod_lo, u_lo);
    uint64x2_t lt_hi = vcltq_u64(prod_hi, u_hi);
    uint32x2_t lt32_lo = vmovn_u64(lt_lo);
    uint32x2_t lt32_hi = vmovn_u64(lt_hi);
    uint32x4_t fixup = vandq_u32(vcombine_u32(lt32_lo, lt32_hi), p_vec);
    int32x4_t wb_red = vaddq_s32(q, vreinterpretq_s32_u32(fixup));
    return wb_red;
}

/* ══════════ REDC sqdmulh Montgomery (new, 4-lane) ═════���════ */
static inline int32x4_t redc_sqdmulh(int32x4_t b, int32x4_t tw,
    int32x4_t mu_tw, int32x4_t p_vec_s, uint32x4_t p_vec) {
    int32x4_t c_hi  = vqdmulhq_s32(tw, b);
    int32x4_t q     = vmulq_s32(b, mu_tw);
    int32x4_t qp_hi = vqdmulhq_s32(q, p_vec_s);
    int32x4_t d     = vhsubq_s32(c_hi, qp_hi);
    uint32x4_t uf   = vcltq_s32(c_hi, qp_hi);
    int32x4_t wb    = vreinterpretq_s32_u32(
        vmlsq_u32(vreinterpretq_u32_s32(d), uf, p_vec));
    return wb;
}

static double elapsed_ns(struct timespec *t0, struct timespec *t1) {
    return (t1->tv_sec - t0->tv_sec) * 1e9 + (t1->tv_nsec - t0->tv_nsec);
}

int main(void) {
    const int N = 10000000;
    int32_t __attribute__((aligned(16)))data_a[4] = {100, 200, 300, 400};
    int32_t __attribute__((aligned(16)))data_b[4] = {500, 600, 700, 800};
    int32_t __attribute__((aligned(16)))tw_vals[4] = {12345, 23456, 34567, 45678};
    /* mu_tw = tw * MU mod 2^32 */
    int32_t __attribute__((aligned(16)))mu_tw_vals[4];
    for (int i = 0; i < 4; i++)
        mu_tw_vals[i] = (int32_t)(((uint64_t)(uint32_t)tw_vals[i] * (uint64_t)MU) & 0xFFFFFFFFULL);

    uint32x4_t p_vec = vdupq_n_u32(P);
    uint32x4_t mu_vec = vdupq_n_u32(MU);
    int32x4_t p_vec_s = vdupq_n_s32((int32_t)P);
    int32x4_t mu_tw_v = vld1q_s32(mu_tw_vals);

    struct timespec t0, t1;
    volatile int32_t sink;

    /* ── Warmup ── */
    for (int i = 0; i < 1000; i++) {
        int32x4_t b = vld1q_s32(data_b);
        int32x4_t w = vld1q_s32(tw_vals);
        int32x4_t r = redc_vmull(b, w, p_vec, mu_vec);
        vst1q_s32(data_b, r);
    }
    data_b[0]=500; data_b[1]=600; data_b[2]=700; data_b[3]=800;

    /* ── Benchmark vmull ── */
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        int32x4_t b = vld1q_s32(data_b);
        int32x4_t w = vld1q_s32(tw_vals);
        int32x4_t r = redc_vmull(b, w, p_vec, mu_vec);
        vst1q_s32(data_b, r);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    sink = data_b[0];
    double vmull_ns = elapsed_ns(&t0, &t1);

    /* Reset */
    data_b[0]=500; data_b[1]=600; data_b[2]=700; data_b[3]=800;

    /* ── Benchmark sqdmulh ── */
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) {
        int32x4_t b = vld1q_s32(data_b);
        int32x4_t w = vld1q_s32(tw_vals);
        int32x4_t r = redc_sqdmulh(b, w, mu_tw_v, p_vec_s, p_vec);
        vst1q_s32(data_b, r);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    sink = data_b[0];
    double sqdmulh_ns = elapsed_ns(&t0, &t1);

    (void)sink;
    printf("# Isolated REDC Microbenchmark (N=%d iterations, 4 elements each)\n", N);
    printf("vmull:   %.2f ns/call  (%.2f ns/element)\n", vmull_ns/N, vmull_ns/(N*4));
    printf("sqdmulh: %.2f ns/call  (%.2f ns/element)\n", sqdmulh_ns/N, sqdmulh_ns/(N*4));
    printf("Ratio vmull/sqdmulh: %.2fx\n", vmull_ns / sqdmulh_ns);
    printf("# redc_vmull,%.2f,%.2f\n", vmull_ns/N, vmull_ns/(N*4));
    printf("# redc_sqdmulh,%.2f,%.2f\n", sqdmulh_ns/N, sqdmulh_ns/(N*4));
    return 0;
}
