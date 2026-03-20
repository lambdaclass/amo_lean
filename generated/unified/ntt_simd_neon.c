/* AMO-Lean Unified CodeGen — ALL decisions from e-graph cost model
 * N = 4096, p = 2013265921
 * Mode: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ExecMode.simdNEON (from isSimd=true, lanes=4)
 * Reduction: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ReductionStrategy.montgomery (from wideningPenalty=8)
 * Word size: u32 (from field bit width)
 * Backend: C (NEON SIMD)
 *
 * NOT hardcoded — change HardwareCost to get different code.
 * Verification: solinasFold_mod_correct / montyReduce evaluates to x %% p
 */

#include <arm_neon.h>
#include <stdint.h>
#include <stddef.h>

static const int32x4_t v_p = {2013265921, 2013265921, 2013265921, 2013265921};
static const int32x4_t v_mu = {(int32_t)0x88000001, (int32_t)0x88000001, (int32_t)0x88000001, (int32_t)0x88000001};

static inline void butterfly(int32x4_t *a, int32x4_t *b, int32x4_t w) {
    int32x4_t orig_a = *a;
    int32x4_t wb = vmulq_s32(w, *b);
    int32x4_t mu_rhs = vmulq_s32(*b, v_mu);
    int32x4_t c_hi = vqdmulhq_s32(orig_a, wb);
    int32x4_t q = vmulq_s32(orig_a, mu_rhs);
    int32x4_t qp_hi = vqdmulhq_s32(q, v_p);
    int32x4_t d = vhsubq_s32(c_hi, qp_hi);
    uint32x4_t uf = vcltq_s32(c_hi, qp_hi);
    int32x4_t wb_red = vreinterpretq_s32_u32(
        vmlsq_u32(vreinterpretq_u32_s32(d), uf, vreinterpretq_u32_s32(v_p)));
    int32x4_t sum = vaddq_s32(orig_a, wb_red);
    uint32x4_t su = vreinterpretq_u32_s32(sum);
    *a = vreinterpretq_s32_u32(vminq_u32(su, vsubq_u32(su, vreinterpretq_u32_s32(v_p))));
    int32x4_t dif = vsubq_s32(orig_a, wb_red);
    uint32x4_t du = vreinterpretq_u32_s32(dif);
    *b = vreinterpretq_s32_u32(vminq_u32(du, vaddq_u32(du, vreinterpretq_u32_s32(v_p))));
}
void ntt_simd_neon(int32_t *data, size_t n, const int32_t *twiddles) {
    size_t log_n = 12;
    for (size_t stage = 0; stage < log_n; stage++) {
        size_t half = 1 << (log_n - stage - 1);
        for (size_t group = 0; group < (1u << stage); group++) {
            for (size_t pair = 0; pair < half; pair += 4) {
                size_t i = group * 2 * half + pair;
                size_t j = i + half;
                size_t tw_idx = stage * (n / 2) + group * half + pair;
                int32x4_t va = vld1q_s32(&data[i]);
                int32x4_t vb = vld1q_s32(&data[j]);
                int32x4_t vw = vld1q_s32(&twiddles[tw_idx]);
                butterfly(&va, &vb, vw);
                vst1q_s32(&data[i], va);
                vst1q_s32(&data[j], vb);
            }
        }
    }
}
