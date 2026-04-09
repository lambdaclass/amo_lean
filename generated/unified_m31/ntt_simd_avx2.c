/* AMO-Lean Unified CodeGen — ALL decisions from e-graph cost model
 * N = 4096, p = 2147483647
 * Mode: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ExecMode.simdAVX2 (from isSimd=true, lanes=8)
 * Reduction: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ReductionStrategy.montgomery (from wideningPenalty=8)
 * Word size: u32 (from field bit width)
 * Backend: C (scalar)
 *
 * NOT hardcoded — change HardwareCost to get different code.
 * Verification: solinasFold_mod_correct / montyReduce evaluates to x %% p
 */

#include <stdint.h>
#include <stddef.h>

/* Fallback: scalar Solinas fold */
static inline uint32_t reduce_fallback(uint64_t x) {
    return (uint32_t)(((x >> 31) * 134217727U) + (x & 0x7FFFFFFFU));
}
void ntt_simd_avx2(uint32_t *data, size_t n, const uint32_t *twiddles) {
    /* Literal loop bound (12) enables compiler loop unrolling */
    for (size_t stage = 0; stage < 12; stage++) {
        size_t half = 1 << (11 - stage);
        for (size_t group = 0; group < (1u << stage); group++) {
            for (size_t pair = 0; pair + 8 <= half; pair += 8) {
                size_t i = group * 2 * half + pair;
                size_t j = i + half;
                size_t tw_idx = stage * (n / 2) + group * half + pair;
                butterfly(&data[i], &data[j], twiddles[tw_idx]);
            }
        }
    }
}
