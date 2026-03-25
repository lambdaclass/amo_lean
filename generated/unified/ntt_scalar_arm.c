/* AMO-Lean Unified CodeGen — ALL decisions from e-graph cost model
 * N = 4096, p = 2013265921
 * Mode: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ExecMode.scalar (from isSimd=false, lanes=1)
 * Reduction: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ReductionStrategy.solinasFold (from wideningPenalty=0)
 * Word size: u32 (from field bit width)
 * Backend: C (scalar)
 *
 * NOT hardcoded — change HardwareCost to get different code.
 * Verification: solinasFold_mod_correct / montyReduce evaluates to x %% p
 */

#include <stdint.h>
#include <stddef.h>

static inline uint32_t solinas_fold(uint64_t x) {
    return (uint32_t)(((x >> 31) * 134217727U) + (x & 2147483647U));
}

static inline void butterfly(uint32_t *a, uint32_t *b, uint32_t w) {
    uint32_t orig_a = *a;
    uint32_t wb = solinas_fold((uint64_t)w * (uint64_t)(*b));
    *a = solinas_fold((uint64_t)orig_a + (uint64_t)wb);
    *b = solinas_fold((uint64_t)2013265921U + (uint64_t)orig_a - (uint64_t)wb);
}
void ntt_scalar_arm(uint32_t *data, size_t n, const uint32_t *twiddles) {
    /* Literal loop bound (12) enables compiler loop unrolling */
    for (size_t stage = 0; stage < 12; stage++) {
        size_t half = 1 << (11 - stage);
        for (size_t group = 0; group < (1u << stage); group++) {
            for (size_t pair = 0; pair + 1 <= half; pair += 1) {
                size_t i = group * 2 * half + pair;
                size_t j = i + half;
                size_t tw_idx = stage * (n / 2) + group * half + pair;
                butterfly(&data[i], &data[j], twiddles[tw_idx]);
            }
        }
    }
}
