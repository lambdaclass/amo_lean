/* AMO-Lean Unified CodeGen — ALL decisions from e-graph cost model
 * N = 4096, p = 18446744069414584321
 * Mode: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ExecMode.scalar (from isSimd=false, lanes=1)
 * Reduction: AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen.ReductionStrategy.solinasFold (from wideningPenalty=0)
 * Word size: u64 (from field bit width)
 * Backend: C (scalar)
 *
 * NOT hardcoded — change HardwareCost to get different code.
 * Verification: solinasFold_mod_correct / montyReduce evaluates to x %% p
 */

#include <stdint.h>
#include <stddef.h>

#define GOLDILOCKS_P 0xFFFFFFFF00000001ULL
#define NEG_ORDER 0xFFFFFFFFULL

static inline uint64_t goldilocks_reduce128(__uint128_t x) {
    uint64_t x_lo = (uint64_t)x;
    uint64_t x_hi = (uint64_t)(x >> 64);
    uint64_t x_hi_hi = x_hi >> 32;
    uint64_t x_hi_lo = x_hi & NEG_ORDER;
    /* t0 = x_lo - x_hi_hi (with borrow handling) */
    uint64_t t0;
    int borrow = __builtin_sub_overflow(x_lo, x_hi_hi, &t0);
    if (borrow) t0 -= NEG_ORDER;
    /* t1 = x_hi_lo * NEG_ORDER */
    uint64_t t1 = x_hi_lo * NEG_ORDER;
    /* result = t0 + t1 (with carry handling) */
    uint64_t result;
    int carry = __builtin_add_overflow(t0, t1, &result);
    if (carry || result >= GOLDILOCKS_P) result -= GOLDILOCKS_P;
    return result;
}

static inline void butterfly(uint64_t *a, uint64_t *b, uint64_t w) {
    uint64_t orig_a = *a;
    uint64_t wb = goldilocks_reduce128((__uint128_t)w * (__uint128_t)(*b));
    __uint128_t sum128 = (__uint128_t)orig_a + (__uint128_t)wb;
    *a = goldilocks_reduce128(sum128);
    __uint128_t diff128 = (__uint128_t)GOLDILOCKS_P + (__uint128_t)orig_a - (__uint128_t)wb;
    *b = goldilocks_reduce128(diff128);
}
void ntt_scalar_arm(uint64_t *data, size_t n, const uint64_t *twiddles) {
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
