/* AMO-Lean Generated FRI Fold — e-graph optimized
 * p = 2130706433, reduction = solinasFold
 * Operation: result[i] = reduce(even[i] + reduce(alpha * odd[i]))
 * E-graph selected solinasFold for scalar mode
 * Verified: solinasFold_mod_correct
 */

#include <stdint.h>
#include <stddef.h>

static inline uint32_t reduce(uint64_t x) {
    return (uint32_t)(((x >> 31) * 1U) + (x & 2147483647U));
}

void fri_fold_p2130706433(const uint32_t *even, const uint32_t *odd,
               uint32_t alpha, uint32_t *result, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint32_t prod_red = reduce((uint64_t)alpha * (uint64_t)odd[i]);
        result[i] = reduce((uint64_t)even[i] + (uint64_t)prod_red);
    }
}
