/* AMO-Lean Generated Dot Product — e-graph optimized
 * p = 2130706433, reduction = solinasFold
 * result = Σ reduce(a[i] * b[i]) mod p
 * Verified: solinasFold_mod_correct
 */

#include <stdint.h>
#include <stddef.h>

#define P 2130706433U

static inline uint32_t reduce(uint64_t x) {
    return (uint32_t)(x % P);
}

uint32_t dot_product_p2130706433(const uint32_t *a, const uint32_t *b, size_t n) {
    uint32_t acc = 0;
    for (size_t i = 0; i < n; i++) {
        uint32_t prod = reduce((uint64_t)a[i] * (uint64_t)b[i]);
        acc = reduce((uint64_t)acc + (uint64_t)prod);
    }
    return acc;
}
