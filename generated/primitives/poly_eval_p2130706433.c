/* AMO-Lean Generated Polynomial Evaluation — Horner's method
 * p = 2130706433, degree = 7, reduction = solinasFold
 * p(x) = coeffs[0] + x*(coeffs[1] + x*(coeffs[2] + ... ))
 * Each mul + add uses e-graph-selected reduction
 * Verified: solinasFold_mod_correct
 */

#include <stdint.h>
#include <stddef.h>

#define P 2130706433U

static inline uint32_t reduce(uint64_t x) {
    return (uint32_t)(x % P);
}

uint32_t poly_eval_p2130706433(const uint32_t *coeffs, size_t degree, uint32_t x) {
    uint32_t acc = coeffs[degree];
    for (size_t i = degree; i > 0; i--) {
        acc = reduce((uint64_t)x * (uint64_t)acc);    /* x * acc mod p */
        acc = reduce((uint64_t)coeffs[i-1] + (uint64_t)acc); /* a_i + x*acc mod p */
    }
    return acc;
}
