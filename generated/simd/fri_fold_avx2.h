#include <immintrin.h>

/* FRI fold: result[i] = fold(even[i] + fold(alpha * odd[i]))
 * Each lane processes one evaluation point independently.
 * Verified: solinasFold_mod_correct (scalar level)
 */
static inline __m256i fri_fold_2013265921(
    __m256i even, __m256i odd, __m256i alpha) {
    /* Step 1: alpha * odd (lane-wise multiply) */
    __m256i prod = _mm256_mullo_epi32(alpha, odd);
    /* Step 2: fold(alpha * odd) */
    __m256i x = prod;
    __m256i prod_folded = _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(x, 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(x, _mm256_set1_epi32(2147483647)));
    /* Step 3: even + fold(alpha * odd) */
    __m256i sum = _mm256_add_epi32(even, prod_folded);
    /* Step 4: fold(sum) */
    x = sum;
    return _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(x, 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(x, _mm256_set1_epi32(2147483647)));
}