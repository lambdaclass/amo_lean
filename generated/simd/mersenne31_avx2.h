/* AMO-Lean Generated SIMD — Mersenne31 (p = 2^31 - 1)
 * Target: avx2 (8 lanes × u32)
 * Verified: solinasFold_mod_correct
 */

#include <immintrin.h>
#include <stdint.h>

#define MERSENNE31_P 0x7FFFFFFFU

/* ═══ Mersenne fold: fold(x) = (x >> 31) + (x & mask) ═══ */
static inline __m256i mersenne_fold_31(__m256i x) {
    return _mm256_add_epi32(_mm256_srli_epi32(x, 31), _mm256_and_si256(x, _mm256_set1_epi32(2147483647)));
}

/* ═══ Butterfly ═══ */
static inline __m256i butterfly_sum_2147483647(__m256i a, __m256i w, __m256i b) {
    return _mm256_add_epi32(_mm256_srli_epi32(_mm256_add_epi32(a, _mm256_add_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), 31), _mm256_and_si256(_mm256_add_epi32(a, _mm256_add_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), _mm256_set1_epi32(2147483647)));
}
static inline __m256i butterfly_diff_2147483647(__m256i a, __m256i w, __m256i b) {
    return _mm256_add_epi32(_mm256_srli_epi32(_mm256_sub_epi32(_mm256_add_epi32(_mm256_set1_epi32(2147483647), a), _mm256_add_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), 31), _mm256_and_si256(_mm256_sub_epi32(_mm256_add_epi32(_mm256_set1_epi32(2147483647), a), _mm256_add_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), _mm256_set1_epi32(2147483647)));
}
