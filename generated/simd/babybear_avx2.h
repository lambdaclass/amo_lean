/* AMO-Lean Generated SIMD — BabyBear (p = 2^31 - 2^27 + 1)
 * Target: avx2 (8 lanes × u32)
 * Verified: solinasFold_mod_correct, butterflyDirectSum_correct
 * Generated from: AmoLean/EGraph/Verified/Bitwise/NTTBridge.lean
 */

#include <immintrin.h>
#include <stdint.h>

#define BABYBEAR_P 0x78000001U
#define BABYBEAR_C 134217727U  /* 2^27 - 1 */

/* ═══ Solinas fold: fold(x) % p = x % p ═══ */
static inline __m256i solinas_fold_31_134217727(__m256i x) {
    return _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(x, 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(x, _mm256_set1_epi32(2147483647)));
}

/* ═══ Butterfly sum: a' = fold(a + fold(w*b)) ═══ */
static inline __m256i butterfly_sum_2013265921(__m256i a, __m256i w, __m256i b) {
    return _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(_mm256_add_epi32(a, _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(_mm256_add_epi32(a, _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), _mm256_set1_epi32(2147483647)));
}

/* ═══ Butterfly diff: b' = fold(p + a - fold(w*b)) ═══ */
static inline __m256i butterfly_diff_2013265921(__m256i a, __m256i w, __m256i b) {
    return _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(_mm256_sub_epi32(_mm256_add_epi32(_mm256_set1_epi32(2013265921), a), _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(_mm256_sub_epi32(_mm256_add_epi32(_mm256_set1_epi32(2013265921), a), _mm256_add_epi32(_mm256_mullo_epi32(_mm256_srli_epi32(_mm256_mullo_epi32(w, b), 31), _mm256_set1_epi32(134217727)), _mm256_and_si256(_mm256_mullo_epi32(w, b), _mm256_set1_epi32(2147483647)))), _mm256_set1_epi32(2147483647)));
}

/* ═══ Butterfly pair (in-place) ═══ */
static inline void butterfly_pair_2013265921(__m256i *a, __m256i *b, __m256i w) {
    __m256i sum = butterfly_sum_2013265921(*a, w, *b);
    __m256i diff = butterfly_diff_2013265921(*a, w, *b);
    *a = sum;
    *b = diff;
}
