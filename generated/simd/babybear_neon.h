/* AMO-Lean Generated SIMD — BabyBear (p = 2^31 - 2^27 + 1)
 * Target: neon (4 lanes × u32)
 * Verified: solinasFold_mod_correct, butterflyDirectSum_correct
 * Generated from: AmoLean/EGraph/Verified/Bitwise/NTTBridge.lean
 */

#include <arm_neon.h>
#include <stdint.h>

#define BABYBEAR_P 0x78000001U
#define BABYBEAR_C 134217727U  /* 2^27 - 1 */

/* ═══ Solinas fold: fold(x) % p = x % p ═══ */
static inline uint32x4_t solinas_fold_31_134217727(uint32x4_t x) {
    return vaddq_u32(vmulq_u32(vshrq_n_u32(x, 31), vdupq_n_u32(134217727)), vandq_u32(x, vdupq_n_u32(2147483647)));
}

/* ═══ Butterfly sum: a' = fold(a + fold(w*b)) ═══ */
static inline uint32x4_t butterfly_sum_2013265921(uint32x4_t a, uint32x4_t w, uint32x4_t b) {
    return vaddq_u32(vmulq_u32(vshrq_n_u32(vaddq_u32(a, vaddq_u32(vmulq_u32(vshrq_n_u32(vmulq_u32(w, b), 31), vdupq_n_u32(134217727)), vandq_u32(vmulq_u32(w, b), vdupq_n_u32(2147483647)))), 31), vdupq_n_u32(134217727)), vandq_u32(vaddq_u32(a, vaddq_u32(vmulq_u32(vshrq_n_u32(vmulq_u32(w, b), 31), vdupq_n_u32(134217727)), vandq_u32(vmulq_u32(w, b), vdupq_n_u32(2147483647)))), vdupq_n_u32(2147483647)));
}

/* ═══ Butterfly diff: b' = fold(p + a - fold(w*b)) ═══ */
static inline uint32x4_t butterfly_diff_2013265921(uint32x4_t a, uint32x4_t w, uint32x4_t b) {
    return vaddq_u32(vmulq_u32(vshrq_n_u32(vsubq_u32(vaddq_u32(vdupq_n_u32(2013265921), a), vaddq_u32(vmulq_u32(vshrq_n_u32(vmulq_u32(w, b), 31), vdupq_n_u32(134217727)), vandq_u32(vmulq_u32(w, b), vdupq_n_u32(2147483647)))), 31), vdupq_n_u32(134217727)), vandq_u32(vsubq_u32(vaddq_u32(vdupq_n_u32(2013265921), a), vaddq_u32(vmulq_u32(vshrq_n_u32(vmulq_u32(w, b), 31), vdupq_n_u32(134217727)), vandq_u32(vmulq_u32(w, b), vdupq_n_u32(2147483647)))), vdupq_n_u32(2147483647)));
}

/* ═══ Butterfly pair (in-place) ═══ */
static inline void butterfly_pair_2013265921(uint32x4_t *a, uint32x4_t *b, uint32x4_t w) {
    uint32x4_t sum = butterfly_sum_2013265921(*a, w, *b);
    uint32x4_t diff = butterfly_diff_2013265921(*a, w, *b);
    *a = sum;
    *b = diff;
}
