/* FRI fold: result[i] = fold(even[i] + fold(alpha * odd[i]))
 * Each lane processes one evaluation point independently.
 * Verified: solinasFold_mod_correct (scalar level)
 */
static inline uint32x4_t fri_fold_2013265921(
    uint32x4_t even, uint32x4_t odd, uint32x4_t alpha) {
    /* Step 1: alpha * odd (lane-wise multiply) */
    uint32x4_t prod = vmulq_u32(alpha, odd);
    /* Step 2: fold(alpha * odd) */
    uint32x4_t x = prod;
    uint32x4_t prod_folded = vaddq_u32(vmulq_u32(vshrq_n_u32(x, 31), vdupq_n_u32(134217727)), vandq_u32(x, vdupq_n_u32(2147483647)));
    /* Step 3: even + fold(alpha * odd) */
    uint32x4_t sum = vaddq_u32(even, prod_folded);
    /* Step 4: fold(sum) */
    x = sum;
    return vaddq_u32(vmulq_u32(vshrq_n_u32(x, 31), vdupq_n_u32(134217727)), vandq_u32(x, vdupq_n_u32(2147483647)));
}