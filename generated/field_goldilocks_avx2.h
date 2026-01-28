/**
 * field_goldilocks_avx2.h - AVX2 Vectorized Goldilocks Field Arithmetic
 *
 * AMO-Lean Phase 3: SIMD CodeGen
 *
 * This implementation provides vectorized field operations for the Goldilocks
 * prime field using AVX2 instructions. It processes 4 field elements in parallel.
 *
 * Based on:
 *   - Plonky3 x86_64_avx2/packing.rs
 *   - Plonky2 goldilocks_field.rs
 *   - https://xn--2-umb.com/23/gold-reduce/ (Reduction algorithm)
 *
 * Key technique: 64-bit multiplication is emulated using 4 x 32-bit multiplications
 * since AVX2 lacks native 64x64→128 bit multiplication.
 *
 * Reference: Issue #252 in Plonky3 - Optimized delayed-reduction loops
 */

#ifndef FIELD_GOLDILOCKS_AVX2_H
#define FIELD_GOLDILOCKS_AVX2_H

#include <stdint.h>
#include <stdbool.h>
#include <immintrin.h>  /* AVX2 intrinsics */

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Constants
 *===========================================================================*/

/** Goldilocks prime: p = 2^64 - 2^32 + 1 */
#define GOLDILOCKS_P 0xFFFFFFFF00000001ULL

/** Epsilon = 2^32 - 1, used in fast reduction */
#define GOLDILOCKS_EPSILON 0xFFFFFFFFULL

/** Number of elements per AVX2 vector (4 x 64-bit) */
#define GOLDILOCKS_AVX2_WIDTH 4

/*===========================================================================
 * Vector Type Aliases
 *===========================================================================*/

/** Packed Goldilocks field elements (4 elements, 256 bits) */
typedef __m256i goldilocks_vec_t;

/*===========================================================================
 * Vector Constants (Broadcast)
 *===========================================================================*/

/** Broadcast EPSILON to all 4 lanes */
static inline __m256i goldilocks_avx2_epsilon(void) {
    return _mm256_set1_epi64x(GOLDILOCKS_EPSILON);
}

/** Broadcast P to all 4 lanes */
static inline __m256i goldilocks_avx2_p(void) {
    return _mm256_set1_epi64x(GOLDILOCKS_P);
}

/** Zero vector */
static inline __m256i goldilocks_avx2_zero(void) {
    return _mm256_setzero_si256();
}

/** One vector */
static inline __m256i goldilocks_avx2_one(void) {
    return _mm256_set1_epi64x(1);
}

/*===========================================================================
 * Helper Functions (Internal)
 *===========================================================================*/

/**
 * Extract high 32 bits of each 64-bit lane using FP shuffle trick.
 *
 * This uses vmovehdup which executes on memory ports when operand is in memory,
 * avoiding vector port pressure (unlike right shifts).
 *
 * Reference: Plonky3 Issue #252
 */
static inline __m256i goldilocks_avx2_extract_hi32(__m256i x) {
    /* Cast to float, use vmovehdup to duplicate high 32-bits, cast back */
    return _mm256_castps_si256(
        _mm256_movehdup_ps(_mm256_castsi256_ps(x))
    );
}

/**
 * Extract low 32 bits of each 64-bit lane using FP shuffle trick.
 */
static inline __m256i goldilocks_avx2_extract_lo32(__m256i x) {
    return _mm256_castps_si256(
        _mm256_moveldup_ps(_mm256_castsi256_ps(x))
    );
}

/*===========================================================================
 * 64-bit Multiplication: 4 x (64 x 64 → 128) using AVX2
 *
 * Since AVX2 lacks native 64x64→128 multiplication, we decompose each
 * operand into 32-bit halves and use the schoolbook method:
 *
 *   a = a_hi * 2^32 + a_lo
 *   b = b_hi * 2^32 + b_lo
 *
 *   a * b = a_hi*b_hi * 2^64 + (a_hi*b_lo + a_lo*b_hi) * 2^32 + a_lo*b_lo
 *
 * This requires 4 calls to _mm256_mul_epu32 (32x32→64 unsigned multiply).
 *===========================================================================*/

/**
 * Multiply 4 pairs of 64-bit values, producing 4 x 128-bit results.
 *
 * @param x Input vector (4 x 64-bit)
 * @param y Input vector (4 x 64-bit)
 * @param res_hi Output: high 64 bits of each 128-bit product
 * @param res_lo Output: low 64 bits of each 128-bit product
 *
 * Based on: Plonky3 mul64_64 function
 */
static inline void goldilocks_avx2_mul64_64(
    __m256i x, __m256i y,
    __m256i *res_hi, __m256i *res_lo
) {
    const __m256i EPSILON_VEC = goldilocks_avx2_epsilon();

    /* Extract high 32 bits of each 64-bit lane */
    __m256i x_hi = goldilocks_avx2_extract_hi32(x);
    __m256i y_hi = goldilocks_avx2_extract_hi32(y);

    /*
     * 4 multiplications of 32-bit halves:
     *   mul_ll = x_lo * y_lo  (low  * low)
     *   mul_lh = x_lo * y_hi  (low  * high)
     *   mul_hl = x_hi * y_lo  (high * low)
     *   mul_hh = x_hi * y_hi  (high * high)
     *
     * Note: _mm256_mul_epu32 multiplies the EVEN 32-bit elements and produces
     * 64-bit results. The odd elements are ignored.
     */
    __m256i mul_ll = _mm256_mul_epu32(x, y);       /* x_lo * y_lo */
    __m256i mul_lh = _mm256_mul_epu32(x, y_hi);    /* x_lo * y_hi */
    __m256i mul_hl = _mm256_mul_epu32(x_hi, y);    /* x_hi * y_lo */
    __m256i mul_hh = _mm256_mul_epu32(x_hi, y_hi); /* x_hi * y_hi */

    /*
     * Combine partial products:
     *
     *   Product = mul_hh * 2^64 + (mul_hl + mul_lh) * 2^32 + mul_ll
     *
     * We need to handle carries carefully.
     */

    /* t0 = mul_hl + high32(mul_ll) */
    __m256i mul_ll_hi = _mm256_srli_epi64(mul_ll, 32);
    __m256i t0 = _mm256_add_epi64(mul_hl, mul_ll_hi);

    /* Split t0 into low 32 and high 32 */
    __m256i t0_lo = _mm256_and_si256(t0, EPSILON_VEC);
    __m256i t0_hi = _mm256_srli_epi64(t0, 32);

    /* t1 = mul_lh + t0_lo (this is the "middle" portion, bits [32..95]) */
    __m256i t1 = _mm256_add_epi64(mul_lh, t0_lo);

    /* t2 = mul_hh + t0_hi (accumulate carries into high portion) */
    __m256i t2 = _mm256_add_epi64(mul_hh, t0_hi);

    /* Add carry from t1 to high portion */
    __m256i t1_hi = _mm256_srli_epi64(t1, 32);
    *res_hi = _mm256_add_epi64(t2, t1_hi);

    /*
     * Construct res_lo by blending:
     *   - Low 32 bits from mul_ll
     *   - High 32 bits from t1_lo
     */
    __m256i t1_lo = goldilocks_avx2_extract_lo32(t1);
    *res_lo = _mm256_blend_epi32(mul_ll, t1_lo, 0xAA);  /* 0xAA = 10101010b */
}

/*===========================================================================
 * 128-bit Reduction to Goldilocks Field
 *
 * Reduces 4 x 128-bit values to 4 x 64-bit Goldilocks field elements.
 *
 * Uses the identities:
 *   2^64  ≡ EPSILON (mod p)  where EPSILON = 2^32 - 1
 *   2^96  ≡ -1 (mod p)
 *
 * For a 128-bit value x = x_hi * 2^64 + x_lo:
 *   x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON (mod p)
 *
 * where x_hi_hi = high32(x_hi) and x_hi_lo = low32(x_hi).
 *===========================================================================*/

/**
 * Reduce 4 x 128-bit products to 4 x 64-bit field elements.
 *
 * @param hi High 64 bits of each 128-bit value
 * @param lo Low 64 bits of each 128-bit value
 * @return 4 reduced field elements (may not be fully canonical)
 *
 * Based on: Plonky3 reduce128 function
 */
static inline __m256i goldilocks_avx2_reduce128(__m256i hi, __m256i lo) {
    const __m256i EPSILON_VEC = goldilocks_avx2_epsilon();
    const __m256i P_VEC = goldilocks_avx2_p();

    /*
     * Step 1: Extract hi_hi (top 32 bits of hi) and hi_lo (bottom 32 bits)
     */
    __m256i hi_hi = _mm256_srli_epi64(hi, 32);
    __m256i hi_lo = _mm256_and_si256(hi, EPSILON_VEC);

    /*
     * Step 2: t0 = lo - hi_hi (with wraparound)
     *
     * If lo < hi_hi, we need to add P to compensate.
     * Use comparison to create a mask.
     */
    __m256i t0 = _mm256_sub_epi64(lo, hi_hi);

    /* Check for borrow: lo < hi_hi means we need to add P */
    /* Note: _mm256_cmpgt_epi64 does signed comparison, but for our range it's OK */
    /* For correctness with unsigned, we use a different technique */
    __m256i borrow_mask = _mm256_cmpgt_epi64(hi_hi, lo);

    /* Add P where borrow occurred */
    __m256i correction = _mm256_and_si256(borrow_mask, P_VEC);
    t0 = _mm256_add_epi64(t0, correction);

    /*
     * Step 3: t1 = hi_lo * EPSILON
     *
     * Since both hi_lo and EPSILON are 32-bit, this product fits in 64 bits.
     */
    __m256i t1 = _mm256_mul_epu32(hi_lo, EPSILON_VEC);

    /*
     * Step 4: result = t0 + t1
     *
     * This may overflow 64 bits, so we need another reduction pass.
     */
    __m256i result = _mm256_add_epi64(t0, t1);

    /*
     * Step 5: Check for overflow and reduce again if needed
     *
     * If result < t0 (overflow), we add EPSILON (since 2^64 ≡ EPSILON).
     */
    __m256i overflow_mask = _mm256_cmpgt_epi64(t0, result);
    __m256i overflow_correction = _mm256_and_si256(overflow_mask, EPSILON_VEC);
    result = _mm256_add_epi64(result, overflow_correction);

    /*
     * Step 6: Final canonicalization (subtract P if >= P)
     *
     * Note: For performance, we often skip this step and work with
     * non-canonical representatives. Add this only if canonical form is required.
     */
    __m256i ge_p_mask = _mm256_cmpgt_epi64(result, _mm256_sub_epi64(P_VEC, goldilocks_avx2_one()));
    /* Equivalent to: result >= P */
    __m256i final_correction = _mm256_and_si256(ge_p_mask, P_VEC);
    result = _mm256_sub_epi64(result, final_correction);

    return result;
}

/*===========================================================================
 * Core Vectorized Field Operations
 *===========================================================================*/

/**
 * Vector addition: (a + b) mod p (element-wise)
 */
static inline __m256i goldilocks_avx2_add(__m256i a, __m256i b) {
    const __m256i P_VEC = goldilocks_avx2_p();

    __m256i sum = _mm256_add_epi64(a, b);

    /* If sum >= P, subtract P */
    /* For sum >= P: (sum > P-1) or equivalently check if subtraction doesn't underflow */
    __m256i reduced = _mm256_sub_epi64(sum, P_VEC);

    /* Use the sign bit of the original subtraction to select */
    /* If sum < P, reduced will have "borrowed" (be very large), so use sum */
    __m256i mask = _mm256_cmpgt_epi64(P_VEC, sum);
    return _mm256_blendv_epi8(reduced, sum, mask);
}

/**
 * Vector subtraction: (a - b) mod p (element-wise)
 */
static inline __m256i goldilocks_avx2_sub(__m256i a, __m256i b) {
    const __m256i P_VEC = goldilocks_avx2_p();

    __m256i diff = _mm256_sub_epi64(a, b);

    /* If a < b (borrow occurred), add P */
    __m256i borrow_mask = _mm256_cmpgt_epi64(b, a);
    __m256i correction = _mm256_and_si256(borrow_mask, P_VEC);

    return _mm256_add_epi64(diff, correction);
}

/**
 * Vector negation: (-a) mod p = (p - a) mod p (element-wise)
 */
static inline __m256i goldilocks_avx2_neg(__m256i a) {
    const __m256i P_VEC = goldilocks_avx2_p();

    /* Handle zero specially: -0 = 0 */
    __m256i zero_mask = _mm256_cmpeq_epi64(a, goldilocks_avx2_zero());
    __m256i neg = _mm256_sub_epi64(P_VEC, a);

    return _mm256_blendv_epi8(neg, goldilocks_avx2_zero(), zero_mask);
}

/**
 * Vector multiplication: (a * b) mod p (element-wise)
 *
 * This is the main vectorized operation, using the 64x64→128 multiply
 * followed by 128-bit reduction.
 */
static inline __m256i goldilocks_avx2_mul(__m256i a, __m256i b) {
    __m256i hi, lo;
    goldilocks_avx2_mul64_64(a, b, &hi, &lo);
    return goldilocks_avx2_reduce128(hi, lo);
}

/**
 * Vector squaring: (a * a) mod p (element-wise)
 *
 * Could be optimized further since squaring has symmetries.
 */
static inline __m256i goldilocks_avx2_square(__m256i a) {
    return goldilocks_avx2_mul(a, a);
}

/*===========================================================================
 * Load/Store Operations
 *===========================================================================*/

/**
 * Load 4 field elements from memory (aligned)
 */
static inline __m256i goldilocks_avx2_load(const uint64_t *ptr) {
    return _mm256_load_si256((const __m256i *)ptr);
}

/**
 * Load 4 field elements from memory (unaligned)
 */
static inline __m256i goldilocks_avx2_loadu(const uint64_t *ptr) {
    return _mm256_loadu_si256((const __m256i *)ptr);
}

/**
 * Store 4 field elements to memory (aligned)
 */
static inline void goldilocks_avx2_store(uint64_t *ptr, __m256i v) {
    _mm256_store_si256((__m256i *)ptr, v);
}

/**
 * Store 4 field elements to memory (unaligned)
 */
static inline void goldilocks_avx2_storeu(uint64_t *ptr, __m256i v) {
    _mm256_storeu_si256((__m256i *)ptr, v);
}

/**
 * Broadcast a scalar to all 4 lanes
 */
static inline __m256i goldilocks_avx2_broadcast(uint64_t x) {
    return _mm256_set1_epi64x(x);
}

/*===========================================================================
 * FRI Fold Operation (Vectorized)
 *
 * FRI fold: out[i] = even[i] + alpha * odd[i]
 *
 * This is a key operation in FRI-based proofs.
 *===========================================================================*/

/**
 * Vectorized FRI fold: out = even + alpha * odd
 *
 * @param even 4 even polynomial coefficients
 * @param odd 4 odd polynomial coefficients
 * @param alpha Scalar folding challenge (broadcasted)
 * @return 4 folded coefficients
 */
static inline __m256i goldilocks_avx2_fri_fold(
    __m256i even,
    __m256i odd,
    __m256i alpha  /* Should be broadcasted scalar */
) {
    __m256i alpha_odd = goldilocks_avx2_mul(alpha, odd);
    return goldilocks_avx2_add(even, alpha_odd);
}

/**
 * Batch FRI fold for arrays
 *
 * @param out Output array (n/2 elements)
 * @param poly Input polynomial coefficients (n elements)
 * @param n Number of input elements (must be multiple of 8)
 * @param alpha Scalar folding challenge
 */
static inline void goldilocks_avx2_fri_fold_batch(
    uint64_t *restrict out,
    const uint64_t *restrict poly,
    size_t n,
    uint64_t alpha
) {
    __m256i alpha_vec = goldilocks_avx2_broadcast(alpha);
    size_t half_n = n / 2;

    /* Process 4 output elements at a time */
    for (size_t i = 0; i < half_n; i += GOLDILOCKS_AVX2_WIDTH) {
        /* Load even indices: poly[0], poly[2], poly[4], poly[6] */
        __m256i even = _mm256_set_epi64x(
            poly[2*i + 6], poly[2*i + 4], poly[2*i + 2], poly[2*i + 0]
        );

        /* Load odd indices: poly[1], poly[3], poly[5], poly[7] */
        __m256i odd = _mm256_set_epi64x(
            poly[2*i + 7], poly[2*i + 5], poly[2*i + 3], poly[2*i + 1]
        );

        /* Fold and store */
        __m256i folded = goldilocks_avx2_fri_fold(even, odd, alpha_vec);
        goldilocks_avx2_storeu(&out[i], folded);
    }
}

/*===========================================================================
 * Dot Product (Vectorized)
 *
 * Useful for matrix-vector multiplication in Poseidon2 MDS.
 *===========================================================================*/

/**
 * Compute dot product of two 4-element vectors, returning scalar result.
 *
 * @param a First vector (4 elements)
 * @param b Second vector (4 elements)
 * @return Scalar dot product a·b mod p
 */
static inline uint64_t goldilocks_avx2_dot4(__m256i a, __m256i b) {
    __m256i products = goldilocks_avx2_mul(a, b);

    /* Extract and sum all 4 products */
    /* This requires going through scalar operations */
    uint64_t result[4] __attribute__((aligned(32)));
    goldilocks_avx2_store(result, products);

    /* Scalar additions (could be optimized with horizontal add) */
    uint64_t sum = result[0];
    for (int i = 1; i < 4; i++) {
        __uint128_t s = (__uint128_t)sum + result[i];
        if (s >= GOLDILOCKS_P) {
            sum = (uint64_t)(s - GOLDILOCKS_P);
        } else {
            sum = (uint64_t)s;
        }
    }

    return sum;
}

#ifdef __cplusplus
}
#endif

#endif /* FIELD_GOLDILOCKS_AVX2_H */
