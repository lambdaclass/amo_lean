/**
 * field_goldilocks.h - Goldilocks Field Arithmetic for AMO-Lean
 *
 * Phase 1: Corrected Implementation
 *
 * Goldilocks Field: F_p where p = 2^64 - 2^32 + 1
 *
 * This implementation uses the special structure of the Goldilocks prime
 * to achieve fast modular reduction without division.
 *
 * Key identities:
 *   - 2^64 ≡ 2^32 - 1 ≡ EPSILON (mod p)
 *   - 2^96 ≡ -1 (mod p)
 *
 * Reference: Plonky2 goldilocks_field.rs
 * https://github.com/0xPolygonZero/plonky2/blob/main/field/src/goldilocks_field.rs
 *
 * CRITICAL FIXES from Phase 0:
 *   - Uses __uint128_t for intermediate sums to prevent overflow
 *   - Uses specialized Goldilocks reduction (NOT Barrett)
 *   - Includes comprehensive edge case handling
 */

#ifndef FIELD_GOLDILOCKS_H
#define FIELD_GOLDILOCKS_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Constants
 *===========================================================================*/

/** Goldilocks prime: p = 2^64 - 2^32 + 1 */
#define GOLDILOCKS_ORDER 0xFFFFFFFF00000001ULL

/** Epsilon: 2^32 - 1, used in fast reduction */
#define GOLDILOCKS_EPSILON 0xFFFFFFFFULL

/** Field type */
typedef uint64_t goldilocks_t;

/** For compatibility with existing code */
#ifdef FIELD_GOLDILOCKS
typedef goldilocks_t field_t;
#define FIELD_NAME "goldilocks"
#define FIELD_ORDER GOLDILOCKS_ORDER
#endif

/*===========================================================================
 * Internal Helper Functions
 *===========================================================================*/

/**
 * Reduce a 128-bit value modulo Goldilocks prime.
 *
 * Uses the identity: 2^64 ≡ EPSILON (mod p) and 2^96 ≡ -1 (mod p)
 *
 * For x = x_lo + x_hi * 2^64:
 *   Split x_hi into x_hi_hi (top 32 bits) and x_hi_lo (bottom 32 bits)
 *   x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON (mod p)
 *
 * @param x 128-bit value to reduce
 * @return x mod p as a 64-bit value
 */
static inline goldilocks_t goldilocks_reduce128(__uint128_t x) {
    uint64_t x_lo = (uint64_t)x;
    uint64_t x_hi = (uint64_t)(x >> 64);

    /* If no high part, simple reduction */
    if (x_hi == 0) {
        return (x_lo >= GOLDILOCKS_ORDER) ? x_lo - GOLDILOCKS_ORDER : x_lo;
    }

    /* Split x_hi into top 32 bits and bottom 32 bits */
    uint64_t x_hi_hi = x_hi >> 32;           /* Top 32 bits of x_hi */
    uint64_t x_hi_lo = x_hi & GOLDILOCKS_EPSILON;  /* Bottom 32 bits of x_hi */

    /*
     * Apply reduction:
     *   2^96 ≡ -1 (mod p)  =>  x_hi_hi * 2^96 ≡ -x_hi_hi (mod p)
     *   2^64 ≡ EPSILON (mod p)  =>  x_hi_lo * 2^64 ≡ x_hi_lo * EPSILON (mod p)
     *
     * So: x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON (mod p)
     */

    /* Step 1: t0 = x_lo - x_hi_hi (may underflow) */
    uint64_t t0;
    bool borrow = x_lo < x_hi_hi;
    if (borrow) {
        /* x_lo - x_hi_hi underflows, add p to compensate */
        /* t0 = x_lo - x_hi_hi + p = x_lo + (p - x_hi_hi) */
        t0 = x_lo + (GOLDILOCKS_ORDER - x_hi_hi);
    } else {
        t0 = x_lo - x_hi_hi;
    }

    /* Step 2: t1 = x_hi_lo * EPSILON (fits in 64 bits since both are 32-bit) */
    uint64_t t1 = x_hi_lo * GOLDILOCKS_EPSILON;

    /* Step 3: result = t0 + t1 (may overflow, use 128-bit) */
    __uint128_t sum = (__uint128_t)t0 + t1;

    /* If sum overflowed 64 bits, we need another reduction round */
    if (sum >= ((__uint128_t)1 << 64)) {
        /* sum = sum_lo + sum_hi * 2^64, where sum_hi is small (at most ~1) */
        uint64_t sum_lo = (uint64_t)sum;
        uint64_t sum_hi = (uint64_t)(sum >> 64);
        /* 2^64 ≡ EPSILON, so add sum_hi * EPSILON */
        sum = (__uint128_t)sum_lo + sum_hi * GOLDILOCKS_EPSILON;
    }

    /* Final reduction if >= p */
    uint64_t result = (uint64_t)sum;
    if (result >= GOLDILOCKS_ORDER) {
        result -= GOLDILOCKS_ORDER;
    }

    return result;
}

/*===========================================================================
 * Core Field Operations
 *===========================================================================*/

/**
 * Field addition: (a + b) mod p
 *
 * CRITICAL: Uses __uint128_t to prevent overflow.
 * The original Phase 0 implementation had a silent overflow bug here.
 *
 * @param a First operand (must be < p)
 * @param b Second operand (must be < p)
 * @return (a + b) mod p
 */
static inline goldilocks_t goldilocks_add(goldilocks_t a, goldilocks_t b) {
    __uint128_t sum = (__uint128_t)a + b;

    /*
     * Since a, b < p < 2^64, we have sum < 2^65.
     * If sum >= p, subtract p.
     * If sum overflowed into the high 64 bits, that means sum >= 2^64 > p,
     * so we definitely need to subtract p.
     */
    if (sum >= GOLDILOCKS_ORDER) {
        return (goldilocks_t)(sum - GOLDILOCKS_ORDER);
    }
    return (goldilocks_t)sum;
}

/**
 * Field subtraction: (a - b) mod p
 *
 * @param a First operand (must be < p)
 * @param b Second operand (must be < p)
 * @return (a - b + p) mod p
 */
static inline goldilocks_t goldilocks_sub(goldilocks_t a, goldilocks_t b) {
    if (a >= b) {
        return a - b;
    } else {
        /* a < b, so result would be negative. Add p. */
        return GOLDILOCKS_ORDER - b + a;
    }
}

/**
 * Field negation: (-a) mod p = (p - a) mod p
 *
 * @param a Operand (must be < p)
 * @return (p - a) mod p
 */
static inline goldilocks_t goldilocks_neg(goldilocks_t a) {
    if (a == 0) {
        return 0;
    }
    return GOLDILOCKS_ORDER - a;
}

/**
 * Field multiplication: (a * b) mod p
 *
 * Uses specialized Goldilocks reduction (NOT Barrett).
 *
 * @param a First operand (must be < p)
 * @param b Second operand (must be < p)
 * @return (a * b) mod p
 */
static inline goldilocks_t goldilocks_mul(goldilocks_t a, goldilocks_t b) {
    __uint128_t product = (__uint128_t)a * b;
    return goldilocks_reduce128(product);
}

/**
 * Field squaring: (a * a) mod p
 *
 * @param a Operand (must be < p)
 * @return (a * a) mod p
 */
static inline goldilocks_t goldilocks_square(goldilocks_t a) {
    return goldilocks_mul(a, a);
}

/**
 * Field exponentiation: (base ^ exp) mod p
 *
 * Uses binary exponentiation (square-and-multiply).
 *
 * @param base Base (must be < p)
 * @param exp Exponent
 * @return (base ^ exp) mod p
 */
static inline goldilocks_t goldilocks_pow(goldilocks_t base, uint64_t exp) {
    goldilocks_t result = 1;
    goldilocks_t b = base;

    while (exp > 0) {
        if (exp & 1) {
            result = goldilocks_mul(result, b);
        }
        b = goldilocks_square(b);
        exp >>= 1;
    }

    return result;
}

/**
 * Field multiplicative inverse: a^(-1) mod p
 *
 * Uses Fermat's little theorem: a^(-1) ≡ a^(p-2) (mod p)
 *
 * @param a Operand (must be < p and != 0)
 * @return a^(-1) mod p, or 0 if a == 0
 */
static inline goldilocks_t goldilocks_inv(goldilocks_t a) {
    if (a == 0) {
        return 0;  /* Undefined, return 0 as sentinel */
    }
    /* p - 2 = 0xFFFFFFFF00000001 - 2 = 0xFFFFFFFEFFFFFFFF */
    return goldilocks_pow(a, GOLDILOCKS_ORDER - 2);
}

/*===========================================================================
 * Compatibility Macros for Existing Code
 *===========================================================================*/

#ifdef FIELD_GOLDILOCKS

#define field_add(a, b) goldilocks_add(a, b)
#define field_sub(a, b) goldilocks_sub(a, b)
#define field_mul(a, b) goldilocks_mul(a, b)
#define field_neg(a) goldilocks_neg(a)
#define field_inv(a) goldilocks_inv(a)
#define field_square(a) goldilocks_square(a)
#define field_pow(a, e) goldilocks_pow(a, e)

#endif /* FIELD_GOLDILOCKS */

/*===========================================================================
 * S-Box for Poseidon2 (CRITICAL: Must use x^7, NOT x^5)
 *
 * For the S-Box to be a bijection, gcd(d, p-1) = 1 is required.
 *
 * Goldilocks: p-1 = 2^32 × 3 × 5 × 17 × 257 × 65537
 *   - gcd(5, p-1) = 5 ≠ 1  →  x^5 is NOT invertible (INSECURE)
 *   - gcd(7, p-1) = 1      →  x^7 IS invertible (SECURE)
 *
 * BN254 uses x^5, but Goldilocks MUST use x^7.
 *===========================================================================*/

/** S-Box exponent for Goldilocks (MUST be 7, not 5) */
#define GOLDILOCKS_SBOX_EXPONENT 7

/**
 * S-Box: x^7 (for Poseidon2 on Goldilocks)
 *
 * Computes x^7 using 3 multiplications:
 *   x^2 = x * x
 *   x^4 = x^2 * x^2
 *   x^6 = x^4 * x^2
 *   x^7 = x^6 * x
 *
 * @param x Input field element
 * @return x^7 mod p
 */
static inline goldilocks_t goldilocks_sbox(goldilocks_t x) {
    goldilocks_t x2 = goldilocks_square(x);     /* x^2 */
    goldilocks_t x4 = goldilocks_square(x2);    /* x^4 */
    goldilocks_t x6 = goldilocks_mul(x4, x2);   /* x^6 */
    return goldilocks_mul(x6, x);               /* x^7 */
}

/**
 * Inverse S-Box: x^(1/7) mod p
 *
 * Uses the fact that (x^7)^((p-1+7)/7) = x^(p-1+1) = x
 * when gcd(7, p-1) = 1.
 *
 * Inverse exponent: 7^(-1) mod (p-1)
 * For Goldilocks: inv_exp = 10540996611094048183
 *
 * @param x Input field element (assumed to be x^7 for some x)
 * @return x such that sbox(x) = input
 */
#define GOLDILOCKS_SBOX_INV_EXPONENT 10540996611094048183ULL

static inline goldilocks_t goldilocks_sbox_inv(goldilocks_t x) {
    return goldilocks_pow(x, GOLDILOCKS_SBOX_INV_EXPONENT);
}

#ifdef FIELD_GOLDILOCKS
#define field_sbox(x) goldilocks_sbox(x)
#define field_sbox_inv(x) goldilocks_sbox_inv(x)
#endif

/*===========================================================================
 * Validation Helpers
 *===========================================================================*/

/**
 * Check if a value is a valid field element (< p)
 */
static inline bool goldilocks_is_valid(goldilocks_t a) {
    return a < GOLDILOCKS_ORDER;
}

/**
 * Reduce a potentially out-of-range value to a valid field element
 */
static inline goldilocks_t goldilocks_reduce(goldilocks_t a) {
    return (a >= GOLDILOCKS_ORDER) ? a - GOLDILOCKS_ORDER : a;
}

#ifdef __cplusplus
}
#endif

#endif /* FIELD_GOLDILOCKS_H */
