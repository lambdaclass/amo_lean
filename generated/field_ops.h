/**
 * field_ops.h - Field Arithmetic Operations for AMO-Lean Generated Code
 *
 * This header provides configurable field arithmetic operations.
 * The generated C code calls field_add/field_mul/field_sub instead of
 * native operators, allowing the same generated code to work with
 * different field implementations.
 *
 * Design Decision: DD-002 (Option A)
 *
 * Configuration:
 *   - FIELD_NATIVE: Use native uint64_t arithmetic (testing only, mod 2^64)
 *   - FIELD_GOLDILOCKS: Goldilocks field (p = 2^64 - 2^32 + 1)
 *   - FIELD_BN254: BN254 scalar field (requires external library)
 *
 * Usage:
 *   #define FIELD_NATIVE
 *   #include "field_ops.h"
 *
 * WARNING: FIELD_NATIVE is mathematically incorrect for real cryptographic
 * use. It exists only for quick testing where overflow behavior doesn't
 * affect the test (e.g., checking memory access patterns).
 */

#ifndef FIELD_OPS_H
#define FIELD_OPS_H

#include <stdint.h>
#include <assert.h>

/* =========================================================================
 * Field Type Definition
 * ========================================================================= */

typedef uint64_t field_t;

/* =========================================================================
 * Native Arithmetic (Testing Only - NOT CRYPTOGRAPHICALLY CORRECT)
 * ========================================================================= */

#if defined(FIELD_NATIVE)

#define FIELD_NAME "native_uint64"

static inline field_t field_add(field_t a, field_t b) {
    return a + b;
}

static inline field_t field_sub(field_t a, field_t b) {
    return a - b;
}

static inline field_t field_mul(field_t a, field_t b) {
    return a * b;
}

static inline field_t field_neg(field_t a) {
    return -a;
}

/* =========================================================================
 * Goldilocks Field (p = 2^64 - 2^32 + 1)
 *
 * Phase 1: Corrected implementation based on Plonky2 goldilocks_field.rs
 *
 * Key identities:
 *   - 2^64 ≡ 2^32 - 1 ≡ EPSILON (mod p)
 *   - 2^96 ≡ -1 (mod p)
 *
 * Reference: https://github.com/0xPolygonZero/plonky2
 * ========================================================================= */

#elif defined(FIELD_GOLDILOCKS)

#define FIELD_NAME "goldilocks"
#define GOLDILOCKS_P 0xFFFFFFFF00000001ULL
#define GOLDILOCKS_EPSILON 0xFFFFFFFFULL

/**
 * Reduce a 128-bit value modulo Goldilocks prime using specialized reduction.
 *
 * Uses the identity: 2^64 ≡ EPSILON (mod p) and 2^96 ≡ -1 (mod p)
 *
 * For x = x_lo + x_hi * 2^64:
 *   Split x_hi into x_hi_hi (top 32 bits) and x_hi_lo (bottom 32 bits)
 *   x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON (mod p)
 */
static inline field_t field_reduce128(__uint128_t x) {
    uint64_t x_lo = (uint64_t)x;
    uint64_t x_hi = (uint64_t)(x >> 64);

    if (x_hi == 0) {
        return (x_lo >= GOLDILOCKS_P) ? x_lo - GOLDILOCKS_P : x_lo;
    }

    /* Split x_hi into top 32 bits and bottom 32 bits */
    uint64_t x_hi_hi = x_hi >> 32;
    uint64_t x_hi_lo = x_hi & GOLDILOCKS_EPSILON;

    /* Apply reduction: x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON (mod p) */
    uint64_t t0;
    if (x_lo >= x_hi_hi) {
        t0 = x_lo - x_hi_hi;
    } else {
        t0 = x_lo + (GOLDILOCKS_P - x_hi_hi);
    }

    uint64_t t1 = x_hi_lo * GOLDILOCKS_EPSILON;
    __uint128_t sum = (__uint128_t)t0 + t1;

    if (sum >= ((__uint128_t)1 << 64)) {
        uint64_t sum_lo = (uint64_t)sum;
        uint64_t sum_hi = (uint64_t)(sum >> 64);
        sum = (__uint128_t)sum_lo + sum_hi * GOLDILOCKS_EPSILON;
    }

    uint64_t result = (uint64_t)sum;
    return (result >= GOLDILOCKS_P) ? result - GOLDILOCKS_P : result;
}

/**
 * Field addition: (a + b) mod p
 * CRITICAL: Uses __uint128_t to prevent silent overflow.
 */
static inline field_t field_add(field_t a, field_t b) {
    __uint128_t sum = (__uint128_t)a + b;
    return (sum >= GOLDILOCKS_P) ? (field_t)(sum - GOLDILOCKS_P) : (field_t)sum;
}

/**
 * Field subtraction: (a - b) mod p
 */
static inline field_t field_sub(field_t a, field_t b) {
    if (a >= b) {
        return a - b;
    } else {
        return GOLDILOCKS_P - b + a;
    }
}

/**
 * Field multiplication: (a * b) mod p using specialized reduction.
 */
static inline field_t field_mul(field_t a, field_t b) {
    __uint128_t prod = (__uint128_t)a * b;
    return field_reduce128(prod);
}

/**
 * Field negation: (-a) mod p
 */
static inline field_t field_neg(field_t a) {
    if (a == 0) return 0;
    return GOLDILOCKS_P - a;
}

/* =========================================================================
 * BN254 Scalar Field (stub - requires external library)
 * ========================================================================= */

#elif defined(FIELD_BN254)

#define FIELD_NAME "bn254"

// BN254 scalar field modulus (as string for reference):
// p = 21888242871839275222246405745257275088548364400416034343698204186575808495617

// BN254 requires multi-precision arithmetic. This is a stub that
// should be replaced with calls to an external library like:
// - libff
// - arkworks (via FFI)
// - Constantine
// - gnark-crypto

#error "FIELD_BN254 requires external multi-precision library integration"

/* =========================================================================
 * Default: No field selected
 * ========================================================================= */

#else

#error "No field selected. Define one of: FIELD_NATIVE, FIELD_GOLDILOCKS, FIELD_BN254"

#endif

/* =========================================================================
 * Common Vector Operations (field-independent)
 *
 * Note: FRI-specific operations are in fri_fold.h
 * ========================================================================= */

/**
 * Scalar-vector multiplication: out[i] = scalar * in[i]
 */
static inline void field_smul_vec(
    const field_t* restrict in,
    field_t* restrict out,
    field_t scalar,
    size_t n
) {
#ifdef DEBUG
    assert(in != NULL && "input is null");
    assert(out != NULL && "output is null");
    assert(out != in && "output aliases input");
#endif
    for (size_t i = 0; i < n; i++) {
        out[i] = field_mul(scalar, in[i]);
    }
}

/**
 * Vector addition: out[i] = a[i] + b[i]
 */
static inline void field_add_vec(
    const field_t* restrict a,
    const field_t* restrict b,
    field_t* restrict out,
    size_t n
) {
#ifdef DEBUG
    assert(a != NULL && "a is null");
    assert(b != NULL && "b is null");
    assert(out != NULL && "output is null");
    assert(out != a && out != b && "output aliases input");
#endif
    for (size_t i = 0; i < n; i++) {
        out[i] = field_add(a[i], b[i]);
    }
}

#endif /* FIELD_OPS_H */
