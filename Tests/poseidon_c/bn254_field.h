/**
 * BN254 Field Arithmetic
 * Implementation for Poseidon2 S-box testing
 *
 * Field: BN254 scalar field
 * p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
 *
 * Representation: 4 x 64-bit limbs, little-endian
 * Montgomery form: x_mont = x * R mod p, where R = 2^256
 */

#ifndef BN254_FIELD_H
#define BN254_FIELD_H

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================================
 * Constants
 * ============================================================================ */

/* BN254 scalar field modulus p */
static const uint64_t BN254_P[4] = {
    0x43e1f593f0000001ULL,  /* limb 0 (least significant) */
    0x2833e84879b97091ULL,  /* limb 1 */
    0xb85045b68181585dULL,  /* limb 2 */
    0x30644e72e131a029ULL   /* limb 3 (most significant) */
};

/* R^2 mod p for Montgomery conversion */
static const uint64_t BN254_R2[4] = {
    0x1bb8e645ae216da7ULL,
    0x53fe3ab1e35c59e3ULL,
    0x8c49833d53bb8085ULL,
    0x0216d0b17f4e44a5ULL
};

/* -p^(-1) mod 2^64 for Montgomery reduction */
static const uint64_t BN254_INV = 0xc2e1f593efffffffULL;

/* ============================================================================
 * Type Definitions
 * ============================================================================ */

typedef struct {
    uint64_t limbs[4];
} bn254_fe;  /* Field element */

typedef struct {
    bn254_fe elem[3];
} poseidon_state_3;

typedef struct {
    uint64_t modulus[4];
    uint64_t r2[4];
    uint64_t inv;
} field_params;

/* ============================================================================
 * Basic Operations
 * ============================================================================ */

/* Initialize field parameters */
static inline void bn254_init_params(field_params *p) {
    memcpy(p->modulus, BN254_P, sizeof(BN254_P));
    memcpy(p->r2, BN254_R2, sizeof(BN254_R2));
    p->inv = BN254_INV;
}

/* Copy field element */
static inline void bn254_copy(bn254_fe *dst, const bn254_fe *src) {
    memcpy(dst->limbs, src->limbs, sizeof(dst->limbs));
}

/* Set to zero */
static inline void bn254_zero(bn254_fe *a) {
    memset(a->limbs, 0, sizeof(a->limbs));
}

/* Set to one (in Montgomery form) */
void bn254_one(bn254_fe *a, const field_params *p);

/* Check equality */
static inline bool bn254_eq(const bn254_fe *a, const bn254_fe *b) {
    return memcmp(a->limbs, b->limbs, sizeof(a->limbs)) == 0;
}

/* Compare: returns -1 if a < b, 0 if a == b, 1 if a > b */
int bn254_cmp(const bn254_fe *a, const bn254_fe *b);

/* ============================================================================
 * Arithmetic Operations
 * ============================================================================ */

/* Addition: c = a + b mod p */
void bn254_add(bn254_fe *c, const bn254_fe *a, const bn254_fe *b, const field_params *p);

/* Subtraction: c = a - b mod p */
void bn254_sub(bn254_fe *c, const bn254_fe *a, const bn254_fe *b, const field_params *p);

/* Montgomery multiplication: c = a * b * R^(-1) mod p */
void bn254_mul(bn254_fe *c, const bn254_fe *a, const bn254_fe *b, const field_params *p);

/* Montgomery squaring: c = a^2 * R^(-1) mod p */
void bn254_sqr(bn254_fe *c, const bn254_fe *a, const field_params *p);

/* Convert to Montgomery form: a_mont = a * R mod p */
void bn254_to_mont(bn254_fe *a_mont, const bn254_fe *a, const field_params *p);

/* Convert from Montgomery form: a = a_mont * R^(-1) mod p */
void bn254_from_mont(bn254_fe *a, const bn254_fe *a_mont, const field_params *p);

/* ============================================================================
 * S-box Operations
 * ============================================================================ */

/* S-box: x^5 using square chain (3 multiplications) */
void bn254_sbox5(bn254_fe *out, const bn254_fe *x, const field_params *p);

/* Full round S-box: apply x^5 to all state elements */
void bn254_sbox5_full_round(poseidon_state_3 *state, const field_params *p);

/* Partial round S-box: apply x^5 only to state[0] */
void bn254_sbox5_partial_round(poseidon_state_3 *state, const field_params *p);

/* ============================================================================
 * Utility Functions
 * ============================================================================ */

/* Print field element (for debugging) */
void bn254_print(const char *label, const bn254_fe *a);

/* Set from uint64_t (converts to Montgomery form) */
void bn254_from_u64(bn254_fe *a, uint64_t val, const field_params *p);

/* Set from 4 limbs (already in Montgomery form) */
static inline void bn254_from_limbs(bn254_fe *a, const uint64_t limbs[4]) {
    memcpy(a->limbs, limbs, sizeof(a->limbs));
}

/* Random field element (for testing) */
void bn254_random(bn254_fe *a, const field_params *p);

/* Seed the PRNG (for reproducible tests) */
void bn254_seed_random(uint64_t seed);

#ifdef __cplusplus
}
#endif

#endif /* BN254_FIELD_H */
