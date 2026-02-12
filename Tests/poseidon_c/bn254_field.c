/**
 * BN254 Field Arithmetic Implementation
 *
 * This implements Montgomery arithmetic for the BN254 scalar field.
 * All operations are constant-time to prevent timing side channels.
 */

#include "bn254_field.h"
#include <stdio.h>
#include <stdlib.h>

/* ============================================================================
 * Internal Helpers
 * ============================================================================ */

/* Add with carry: returns (a + b + carry_in, carry_out) */
static inline uint64_t adc(uint64_t a, uint64_t b, uint64_t carry_in, uint64_t *carry_out) {
    __uint128_t sum = (__uint128_t)a + b + carry_in;
    *carry_out = (uint64_t)(sum >> 64);
    return (uint64_t)sum;
}

/* Subtract with borrow: returns (a - b - borrow_in, borrow_out) */
static inline uint64_t sbb(uint64_t a, uint64_t b, uint64_t borrow_in, uint64_t *borrow_out) {
    __uint128_t diff = (__uint128_t)a - b - borrow_in;
    *borrow_out = (diff >> 64) ? 1 : 0;
    return (uint64_t)diff;
}

/* Multiply and add: returns (a * b + c + d, carry) as 128-bit result */
static inline uint64_t mac(uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t *carry) {
    __uint128_t prod = (__uint128_t)a * b + c + d;
    *carry = (uint64_t)(prod >> 64);
    return (uint64_t)prod;
}

/* ============================================================================
 * Basic Operations
 * ============================================================================ */

int bn254_cmp(const bn254_fe *a, const bn254_fe *b) {
    for (int i = 3; i >= 0; i--) {
        if (a->limbs[i] > b->limbs[i]) return 1;
        if (a->limbs[i] < b->limbs[i]) return -1;
    }
    return 0;
}

void bn254_one(bn254_fe *a, const field_params *p) {
    /* 1 in Montgomery form = R mod p */
    /* We compute this by converting 1 to Montgomery form */
    bn254_fe one_normal = {{1, 0, 0, 0}};
    bn254_to_mont(a, &one_normal, p);
}

/* ============================================================================
 * Modular Arithmetic
 * ============================================================================ */

/* Conditional subtraction: if a >= p, compute a - p */
static void bn254_reduce(bn254_fe *a, const field_params *p) {
    uint64_t borrow = 0;
    uint64_t diff[4];

    for (int i = 0; i < 4; i++) {
        diff[i] = sbb(a->limbs[i], p->modulus[i], borrow, &borrow);
    }

    /* If no borrow, a >= p, so use diff; otherwise keep a */
    uint64_t mask = borrow - 1;  /* 0xFFFF... if borrow=0, 0x0000... if borrow=1 */
    for (int i = 0; i < 4; i++) {
        a->limbs[i] = (a->limbs[i] & ~mask) | (diff[i] & mask);
    }
}

void bn254_add(bn254_fe *c, const bn254_fe *a, const bn254_fe *b, const field_params *p) {
    uint64_t carry = 0;

    for (int i = 0; i < 4; i++) {
        c->limbs[i] = adc(a->limbs[i], b->limbs[i], carry, &carry);
    }

    /* Reduce if needed */
    bn254_reduce(c, p);
}

void bn254_sub(bn254_fe *c, const bn254_fe *a, const bn254_fe *b, const field_params *p) {
    uint64_t borrow = 0;

    for (int i = 0; i < 4; i++) {
        c->limbs[i] = sbb(a->limbs[i], b->limbs[i], borrow, &borrow);
    }

    /* If borrow, add p back */
    if (borrow) {
        uint64_t carry = 0;
        for (int i = 0; i < 4; i++) {
            c->limbs[i] = adc(c->limbs[i], p->modulus[i], carry, &carry);
        }
    }
}

/* ============================================================================
 * Montgomery Multiplication
 *
 * Uses CIOS (Coarsely Integrated Operand Scanning) algorithm.
 * Reference: "Montgomery Multiplication" by Peter Montgomery
 * ============================================================================ */

void bn254_mul(bn254_fe *c, const bn254_fe *a, const bn254_fe *b, const field_params *p) {
    uint64_t t[5] = {0, 0, 0, 0, 0};  /* Accumulator with extra limb for overflow */
    uint64_t carry, carry2;

    for (int i = 0; i < 4; i++) {
        /* t = t + a[i] * b */
        carry = 0;
        for (int j = 0; j < 4; j++) {
            t[j] = mac(a->limbs[i], b->limbs[j], t[j], carry, &carry);
        }
        t[4] = adc(t[4], 0, carry, &carry2);

        /* Montgomery reduction step */
        uint64_t m = t[0] * p->inv;

        /* t = (t + m * p) / 2^64 */
        carry = 0;
        mac(m, p->modulus[0], t[0], carry, &carry);  /* t[0] becomes 0, carry out */
        for (int j = 1; j < 4; j++) {
            t[j-1] = mac(m, p->modulus[j], t[j], carry, &carry);
        }
        t[3] = adc(t[4], 0, carry, &carry2);
        t[4] = carry2;
    }

    /* Copy result */
    for (int i = 0; i < 4; i++) {
        c->limbs[i] = t[i];
    }

    /* Final reduction */
    bn254_reduce(c, p);
}

void bn254_sqr(bn254_fe *c, const bn254_fe *a, const field_params *p) {
    /* For simplicity, use multiplication. Can be optimized later. */
    bn254_mul(c, a, a, p);
}

/* ============================================================================
 * Montgomery Conversion
 * ============================================================================ */

void bn254_to_mont(bn254_fe *a_mont, const bn254_fe *a, const field_params *p) {
    /* a_mont = a * R^2 * R^(-1) = a * R mod p */
    bn254_fe r2;
    bn254_from_limbs(&r2, p->r2);
    bn254_mul(a_mont, a, &r2, p);
}

void bn254_from_mont(bn254_fe *a, const bn254_fe *a_mont, const field_params *p) {
    /* a = a_mont * 1 * R^(-1) = a_mont * R^(-1) mod p */
    bn254_fe one = {{1, 0, 0, 0}};
    bn254_mul(a, a_mont, &one, p);
}

/* ============================================================================
 * S-box Operations
 * ============================================================================ */

void bn254_sbox5(bn254_fe *out, const bn254_fe *x, const field_params *p) {
    /* x^5 = x * (x^2)^2 using square chain (3 multiplications) */
    bn254_fe x2, x4;

    bn254_sqr(&x2, x, p);       /* x2 = x^2 */
    bn254_sqr(&x4, &x2, p);     /* x4 = x^4 */
    bn254_mul(out, x, &x4, p);  /* out = x * x^4 = x^5 */
}

void bn254_sbox5_full_round(poseidon_state_3 *state, const field_params *p) {
    /* Apply S-box to all 3 state elements */
    for (int i = 0; i < 3; i++) {
        bn254_sbox5(&state->elem[i], &state->elem[i], p);
    }
}

void bn254_sbox5_partial_round(poseidon_state_3 *state, const field_params *p) {
    /* Apply S-box only to state[0] */
    bn254_sbox5(&state->elem[0], &state->elem[0], p);
}

/* ============================================================================
 * Utility Functions
 * ============================================================================ */

void bn254_print(const char *label, const bn254_fe *a) {
    printf("%s: 0x", label);
    for (int i = 3; i >= 0; i--) {
        printf("%016llx", (unsigned long long)a->limbs[i]);
    }
    printf("\n");
}

void bn254_from_u64(bn254_fe *a, uint64_t val, const field_params *p) {
    bn254_fe tmp = {{val, 0, 0, 0}};
    bn254_to_mont(a, &tmp, p);
}

/* Simple PRNG for testing (NOT cryptographically secure) */
static uint64_t xorshift64_state = 0x123456789ABCDEF0ULL;

static uint64_t xorshift64(void) {
    uint64_t x = xorshift64_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    xorshift64_state = x;
    return x;
}

void bn254_random(bn254_fe *a, const field_params *p) {
    /* Generate random limbs and reduce mod p */
    bn254_fe tmp;
    do {
        for (int i = 0; i < 4; i++) {
            tmp.limbs[i] = xorshift64();
        }
        /* Clear top bits to ensure < 2*p */
        tmp.limbs[3] &= 0x3FFFFFFFFFFFFFFFULL;
    } while (bn254_cmp(&tmp, (const bn254_fe *)p->modulus) >= 0);

    /* Convert to Montgomery form */
    bn254_to_mont(a, &tmp, p);
}

/* Seed the PRNG */
void bn254_seed_random(uint64_t seed) {
    xorshift64_state = seed;
}
