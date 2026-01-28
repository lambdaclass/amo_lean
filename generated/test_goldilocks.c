/**
 * test_goldilocks.c - Comprehensive Tests for Goldilocks Field
 *
 * Phase 1: Edge Case Testing
 *
 * This file tests all critical edge cases identified in the technical review:
 * - Zero and identity operations
 * - Maximum values (p-1)
 * - Overflow scenarios ((p-1) + (p-1))
 * - Values near 2^32 (the special exponent)
 * - Reduction correctness
 *
 * Compile with sanitizers:
 *   clang -DFIELD_GOLDILOCKS -O1 -g -fsanitize=undefined,integer \
 *         -o test_goldilocks test_goldilocks.c
 *
 * Run:
 *   ./test_goldilocks
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#define FIELD_GOLDILOCKS
#include "field_goldilocks.h"

/*===========================================================================
 * Test Infrastructure
 *===========================================================================*/

static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) \
    do { \
        tests_run++; \
        printf("  [%3d] %-50s ", tests_run, name); \
    } while(0)

#define PASS() \
    do { \
        tests_passed++; \
        printf("PASS\n"); \
    } while(0)

#define FAIL(msg, ...) \
    do { \
        tests_failed++; \
        printf("FAIL\n"); \
        printf("        " msg "\n", ##__VA_ARGS__); \
    } while(0)

#define ASSERT_EQ(expected, actual, msg) \
    do { \
        if ((expected) != (actual)) { \
            FAIL(msg ": expected 0x%llx, got 0x%llx", \
                 (unsigned long long)(expected), (unsigned long long)(actual)); \
            return; \
        } \
    } while(0)

/*===========================================================================
 * Constants for Testing
 *===========================================================================*/

#define P GOLDILOCKS_ORDER
#define P_MINUS_1 (GOLDILOCKS_ORDER - 1)
#define P_MINUS_2 (GOLDILOCKS_ORDER - 2)
#define EPSILON GOLDILOCKS_EPSILON
#define TWO_POW_32 (1ULL << 32)
#define TWO_POW_32_MINUS_1 ((1ULL << 32) - 1)
#define TWO_POW_32_PLUS_1 ((1ULL << 32) + 1)

/*===========================================================================
 * Addition Tests
 *===========================================================================*/

void test_add_zero_zero(void) {
    TEST("add: 0 + 0 = 0");
    goldilocks_t result = goldilocks_add(0, 0);
    ASSERT_EQ(0, result, "0 + 0");
    PASS();
}

void test_add_zero_one(void) {
    TEST("add: 0 + 1 = 1");
    goldilocks_t result = goldilocks_add(0, 1);
    ASSERT_EQ(1, result, "0 + 1");
    PASS();
}

void test_add_one_pMinus1(void) {
    TEST("add: 1 + (p-1) = 0 (wrap)");
    goldilocks_t result = goldilocks_add(1, P_MINUS_1);
    ASSERT_EQ(0, result, "1 + (p-1)");
    PASS();
}

void test_add_pMinus1_pMinus1(void) {
    TEST("add: (p-1) + (p-1) = p-2 (MAX OVERFLOW)");
    /*
     * This is the CRITICAL test that would have failed with the buggy
     * Phase 0 implementation. (p-1) + (p-1) = 2p - 2, which overflows
     * 64 bits. The correct result is (2p - 2) mod p = p - 2.
     */
    goldilocks_t result = goldilocks_add(P_MINUS_1, P_MINUS_1);
    ASSERT_EQ(P_MINUS_2, result, "(p-1) + (p-1)");
    PASS();
}

void test_add_half_half(void) {
    TEST("add: p/2 + p/2 ≈ p-1");
    goldilocks_t half = P / 2;
    goldilocks_t result = goldilocks_add(half, half);
    /* p/2 + p/2 = p (if p even) or p-1 (if p odd). p is odd, so... */
    /* Actually (p-1)/2 + (p-1)/2 = p - 1 */
    goldilocks_t expected = (P % 2 == 0) ? 0 : P - 1;
    /* p = 2^64 - 2^32 + 1 is odd, and p/2 truncates, so half + half = p-1 or 0 */
    /* half = (p-1)/2 when p is odd, so half + half = p - 1 */
    ASSERT_EQ(P - 1, result, "p/2 + p/2");
    PASS();
}

void test_add_near_2pow32(void) {
    TEST("add: (2^32-1) + (2^32+1) = 2^33");
    goldilocks_t a = TWO_POW_32_MINUS_1;
    goldilocks_t b = TWO_POW_32_PLUS_1;
    goldilocks_t result = goldilocks_add(a, b);
    goldilocks_t expected = (1ULL << 33);  /* 2^33, which is < p */
    ASSERT_EQ(expected, result, "(2^32-1) + (2^32+1)");
    PASS();
}

/*===========================================================================
 * Subtraction Tests
 *===========================================================================*/

void test_sub_zero_zero(void) {
    TEST("sub: 0 - 0 = 0");
    goldilocks_t result = goldilocks_sub(0, 0);
    ASSERT_EQ(0, result, "0 - 0");
    PASS();
}

void test_sub_one_one(void) {
    TEST("sub: 1 - 1 = 0");
    goldilocks_t result = goldilocks_sub(1, 1);
    ASSERT_EQ(0, result, "1 - 1");
    PASS();
}

void test_sub_zero_one(void) {
    TEST("sub: 0 - 1 = p-1 (underflow)");
    goldilocks_t result = goldilocks_sub(0, 1);
    ASSERT_EQ(P_MINUS_1, result, "0 - 1");
    PASS();
}

void test_sub_pMinus1_pMinus1(void) {
    TEST("sub: (p-1) - (p-1) = 0");
    goldilocks_t result = goldilocks_sub(P_MINUS_1, P_MINUS_1);
    ASSERT_EQ(0, result, "(p-1) - (p-1)");
    PASS();
}

/*===========================================================================
 * Multiplication Tests
 *===========================================================================*/

void test_mul_zero_any(void) {
    TEST("mul: 0 * random = 0");
    goldilocks_t result = goldilocks_mul(0, 12345678901234ULL);
    ASSERT_EQ(0, result, "0 * x");
    PASS();
}

void test_mul_one_any(void) {
    TEST("mul: 1 * x = x");
    goldilocks_t x = 9876543210ULL;
    goldilocks_t result = goldilocks_mul(1, x);
    ASSERT_EQ(x, result, "1 * x");
    PASS();
}

void test_mul_pMinus1_pMinus1(void) {
    TEST("mul: (p-1) * (p-1) = 1 (MAX PRODUCT)");
    /*
     * (p-1)^2 mod p = (-1)^2 mod p = 1
     * This tests the maximum possible product: (p-1)^2 ≈ 2^128
     */
    goldilocks_t result = goldilocks_mul(P_MINUS_1, P_MINUS_1);
    ASSERT_EQ(1, result, "(p-1) * (p-1)");
    PASS();
}

void test_mul_near_sqrt_p(void) {
    TEST("mul: 2^32 * 2^32 = 2^64 mod p = EPSILON");
    goldilocks_t a = TWO_POW_32;
    goldilocks_t result = goldilocks_mul(a, a);
    /* 2^64 mod p = 2^32 - 1 = EPSILON */
    ASSERT_EQ(EPSILON, result, "2^32 * 2^32");
    PASS();
}

void test_mul_epsilon_squared(void) {
    TEST("mul: EPSILON * EPSILON");
    /*
     * EPSILON = 2^32 - 1
     * EPSILON^2 = 2^64 - 2^33 + 1
     * 2^64 ≡ EPSILON (mod p)
     * So EPSILON^2 ≡ EPSILON - 2^33 + 1 (mod p)
     * = (2^32 - 1) - 2^33 + 1 = 2^32 - 2^33 = -2^32 ≡ p - 2^32 (mod p)
     */
    goldilocks_t result = goldilocks_mul(EPSILON, EPSILON);
    goldilocks_t expected = P - TWO_POW_32;
    ASSERT_EQ(expected, result, "EPSILON * EPSILON");
    PASS();
}

/*===========================================================================
 * Reduction Tests
 *===========================================================================*/

void test_reduce128_pure_low(void) {
    TEST("reduce128: x < p (no reduction needed)");
    __uint128_t x = P_MINUS_1;
    goldilocks_t result = goldilocks_reduce128(x);
    ASSERT_EQ(P_MINUS_1, result, "x < p");
    PASS();
}

void test_reduce128_exactly_p(void) {
    TEST("reduce128: x = p -> 0");
    __uint128_t x = P;
    goldilocks_t result = goldilocks_reduce128(x);
    ASSERT_EQ(0, result, "x = p");
    PASS();
}

void test_reduce128_2pow64(void) {
    TEST("reduce128: 2^64 mod p = EPSILON");
    __uint128_t x = (__uint128_t)1 << 64;
    goldilocks_t result = goldilocks_reduce128(x);
    ASSERT_EQ(EPSILON, result, "2^64 mod p");
    PASS();
}

void test_reduce128_2pow96(void) {
    TEST("reduce128: 2^96 mod p = p-1 = -1");
    __uint128_t x = (__uint128_t)1 << 96;
    goldilocks_t result = goldilocks_reduce128(x);
    ASSERT_EQ(P_MINUS_1, result, "2^96 mod p");
    PASS();
}

void test_reduce128_max_product(void) {
    TEST("reduce128: (p-1)^2 mod p = 1");
    __uint128_t x = (__uint128_t)P_MINUS_1 * P_MINUS_1;
    goldilocks_t result = goldilocks_reduce128(x);
    ASSERT_EQ(1, result, "(p-1)^2 mod p");
    PASS();
}

/*===========================================================================
 * Negation and Inverse Tests
 *===========================================================================*/

void test_neg_zero(void) {
    TEST("neg: -0 = 0");
    goldilocks_t result = goldilocks_neg(0);
    ASSERT_EQ(0, result, "-0");
    PASS();
}

void test_neg_one(void) {
    TEST("neg: -1 = p-1");
    goldilocks_t result = goldilocks_neg(1);
    ASSERT_EQ(P_MINUS_1, result, "-1");
    PASS();
}

void test_neg_pMinus1(void) {
    TEST("neg: -(p-1) = 1");
    goldilocks_t result = goldilocks_neg(P_MINUS_1);
    ASSERT_EQ(1, result, "-(p-1)");
    PASS();
}

void test_inv_one(void) {
    TEST("inv: 1^(-1) = 1");
    goldilocks_t result = goldilocks_inv(1);
    ASSERT_EQ(1, result, "1^(-1)");
    PASS();
}

void test_inv_pMinus1(void) {
    TEST("inv: (p-1)^(-1) = p-1 (since (p-1)^2 = 1)");
    goldilocks_t result = goldilocks_inv(P_MINUS_1);
    ASSERT_EQ(P_MINUS_1, result, "(p-1)^(-1)");
    PASS();
}

void test_inv_verify(void) {
    TEST("inv: x * x^(-1) = 1");
    goldilocks_t x = 12345678901234567ULL;
    goldilocks_t x_inv = goldilocks_inv(x);
    goldilocks_t product = goldilocks_mul(x, x_inv);
    ASSERT_EQ(1, product, "x * x^(-1)");
    PASS();
}

/*===========================================================================
 * Field Law Tests
 *===========================================================================*/

void test_add_commutative(void) {
    TEST("field law: a + b = b + a");
    goldilocks_t a = 0xDEADBEEFCAFEBABEULL % P;
    goldilocks_t b = 0x123456789ABCDEF0ULL % P;
    goldilocks_t ab = goldilocks_add(a, b);
    goldilocks_t ba = goldilocks_add(b, a);
    ASSERT_EQ(ab, ba, "commutativity");
    PASS();
}

void test_mul_commutative(void) {
    TEST("field law: a * b = b * a");
    goldilocks_t a = 0xDEADBEEFCAFEBABEULL % P;
    goldilocks_t b = 0x123456789ABCDEF0ULL % P;
    goldilocks_t ab = goldilocks_mul(a, b);
    goldilocks_t ba = goldilocks_mul(b, a);
    ASSERT_EQ(ab, ba, "commutativity");
    PASS();
}

void test_add_associative(void) {
    TEST("field law: (a + b) + c = a + (b + c)");
    goldilocks_t a = 0x1111111111111111ULL % P;
    goldilocks_t b = 0x2222222222222222ULL % P;
    goldilocks_t c = 0x3333333333333333ULL % P;
    goldilocks_t lhs = goldilocks_add(goldilocks_add(a, b), c);
    goldilocks_t rhs = goldilocks_add(a, goldilocks_add(b, c));
    ASSERT_EQ(lhs, rhs, "associativity");
    PASS();
}

void test_mul_associative(void) {
    TEST("field law: (a * b) * c = a * (b * c)");
    goldilocks_t a = 0x1111111111111111ULL % P;
    goldilocks_t b = 0x2222222222222222ULL % P;
    goldilocks_t c = 0x3333333333333333ULL % P;
    goldilocks_t lhs = goldilocks_mul(goldilocks_mul(a, b), c);
    goldilocks_t rhs = goldilocks_mul(a, goldilocks_mul(b, c));
    ASSERT_EQ(lhs, rhs, "associativity");
    PASS();
}

void test_distributive(void) {
    TEST("field law: a * (b + c) = a*b + a*c");
    goldilocks_t a = 0xAAAAAAAAAAAAAAAAULL % P;
    goldilocks_t b = 0xBBBBBBBBBBBBBBBBULL % P;
    goldilocks_t c = 0xCCCCCCCCCCCCCCCCULL % P;
    goldilocks_t lhs = goldilocks_mul(a, goldilocks_add(b, c));
    goldilocks_t rhs = goldilocks_add(goldilocks_mul(a, b), goldilocks_mul(a, c));
    ASSERT_EQ(lhs, rhs, "distributivity");
    PASS();
}

/*===========================================================================
 * S-Box Tests (CRITICAL: Must be x^7, not x^5)
 *===========================================================================*/

void test_sbox_zero(void) {
    TEST("sbox: 0^7 = 0");
    goldilocks_t result = goldilocks_sbox(0);
    ASSERT_EQ(0, result, "0^7");
    PASS();
}

void test_sbox_one(void) {
    TEST("sbox: 1^7 = 1");
    goldilocks_t result = goldilocks_sbox(1);
    ASSERT_EQ(1, result, "1^7");
    PASS();
}

void test_sbox_two(void) {
    TEST("sbox: 2^7 = 128");
    goldilocks_t result = goldilocks_sbox(2);
    ASSERT_EQ(128, result, "2^7");
    PASS();
}

void test_sbox_invertibility(void) {
    TEST("sbox: sbox_inv(sbox(x)) = x (invertibility)");
    goldilocks_t x = 12345678901234567ULL;
    goldilocks_t y = goldilocks_sbox(x);
    goldilocks_t x_recovered = goldilocks_sbox_inv(y);
    ASSERT_EQ(x, x_recovered, "sbox invertibility");
    PASS();
}

void test_sbox_random_invertibility(void) {
    TEST("sbox: random invertibility test");
    /* Test with several random values */
    goldilocks_t test_values[] = {
        42, 1000000007, 0xDEADBEEFULL, 0xCAFEBABEULL,
        P_MINUS_1, P_MINUS_2, TWO_POW_32, EPSILON
    };
    for (size_t i = 0; i < sizeof(test_values)/sizeof(test_values[0]); i++) {
        goldilocks_t x = test_values[i];
        goldilocks_t y = goldilocks_sbox(x);
        goldilocks_t x_recovered = goldilocks_sbox_inv(y);
        if (x != x_recovered) {
            FAIL("Failed for x = 0x%llx", (unsigned long long)x);
            return;
        }
    }
    PASS();
}

void test_sbox_exponent_is_7(void) {
    TEST("sbox: verifying exponent is 7 (not 5)");
    /* Verify by computing x^7 manually and comparing */
    goldilocks_t x = 3;
    goldilocks_t expected = goldilocks_pow(x, 7);
    goldilocks_t actual = goldilocks_sbox(x);
    ASSERT_EQ(expected, actual, "sbox uses exponent 7");
    PASS();
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║     GOLDILOCKS FIELD TESTS (Phase 1)                         ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");
    printf("\n");
    printf("Field: Goldilocks (p = 2^64 - 2^32 + 1)\n");
    printf("p = 0x%llx\n", (unsigned long long)P);
    printf("EPSILON = 0x%llx\n", (unsigned long long)EPSILON);
    printf("\n");

    printf("=== Addition Tests ===\n");
    test_add_zero_zero();
    test_add_zero_one();
    test_add_one_pMinus1();
    test_add_pMinus1_pMinus1();
    test_add_half_half();
    test_add_near_2pow32();

    printf("\n=== Subtraction Tests ===\n");
    test_sub_zero_zero();
    test_sub_one_one();
    test_sub_zero_one();
    test_sub_pMinus1_pMinus1();

    printf("\n=== Multiplication Tests ===\n");
    test_mul_zero_any();
    test_mul_one_any();
    test_mul_pMinus1_pMinus1();
    test_mul_near_sqrt_p();
    test_mul_epsilon_squared();

    printf("\n=== Reduction Tests ===\n");
    test_reduce128_pure_low();
    test_reduce128_exactly_p();
    test_reduce128_2pow64();
    test_reduce128_2pow96();
    test_reduce128_max_product();

    printf("\n=== Negation and Inverse Tests ===\n");
    test_neg_zero();
    test_neg_one();
    test_neg_pMinus1();
    test_inv_one();
    test_inv_pMinus1();
    test_inv_verify();

    printf("\n=== Field Law Tests ===\n");
    test_add_commutative();
    test_mul_commutative();
    test_add_associative();
    test_mul_associative();
    test_distributive();

    printf("\n=== S-Box Tests (x^7) ===\n");
    test_sbox_zero();
    test_sbox_one();
    test_sbox_two();
    test_sbox_invertibility();
    test_sbox_random_invertibility();
    test_sbox_exponent_is_7();

    printf("\n");
    printf("════════════════════════════════════════════════════════════════\n");
    printf("Results: %d/%d tests passed\n", tests_passed, tests_run);

    if (tests_failed > 0) {
        printf("FAILED: %d tests\n", tests_failed);
        printf("════════════════════════════════════════════════════════════════\n");
        return 1;
    }

    printf("ALL TESTS PASSED ✓\n");
    printf("════════════════════════════════════════════════════════════════\n");
    return 0;
}
