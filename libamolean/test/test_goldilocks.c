/**
 * AMO-Lean: Goldilocks Field Tests (Scalar)
 *
 * Tests for the formally verified Goldilocks field implementation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <amolean/field_goldilocks.h>

#define TEST_COUNT 37

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name, cond) do { \
    if (cond) { \
        printf("  [PASS] %s\n", name); \
        tests_passed++; \
    } else { \
        printf("  [FAIL] %s\n", name); \
        tests_failed++; \
    } \
} while(0)

/* Test helper: Simple PRNG for reproducible tests */
static uint64_t prng_state = 0x123456789ABCDEF0ULL;
static uint64_t prng_next(void) {
    prng_state ^= prng_state >> 12;
    prng_state ^= prng_state << 25;
    prng_state ^= prng_state >> 27;
    return prng_state * 0x2545F4914F6CDD1DULL;
}

static uint64_t random_field_element(void) {
    return prng_next() % GOLDILOCKS_P;
}

void test_addition(void) {
    printf("\n=== Addition Tests ===\n");

    /* 0 + 0 = 0 */
    TEST("0 + 0 = 0", goldilocks_add(0, 0) == 0);

    /* 1 + 0 = 1 */
    TEST("1 + 0 = 1", goldilocks_add(1, 0) == 1);

    /* p-1 + 1 = 0 (wraparound) */
    TEST("(p-1) + 1 = 0", goldilocks_add(GOLDILOCKS_P - 1, 1) == 0);

    /* Random tests */
    int random_passed = 1;
    for (int i = 0; i < 100; i++) {
        uint64_t a = random_field_element();
        uint64_t b = random_field_element();
        uint64_t result = goldilocks_add(a, b);
        if (result >= GOLDILOCKS_P) {
            random_passed = 0;
            break;
        }
    }
    TEST("100 random additions in field", random_passed);
}

void test_subtraction(void) {
    printf("\n=== Subtraction Tests ===\n");

    /* 0 - 0 = 0 */
    TEST("0 - 0 = 0", goldilocks_sub(0, 0) == 0);

    /* 1 - 1 = 0 */
    TEST("1 - 1 = 0", goldilocks_sub(1, 1) == 0);

    /* 0 - 1 = p - 1 */
    TEST("0 - 1 = p-1", goldilocks_sub(0, 1) == GOLDILOCKS_P - 1);

    /* Random tests */
    int random_passed = 1;
    for (int i = 0; i < 100; i++) {
        uint64_t a = random_field_element();
        uint64_t b = random_field_element();
        uint64_t result = goldilocks_sub(a, b);
        if (result >= GOLDILOCKS_P) {
            random_passed = 0;
            break;
        }
    }
    TEST("100 random subtractions in field", random_passed);
}

void test_multiplication(void) {
    printf("\n=== Multiplication Tests ===\n");

    /* 0 * anything = 0 */
    TEST("0 * 12345 = 0", goldilocks_mul(0, 12345) == 0);

    /* 1 * x = x */
    TEST("1 * 12345 = 12345", goldilocks_mul(1, 12345) == 12345);

    /* EPSILON * EPSILON */
    uint64_t eps_sq = goldilocks_mul(GOLDILOCKS_EPSILON, GOLDILOCKS_EPSILON);
    TEST("EPSILON^2 in field", eps_sq < GOLDILOCKS_P);

    /* Random tests */
    int random_passed = 1;
    for (int i = 0; i < 100; i++) {
        uint64_t a = random_field_element();
        uint64_t b = random_field_element();
        uint64_t result = goldilocks_mul(a, b);
        if (result >= GOLDILOCKS_P) {
            random_passed = 0;
            break;
        }
    }
    TEST("100 random multiplications in field", random_passed);
}

void test_power(void) {
    printf("\n=== Power Tests ===\n");

    /* x^0 = 1 */
    TEST("12345^0 = 1", goldilocks_pow(12345, 0) == 1);

    /* x^1 = x */
    TEST("12345^1 = 12345", goldilocks_pow(12345, 1) == 12345);

    /* 2^10 = 1024 */
    TEST("2^10 = 1024", goldilocks_pow(2, 10) == 1024);

    /* Fermat's little theorem: x^(p-1) = 1 for x != 0 */
    uint64_t x = 7;
    TEST("7^(p-1) = 1 (Fermat)", goldilocks_pow(x, GOLDILOCKS_P - 1) == 1);
}

void test_edge_cases(void) {
    printf("\n=== Edge Case Tests ===\n");

    /* Maximum value that needs reduction */
    uint64_t max_val = GOLDILOCKS_P - 1;
    TEST("(p-1) + (p-1) < p", goldilocks_add(max_val, max_val) < GOLDILOCKS_P);

    /* Verify EPSILON constant */
    TEST("EPSILON = 2^32 - 1", GOLDILOCKS_EPSILON == 0xFFFFFFFFULL);

    /* Verify p = 2^64 - 2^32 + 1 */
    TEST("p = 2^64 - EPSILON", GOLDILOCKS_P == (0ULL - GOLDILOCKS_EPSILON));
}

int main(void) {
    printf("AMO-Lean Goldilocks Field Tests (Scalar)\n");
    printf("=========================================\n");

    test_addition();
    test_subtraction();
    test_multiplication();
    test_power();
    test_edge_cases();

    printf("\n=========================================\n");
    printf("Results: %d/%d tests passed\n", tests_passed, tests_passed + tests_failed);

    return tests_failed > 0 ? 1 : 0;
}
