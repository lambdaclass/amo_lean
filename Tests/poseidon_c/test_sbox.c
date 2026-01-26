/**
 * Poseidon2 S-box Tests
 *
 * Test 2.1: S-Box Isolation Test (Correctness)
 * Test 2.2: Partial Round Logic Check (State Integrity)
 *
 * These tests verify mathematical correctness of the S-box implementation.
 */

#include "bn254_field.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ============================================================================
 * Test Infrastructure
 * ============================================================================ */

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_ASSERT(cond, msg) do { \
    if (!(cond)) { \
        printf("  FAIL: %s\n", msg); \
        tests_failed++; \
        return 0; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b, msg) do { \
    if (!bn254_eq(a, b)) { \
        printf("  FAIL: %s\n", msg); \
        bn254_print("    Expected", b); \
        bn254_print("    Got", a); \
        tests_failed++; \
        return 0; \
    } \
} while(0)

/* ============================================================================
 * Test 2.1: S-Box Isolation Test
 *
 * Verifies that x^5 is computed correctly by checking:
 * 1. Known test vectors
 * 2. Algebraic identity: x^5 = x * x^4 = x * (x^2)^2
 * 3. Edge cases: 0^5 = 0, 1^5 = 1
 * ============================================================================ */

/* Compute x^5 the naive way (5 multiplications) for verification */
static void naive_pow5(bn254_fe *out, const bn254_fe *x, const field_params *p) {
    bn254_fe x2, x3, x4;
    bn254_mul(&x2, x, x, p);      /* x^2 */
    bn254_mul(&x3, &x2, x, p);    /* x^3 */
    bn254_mul(&x4, &x3, x, p);    /* x^4 */
    bn254_mul(out, &x4, x, p);    /* x^5 */
}

static int test_sbox_zero(const field_params *p) {
    printf("  Test: 0^5 = 0\n");

    bn254_fe zero, result;
    bn254_zero(&zero);
    bn254_to_mont(&zero, &zero, p);  /* 0 in Montgomery form */

    bn254_sbox5(&result, &zero, p);

    /* 0^5 should be 0 */
    bn254_fe expected;
    bn254_zero(&expected);
    bn254_to_mont(&expected, &expected, p);

    TEST_ASSERT_EQ(&result, &expected, "0^5 should equal 0");

    printf("    PASS\n");
    tests_passed++;
    return 1;
}

static int test_sbox_one(const field_params *p) {
    printf("  Test: 1^5 = 1\n");

    bn254_fe one, result;
    bn254_one(&one, p);

    bn254_sbox5(&result, &one, p);

    /* 1^5 should be 1 */
    TEST_ASSERT_EQ(&result, &one, "1^5 should equal 1");

    printf("    PASS\n");
    tests_passed++;
    return 1;
}

static int test_sbox_small_values(const field_params *p) {
    printf("  Test: Small values (2^5=32, 3^5=243, 4^5=1024)\n");

    /* Test x = 2 */
    bn254_fe x, result, expected;
    bn254_from_u64(&x, 2, p);
    bn254_sbox5(&result, &x, p);
    bn254_from_u64(&expected, 32, p);  /* 2^5 = 32 */
    TEST_ASSERT_EQ(&result, &expected, "2^5 should equal 32");

    /* Test x = 3 */
    bn254_from_u64(&x, 3, p);
    bn254_sbox5(&result, &x, p);
    bn254_from_u64(&expected, 243, p);  /* 3^5 = 243 */
    TEST_ASSERT_EQ(&result, &expected, "3^5 should equal 243");

    /* Test x = 4 */
    bn254_from_u64(&x, 4, p);
    bn254_sbox5(&result, &x, p);
    bn254_from_u64(&expected, 1024, p);  /* 4^5 = 1024 */
    TEST_ASSERT_EQ(&result, &expected, "4^5 should equal 1024");

    printf("    PASS\n");
    tests_passed++;
    return 1;
}

static int test_sbox_vs_naive(const field_params *p, int num_tests) {
    printf("  Test: Square chain vs naive multiplication (%d random values)\n", num_tests);

    bn254_fe x, result_opt, result_naive;

    for (int i = 0; i < num_tests; i++) {
        bn254_random(&x, p);

        /* Optimized: square chain */
        bn254_sbox5(&result_opt, &x, p);

        /* Naive: 5 multiplications */
        naive_pow5(&result_naive, &x, p);

        if (!bn254_eq(&result_opt, &result_naive)) {
            printf("    FAIL at iteration %d\n", i);
            bn254_print("    x", &x);
            bn254_print("    optimized", &result_opt);
            bn254_print("    naive", &result_naive);
            tests_failed++;
            return 0;
        }
    }

    printf("    PASS (%d tests)\n", num_tests);
    tests_passed++;
    return 1;
}

static int test_sbox_algebraic_identity(const field_params *p, int num_tests) {
    printf("  Test: Algebraic identity x^5 = x * (x^2)^2 (%d random values)\n", num_tests);

    bn254_fe x, x2, x4, x5_direct, x5_identity;

    for (int i = 0; i < num_tests; i++) {
        bn254_random(&x, p);

        /* Direct: x^5 using sbox5 */
        bn254_sbox5(&x5_direct, &x, p);

        /* Identity: x * (x^2)^2 */
        bn254_sqr(&x2, &x, p);       /* x^2 */
        bn254_sqr(&x4, &x2, p);      /* (x^2)^2 = x^4 */
        bn254_mul(&x5_identity, &x, &x4, p);  /* x * x^4 */

        if (!bn254_eq(&x5_direct, &x5_identity)) {
            printf("    FAIL at iteration %d\n", i);
            bn254_print("    x", &x);
            bn254_print("    sbox5", &x5_direct);
            bn254_print("    x*(x^2)^2", &x5_identity);
            tests_failed++;
            return 0;
        }
    }

    printf("    PASS (%d tests)\n", num_tests);
    tests_passed++;
    return 1;
}

/* ============================================================================
 * Test 2.2: Partial Round Logic Check
 *
 * Verifies that partial_round ONLY modifies state[0], leaving
 * state[1] and state[2] completely unchanged (bit-for-bit).
 * ============================================================================ */

static int test_partial_round_isolation(const field_params *p, int num_tests) {
    printf("  Test: Partial round isolation (%d random states)\n", num_tests);

    poseidon_state_3 state, state_before;

    for (int i = 0; i < num_tests; i++) {
        /* Generate random state */
        bn254_random(&state.elem[0], p);
        bn254_random(&state.elem[1], p);
        bn254_random(&state.elem[2], p);

        /* Save original state */
        memcpy(&state_before, &state, sizeof(state));

        /* Apply partial round */
        bn254_sbox5_partial_round(&state, p);

        /* Check: state[1] must be IDENTICAL to original */
        if (!bn254_eq(&state.elem[1], &state_before.elem[1])) {
            printf("    FAIL: state[1] was modified at iteration %d\n", i);
            bn254_print("    before", &state_before.elem[1]);
            bn254_print("    after", &state.elem[1]);
            tests_failed++;
            return 0;
        }

        /* Check: state[2] must be IDENTICAL to original */
        if (!bn254_eq(&state.elem[2], &state_before.elem[2])) {
            printf("    FAIL: state[2] was modified at iteration %d\n", i);
            bn254_print("    before", &state_before.elem[2]);
            bn254_print("    after", &state.elem[2]);
            tests_failed++;
            return 0;
        }

        /* Check: state[0] MUST have changed (unless it was 0 or 1) */
        bn254_fe expected_s0;
        bn254_sbox5(&expected_s0, &state_before.elem[0], p);

        if (!bn254_eq(&state.elem[0], &expected_s0)) {
            printf("    FAIL: state[0] incorrect at iteration %d\n", i);
            bn254_print("    original", &state_before.elem[0]);
            bn254_print("    expected x^5", &expected_s0);
            bn254_print("    got", &state.elem[0]);
            tests_failed++;
            return 0;
        }
    }

    printf("    PASS (%d tests)\n", num_tests);
    tests_passed++;
    return 1;
}

static int test_full_round_all_change(const field_params *p, int num_tests) {
    printf("  Test: Full round modifies all elements (%d random states)\n", num_tests);

    poseidon_state_3 state;
    bn254_fe expected[3];

    for (int i = 0; i < num_tests; i++) {
        /* Generate random state (avoiding 0 and 1 which are fixed points) */
        for (int j = 0; j < 3; j++) {
            do {
                bn254_random(&state.elem[j], p);
            } while (bn254_eq(&state.elem[j], &(bn254_fe){{0,0,0,0}}));
        }

        /* Compute expected values */
        for (int j = 0; j < 3; j++) {
            bn254_sbox5(&expected[j], &state.elem[j], p);
        }

        /* Apply full round */
        bn254_sbox5_full_round(&state, p);

        /* Verify all elements are correct */
        for (int j = 0; j < 3; j++) {
            if (!bn254_eq(&state.elem[j], &expected[j])) {
                printf("    FAIL: state[%d] incorrect at iteration %d\n", j, i);
                tests_failed++;
                return 0;
            }
        }
    }

    printf("    PASS (%d tests)\n", num_tests);
    tests_passed++;
    return 1;
}

/* ============================================================================
 * Main Test Runner
 * ============================================================================ */

int main(int argc, char *argv[]) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Poseidon2 S-box Critical Correctness Tests\n");
    printf("  Phase Poseidon - Pre-Phase 3 Validation\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    /* Initialize field parameters */
    field_params p;
    bn254_init_params(&p);

    /* Seed PRNG */
    uint64_t seed = (argc > 1) ? (uint64_t)atoll(argv[1]) : (uint64_t)time(NULL);
    printf("Random seed: %llu\n\n", (unsigned long long)seed);
    bn254_seed_random(seed);

    /* Test 2.1: S-Box Isolation Test */
    printf("══════ Test 2.1: S-Box Isolation Test ══════\n");
    test_sbox_zero(&p);
    test_sbox_one(&p);
    test_sbox_small_values(&p);
    test_sbox_vs_naive(&p, 1000);
    test_sbox_algebraic_identity(&p, 1000);
    printf("\n");

    /* Test 2.2: Partial Round Logic Check */
    printf("══════ Test 2.2: Partial Round Logic Check ══════\n");
    test_partial_round_isolation(&p, 1000);
    test_full_round_all_change(&p, 100);
    printf("\n");

    /* Summary */
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  SUMMARY: %d passed, %d failed\n", tests_passed, tests_failed);
    printf("═══════════════════════════════════════════════════════════════\n");

    return tests_failed > 0 ? 1 : 0;
}
