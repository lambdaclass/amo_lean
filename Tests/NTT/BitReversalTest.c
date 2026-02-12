/**
 * BitReversalTest.c - Bit-Reversal Permutation Validation
 *
 * AMO-Lean Phase 5 QA: Final Audit
 *
 * Verifies that the bit-reversal permutation used in the NTT skeleton
 * is mathematically correct.
 *
 * Key properties tested:
 *   1. Involution: bit_reverse(bit_reverse(x)) = x
 *   2. Bijection: permutation is one-to-one
 *   3. Known values: verify against hand-computed results
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

/*===========================================================================
 * Bit-Reversal Implementation (copied from ntt_skeleton.c)
 *===========================================================================*/

static inline size_t bit_reverse(size_t x, size_t log2_n) {
    size_t result = 0;
    for (size_t i = 0; i < log2_n; i++) {
        result = (result << 1) | (x & 1);
        x >>= 1;
    }
    return result;
}

/*===========================================================================
 * Test Utilities
 *===========================================================================*/

static int tests_passed = 0;
static int tests_failed = 0;

#define ASSERT_EQ(actual, expected, msg) do { \
    if ((actual) == (expected)) { \
        tests_passed++; \
    } else { \
        tests_failed++; \
        printf("FAIL: %s\n", msg); \
        printf("  Expected: %zu\n", (size_t)(expected)); \
        printf("  Actual:   %zu\n", (size_t)(actual)); \
    } \
} while(0)

#define ASSERT_TRUE(cond, msg) do { \
    if (cond) { \
        tests_passed++; \
    } else { \
        tests_failed++; \
        printf("FAIL: %s\n", msg); \
    } \
} while(0)

/*===========================================================================
 * Test 1: Known Values for Small N
 *===========================================================================*/

static void test_known_values(void) {
    printf("\n=== Test 1: Known Values ===\n");

    /* N = 8 (log2_n = 3)
     * Index (binary) -> Reversed (binary) -> Reversed (decimal)
     *   0 (000) -> 000 -> 0
     *   1 (001) -> 100 -> 4
     *   2 (010) -> 010 -> 2
     *   3 (011) -> 110 -> 6
     *   4 (100) -> 001 -> 1
     *   5 (101) -> 101 -> 5
     *   6 (110) -> 011 -> 3
     *   7 (111) -> 111 -> 7
     */
    printf("Testing N=8 (log2_n=3)...\n");
    size_t expected_n8[] = {0, 4, 2, 6, 1, 5, 3, 7};
    for (size_t i = 0; i < 8; i++) {
        size_t rev = bit_reverse(i, 3);
        if (rev != expected_n8[i]) {
            printf("FAIL: bit_reverse(%zu, 3) = %zu, expected %zu\n",
                   i, rev, expected_n8[i]);
            tests_failed++;
        } else {
            tests_passed++;
        }
    }
    printf("N=8 tests: done\n");

    /* N = 16 (log2_n = 4)
     * First few values:
     *   0 (0000) -> 0000 -> 0
     *   1 (0001) -> 1000 -> 8
     *   2 (0010) -> 0100 -> 4
     *   3 (0011) -> 1100 -> 12
     *   4 (0100) -> 0010 -> 2
     *   5 (0101) -> 1010 -> 10
     */
    printf("Testing N=16 (log2_n=4)...\n");
    ASSERT_EQ(bit_reverse(0, 4), 0, "bit_reverse(0, 4) = 0");
    ASSERT_EQ(bit_reverse(1, 4), 8, "bit_reverse(1, 4) = 8");
    ASSERT_EQ(bit_reverse(2, 4), 4, "bit_reverse(2, 4) = 4");
    ASSERT_EQ(bit_reverse(3, 4), 12, "bit_reverse(3, 4) = 12");
    ASSERT_EQ(bit_reverse(4, 4), 2, "bit_reverse(4, 4) = 2");
    ASSERT_EQ(bit_reverse(5, 4), 10, "bit_reverse(5, 4) = 10");
}

/*===========================================================================
 * Test 2: Involution Property
 *===========================================================================*/

static void test_involution(void) {
    printf("\n=== Test 2: Involution (bit_reverse(bit_reverse(x)) = x) ===\n");

    size_t test_sizes[] = {8, 16, 32, 64, 128, 256, 512, 1024};
    size_t log2_sizes[] = {3, 4, 5, 6, 7, 8, 9, 10};

    for (int s = 0; s < 8; s++) {
        size_t n = test_sizes[s];
        size_t log2_n = log2_sizes[s];

        printf("Testing N=%zu...\n", n);
        bool all_pass = true;

        for (size_t i = 0; i < n; i++) {
            size_t rev = bit_reverse(i, log2_n);
            size_t rev_rev = bit_reverse(rev, log2_n);
            if (rev_rev != i) {
                printf("FAIL: bit_reverse(bit_reverse(%zu)) = %zu (expected %zu)\n",
                       i, rev_rev, i);
                all_pass = false;
                tests_failed++;
                break;
            }
        }

        if (all_pass) {
            tests_passed++;
        }
    }
}

/*===========================================================================
 * Test 3: Bijection Property
 *===========================================================================*/

static void test_bijection(void) {
    printf("\n=== Test 3: Bijection (permutation is one-to-one) ===\n");

    size_t test_sizes[] = {8, 16, 32, 64, 128, 256, 512, 1024};
    size_t log2_sizes[] = {3, 4, 5, 6, 7, 8, 9, 10};

    for (int s = 0; s < 8; s++) {
        size_t n = test_sizes[s];
        size_t log2_n = log2_sizes[s];

        printf("Testing N=%zu...\n", n);

        /* Check that all reversed values are distinct */
        bool* seen = (bool*)calloc(n, sizeof(bool));
        if (!seen) {
            printf("FAIL: Memory allocation failed\n");
            tests_failed++;
            continue;
        }

        bool is_bijection = true;
        for (size_t i = 0; i < n; i++) {
            size_t rev = bit_reverse(i, log2_n);
            if (rev >= n) {
                printf("FAIL: bit_reverse(%zu) = %zu >= N=%zu\n", i, rev, n);
                is_bijection = false;
                break;
            }
            if (seen[rev]) {
                printf("FAIL: Duplicate at bit_reverse(%zu) = %zu\n", i, rev);
                is_bijection = false;
                break;
            }
            seen[rev] = true;
        }

        free(seen);

        if (is_bijection) {
            tests_passed++;
        } else {
            tests_failed++;
        }
    }
}

/*===========================================================================
 * Test 4: Large N (N = 4096, 65536)
 *===========================================================================*/

static void test_large_n(void) {
    printf("\n=== Test 4: Large N Tests ===\n");

    /* N = 4096 (log2_n = 12) */
    printf("Testing N=4096 (involution + bijection)...\n");
    {
        size_t n = 4096;
        size_t log2_n = 12;
        bool* seen = (bool*)calloc(n, sizeof(bool));
        if (!seen) {
            printf("FAIL: Memory allocation failed\n");
            tests_failed++;
            return;
        }

        bool pass = true;
        for (size_t i = 0; i < n && pass; i++) {
            size_t rev = bit_reverse(i, log2_n);

            /* Check involution */
            if (bit_reverse(rev, log2_n) != i) {
                printf("FAIL: involution at i=%zu\n", i);
                pass = false;
            }

            /* Check bijection */
            if (rev >= n || seen[rev]) {
                printf("FAIL: bijection at i=%zu, rev=%zu\n", i, rev);
                pass = false;
            }
            seen[rev] = true;
        }

        free(seen);
        if (pass) {
            printf("PASS: N=4096\n");
            tests_passed++;
        } else {
            tests_failed++;
        }
    }

    /* N = 65536 (log2_n = 16) */
    printf("Testing N=65536 (spot check only)...\n");
    {
        size_t n = 65536;
        size_t log2_n = 16;

        /* Spot check a few values */
        ASSERT_EQ(bit_reverse(0, log2_n), 0, "bit_reverse(0, 16) = 0");
        ASSERT_EQ(bit_reverse(1, log2_n), 32768, "bit_reverse(1, 16) = 32768");
        /* 1 in binary is 0000000000000001, reversed is 1000000000000000 = 32768 */

        /* Check involution for a few random indices */
        for (size_t i = 0; i < 1000; i++) {
            size_t idx = (i * 67) % n;  /* Pseudo-random */
            size_t rev = bit_reverse(idx, log2_n);
            size_t rev_rev = bit_reverse(rev, log2_n);
            if (rev_rev != idx) {
                printf("FAIL: involution at idx=%zu\n", idx);
                tests_failed++;
                return;
            }
        }
        printf("PASS: N=65536 spot checks\n");
        tests_passed++;
    }
}

/*===========================================================================
 * Test 5: Permutation Consistency with NTT
 *===========================================================================*/

static void test_permutation_consistency(void) {
    printf("\n=== Test 5: Permutation Consistency ===\n");

    /* For NTT, after bit-reverse permutation, element at index i
     * should end up at bit_reverse(i). We test this explicitly. */

    printf("Testing that permutation produces correct reordering...\n");

    size_t n = 8;
    size_t log2_n = 3;

    /* Original array: [0, 1, 2, 3, 4, 5, 6, 7] */
    size_t original[8] = {0, 1, 2, 3, 4, 5, 6, 7};
    size_t permuted[8];

    /* Apply bit-reversal permutation */
    for (size_t i = 0; i < n; i++) {
        size_t j = bit_reverse(i, log2_n);
        permuted[j] = original[i];
    }

    /* After bit-reversal: [0, 4, 2, 6, 1, 5, 3, 7]
     * Because:
     *   original[0] -> permuted[bit_reverse(0)] = permuted[0] = 0
     *   original[1] -> permuted[bit_reverse(1)] = permuted[4] = 1
     *   original[2] -> permuted[bit_reverse(2)] = permuted[2] = 2
     *   original[3] -> permuted[bit_reverse(3)] = permuted[6] = 3
     *   original[4] -> permuted[bit_reverse(4)] = permuted[1] = 4
     *   original[5] -> permuted[bit_reverse(5)] = permuted[5] = 5
     *   original[6] -> permuted[bit_reverse(6)] = permuted[3] = 6
     *   original[7] -> permuted[bit_reverse(7)] = permuted[7] = 7
     */
    size_t expected[8] = {0, 4, 2, 6, 1, 5, 3, 7};

    bool match = true;
    for (size_t i = 0; i < n; i++) {
        if (permuted[i] != expected[i]) {
            printf("FAIL: permuted[%zu] = %zu, expected %zu\n",
                   i, permuted[i], expected[i]);
            match = false;
        }
    }

    if (match) {
        printf("PASS: Permutation produces expected reordering\n");
        tests_passed++;
    } else {
        tests_failed++;
    }
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Bit-Reversal Test: Permutation Validation\n");
    printf("  AMO-Lean Phase 5 QA Final Audit\n");
    printf("═══════════════════════════════════════════════════════════════\n");

    test_known_values();
    test_involution();
    test_bijection();
    test_large_n();
    test_permutation_consistency();

    printf("\n═══════════════════════════════════════════════════════════════\n");
    printf("  Results: %d passed, %d failed\n", tests_passed, tests_failed);
    printf("═══════════════════════════════════════════════════════════════\n");

    return tests_failed > 0 ? 1 : 0;
}
