/**
 * AMO-Lean: Goldilocks Field Tests (AVX2)
 *
 * Tests for the AVX2-optimized Goldilocks field implementation.
 * Validates that SIMD operations match scalar operations.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <amolean/field_goldilocks.h>
#include <amolean/field_goldilocks_avx2.h>

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

/* Extract elements from AVX2 vector */
static void extract_avx2(const __m256i v, uint64_t out[4]) {
    _mm256_storeu_si256((__m256i*)out, v);
}

void test_avx2_add_consistency(void) {
    printf("\n=== AVX2 Addition Consistency Tests ===\n");

    int all_passed = 1;
    for (int i = 0; i < 100 && all_passed; i++) {
        uint64_t a[4], b[4], result_scalar[4], result_avx2[4];

        for (int j = 0; j < 4; j++) {
            a[j] = random_field_element();
            b[j] = random_field_element();
            result_scalar[j] = goldilocks_add(a[j], b[j]);
        }

        __m256i va = _mm256_loadu_si256((const __m256i*)a);
        __m256i vb = _mm256_loadu_si256((const __m256i*)b);
        __m256i vr = goldilocks_avx2_add(va, vb);
        extract_avx2(vr, result_avx2);

        for (int j = 0; j < 4; j++) {
            if (result_scalar[j] != result_avx2[j]) {
                all_passed = 0;
                break;
            }
        }
    }
    TEST("400 AVX2 additions match scalar", all_passed);
}

void test_avx2_sub_consistency(void) {
    printf("\n=== AVX2 Subtraction Consistency Tests ===\n");

    int all_passed = 1;
    for (int i = 0; i < 100 && all_passed; i++) {
        uint64_t a[4], b[4], result_scalar[4], result_avx2[4];

        for (int j = 0; j < 4; j++) {
            a[j] = random_field_element();
            b[j] = random_field_element();
            result_scalar[j] = goldilocks_sub(a[j], b[j]);
        }

        __m256i va = _mm256_loadu_si256((const __m256i*)a);
        __m256i vb = _mm256_loadu_si256((const __m256i*)b);
        __m256i vr = goldilocks_avx2_sub(va, vb);
        extract_avx2(vr, result_avx2);

        for (int j = 0; j < 4; j++) {
            if (result_scalar[j] != result_avx2[j]) {
                all_passed = 0;
                break;
            }
        }
    }
    TEST("400 AVX2 subtractions match scalar", all_passed);
}

void test_avx2_mul_consistency(void) {
    printf("\n=== AVX2 Multiplication Consistency Tests ===\n");

    int all_passed = 1;
    for (int i = 0; i < 100 && all_passed; i++) {
        uint64_t a[4], b[4], result_scalar[4], result_avx2[4];

        for (int j = 0; j < 4; j++) {
            a[j] = random_field_element();
            b[j] = random_field_element();
            result_scalar[j] = goldilocks_mul(a[j], b[j]);
        }

        __m256i va = _mm256_loadu_si256((const __m256i*)a);
        __m256i vb = _mm256_loadu_si256((const __m256i*)b);
        __m256i vr = goldilocks_avx2_mul(va, vb);
        extract_avx2(vr, result_avx2);

        for (int j = 0; j < 4; j++) {
            if (result_scalar[j] != result_avx2[j]) {
                all_passed = 0;
                printf("    Mismatch at test %d, lane %d:\n", i, j);
                printf("      a=%llu, b=%llu\n", (unsigned long long)a[j], (unsigned long long)b[j]);
                printf("      scalar=%llu, avx2=%llu\n",
                       (unsigned long long)result_scalar[j],
                       (unsigned long long)result_avx2[j]);
                break;
            }
        }
    }
    TEST("400 AVX2 multiplications match scalar", all_passed);
}

void test_avx2_edge_cases(void) {
    printf("\n=== AVX2 Edge Case Tests ===\n");

    /* Test with maximum values */
    uint64_t max_vals[4] = {
        GOLDILOCKS_P - 1,
        GOLDILOCKS_P - 1,
        GOLDILOCKS_P - 1,
        GOLDILOCKS_P - 1
    };
    uint64_t ones[4] = {1, 1, 1, 1};
    uint64_t result[4];

    __m256i vmax = _mm256_loadu_si256((const __m256i*)max_vals);
    __m256i vone = _mm256_loadu_si256((const __m256i*)ones);
    __m256i vr = goldilocks_avx2_add(vmax, vone);
    extract_avx2(vr, result);

    int all_zero = 1;
    for (int j = 0; j < 4; j++) {
        if (result[j] != 0) all_zero = 0;
    }
    TEST("(p-1) + 1 = 0 in all lanes", all_zero);

    /* Test 0 - 1 = p - 1 */
    uint64_t zeros[4] = {0, 0, 0, 0};
    __m256i vzero = _mm256_loadu_si256((const __m256i*)zeros);
    vr = goldilocks_avx2_sub(vzero, vone);
    extract_avx2(vr, result);

    int all_p_minus_1 = 1;
    for (int j = 0; j < 4; j++) {
        if (result[j] != GOLDILOCKS_P - 1) all_p_minus_1 = 0;
    }
    TEST("0 - 1 = p-1 in all lanes", all_p_minus_1);
}

int main(void) {
    printf("AMO-Lean Goldilocks Field Tests (AVX2)\n");
    printf("======================================\n");

    test_avx2_add_consistency();
    test_avx2_sub_consistency();
    test_avx2_mul_consistency();
    test_avx2_edge_cases();

    printf("\n======================================\n");
    printf("Results: %d/%d tests passed\n", tests_passed, tests_passed + tests_failed);

    return tests_failed > 0 ? 1 : 0;
}
