/**
 * test_goldilocks_avx2.c - Test suite for AVX2 Goldilocks implementation
 *
 * AMO-Lean Phase 3
 *
 * Compile with:
 *   clang -O3 -mavx2 -o test_goldilocks_avx2 test_goldilocks_avx2.c -lm
 *
 * Or with sanitizers:
 *   clang -O1 -g -mavx2 -fsanitize=address,undefined -o test_goldilocks_avx2 test_goldilocks_avx2.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdbool.h>

#define FIELD_GOLDILOCKS
#include "field_goldilocks.h"
#include "field_goldilocks_avx2.h"

/*===========================================================================
 * Test Helpers
 *===========================================================================*/

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) printf("  Testing %s... ", name)
#define PASS() do { printf("PASS\n"); tests_passed++; } while(0)
#define FAIL(msg) do { printf("FAIL: %s\n", msg); tests_failed++; } while(0)

/* Simple PRNG for test vectors */
static uint64_t test_rng_state = 0x123456789ABCDEF0ULL;

static uint64_t test_rand64(void) {
    test_rng_state ^= test_rng_state << 13;
    test_rng_state ^= test_rng_state >> 7;
    test_rng_state ^= test_rng_state << 17;
    return test_rng_state % GOLDILOCKS_P;
}

/*===========================================================================
 * Test: AVX2 vs Scalar Consistency
 *===========================================================================*/

static bool test_add_consistency(void) {
    uint64_t a[4] __attribute__((aligned(32)));
    uint64_t b[4] __attribute__((aligned(32)));
    uint64_t result_avx2[4] __attribute__((aligned(32)));

    /* Generate random test vectors */
    for (int i = 0; i < 4; i++) {
        a[i] = test_rand64();
        b[i] = test_rand64();
    }

    /* AVX2 addition */
    __m256i va = goldilocks_avx2_load(a);
    __m256i vb = goldilocks_avx2_load(b);
    __m256i vr = goldilocks_avx2_add(va, vb);
    goldilocks_avx2_store(result_avx2, vr);

    /* Compare with scalar */
    for (int i = 0; i < 4; i++) {
        uint64_t expected = goldilocks_add(a[i], b[i]);
        if (result_avx2[i] != expected) {
            printf("Mismatch at index %d: AVX2=%lu, scalar=%lu\n",
                   i, result_avx2[i], expected);
            return false;
        }
    }

    return true;
}

static bool test_sub_consistency(void) {
    uint64_t a[4] __attribute__((aligned(32)));
    uint64_t b[4] __attribute__((aligned(32)));
    uint64_t result_avx2[4] __attribute__((aligned(32)));

    for (int i = 0; i < 4; i++) {
        a[i] = test_rand64();
        b[i] = test_rand64();
    }

    __m256i va = goldilocks_avx2_load(a);
    __m256i vb = goldilocks_avx2_load(b);
    __m256i vr = goldilocks_avx2_sub(va, vb);
    goldilocks_avx2_store(result_avx2, vr);

    for (int i = 0; i < 4; i++) {
        uint64_t expected = goldilocks_sub(a[i], b[i]);
        if (result_avx2[i] != expected) {
            printf("Mismatch at index %d: AVX2=%lu, scalar=%lu\n",
                   i, result_avx2[i], expected);
            return false;
        }
    }

    return true;
}

static bool test_mul_consistency(void) {
    uint64_t a[4] __attribute__((aligned(32)));
    uint64_t b[4] __attribute__((aligned(32)));
    uint64_t result_avx2[4] __attribute__((aligned(32)));

    for (int i = 0; i < 4; i++) {
        a[i] = test_rand64();
        b[i] = test_rand64();
    }

    __m256i va = goldilocks_avx2_load(a);
    __m256i vb = goldilocks_avx2_load(b);
    __m256i vr = goldilocks_avx2_mul(va, vb);
    goldilocks_avx2_store(result_avx2, vr);

    for (int i = 0; i < 4; i++) {
        uint64_t expected = goldilocks_mul(a[i], b[i]);
        if (result_avx2[i] != expected) {
            printf("Mismatch at index %d: a=%lu, b=%lu, AVX2=%lu, scalar=%lu\n",
                   i, a[i], b[i], result_avx2[i], expected);
            return false;
        }
    }

    return true;
}

/*===========================================================================
 * Test: Edge Cases
 *===========================================================================*/

static bool test_edge_cases(void) {
    uint64_t a[4] __attribute__((aligned(32))) = {0, 1, GOLDILOCKS_P - 1, GOLDILOCKS_EPSILON};
    uint64_t b[4] __attribute__((aligned(32))) = {GOLDILOCKS_P - 1, 0, 1, GOLDILOCKS_EPSILON};
    uint64_t result_avx2[4] __attribute__((aligned(32)));

    /* Test multiplication edge cases */
    __m256i va = goldilocks_avx2_load(a);
    __m256i vb = goldilocks_avx2_load(b);
    __m256i vr = goldilocks_avx2_mul(va, vb);
    goldilocks_avx2_store(result_avx2, vr);

    for (int i = 0; i < 4; i++) {
        uint64_t expected = goldilocks_mul(a[i], b[i]);
        if (result_avx2[i] != expected) {
            printf("Edge case mismatch at index %d: a=%lu, b=%lu, AVX2=%lu, scalar=%lu\n",
                   i, a[i], b[i], result_avx2[i], expected);
            return false;
        }
    }

    return true;
}

/*===========================================================================
 * Test: FRI Fold
 *===========================================================================*/

static bool test_fri_fold(void) {
    uint64_t even[4] __attribute__((aligned(32)));
    uint64_t odd[4] __attribute__((aligned(32)));
    uint64_t result_avx2[4] __attribute__((aligned(32)));

    for (int i = 0; i < 4; i++) {
        even[i] = test_rand64();
        odd[i] = test_rand64();
    }

    uint64_t alpha = test_rand64();

    /* AVX2 FRI fold */
    __m256i veven = goldilocks_avx2_load(even);
    __m256i vodd = goldilocks_avx2_load(odd);
    __m256i valpha = goldilocks_avx2_broadcast(alpha);
    __m256i vr = goldilocks_avx2_fri_fold(veven, vodd, valpha);
    goldilocks_avx2_store(result_avx2, vr);

    /* Compare with scalar */
    for (int i = 0; i < 4; i++) {
        uint64_t alpha_odd = goldilocks_mul(alpha, odd[i]);
        uint64_t expected = goldilocks_add(even[i], alpha_odd);
        if (result_avx2[i] != expected) {
            printf("FRI fold mismatch at index %d: AVX2=%lu, scalar=%lu\n",
                   i, result_avx2[i], expected);
            return false;
        }
    }

    return true;
}

/*===========================================================================
 * Benchmark
 *===========================================================================*/

#define BENCH_ITERATIONS 1000000

static void benchmark_mul(void) {
    uint64_t a[4] __attribute__((aligned(32))) = {0x123456789ABCDEF0ULL % GOLDILOCKS_P,
                                                   0xFEDCBA9876543210ULL % GOLDILOCKS_P,
                                                   0xDEADBEEFCAFEBABEULL % GOLDILOCKS_P,
                                                   0x0102030405060708ULL % GOLDILOCKS_P};
    uint64_t b[4] __attribute__((aligned(32))) = {0xAAAABBBBCCCCDDDDULL % GOLDILOCKS_P,
                                                   0x1111222233334444ULL % GOLDILOCKS_P,
                                                   0x5555666677778888ULL % GOLDILOCKS_P,
                                                   0x9999AAAABBBBCCCCULL % GOLDILOCKS_P};

    __m256i va = goldilocks_avx2_load(a);
    __m256i vb = goldilocks_avx2_load(b);
    __m256i vr;

    /* Warmup */
    for (int i = 0; i < 10000; i++) {
        vr = goldilocks_avx2_mul(va, vb);
        va = vr;  /* Prevent optimization */
    }

    /* AVX2 benchmark */
    clock_t start = clock();
    for (int i = 0; i < BENCH_ITERATIONS; i++) {
        vr = goldilocks_avx2_mul(va, vb);
        va = _mm256_xor_si256(va, vr);  /* Prevent optimization */
    }
    clock_t end = clock();

    double avx2_time = (double)(end - start) / CLOCKS_PER_SEC;
    double avx2_throughput = (4.0 * BENCH_ITERATIONS) / avx2_time / 1e6;

    /* Scalar benchmark */
    uint64_t sa = a[0], sb = b[0], sr;
    start = clock();
    for (int i = 0; i < BENCH_ITERATIONS; i++) {
        sr = goldilocks_mul(sa, sb);
        sa ^= sr;  /* Prevent optimization */
    }
    end = clock();

    double scalar_time = (double)(end - start) / CLOCKS_PER_SEC;
    double scalar_throughput = (double)BENCH_ITERATIONS / scalar_time / 1e6;

    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║                     BENCHMARK RESULTS                        ║\n");
    printf("╠══════════════════════════════════════════════════════════════╣\n");
    printf("║  Scalar multiplication:                                      ║\n");
    printf("║    Time: %.3f s for %d ops                              ║\n", scalar_time, BENCH_ITERATIONS);
    printf("║    Throughput: %.2f M mul/s                               ║\n", scalar_throughput);
    printf("║                                                              ║\n");
    printf("║  AVX2 multiplication (4 elements):                           ║\n");
    printf("║    Time: %.3f s for %d ops                              ║\n", avx2_time, BENCH_ITERATIONS);
    printf("║    Throughput: %.2f M mul/s (4x parallel)                 ║\n", avx2_throughput);
    printf("║                                                              ║\n");
    printf("║  Speedup: %.2fx                                             ║\n", avx2_throughput / scalar_throughput);
    printf("╚══════════════════════════════════════════════════════════════╝\n");
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║     AMO-LEAN PHASE 3: AVX2 GOLDILOCKS TEST SUITE             ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");

    /* Run multiple iterations for random tests */
    printf("Running consistency tests (100 iterations each)...\n");

    for (int iter = 0; iter < 100; iter++) {
        TEST("addition consistency");
        if (test_add_consistency()) { PASS(); } else { FAIL("mismatch"); }

        TEST("subtraction consistency");
        if (test_sub_consistency()) { PASS(); } else { FAIL("mismatch"); }

        TEST("multiplication consistency");
        if (test_mul_consistency()) { PASS(); } else { FAIL("mismatch"); }
    }

    printf("\nRunning edge case tests...\n");
    TEST("edge cases");
    if (test_edge_cases()) { PASS(); } else { FAIL("mismatch"); }

    printf("\nRunning FRI fold tests (100 iterations)...\n");
    for (int iter = 0; iter < 100; iter++) {
        TEST("FRI fold");
        if (test_fri_fold()) { PASS(); } else { FAIL("mismatch"); }
    }

    /* Summary */
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║                       TEST SUMMARY                           ║\n");
    printf("╠══════════════════════════════════════════════════════════════╣\n");
    printf("║  Passed: %d                                                   ║\n", tests_passed);
    printf("║  Failed: %d                                                   ║\n", tests_failed);
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    /* Run benchmark if all tests passed */
    if (tests_failed == 0) {
        printf("\nAll tests passed! Running benchmark...\n");
        benchmark_mul();
    }

    return tests_failed > 0 ? 1 : 0;
}
