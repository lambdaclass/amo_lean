/**
 * oracle_test.c - Plonky3 vs AMO-Lean Oracle Testing
 *
 * Phase 6A.3 & 6A.4: Order Detection and Equivalence Verification
 *
 * This test suite verifies that Plonky3 and AMO-Lean produce identical
 * NTT results for the Goldilocks field.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <dlfcn.h>

/* Include AMO-Lean NTT implementation */
#include "../../generated/field_goldilocks.h"
#include "../../generated/ntt_kernel.h"

/* Forward declaration - we include the skeleton inline */
static int ntt_forward(goldilocks_t* data, size_t n, goldilocks_t omega);
static int ntt_inverse(goldilocks_t* data, size_t n, goldilocks_t omega, goldilocks_t n_inv);

/* Include the skeleton implementation */
#include "../../generated/ntt_skeleton.c"

/*===========================================================================
 * Plonky3 Function Types
 *===========================================================================*/

typedef int (*plonky3_ntt_fn)(uint64_t*, size_t);
typedef uint64_t (*plonky3_omega_fn)(size_t);
typedef uint64_t (*plonky3_prime_fn)(void);

/*===========================================================================
 * Test Parameters
 *===========================================================================*/

typedef struct {
    size_t n;
    size_t log2_n;
    uint64_t omega;
    uint64_t n_inv;
} TestParams;

/* Omega values from Plonky3 TWO_ADIC_GENERATORS, n_inv computed */
static const TestParams TEST_PARAMS[] = {
    /* N=8 (2^3) */
    {8, 3, 0xFFFFFFFEFF000001ULL, 0xDFFFFFFF20000001ULL},
    /* N=16 (2^4) */
    {16, 4, 0xEFFFFFFF00000001ULL, 0xEFFFFFFF10000001ULL},
    /* N=32 (2^5) */
    {32, 5, 0x00003FFFFFFFC000ULL, 0xF7FFFFFF08000001ULL},
    /* N=64 (2^6) */
    {64, 6, 0x0000008000000000ULL, 0xFBFFFFFF04000001ULL},
    /* N=128 (2^7) */
    {128, 7, 0xF80007FF08000001ULL, 0xFDFFFFFF02000001ULL},
    /* N=256 (2^8) */
    {256, 8, 0xBF79143CE60CA966ULL, 0xFEFFFFFF01000001ULL},
    /* N=512 (2^9) */
    {512, 9, 0x1905D02A5C411F4EULL, 0xFF7FFFFF00800001ULL},
    /* N=1024 (2^10) */
    {1024, 10, 0x9D8F2AD78BFED972ULL, 0xFFBFFFFF00400001ULL},
};
#define NUM_TEST_PARAMS (sizeof(TEST_PARAMS) / sizeof(TEST_PARAMS[0]))

/*===========================================================================
 * Test Configuration
 *===========================================================================*/

#define NUM_RANDOM_TESTS 50
#define MAX_DIFF_DISPLAY 5

/*===========================================================================
 * Test Results
 *===========================================================================*/

typedef struct {
    int passed;
    int failed;
    int total;
} TestResult;

static TestResult global_result = {0, 0, 0};

#define TEST(name, condition) do { \
    global_result.total++; \
    if (condition) { \
        printf("    [PASS] %s\n", name); \
        global_result.passed++; \
    } else { \
        printf("    [FAIL] %s\n", name); \
        global_result.failed++; \
    } \
} while(0)

/*===========================================================================
 * Utility Functions
 *===========================================================================*/

/* Random value in Goldilocks field */
static uint64_t random_goldilocks(void) {
    uint64_t r = ((uint64_t)rand() << 32) | (uint64_t)rand();
    return r % GOLDILOCKS_ORDER;
}

/* Compare two arrays */
static int arrays_equal(const uint64_t* a, const uint64_t* b, size_t n) {
    for (size_t i = 0; i < n; i++) {
        if (a[i] != b[i]) return 0;
    }
    return 1;
}

/* Print first few differences */
static void print_differences(const uint64_t* plonky3, const uint64_t* amolean,
                               size_t n, int max_show) {
    int shown = 0;
    for (size_t i = 0; i < n && shown < max_show; i++) {
        if (plonky3[i] != amolean[i]) {
            printf("      [%zu] Plonky3: %llu, AMO-Lean: %llu\n",
                   i, (unsigned long long)plonky3[i],
                   (unsigned long long)amolean[i]);
            shown++;
        }
    }
    if (shown < max_show) {
        int total_diff = 0;
        for (size_t i = 0; i < n; i++) {
            if (plonky3[i] != amolean[i]) total_diff++;
        }
        if (total_diff > shown) {
            printf("      ... and %d more differences\n", total_diff - shown);
        }
    }
}

/*===========================================================================
 * Phase 6A.3: Order Detection
 *===========================================================================*/

typedef enum {
    ORDER_MATCH = 0,
    ORDER_MISMATCH = 1,
    ORDER_ERROR = -1
} OrderResult;

/**
 * Detect if Plonky3 and AMO-Lean use the same I/O order.
 *
 * Since both use Radix-2 DIT with bit-reversal before the loop,
 * they should produce identical results.
 */
static OrderResult detect_order_compatibility(plonky3_ntt_fn plonky3_ntt) {
    printf("\n=== Phase 6A.3: Order Compatibility Detection ===\n");

    /* Use small size for quick test */
    const size_t n = 8;
    const uint64_t omega = TEST_PARAMS[0].omega;

    uint64_t input[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    uint64_t plonky3_result[8];
    uint64_t amolean_result[8];

    /* Copy input */
    memcpy(plonky3_result, input, sizeof(input));
    memcpy(amolean_result, input, sizeof(input));

    /* Run Plonky3 NTT */
    int ret = plonky3_ntt(plonky3_result, n);
    if (ret != 0) {
        printf("  ERROR: Plonky3 NTT failed\n");
        return ORDER_ERROR;
    }

    /* Run AMO-Lean NTT */
    ret = ntt_forward(amolean_result, n, omega);
    if (ret != 0) {
        printf("  ERROR: AMO-Lean NTT failed\n");
        return ORDER_ERROR;
    }

    /* Compare */
    printf("  Input:         [1, 2, 3, 4, 5, 6, 7, 8]\n");
    printf("  Plonky3 NTT:   [");
    for (int i = 0; i < 8; i++) printf("%llu%s", (unsigned long long)plonky3_result[i], i<7?", ":"");
    printf("]\n");
    printf("  AMO-Lean NTT:  [");
    for (int i = 0; i < 8; i++) printf("%llu%s", (unsigned long long)amolean_result[i], i<7?", ":"");
    printf("]\n");

    if (arrays_equal(plonky3_result, amolean_result, n)) {
        printf("  Result: MATCH - Both use same I/O order (RN: bit-reverse input, natural output)\n");
        return ORDER_MATCH;
    } else {
        printf("  Result: MISMATCH - Different I/O order detected\n");
        print_differences(plonky3_result, amolean_result, n, 8);
        return ORDER_MISMATCH;
    }
}

/*===========================================================================
 * Phase 6A.4: Oracle Tests
 *===========================================================================*/

/**
 * Test with a specific input vector
 */
static int test_vector(plonky3_ntt_fn plonky3_ntt,
                       const TestParams* params,
                       const uint64_t* input,
                       const char* test_name) {
    size_t n = params->n;

    uint64_t* plonky3_result = malloc(n * sizeof(uint64_t));
    uint64_t* amolean_result = malloc(n * sizeof(uint64_t));

    if (!plonky3_result || !amolean_result) {
        free(plonky3_result);
        free(amolean_result);
        return 0;
    }

    memcpy(plonky3_result, input, n * sizeof(uint64_t));
    memcpy(amolean_result, input, n * sizeof(uint64_t));

    /* Run both NTTs */
    plonky3_ntt(plonky3_result, n);
    ntt_forward(amolean_result, n, params->omega);

    /* Compare */
    int match = arrays_equal(plonky3_result, amolean_result, n);

    if (!match && global_result.failed < MAX_DIFF_DISPLAY) {
        printf("      Differences for %s:\n", test_name);
        print_differences(plonky3_result, amolean_result, n, 3);
    }

    free(plonky3_result);
    free(amolean_result);
    return match;
}

/**
 * Run oracle tests for a specific size
 */
static void run_oracle_tests_for_size(plonky3_ntt_fn plonky3_ntt,
                                       const TestParams* params) {
    size_t n = params->n;
    char test_name[64];

    printf("\n  --- N=%zu (2^%zu) ---\n", n, params->log2_n);

    /* Test 1: Sequential input [1, 2, 3, ..., n] */
    uint64_t* seq_input = malloc(n * sizeof(uint64_t));
    for (size_t i = 0; i < n; i++) seq_input[i] = i + 1;
    snprintf(test_name, sizeof(test_name), "N=%zu sequential [1..%zu]", n, n);
    TEST(test_name, test_vector(plonky3_ntt, params, seq_input, test_name));
    free(seq_input);

    /* Test 2: All zeros */
    uint64_t* zero_input = calloc(n, sizeof(uint64_t));
    snprintf(test_name, sizeof(test_name), "N=%zu all zeros", n);
    TEST(test_name, test_vector(plonky3_ntt, params, zero_input, test_name));
    free(zero_input);

    /* Test 3: All ones */
    uint64_t* ones_input = malloc(n * sizeof(uint64_t));
    for (size_t i = 0; i < n; i++) ones_input[i] = 1;
    snprintf(test_name, sizeof(test_name), "N=%zu all ones", n);
    TEST(test_name, test_vector(plonky3_ntt, params, ones_input, test_name));
    free(ones_input);

    /* Test 4: Single non-zero (impulse) */
    uint64_t* impulse_input = calloc(n, sizeof(uint64_t));
    impulse_input[0] = 1;
    snprintf(test_name, sizeof(test_name), "N=%zu impulse [1,0,0,...]", n);
    TEST(test_name, test_vector(plonky3_ntt, params, impulse_input, test_name));
    free(impulse_input);

    /* Test 5: Max values */
    uint64_t* max_input = malloc(n * sizeof(uint64_t));
    for (size_t i = 0; i < n; i++) max_input[i] = GOLDILOCKS_ORDER - 1;
    snprintf(test_name, sizeof(test_name), "N=%zu max values (p-1)", n);
    TEST(test_name, test_vector(plonky3_ntt, params, max_input, test_name));
    free(max_input);

    /* Tests 6+: Random inputs */
    int random_passed = 0;
    for (int r = 0; r < NUM_RANDOM_TESTS; r++) {
        uint64_t* rand_input = malloc(n * sizeof(uint64_t));
        for (size_t i = 0; i < n; i++) {
            rand_input[i] = random_goldilocks();
        }

        if (test_vector(plonky3_ntt, params, rand_input, "random")) {
            random_passed++;
        }

        free(rand_input);
    }

    snprintf(test_name, sizeof(test_name), "N=%zu random (%d/%d)", n, random_passed, NUM_RANDOM_TESTS);
    global_result.total++;
    if (random_passed == NUM_RANDOM_TESTS) {
        printf("    [PASS] %s\n", test_name);
        global_result.passed++;
    } else {
        printf("    [FAIL] %s\n", test_name);
        global_result.failed++;
    }
}

/**
 * Test NTT roundtrip: INTT(NTT(x)) = x
 */
static void test_roundtrip(plonky3_ntt_fn plonky3_ntt,
                           plonky3_ntt_fn plonky3_intt,
                           const TestParams* params) {
    size_t n = params->n;
    char test_name[64];

    /* Test with sequential input */
    uint64_t* data = malloc(n * sizeof(uint64_t));
    uint64_t* original = malloc(n * sizeof(uint64_t));

    for (size_t i = 0; i < n; i++) {
        data[i] = i + 1;
        original[i] = i + 1;
    }

    /* Plonky3 roundtrip */
    plonky3_ntt(data, n);
    plonky3_intt(data, n);

    snprintf(test_name, sizeof(test_name), "N=%zu Plonky3 roundtrip", n);
    TEST(test_name, arrays_equal(data, original, n));

    /* AMO-Lean roundtrip */
    memcpy(data, original, n * sizeof(uint64_t));
    ntt_forward(data, n, params->omega);
    ntt_inverse(data, n, params->omega, params->n_inv);

    snprintf(test_name, sizeof(test_name), "N=%zu AMO-Lean roundtrip", n);
    TEST(test_name, arrays_equal(data, original, n));

    free(data);
    free(original);
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Plonky3 vs AMO-Lean Oracle Testing\n");
    printf("  Phase 6A.3 & 6A.4: Order Detection & Equivalence Verification\n");
    printf("═══════════════════════════════════════════════════════════════\n");

    srand((unsigned int)time(NULL));

    /* Load Plonky3 shim */
    printf("\nLoading Plonky3 shim...\n");

#ifdef __APPLE__
    const char* lib_path = "./plonky3_shim/target/release/libplonky3_shim.dylib";
#else
    const char* lib_path = "./plonky3_shim/target/release/libplonky3_shim.so";
#endif

    void* lib = dlopen(lib_path, RTLD_NOW);
    if (!lib) {
        fprintf(stderr, "ERROR: Failed to load library: %s\n", dlerror());
        return 1;
    }

    plonky3_ntt_fn plonky3_ntt = (plonky3_ntt_fn)dlsym(lib, "plonky3_ntt_forward");
    plonky3_ntt_fn plonky3_intt = (plonky3_ntt_fn)dlsym(lib, "plonky3_ntt_inverse");
    plonky3_omega_fn plonky3_omega = (plonky3_omega_fn)dlsym(lib, "plonky3_get_omega");

    if (!plonky3_ntt || !plonky3_intt || !plonky3_omega) {
        fprintf(stderr, "ERROR: Failed to load functions\n");
        dlclose(lib);
        return 1;
    }

    printf("Plonky3 shim loaded successfully.\n");

    /* Verify omega values match */
    printf("\n=== Omega Value Verification ===\n");
    int omega_match = 1;
    for (size_t i = 0; i < NUM_TEST_PARAMS; i++) {
        uint64_t plonky3_val = plonky3_omega(TEST_PARAMS[i].log2_n);
        uint64_t expected = TEST_PARAMS[i].omega;

        if (plonky3_val != expected) {
            printf("  [MISMATCH] N=%zu: Plonky3=0x%llx, Expected=0x%llx\n",
                   TEST_PARAMS[i].n, (unsigned long long)plonky3_val,
                   (unsigned long long)expected);
            omega_match = 0;
        }
    }
    if (omega_match) {
        printf("  All omega values match!\n");
    }

    /* Phase 6A.3: Order detection */
    OrderResult order = detect_order_compatibility(plonky3_ntt);
    if (order != ORDER_MATCH) {
        printf("\nERROR: Order mismatch detected. Cannot proceed with oracle tests.\n");
        dlclose(lib);
        return 1;
    }

    /* Phase 6A.4: Full oracle tests */
    printf("\n=== Phase 6A.4: Full Oracle Tests ===\n");

    for (size_t i = 0; i < NUM_TEST_PARAMS; i++) {
        run_oracle_tests_for_size(plonky3_ntt, &TEST_PARAMS[i]);
    }

    /* Roundtrip tests */
    printf("\n=== Roundtrip Tests ===\n");
    for (size_t i = 0; i < NUM_TEST_PARAMS; i++) {
        test_roundtrip(plonky3_ntt, plonky3_intt, &TEST_PARAMS[i]);
    }

    /* Summary */
    printf("\n═══════════════════════════════════════════════════════════════\n");
    printf("  FINAL RESULTS\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Total tests:  %d\n", global_result.total);
    printf("  Passed:       %d\n", global_result.passed);
    printf("  Failed:       %d\n", global_result.failed);
    printf("  Success rate: %.1f%%\n",
           100.0 * global_result.passed / global_result.total);
    printf("═══════════════════════════════════════════════════════════════\n");

    if (global_result.failed == 0) {
        printf("\n  *** ALL TESTS PASSED ***\n");
        printf("  Plonky3 and AMO-Lean produce IDENTICAL NTT results!\n\n");
    } else {
        printf("\n  *** SOME TESTS FAILED ***\n");
        printf("  Please investigate the differences above.\n\n");
    }

    dlclose(lib);
    return global_result.failed > 0 ? 1 : 0;
}
