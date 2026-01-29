/**
 * DeepFuzz.c - Deep Fuzzing with Pathological Vectors
 *
 * Phase 6A Hardening: Test 3
 *
 * Purpose: Test NTT implementations with mathematically pathological inputs
 * that are known to stress edge cases in finite field arithmetic.
 *
 * Vector types tested:
 * 1. Sparse vectors: [P-1, 0, ..., 0, 1]
 * 2. Geometric progressions: [1, w, w^2, w^3, ...]
 * 3. Max entropy: All values near 2^64 - 2^32
 * 4. Boundary values: 0, 1, P-1, P-2
 * 5. Alternating patterns: [0, P-1, 0, P-1, ...]
 * 6. Powers of two: [1, 2, 4, 8, ...]
 *
 * Criteria: AMO_NTT(v) == PLONKY3_NTT(v) bit-for-bit
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <dlfcn.h>

/* Include AMO-Lean implementation */
#include "../../../generated/field_goldilocks.h"
#include "../../../generated/ntt_kernel.h"

/* Forward declarations */
static int ntt_forward(goldilocks_t* data, size_t n, goldilocks_t omega);
#include "../../../generated/ntt_skeleton.c"

/*===========================================================================
 * Constants
 *===========================================================================*/

#define GOLDILOCKS_P    0xFFFFFFFF00000001ULL
#define MAX_DIFF_SHOW   5

/*===========================================================================
 * Function Types
 *===========================================================================*/

typedef int (*ntt_fn)(uint64_t*, size_t);
typedef uint64_t (*omega_fn)(size_t);
typedef uint64_t (*mul_fn)(uint64_t, uint64_t);

/*===========================================================================
 * Test Parameters
 *===========================================================================*/

typedef struct {
    size_t n;
    size_t log2_n;
    uint64_t omega;
} TestSize;

static const TestSize SIZES[] = {
    {8,    3,  0xFFFFFFFEFF000001ULL},
    {16,   4,  0xEFFFFFFF00000001ULL},
    {32,   5,  0x00003FFFFFFFC000ULL},
    {64,   6,  0x0000008000000000ULL},
    {128,  7,  0xF80007FF08000001ULL},
    {256,  8,  0xBF79143CE60CA966ULL},
    {512,  9,  0x1905D02A5C411F4EULL},
    {1024, 10, 0x9D8F2AD78BFED972ULL},
};
#define NUM_SIZES (sizeof(SIZES) / sizeof(SIZES[0]))

/*===========================================================================
 * Test Results
 *===========================================================================*/

typedef struct {
    int passed;
    int failed;
    int total;
} TestResult;

static TestResult global_result = {0, 0, 0};

/*===========================================================================
 * Utility Functions
 *===========================================================================*/

/* Compare arrays bit-for-bit */
static int arrays_equal(const uint64_t* a, const uint64_t* b, size_t n) {
    return memcmp(a, b, n * sizeof(uint64_t)) == 0;
}

/* Print differences */
static void print_diff(const uint64_t* plonky3, const uint64_t* amolean, size_t n) {
    int shown = 0;
    for (size_t i = 0; i < n && shown < MAX_DIFF_SHOW; i++) {
        if (plonky3[i] != amolean[i]) {
            printf("        [%zu] P3: 0x%016llx  AMO: 0x%016llx\n",
                   i, (unsigned long long)plonky3[i],
                   (unsigned long long)amolean[i]);
            shown++;
        }
    }
}

/* Modular multiplication (for generating test vectors) */
static uint64_t mod_mul(uint64_t a, uint64_t b, mul_fn mul) {
    return mul(a, b);
}

/* Test a single vector */
static int test_vector(ntt_fn plonky3_ntt, const TestSize* size,
                       const uint64_t* input, const char* name) {
    size_t n = size->n;

    uint64_t* p3_result = malloc(n * sizeof(uint64_t));
    uint64_t* amo_result = malloc(n * sizeof(uint64_t));

    if (!p3_result || !amo_result) {
        free(p3_result);
        free(amo_result);
        return 0;
    }

    memcpy(p3_result, input, n * sizeof(uint64_t));
    memcpy(amo_result, input, n * sizeof(uint64_t));

    /* Run both NTTs */
    plonky3_ntt(p3_result, n);
    ntt_forward(amo_result, n, size->omega);

    /* Compare */
    int match = arrays_equal(p3_result, amo_result, n);

    global_result.total++;
    if (match) {
        global_result.passed++;
        printf("      [PASS] %s\n", name);
    } else {
        global_result.failed++;
        printf("      [FAIL] %s\n", name);
        print_diff(p3_result, amo_result, n);
    }

    free(p3_result);
    free(amo_result);
    return match;
}

/*===========================================================================
 * Pathological Vector Generators
 *===========================================================================*/

/**
 * Sparse vector: [P-1, 0, ..., 0, 1]
 * Tests handling of extreme values with mostly zeros
 */
static void generate_sparse(uint64_t* v, size_t n) {
    memset(v, 0, n * sizeof(uint64_t));
    v[0] = GOLDILOCKS_P - 1;
    v[n - 1] = 1;
}

/**
 * Geometric progression: [1, w, w^2, w^3, ...]
 * This is special because NTT([1,w,w^2,...]) has known structure
 */
static void generate_geometric(uint64_t* v, size_t n, uint64_t omega, mul_fn mul) {
    v[0] = 1;
    for (size_t i = 1; i < n; i++) {
        v[i] = mod_mul(v[i-1], omega, mul);
    }
}

/**
 * Max entropy: All values near 2^64 - 2^32 (close to P)
 * Tests reduction behavior with near-overflow values
 */
static void generate_max_entropy(uint64_t* v, size_t n) {
    for (size_t i = 0; i < n; i++) {
        /* Values in range [P-1000, P-1] */
        v[i] = GOLDILOCKS_P - 1 - (i % 1000);
    }
}

/**
 * Boundary values: Cycle through 0, 1, P-1, P-2
 * Tests extreme field element values
 */
static void generate_boundary(uint64_t* v, size_t n) {
    uint64_t boundaries[] = {0, 1, GOLDILOCKS_P - 1, GOLDILOCKS_P - 2};
    for (size_t i = 0; i < n; i++) {
        v[i] = boundaries[i % 4];
    }
}

/**
 * Alternating: [0, P-1, 0, P-1, ...]
 * Tests handling of maximum contrast
 */
static void generate_alternating(uint64_t* v, size_t n) {
    for (size_t i = 0; i < n; i++) {
        v[i] = (i % 2 == 0) ? 0 : GOLDILOCKS_P - 1;
    }
}

/**
 * Powers of two: [1, 2, 4, 8, ..., 2^k mod P, ...]
 * Wraps around when exceeding P
 */
static void generate_powers_of_two(uint64_t* v, size_t n) {
    v[0] = 1;
    for (size_t i = 1; i < n; i++) {
        /* 2 * v[i-1] mod P */
        uint64_t doubled = v[i-1] << 1;
        if (doubled >= GOLDILOCKS_P) {
            doubled -= GOLDILOCKS_P;
        }
        v[i] = doubled;
    }
}

/**
 * Impulse at different positions: [0, ..., 1, ..., 0]
 * Tests DFT impulse response
 */
static void generate_impulse(uint64_t* v, size_t n, size_t pos) {
    memset(v, 0, n * sizeof(uint64_t));
    v[pos % n] = 1;
}

/**
 * All P-1: [P-1, P-1, ..., P-1]
 * Equivalent to [-1, -1, ..., -1] in the field
 */
static void generate_all_max(uint64_t* v, size_t n) {
    for (size_t i = 0; i < n; i++) {
        v[i] = GOLDILOCKS_P - 1;
    }
}

/**
 * Fibonacci-like: f[0]=1, f[1]=1, f[i]=(f[i-1]+f[i-2]) mod P
 */
static void generate_fibonacci(uint64_t* v, size_t n) {
    v[0] = 1;
    if (n > 1) v[1] = 1;
    for (size_t i = 2; i < n; i++) {
        uint64_t sum = v[i-1] + v[i-2];
        if (sum >= GOLDILOCKS_P) sum -= GOLDILOCKS_P;
        v[i] = sum;
    }
}

/**
 * Random high bits: Random values with high bits set
 * Tests behavior with values that require reduction
 */
static void generate_random_high(uint64_t* v, size_t n, unsigned int seed) {
    srand(seed);
    for (size_t i = 0; i < n; i++) {
        /* Generate value with high bits set */
        uint64_t r = ((uint64_t)rand() << 48) | ((uint64_t)rand() << 32) |
                     ((uint64_t)rand() << 16) | (uint64_t)rand();
        v[i] = r % GOLDILOCKS_P;
    }
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

static void run_deep_fuzz_for_size(ntt_fn plonky3_ntt, mul_fn mul,
                                    const TestSize* size) {
    size_t n = size->n;
    char name[64];

    printf("\n    --- N=%zu (2^%zu) ---\n", n, size->log2_n);

    uint64_t* v = malloc(n * sizeof(uint64_t));
    if (!v) {
        printf("      [ERROR] malloc failed\n");
        return;
    }

    /* Test 1: Sparse */
    generate_sparse(v, n);
    snprintf(name, sizeof(name), "Sparse [P-1, 0..., 1]");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 2: Geometric */
    generate_geometric(v, n, size->omega, mul);
    snprintf(name, sizeof(name), "Geometric [1, w, w^2, ...]");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 3: Max entropy */
    generate_max_entropy(v, n);
    snprintf(name, sizeof(name), "Max entropy [P-1, P-2, ...]");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 4: Boundary values */
    generate_boundary(v, n);
    snprintf(name, sizeof(name), "Boundary [0, 1, P-1, P-2, ...]");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 5: Alternating */
    generate_alternating(v, n);
    snprintf(name, sizeof(name), "Alternating [0, P-1, 0, P-1, ...]");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 6: Powers of two */
    generate_powers_of_two(v, n);
    snprintf(name, sizeof(name), "Powers of 2 [1, 2, 4, 8, ...]");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 7: Impulse at position 0 */
    generate_impulse(v, n, 0);
    snprintf(name, sizeof(name), "Impulse at 0");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 8: Impulse at position n/2 */
    generate_impulse(v, n, n / 2);
    snprintf(name, sizeof(name), "Impulse at n/2");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 9: All max values */
    generate_all_max(v, n);
    snprintf(name, sizeof(name), "All P-1 (all -1 mod P)");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 10: Fibonacci */
    generate_fibonacci(v, n);
    snprintf(name, sizeof(name), "Fibonacci sequence");
    test_vector(plonky3_ntt, size, v, name);

    /* Test 11-15: Random with high bits (different seeds) */
    for (int seed = 1; seed <= 5; seed++) {
        generate_random_high(v, n, 0xDEAD0000 + seed);
        snprintf(name, sizeof(name), "Random high bits (seed %d)", seed);
        test_vector(plonky3_ntt, size, v, name);
    }

    free(v);
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("  Deep Fuzzing - Pathological Vector Testing\n");
    printf("  Phase 6A Hardening Suite\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("\n  Testing mathematically pathological inputs...\n");
    printf("  Criteria: Plonky3 and AMO-Lean must match bit-for-bit\n");

    /* Load library */
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

    ntt_fn plonky3_ntt = (ntt_fn)dlsym(lib, "plonky3_ntt_forward");
    mul_fn mul = (mul_fn)dlsym(lib, "plonky3_mul");

    if (!plonky3_ntt || !mul) {
        fprintf(stderr, "ERROR: Failed to load symbols\n");
        dlclose(lib);
        return 1;
    }

    printf("Library loaded successfully.\n");

    /* Run deep fuzz for each size */
    printf("\n  Running deep fuzz tests...\n");

    for (size_t i = 0; i < NUM_SIZES; i++) {
        run_deep_fuzz_for_size(plonky3_ntt, mul, &SIZES[i]);
    }

    /* Summary */
    printf("\n═══════════════════════════════════════════════════════════════════════\n");
    printf("  DEEP FUZZ SUMMARY\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("  Total tests:  %d\n", global_result.total);
    printf("  Passed:       %d\n", global_result.passed);
    printf("  Failed:       %d\n", global_result.failed);
    printf("  Success rate: %.1f%%\n",
           100.0 * global_result.passed / global_result.total);
    printf("═══════════════════════════════════════════════════════════════════════\n");

    if (global_result.failed == 0) {
        printf("\n  [PASS] All pathological vectors produced identical results!\n");
        printf("\n  VERDICT: Mathematical equivalence VERIFIED.\n");
    } else {
        printf("\n  [FAIL] Some vectors produced different results!\n");
        printf("\n  VERDICT: Mathematical equivalence BROKEN.\n");
    }

    printf("\n═══════════════════════════════════════════════════════════════════════\n");

    dlclose(lib);
    return global_result.failed > 0 ? 1 : 0;
}
