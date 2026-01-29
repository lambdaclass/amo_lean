/**
 * FFI_Stress.c - FFI Torture Test for Memory Leak Detection
 *
 * Phase 6A Hardening: Test 1
 *
 * Purpose: Execute 1,000,000 cross-boundary calls (C→Rust→C) to detect
 * any memory leaks in the Plonky3 shim.
 *
 * Run with: valgrind --leak-check=full --show-leak-kinds=all --error-exitcode=1 ./ffi_stress
 *
 * Criteria: ZERO bytes lost. Any leak is a CRITICAL failure.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <dlfcn.h>
#include <time.h>

/*===========================================================================
 * Configuration
 *===========================================================================*/

#define ITERATIONS          1000000
#define NTT_SIZE            256
#define PROGRESS_INTERVAL   100000

/* Goldilocks prime */
#define GOLDILOCKS_ORDER    0xFFFFFFFF00000001ULL

/*===========================================================================
 * Function Types
 *===========================================================================*/

typedef int (*ntt_fn)(uint64_t*, size_t);
typedef uint64_t (*prime_fn)(void);
typedef uint64_t (*omega_fn)(size_t);
typedef uint64_t (*field_op_fn)(uint64_t, uint64_t);

/*===========================================================================
 * Test Functions
 *===========================================================================*/

/**
 * Test 1: Repeated NTT forward/inverse (most likely to leak)
 */
static int test_ntt_roundtrip(ntt_fn ntt_fwd, ntt_fn ntt_inv, int iterations) {
    printf("\n[TEST 1] NTT Roundtrip Stress (%d iterations)...\n", iterations);

    uint64_t* data = malloc(NTT_SIZE * sizeof(uint64_t));
    uint64_t* backup = malloc(NTT_SIZE * sizeof(uint64_t));

    if (!data || !backup) {
        fprintf(stderr, "  FAIL: malloc failed\n");
        free(data);
        free(backup);
        return 1;
    }

    /* Initialize with pattern */
    for (size_t i = 0; i < NTT_SIZE; i++) {
        backup[i] = (i + 1) % GOLDILOCKS_ORDER;
    }

    int errors = 0;
    clock_t start = clock();

    for (int iter = 0; iter < iterations; iter++) {
        /* Copy fresh data */
        memcpy(data, backup, NTT_SIZE * sizeof(uint64_t));

        /* Forward NTT */
        if (ntt_fwd(data, NTT_SIZE) != 0) {
            errors++;
            continue;
        }

        /* Inverse NTT */
        if (ntt_inv(data, NTT_SIZE) != 0) {
            errors++;
            continue;
        }

        /* Verify roundtrip (spot check every 10000 iterations) */
        if (iter % 10000 == 0) {
            for (size_t i = 0; i < NTT_SIZE; i++) {
                if (data[i] != backup[i]) {
                    errors++;
                    break;
                }
            }
        }

        /* Progress indicator */
        if ((iter + 1) % PROGRESS_INTERVAL == 0) {
            printf("    Progress: %d/%d (%.1f%%)\n",
                   iter + 1, iterations, 100.0 * (iter + 1) / iterations);
        }
    }

    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    free(data);
    free(backup);

    printf("  Completed in %.2f seconds (%.0f calls/sec)\n",
           elapsed, (2.0 * iterations) / elapsed);
    printf("  Errors: %d\n", errors);

    return errors > 0 ? 1 : 0;
}

/**
 * Test 2: Repeated field operations (simpler, high frequency)
 */
static int test_field_ops(field_op_fn add, field_op_fn mul, field_op_fn sub,
                          int iterations) {
    printf("\n[TEST 2] Field Operations Stress (%d iterations)...\n", iterations);

    int errors = 0;
    clock_t start = clock();

    uint64_t a = 12345678901234567ULL % GOLDILOCKS_ORDER;
    uint64_t b = 98765432109876543ULL % GOLDILOCKS_ORDER;

    for (int iter = 0; iter < iterations; iter++) {
        /* Chain of operations */
        uint64_t c = add(a, b);
        uint64_t d = mul(c, a);
        uint64_t e = sub(d, b);

        /* Use result to prevent optimization */
        a = (e + 1) % GOLDILOCKS_ORDER;

        /* Progress */
        if ((iter + 1) % PROGRESS_INTERVAL == 0) {
            printf("    Progress: %d/%d (%.1f%%)\n",
                   iter + 1, iterations, 100.0 * (iter + 1) / iterations);
        }
    }

    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    printf("  Completed in %.2f seconds (%.0f calls/sec)\n",
           elapsed, (3.0 * iterations) / elapsed);
    printf("  Final value: 0x%llx (verification hash)\n", (unsigned long long)a);
    printf("  Errors: %d\n", errors);

    return errors;
}

/**
 * Test 3: Omega value queries (read-only, should never leak)
 */
static int test_omega_queries(omega_fn get_omega, int iterations) {
    printf("\n[TEST 3] Omega Query Stress (%d iterations)...\n", iterations);

    clock_t start = clock();
    uint64_t checksum = 0;

    for (int iter = 0; iter < iterations; iter++) {
        /* Query various omega values */
        for (size_t log_n = 3; log_n <= 16; log_n++) {
            uint64_t omega = get_omega(log_n);
            checksum ^= omega;
        }

        /* Progress */
        if ((iter + 1) % (PROGRESS_INTERVAL / 10) == 0) {
            printf("    Progress: %d/%d (%.1f%%)\n",
                   iter + 1, iterations, 100.0 * (iter + 1) / iterations);
        }
    }

    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    printf("  Completed in %.2f seconds (%.0f queries/sec)\n",
           elapsed, (14.0 * iterations) / elapsed);
    printf("  Checksum: 0x%llx\n", (unsigned long long)checksum);

    return 0;
}

/**
 * Test 4: Varying sizes (allocation stress)
 */
static int test_varying_sizes(ntt_fn ntt_fwd, ntt_fn ntt_inv, int iterations) {
    printf("\n[TEST 4] Varying Size Stress (%d iterations)...\n", iterations);

    size_t sizes[] = {8, 16, 32, 64, 128, 256, 512, 1024};
    int num_sizes = sizeof(sizes) / sizeof(sizes[0]);

    int errors = 0;
    clock_t start = clock();

    for (int iter = 0; iter < iterations; iter++) {
        size_t n = sizes[iter % num_sizes];

        uint64_t* data = malloc(n * sizeof(uint64_t));
        if (!data) {
            errors++;
            continue;
        }

        /* Initialize */
        for (size_t i = 0; i < n; i++) {
            data[i] = (iter + i + 1) % GOLDILOCKS_ORDER;
        }

        /* NTT roundtrip */
        if (ntt_fwd(data, n) != 0 || ntt_inv(data, n) != 0) {
            errors++;
        }

        free(data);

        /* Progress */
        if ((iter + 1) % PROGRESS_INTERVAL == 0) {
            printf("    Progress: %d/%d (%.1f%%)\n",
                   iter + 1, iterations, 100.0 * (iter + 1) / iterations);
        }
    }

    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    printf("  Completed in %.2f seconds\n", elapsed);
    printf("  Errors: %d\n", errors);

    return errors > 0 ? 1 : 0;
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("  FFI Torture Test - Memory Leak Detection\n");
    printf("  Phase 6A Hardening Suite\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("\n  Target: %d iterations per test\n", ITERATIONS);
    printf("  Run with: valgrind --leak-check=full --error-exitcode=1\n");

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

    /* Load functions */
    ntt_fn ntt_fwd = (ntt_fn)dlsym(lib, "plonky3_ntt_forward");
    ntt_fn ntt_inv = (ntt_fn)dlsym(lib, "plonky3_ntt_inverse");
    field_op_fn add = (field_op_fn)dlsym(lib, "plonky3_add");
    field_op_fn mul = (field_op_fn)dlsym(lib, "plonky3_mul");
    field_op_fn sub = (field_op_fn)dlsym(lib, "plonky3_sub");
    omega_fn get_omega = (omega_fn)dlsym(lib, "plonky3_get_omega");

    if (!ntt_fwd || !ntt_inv || !add || !mul || !sub || !get_omega) {
        fprintf(stderr, "ERROR: Failed to load symbols\n");
        dlclose(lib);
        return 1;
    }

    printf("Library loaded successfully.\n");

    /* Run tests */
    int total_errors = 0;

    total_errors += test_ntt_roundtrip(ntt_fwd, ntt_inv, ITERATIONS);
    total_errors += test_field_ops(add, mul, sub, ITERATIONS);
    total_errors += test_omega_queries(get_omega, ITERATIONS / 10);
    total_errors += test_varying_sizes(ntt_fwd, ntt_inv, ITERATIONS / 10);

    /* Summary */
    printf("\n═══════════════════════════════════════════════════════════════════════\n");
    printf("  FFI STRESS TEST SUMMARY\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("  Total errors: %d\n", total_errors);

    if (total_errors == 0) {
        printf("\n  [PASS] All stress tests completed without errors.\n");
        printf("  NOTE: Run with Valgrind to verify zero memory leaks.\n");
    } else {
        printf("\n  [FAIL] Some stress tests had errors.\n");
    }

    printf("\n═══════════════════════════════════════════════════════════════════════\n");

    dlclose(lib);
    return total_errors > 0 ? 1 : 0;
}
