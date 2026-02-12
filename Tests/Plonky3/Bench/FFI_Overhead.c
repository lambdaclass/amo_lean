/**
 * FFI_Overhead.c - FFI Call Overhead Measurement
 *
 * Phase 6A Hardening: Test 5
 *
 * Purpose: Measure the overhead of crossing the FFI boundary.
 * If FFI overhead exceeds 5% of compute time for N=256,
 * the design granularity is flagged as a problem.
 *
 * Tests:
 * 1. Pure noop() call overhead (baseline)
 * 2. Small NTT (N=256) total time
 * 3. Calculate: overhead / compute = percentage
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <dlfcn.h>

/*===========================================================================
 * Configuration
 *===========================================================================*/

#define WARMUP_ITERATIONS     10000
#define BENCHMARK_ITERATIONS  1000000
#define NTT_ITERATIONS        100000
#define NTT_SIZE              256

#define GOLDILOCKS_P          0xFFFFFFFF00000001ULL
#define OMEGA_256             0xBF79143CE60CA966ULL

/*===========================================================================
 * Function Types
 *===========================================================================*/

typedef void (*noop_fn)(void);
typedef int (*ntt_fn)(uint64_t*, size_t);
typedef uint64_t (*field_op_fn)(uint64_t, uint64_t);

/*===========================================================================
 * Timing
 *===========================================================================*/

static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

/*===========================================================================
 * Benchmark Functions
 *===========================================================================*/

static double benchmark_noop(noop_fn noop, int iterations) {
    printf("\n[BENCH 1] Pure FFI noop() call overhead...\n");

    /* Warmup */
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        noop();
    }

    /* Benchmark */
    double start = get_time_ns();
    for (int i = 0; i < iterations; i++) {
        noop();
    }
    double end = get_time_ns();

    double total_ns = end - start;
    double per_call_ns = total_ns / iterations;

    printf("  Iterations:   %d\n", iterations);
    printf("  Total time:   %.2f ms\n", total_ns / 1e6);
    printf("  Per call:     %.2f ns\n", per_call_ns);

    return per_call_ns;
}

static double benchmark_field_op(field_op_fn add, int iterations) {
    printf("\n[BENCH 2] Field operation (add) call...\n");

    uint64_t a = 12345678901234567ULL % GOLDILOCKS_P;
    uint64_t b = 98765432109876543ULL % GOLDILOCKS_P;

    /* Warmup */
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        a = add(a, b);
    }

    /* Benchmark */
    double start = get_time_ns();
    for (int i = 0; i < iterations; i++) {
        a = add(a, b);
    }
    double end = get_time_ns();

    double total_ns = end - start;
    double per_call_ns = total_ns / iterations;

    printf("  Iterations:   %d\n", iterations);
    printf("  Total time:   %.2f ms\n", total_ns / 1e6);
    printf("  Per call:     %.2f ns\n", per_call_ns);
    printf("  (Final a:     0x%llx - prevents optimization)\n", (unsigned long long)a);

    return per_call_ns;
}

static double benchmark_ntt_256(ntt_fn ntt_fwd, int iterations) {
    printf("\n[BENCH 3] NTT (N=%d) total time...\n", NTT_SIZE);

    uint64_t* data = malloc(NTT_SIZE * sizeof(uint64_t));
    uint64_t* backup = malloc(NTT_SIZE * sizeof(uint64_t));

    if (!data || !backup) {
        fprintf(stderr, "  ERROR: malloc failed\n");
        free(data);
        free(backup);
        return -1;
    }

    /* Initialize */
    for (size_t i = 0; i < NTT_SIZE; i++) {
        backup[i] = (i + 1) % GOLDILOCKS_P;
    }

    /* Warmup */
    for (int i = 0; i < WARMUP_ITERATIONS / 100; i++) {
        memcpy(data, backup, NTT_SIZE * sizeof(uint64_t));
        ntt_fwd(data, NTT_SIZE);
    }

    /* Benchmark */
    double start = get_time_ns();
    for (int i = 0; i < iterations; i++) {
        memcpy(data, backup, NTT_SIZE * sizeof(uint64_t));
        ntt_fwd(data, NTT_SIZE);
    }
    double end = get_time_ns();

    double total_ns = end - start;
    double per_call_ns = total_ns / iterations;

    printf("  Iterations:   %d\n", iterations);
    printf("  Total time:   %.2f ms\n", total_ns / 1e6);
    printf("  Per call:     %.2f ns (%.2f us)\n", per_call_ns, per_call_ns / 1000);

    free(data);
    free(backup);

    return per_call_ns;
}

static double benchmark_multiple_ntt_calls(ntt_fn ntt_fwd, ntt_fn ntt_inv, int iterations) {
    printf("\n[BENCH 4] Multiple FFI calls per operation (NTT + INTT)...\n");

    uint64_t* data = malloc(NTT_SIZE * sizeof(uint64_t));
    uint64_t* backup = malloc(NTT_SIZE * sizeof(uint64_t));

    if (!data || !backup) {
        fprintf(stderr, "  ERROR: malloc failed\n");
        free(data);
        free(backup);
        return -1;
    }

    /* Initialize */
    for (size_t i = 0; i < NTT_SIZE; i++) {
        backup[i] = (i + 1) % GOLDILOCKS_P;
    }

    /* Warmup */
    for (int i = 0; i < WARMUP_ITERATIONS / 100; i++) {
        memcpy(data, backup, NTT_SIZE * sizeof(uint64_t));
        ntt_fwd(data, NTT_SIZE);
        ntt_inv(data, NTT_SIZE);
    }

    /* Benchmark */
    double start = get_time_ns();
    for (int i = 0; i < iterations; i++) {
        memcpy(data, backup, NTT_SIZE * sizeof(uint64_t));
        ntt_fwd(data, NTT_SIZE);
        ntt_inv(data, NTT_SIZE);
    }
    double end = get_time_ns();

    double total_ns = end - start;
    double per_roundtrip_ns = total_ns / iterations;

    printf("  Iterations:   %d (each = NTT + INTT = 2 FFI calls)\n", iterations);
    printf("  Total time:   %.2f ms\n", total_ns / 1e6);
    printf("  Per roundtrip: %.2f ns (%.2f us)\n", per_roundtrip_ns, per_roundtrip_ns / 1000);

    free(data);
    free(backup);

    return per_roundtrip_ns;
}

/*===========================================================================
 * Analysis
 *===========================================================================*/

static void analyze_overhead(double noop_ns, double ntt_ns) {
    printf("\n═══════════════════════════════════════════════════════════════════════\n");
    printf("  OVERHEAD ANALYSIS\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");

    if (noop_ns < 0 || ntt_ns < 0) {
        printf("\n  [ERROR] Could not complete analysis due to benchmark failures.\n");
        return;
    }

    /* FFI overhead is approximately the noop time */
    double ffi_overhead_ns = noop_ns;

    /* Compute time is NTT time minus FFI overhead */
    double compute_ns = ntt_ns - ffi_overhead_ns;
    if (compute_ns < 0) compute_ns = ntt_ns;  /* Safety */

    /* Percentage */
    double overhead_percent = (ffi_overhead_ns / ntt_ns) * 100.0;

    printf("\n  Measurements:\n");
    printf("    Pure FFI call (noop):     %.2f ns\n", ffi_overhead_ns);
    printf("    Total NTT (N=256):        %.2f ns\n", ntt_ns);
    printf("    Estimated compute time:   %.2f ns\n", compute_ns);
    printf("\n  FFI Overhead Analysis:\n");
    printf("    Overhead / Total:         %.2f%%\n", overhead_percent);

    /* Verdict */
    printf("\n  Verdict:\n");

    if (overhead_percent <= 1.0) {
        printf("    [EXCELLENT] FFI overhead is negligible (<1%%)\n");
        printf("    The current granularity is optimal.\n");
    } else if (overhead_percent <= 5.0) {
        printf("    [PASS] FFI overhead is acceptable (<5%%)\n");
        printf("    The current granularity is good.\n");
    } else if (overhead_percent <= 10.0) {
        printf("    [WARN] FFI overhead is noticeable (5-10%%)\n");
        printf("    Consider batching operations if performance is critical.\n");
    } else {
        printf("    [FAIL] FFI overhead exceeds 10%%!\n");
        printf("    DESIGN PROBLEM: Granularity too fine.\n");
        printf("    Recommendation: Batch multiple operations per FFI call.\n");
    }

    /* Additional context */
    printf("\n  Context:\n");
    printf("    At N=256, we do ~%d butterfly operations.\n", NTT_SIZE * 8 / 2);
    printf("    Each butterfly is ~10-20 CPU cycles.\n");
    printf("    FFI call is ~%.0f CPU cycles (at 3GHz).\n", ffi_overhead_ns * 3);
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("  FFI Overhead Benchmark\n");
    printf("  Phase 6A Hardening Suite\n");
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("\n  Measuring FFI call overhead vs compute time...\n");
    printf("  Criteria: Overhead should be <5%% of compute for N=256\n");

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

    noop_fn noop = (noop_fn)dlsym(lib, "plonky3_noop");
    ntt_fn ntt_fwd = (ntt_fn)dlsym(lib, "plonky3_ntt_forward");
    ntt_fn ntt_inv = (ntt_fn)dlsym(lib, "plonky3_ntt_inverse");
    field_op_fn add = (field_op_fn)dlsym(lib, "plonky3_add");

    if (!ntt_fwd || !ntt_inv) {
        fprintf(stderr, "ERROR: Failed to load NTT functions\n");
        dlclose(lib);
        return 1;
    }

    if (!noop) {
        printf("\n  WARNING: plonky3_noop not available, using field_add as proxy\n");
    }

    printf("Library loaded successfully.\n");

    /* Run benchmarks */
    double noop_ns = -1;
    if (noop) {
        noop_ns = benchmark_noop(noop, BENCHMARK_ITERATIONS);
    }

    double field_op_ns = -1;
    if (add) {
        field_op_ns = benchmark_field_op(add, BENCHMARK_ITERATIONS);
    }

    /* If noop not available, use field_op as proxy */
    if (noop_ns < 0 && field_op_ns > 0) {
        printf("\n  Using field_add as FFI overhead proxy\n");
        noop_ns = field_op_ns;
    }

    double ntt_ns = benchmark_ntt_256(ntt_fwd, NTT_ITERATIONS);
    double roundtrip_ns = benchmark_multiple_ntt_calls(ntt_fwd, ntt_inv, NTT_ITERATIONS / 2);

    /* Analysis */
    analyze_overhead(noop_ns, ntt_ns);

    /* Additional info */
    printf("\n  Additional Metrics:\n");
    printf("    NTT+INTT roundtrip:       %.2f us\n", roundtrip_ns / 1000);
    printf("    Throughput (N=256):       %.2f M elements/sec\n",
           (NTT_SIZE * 1e9) / (ntt_ns * 1e6));

    printf("\n═══════════════════════════════════════════════════════════════════════\n");

    dlclose(lib);
    return 0;
}
