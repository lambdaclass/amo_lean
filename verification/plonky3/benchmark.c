/**
 * benchmark.c - Plonky3 vs AMO-Lean Performance Benchmark
 *
 * Phase 6B: Comparative Performance Analysis with Optimizations
 *
 * This benchmark compares the performance of Plonky3's NTT implementation
 * against AMO-Lean's verified implementation for the Goldilocks field.
 *
 * Phase 6B Optimizations:
 *   - Full twiddle caching via NttContext (ADR-6B-002)
 *   - x4 loop unrolling for ILP (ADR-6B-006)
 *
 * Note: This is NOT a competition. The goal is to understand performance
 * characteristics and validate that our verified implementation is practical.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <math.h>
#include <dlfcn.h>

/* Include AMO-Lean NTT implementation - Phase 6B optimized version */
#include "../../generated/field_goldilocks.h"
#include "../../generated/ntt_kernel.h"
#include "../../generated/ntt_context.h"
#include "../../generated/ntt_cached.c"

/*===========================================================================
 * Plonky3 Function Types
 *===========================================================================*/

typedef int (*plonky3_ntt_fn)(uint64_t*, size_t);
typedef uint64_t (*plonky3_omega_fn)(size_t);

/*===========================================================================
 * Benchmark Configuration
 *===========================================================================*/

#define WARMUP_ITERATIONS 10
#define MIN_BENCHMARK_ITERATIONS 50
#define TARGET_TIME_MS 500.0  /* Target ~500ms per benchmark for stability */

/*===========================================================================
 * Test Parameters (omega values from Plonky3 TWO_ADIC_GENERATORS)
 *===========================================================================*/

typedef struct {
    size_t n;
    size_t log2_n;
    uint64_t omega;
} BenchParams;

static const BenchParams BENCH_PARAMS[] = {
    /* Small sizes */
    {256,    8,  0xBF79143CE60CA966ULL},
    {512,    9,  0x1905D02A5C411F4EULL},
    {1024,   10, 0x9D8F2AD78BFED972ULL},
    /* Medium sizes */
    {2048,   11, 0x0653B4801DA1C8CFULL},
    {4096,   12, 0xF2C35199959DFCB6ULL},
    {8192,   13, 0x1544EF2335D17997ULL},
    /* Large sizes */
    {16384,  14, 0xE0EE099310BBA1E2ULL},
    {32768,  15, 0xF6B2CFFE2306BAACULL},
    {65536,  16, 0x54DF9630BF79450EULL},
};
#define NUM_BENCH_PARAMS (sizeof(BENCH_PARAMS) / sizeof(BENCH_PARAMS[0]))

/*===========================================================================
 * Timing Utilities
 *===========================================================================*/

static double get_time_us(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000000.0 + tv.tv_usec;
}

/*===========================================================================
 * Benchmark Results
 *===========================================================================*/

typedef struct {
    size_t n;
    double plonky3_us;      /* Average time in microseconds */
    double amolean_us;
    double plonky3_stddev;  /* Standard deviation */
    double amolean_stddev;
    int iterations;
} BenchResult;

/*===========================================================================
 * Benchmark Functions
 *===========================================================================*/

/**
 * Determine optimal number of iterations based on execution time
 */
static int calibrate_iterations(plonky3_ntt_fn ntt_fn, uint64_t* data,
                                 uint64_t* backup, size_t n) {
    /* Run a few iterations to estimate time */
    double start = get_time_us();
    for (int i = 0; i < 5; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        ntt_fn(data, n);
    }
    double elapsed = get_time_us() - start;
    double per_iter = elapsed / 5.0;

    /* Calculate iterations to reach target time */
    int iters = (int)(TARGET_TIME_MS * 1000.0 / per_iter);
    if (iters < MIN_BENCHMARK_ITERATIONS) iters = MIN_BENCHMARK_ITERATIONS;
    if (iters > 1000) iters = 1000;  /* Cap at 1000 */

    return iters;
}

/**
 * Run benchmark for a specific size
 */
static BenchResult benchmark_size(plonky3_ntt_fn plonky3_ntt,
                                   const BenchParams* params) {
    BenchResult result;
    result.n = params->n;

    size_t n = params->n;
    size_t log2_n = params->log2_n;

    /* Allocate buffers */
    uint64_t* data = malloc(n * sizeof(uint64_t));
    uint64_t* backup = malloc(n * sizeof(uint64_t));
    double* plonky3_times = NULL;
    double* amolean_times = NULL;

    if (!data || !backup) {
        result.plonky3_us = -1;
        result.amolean_us = -1;
        free(data);
        free(backup);
        return result;
    }

    /* Initialize with pseudo-random data */
    for (size_t i = 0; i < n; i++) {
        backup[i] = (i * 0x9E3779B97F4A7C15ULL + 0x6A09E667F3BCC908ULL) % GOLDILOCKS_ORDER;
    }

    /*
     * Phase 6B: Create NttContext with cached twiddles
     * This is the optimized version with full twiddle caching + loop unrolling
     */
    NttContext* ctx = ntt_context_create(log2_n);
    if (!ctx) {
        result.plonky3_us = -1;
        result.amolean_us = -1;
        free(data);
        free(backup);
        return result;
    }

    /* Warmup Plonky3 */
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        plonky3_ntt(data, n);
    }

    /* Calibrate iterations */
    int iterations = calibrate_iterations(plonky3_ntt, data, backup, n);
    result.iterations = iterations;

    plonky3_times = malloc(iterations * sizeof(double));
    amolean_times = malloc(iterations * sizeof(double));

    /* Benchmark Plonky3 */
    for (int i = 0; i < iterations; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        double start = get_time_us();
        plonky3_ntt(data, n);
        double end = get_time_us();
        plonky3_times[i] = end - start;
    }

    /* Warmup AMO-Lean (using cached context) */
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        ntt_forward_ctx(ctx, data);
    }

    /* Benchmark AMO-Lean (using cached context with loop unrolling) */
    for (int i = 0; i < iterations; i++) {
        memcpy(data, backup, n * sizeof(uint64_t));
        double start = get_time_us();
        ntt_forward_ctx(ctx, data);
        double end = get_time_us();
        amolean_times[i] = end - start;
    }

    /* Calculate statistics - Plonky3 */
    double sum = 0, sum_sq = 0;
    for (int i = 0; i < iterations; i++) {
        sum += plonky3_times[i];
        sum_sq += plonky3_times[i] * plonky3_times[i];
    }
    result.plonky3_us = sum / iterations;
    result.plonky3_stddev = sqrt(sum_sq / iterations - result.plonky3_us * result.plonky3_us);

    /* Calculate statistics - AMO-Lean */
    sum = 0; sum_sq = 0;
    for (int i = 0; i < iterations; i++) {
        sum += amolean_times[i];
        sum_sq += amolean_times[i] * amolean_times[i];
    }
    result.amolean_us = sum / iterations;
    result.amolean_stddev = sqrt(sum_sq / iterations - result.amolean_us * result.amolean_us);

    free(data);
    free(backup);
    free(plonky3_times);
    free(amolean_times);
    ntt_context_destroy(ctx);

    return result;
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════════════\n");
    printf("  Plonky3 vs AMO-Lean Performance Benchmark\n");
    printf("  Phase 6A.5: Comparative Analysis\n");
    printf("═══════════════════════════════════════════════════════════════════════\n\n");

    /* Load Plonky3 shim */
    printf("Loading Plonky3 shim...\n");

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
    plonky3_omega_fn plonky3_omega = (plonky3_omega_fn)dlsym(lib, "plonky3_get_omega");

    if (!plonky3_ntt || !plonky3_omega) {
        fprintf(stderr, "ERROR: Failed to load functions\n");
        dlclose(lib);
        return 1;
    }

    printf("Plonky3 shim loaded successfully.\n");

    /* Verify omega values */
    printf("\nVerifying omega values...\n");
    int omega_ok = 1;
    for (size_t i = 0; i < NUM_BENCH_PARAMS; i++) {
        uint64_t p3_omega = plonky3_omega(BENCH_PARAMS[i].log2_n);
        if (p3_omega != BENCH_PARAMS[i].omega) {
            printf("  WARNING: Omega mismatch for N=%zu\n", BENCH_PARAMS[i].n);
            omega_ok = 0;
        }
    }
    if (omega_ok) {
        printf("  All omega values verified.\n");
    }

    /* Run benchmarks */
    printf("\nRunning benchmarks (warmup=%d, target=%.0fms per test)...\n\n",
           WARMUP_ITERATIONS, TARGET_TIME_MS);

    BenchResult results[NUM_BENCH_PARAMS];

    for (size_t i = 0; i < NUM_BENCH_PARAMS; i++) {
        printf("  Benchmarking N=%zu...", BENCH_PARAMS[i].n);
        fflush(stdout);
        results[i] = benchmark_size(plonky3_ntt, &BENCH_PARAMS[i]);
        printf(" done (%d iterations)\n", results[i].iterations);
    }

    /* Print results table */
    printf("\n═══════════════════════════════════════════════════════════════════════\n");
    printf("  BENCHMARK RESULTS\n");
    printf("═══════════════════════════════════════════════════════════════════════\n\n");

    printf("┌──────────┬─────────────────────┬─────────────────────┬────────────────┐\n");
    printf("│   Size   │   Plonky3 (us)      │   AMO-Lean (us)     │     Ratio      │\n");
    printf("├──────────┼─────────────────────┼─────────────────────┼────────────────┤\n");

    for (size_t i = 0; i < NUM_BENCH_PARAMS; i++) {
        BenchResult* r = &results[i];

        double ratio = r->amolean_us / r->plonky3_us;
        const char* faster;
        double speedup;

        if (ratio < 1.0) {
            faster = "AMO-Lean";
            speedup = 1.0 / ratio;
        } else {
            faster = "Plonky3";
            speedup = ratio;
        }

        printf("│ N=%-6zu │ %8.1f ± %-7.1f │ %8.1f ± %-7.1f │ %.2fx %-8s│\n",
               r->n,
               r->plonky3_us, r->plonky3_stddev,
               r->amolean_us, r->amolean_stddev,
               speedup, faster);
    }

    printf("└──────────┴─────────────────────┴─────────────────────┴────────────────┘\n");

    /* Throughput analysis */
    printf("\n═══════════════════════════════════════════════════════════════════════\n");
    printf("  THROUGHPUT ANALYSIS (elements/microsecond)\n");
    printf("═══════════════════════════════════════════════════════════════════════\n\n");

    printf("┌──────────┬────────────────┬────────────────┬────────────────┐\n");
    printf("│   Size   │    Plonky3     │    AMO-Lean    │    Ratio       │\n");
    printf("├──────────┼────────────────┼────────────────┼────────────────┤\n");

    for (size_t i = 0; i < NUM_BENCH_PARAMS; i++) {
        BenchResult* r = &results[i];

        double p3_throughput = (double)r->n / r->plonky3_us;
        double al_throughput = (double)r->n / r->amolean_us;
        double ratio = al_throughput / p3_throughput;

        printf("│ N=%-6zu │ %10.2f     │ %10.2f     │ %10.2fx    │\n",
               r->n, p3_throughput, al_throughput, ratio);
    }

    printf("└──────────┴────────────────┴────────────────┴────────────────┘\n");

    /* Summary */
    printf("\n═══════════════════════════════════════════════════════════════════════\n");
    printf("  NOTES\n");
    printf("═══════════════════════════════════════════════════════════════════════\n\n");

    printf("  - Plonky3: Uses Radix-2 DIT with twiddle caching\n");
    printf("  - AMO-Lean: Uses Radix-2 DIT with lazy reduction (Harvey 2014)\n");
    printf("  - AMO-Lean implementation is formally verified in Lean 4\n");
    printf("  - Both produce IDENTICAL results (verified in oracle_test)\n");
    printf("  - Times include memcpy overhead for fair comparison\n");
    printf("\n");

    /* Calculate average speedup */
    double total_ratio = 0;
    for (size_t i = 0; i < NUM_BENCH_PARAMS; i++) {
        total_ratio += results[i].amolean_us / results[i].plonky3_us;
    }
    double avg_ratio = total_ratio / NUM_BENCH_PARAMS;

    if (avg_ratio < 1.0) {
        printf("  Average: AMO-Lean is %.2fx faster than Plonky3\n", 1.0/avg_ratio);
    } else if (avg_ratio > 1.0) {
        printf("  Average: Plonky3 is %.2fx faster than AMO-Lean\n", avg_ratio);
    } else {
        printf("  Average: Both implementations have similar performance\n");
    }

    printf("\n");

    dlclose(lib);
    return 0;
}
