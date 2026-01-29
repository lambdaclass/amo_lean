/**
 * NTT_Final.c - Performance Benchmark
 *
 * AMO-Lean Phase 5 QA: Final Audit
 *
 * Measures NTT throughput for various sizes to validate performance.
 *
 * Metrics:
 *   - Time per NTT transform
 *   - Throughput (elements/second)
 *   - Comparison: lazy vs strict (if implemented)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>

#include "../generated/field_goldilocks.h"
#include "../generated/ntt_kernel.h"
#include "../generated/ntt_skeleton.c"

/*===========================================================================
 * Timing Utilities
 *===========================================================================*/

static double get_time_sec(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec + tv.tv_usec * 1e-6;
}

/*===========================================================================
 * Primitive Roots (from Lean)
 *===========================================================================*/

typedef struct {
    size_t n;
    size_t log2_n;
    goldilocks_t omega;
    goldilocks_t n_inv;
} NttParams;

/* Precomputed parameters from Lean (primitiveRoot n, GoldilocksField.inv ⟨n⟩) */
static const NttParams PARAMS[] = {
    /* N=256 (2^8) */
    {256, 8, 0xBF79143CE60CA966ULL, 0xFEFFFFFF01000001ULL},
    /* N=1024 (2^10) */
    {1024, 10, 0x9D8F2AD78BFED972ULL, 0xFFBFFFFF00400001ULL},
    /* N=4096 (2^12) */
    {4096, 12, 0xF2C35199959DFCB6ULL, 0xFFEFFFFF00100001ULL},
    /* N=16384 (2^14) */
    {16384, 14, 0xE0EE099310BBA1E2ULL, 0xFFFBFFFF00040001ULL},
    /* N=65536 (2^16) */
    {65536, 16, 0x54DF9630BF79450EULL, 0xFFFEFFFF00010001ULL},
    /* N=262144 (2^18) */
    {262144, 18, 0x81281A7B05F9BEACULL, 0xFFFFBFFF00004001ULL},
};
#define NUM_PARAMS (sizeof(PARAMS) / sizeof(PARAMS[0]))

/*===========================================================================
 * Benchmark Functions
 *===========================================================================*/

static void benchmark_ntt(const NttParams* params, int iterations) {
    size_t n = params->n;
    goldilocks_t omega = params->omega;
    goldilocks_t n_inv = params->n_inv;

    /* Allocate data */
    goldilocks_t* data = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));
    goldilocks_t* backup = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));
    if (!data || !backup) {
        printf("FAIL: malloc failed for N=%zu\n", n);
        free(data);
        free(backup);
        return;
    }

    /* Initialize with sequential values */
    for (size_t i = 0; i < n; i++) {
        data[i] = i + 1;
        backup[i] = i + 1;
    }

    /* Warmup */
    ntt_forward(data, n, omega);
    ntt_inverse(data, n, omega, n_inv);
    memcpy(data, backup, n * sizeof(goldilocks_t));

    /* Benchmark forward NTT */
    double start = get_time_sec();
    for (int iter = 0; iter < iterations; iter++) {
        ntt_forward(data, n, omega);
        memcpy(data, backup, n * sizeof(goldilocks_t));  /* Reset for next iteration */
    }
    double end = get_time_sec();

    double total_time = end - start;
    double time_per_ntt = total_time / iterations;
    double throughput = (double)n * iterations / total_time;

    printf("N=%6zu (2^%2zu): %8.3f ms/NTT, %10.2f M elem/s\n",
           n, params->log2_n,
           time_per_ntt * 1000.0,
           throughput / 1e6);

    /* Verify correctness (one final roundtrip) */
    memcpy(data, backup, n * sizeof(goldilocks_t));
    ntt_forward(data, n, omega);
    ntt_inverse(data, n, omega, n_inv);
    for (size_t i = 0; i < n; i++) {
        if (data[i] != backup[i]) {
            printf("  WARNING: Roundtrip verification failed at index %zu\n", i);
            break;
        }
    }

    free(data);
    free(backup);
}

static void benchmark_butterfly_kernel(void) {
    printf("\n=== Butterfly Kernel Microbenchmark ===\n");

    /* Benchmark raw butterfly operations */
    const size_t NUM_OPS = 10000000;

    lazy_goldilocks_t a = 12345678901234567ULL;
    lazy_goldilocks_t b = 98765432109876543ULL;
    goldilocks_t tw = 0xABCDEF0123456789ULL % GOLDILOCKS_ORDER;

    double start = get_time_sec();
    for (size_t i = 0; i < NUM_OPS; i++) {
        lazy_butterfly(&a, &b, tw);
        /* Prevent optimization */
        a = lazy_reduce(a);
        b = lazy_reduce(b);
    }
    double end = get_time_sec();

    double total_time = end - start;
    double ops_per_sec = NUM_OPS / total_time;

    printf("Butterfly ops: %zu iterations\n", NUM_OPS);
    printf("Time: %.3f s\n", total_time);
    printf("Throughput: %.2f M butterflies/s\n", ops_per_sec / 1e6);
    printf("Final values: a=%llu, b=%llu (prevent opt)\n",
           (unsigned long long)lazy_reduce(a),
           (unsigned long long)lazy_reduce(b));
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  NTT Performance Benchmark\n");
    printf("  AMO-Lean Phase 5 QA Final Audit\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    printf("=== Full NTT Benchmark ===\n");
    printf("Running multiple sizes with 100-10000 iterations each...\n\n");

    /* Adjust iterations based on size (larger = fewer iterations) */
    int iterations[] = {10000, 5000, 1000, 500, 100, 50};

    for (size_t i = 0; i < NUM_PARAMS; i++) {
        benchmark_ntt(&PARAMS[i], iterations[i]);
    }

    benchmark_butterfly_kernel();

    printf("\n═══════════════════════════════════════════════════════════════\n");
    printf("  Benchmark Complete\n");
    printf("═══════════════════════════════════════════════════════════════\n");

    return 0;
}
