/**
 * bench_fri_fold.c - Benchmark for FRI fold operation
 *
 * This program benchmarks the generated FRI fold implementation.
 * It outputs timing information that can be parsed by the Lean benchmark harness.
 *
 * Compile:
 *   clang -DFIELD_NATIVE -O3 -march=native -o bench_fri_fold bench_fri_fold.c
 *
 * Usage:
 *   ./bench_fri_fold <size> <iterations>
 *
 * Output format (JSON):
 *   {"size": N, "iterations": I, "total_ns": T, "avg_ns": A}
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

#ifndef FIELD_NATIVE
#define FIELD_NATIVE
#endif
#include "field_ops.h"
#include "fri_fold.h"

/* Get current time in nanoseconds */
static uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/* Initialize array with pseudo-random values */
static void init_array(field_t* arr, size_t n, uint64_t seed) {
    uint64_t x = seed;
    for (size_t i = 0; i < n; i++) {
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;  /* LCG */
        arr[i] = x;
    }
}

int main(int argc, char** argv) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <size> <iterations>\n", argv[0]);
        return 1;
    }

    size_t size = (size_t)atol(argv[1]);
    size_t iterations = (size_t)atol(argv[2]);

    if (size == 0 || iterations == 0) {
        fprintf(stderr, "Error: size and iterations must be positive\n");
        return 1;
    }

    /* Allocate arrays */
    field_t* even = malloc(size * sizeof(field_t));
    field_t* odd = malloc(size * sizeof(field_t));
    field_t* out = malloc(size * sizeof(field_t));

    if (!even || !odd || !out) {
        fprintf(stderr, "Error: memory allocation failed\n");
        return 1;
    }

    /* Initialize with deterministic pseudo-random values */
    init_array(even, size, 12345);
    init_array(odd, size, 67890);
    field_t alpha = 0xDEADBEEFCAFEBABEULL;

    /* Warmup */
    for (size_t i = 0; i < 10; i++) {
        fri_fold(size, even, odd, out, alpha);
    }

    /* Benchmark */
    volatile field_t checksum = 0;  /* Prevent optimization */
    uint64_t start = get_time_ns();
    for (size_t i = 0; i < iterations; i++) {
        fri_fold(size, even, odd, out, alpha);
        checksum += out[0];  /* Use result to prevent dead code elimination */
    }
    uint64_t end = get_time_ns();

    uint64_t total_ns = end - start;
    double avg_ns = (double)total_ns / (double)iterations;

    /* Output JSON result - checksum ensures loop wasn't optimized away */
    printf("{\"size\": %zu, \"iterations\": %zu, \"total_ns\": %llu, \"avg_ns\": %.2f, \"checksum\": %llu}\n",
           size, iterations, (unsigned long long)total_ns, avg_ns, (unsigned long long)checksum);

    /* Cleanup */
    free(even);
    free(odd);
    free(out);

    return 0;
}
