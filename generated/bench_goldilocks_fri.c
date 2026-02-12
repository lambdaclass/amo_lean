/**
 * bench_goldilocks_fri.c - Phase 1 Benchmark: FRI Fold with Goldilocks Field
 *
 * Compares performance of FRI fold operation:
 * - UInt64 native (Phase 0)
 * - Goldilocks field (Phase 1)
 *
 * Compile:
 *   gcc -O3 -march=native -o bench_goldilocks_fri bench_goldilocks_fri.c
 *
 * Run:
 *   ./bench_goldilocks_fri [size] [iterations]
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include "field_goldilocks.h"

/*===========================================================================
 * Timing Infrastructure
 *===========================================================================*/

static inline uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/*===========================================================================
 * Test Data Generation
 *===========================================================================*/

/**
 * Simple LCG for reproducible pseudo-random data
 */
static inline uint64_t lcg_next(uint64_t *state) {
    *state = *state * 6364136223846793005ULL + 1442695040888963407ULL;
    return *state;
}

/**
 * Generate test data for UInt64 mode
 */
void generate_uint64_data(uint64_t *even, uint64_t *odd, size_t size, uint64_t seed) {
    uint64_t state = seed;
    for (size_t i = 0; i < size; i++) {
        even[i] = lcg_next(&state);
        odd[i] = lcg_next(&state);
    }
}

/**
 * Generate test data for Goldilocks mode (values < p)
 */
void generate_goldilocks_data(goldilocks_t *even, goldilocks_t *odd, size_t size, uint64_t seed) {
    uint64_t state = seed;
    for (size_t i = 0; i < size; i++) {
        even[i] = goldilocks_reduce(lcg_next(&state));
        odd[i] = goldilocks_reduce(lcg_next(&state));
    }
}

/*===========================================================================
 * FRI Fold Implementations
 *===========================================================================*/

/**
 * FRI fold with native UInt64 (Phase 0 - wrapping arithmetic)
 *
 * out[i] = even[i] + alpha * odd[i]
 */
void fri_fold_uint64(const uint64_t *restrict even,
                     const uint64_t *restrict odd,
                     uint64_t *restrict out,
                     uint64_t alpha,
                     size_t size) {
    for (size_t i = 0; i < size; i++) {
        out[i] = even[i] + alpha * odd[i];
    }
}

/**
 * FRI fold with Goldilocks field (Phase 1 - proper field arithmetic)
 *
 * out[i] = (even[i] + alpha * odd[i]) mod p
 */
void fri_fold_goldilocks(const goldilocks_t *restrict even,
                         const goldilocks_t *restrict odd,
                         goldilocks_t *restrict out,
                         goldilocks_t alpha,
                         size_t size) {
    for (size_t i = 0; i < size; i++) {
        goldilocks_t product = goldilocks_mul(alpha, odd[i]);
        out[i] = goldilocks_add(even[i], product);
    }
}

/*===========================================================================
 * Benchmark Functions
 *===========================================================================*/

typedef struct {
    uint64_t total_ns;
    double avg_ns_per_iter;
    double avg_ns_per_element;
    uint64_t checksum;
} BenchmarkResult;

/**
 * Benchmark UInt64 FRI fold
 */
BenchmarkResult benchmark_uint64(size_t size, size_t iterations) {
    uint64_t *even = malloc(size * sizeof(uint64_t));
    uint64_t *odd = malloc(size * sizeof(uint64_t));
    uint64_t *out = malloc(size * sizeof(uint64_t));

    generate_uint64_data(even, odd, size, 12345);
    uint64_t alpha = 0xDEADBEEFCAFEBABEULL;

    /* Warmup */
    for (int w = 0; w < 10; w++) {
        fri_fold_uint64(even, odd, out, alpha, size);
    }

    /* Benchmark */
    uint64_t start = get_time_ns();
    for (size_t i = 0; i < iterations; i++) {
        fri_fold_uint64(even, odd, out, alpha, size);
    }
    uint64_t end = get_time_ns();

    /* Compute checksum */
    uint64_t checksum = 0;
    for (size_t i = 0; i < size; i++) {
        checksum += out[i];
    }

    BenchmarkResult result = {
        .total_ns = end - start,
        .avg_ns_per_iter = (double)(end - start) / iterations,
        .avg_ns_per_element = (double)(end - start) / (iterations * size),
        .checksum = checksum
    };

    free(even);
    free(odd);
    free(out);

    return result;
}

/**
 * Benchmark Goldilocks FRI fold
 */
BenchmarkResult benchmark_goldilocks(size_t size, size_t iterations) {
    goldilocks_t *even = malloc(size * sizeof(goldilocks_t));
    goldilocks_t *odd = malloc(size * sizeof(goldilocks_t));
    goldilocks_t *out = malloc(size * sizeof(goldilocks_t));

    generate_goldilocks_data(even, odd, size, 12345);
    goldilocks_t alpha = goldilocks_reduce(0xDEADBEEFCAFEBABEULL);

    /* Warmup */
    for (int w = 0; w < 10; w++) {
        fri_fold_goldilocks(even, odd, out, alpha, size);
    }

    /* Benchmark */
    uint64_t start = get_time_ns();
    for (size_t i = 0; i < iterations; i++) {
        fri_fold_goldilocks(even, odd, out, alpha, size);
    }
    uint64_t end = get_time_ns();

    /* Compute checksum */
    uint64_t checksum = 0;
    for (size_t i = 0; i < size; i++) {
        checksum += out[i];
    }

    BenchmarkResult result = {
        .total_ns = end - start,
        .avg_ns_per_iter = (double)(end - start) / iterations,
        .avg_ns_per_element = (double)(end - start) / (iterations * size),
        .checksum = checksum
    };

    free(even);
    free(odd);
    free(out);

    return result;
}

/*===========================================================================
 * Main
 *===========================================================================*/

void print_separator(void) {
    printf("════════════════════════════════════════════════════════════════\n");
}

int main(int argc, char *argv[]) {
    size_t size = 1024;
    size_t iterations = 10000;

    if (argc >= 2) {
        size = (size_t)atol(argv[1]);
    }
    if (argc >= 3) {
        iterations = (size_t)atol(argv[2]);
    }

    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║     PHASE 1 BENCHMARK: FRI FOLD (UInt64 vs Goldilocks)       ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");

    printf("Configuration:\n");
    printf("  Size:       %zu elements\n", size);
    printf("  Iterations: %zu\n", iterations);
    printf("  Goldilocks p = 0x%llx\n\n", (unsigned long long)GOLDILOCKS_ORDER);

    print_separator();
    printf("Running benchmarks...\n");
    print_separator();
    printf("\n");

    /* Benchmark UInt64 */
    printf("UInt64 (Phase 0):\n");
    BenchmarkResult uint64_result = benchmark_uint64(size, iterations);
    printf("  Total time:    %llu ns\n", (unsigned long long)uint64_result.total_ns);
    printf("  Avg per iter:  %.2f ns\n", uint64_result.avg_ns_per_iter);
    printf("  Avg per elem:  %.4f ns\n", uint64_result.avg_ns_per_element);
    printf("  Checksum:      0x%llx\n\n", (unsigned long long)uint64_result.checksum);

    /* Benchmark Goldilocks */
    printf("Goldilocks (Phase 1):\n");
    BenchmarkResult gold_result = benchmark_goldilocks(size, iterations);
    printf("  Total time:    %llu ns\n", (unsigned long long)gold_result.total_ns);
    printf("  Avg per iter:  %.2f ns\n", gold_result.avg_ns_per_iter);
    printf("  Avg per elem:  %.4f ns\n", gold_result.avg_ns_per_element);
    printf("  Checksum:      0x%llx\n\n", (unsigned long long)gold_result.checksum);

    print_separator();
    printf("COMPARISON\n");
    print_separator();
    printf("\n");

    double overhead = (double)gold_result.total_ns / uint64_result.total_ns;
    double uint64_throughput = (double)(size * iterations) / (uint64_result.total_ns / 1e9) / 1e6;
    double gold_throughput = (double)(size * iterations) / (gold_result.total_ns / 1e9) / 1e6;

    printf("Overhead: Goldilocks is %.2fx slower than UInt64\n", overhead);
    printf("\n");
    printf("Throughput:\n");
    printf("  UInt64:     %.2f M elements/sec\n", uint64_throughput);
    printf("  Goldilocks: %.2f M elements/sec\n", gold_throughput);
    printf("\n");

    /* Assessment */
    if (overhead < 2.0) {
        printf("✅ Goldilocks overhead is acceptable (< 2x)\n");
    } else if (overhead < 5.0) {
        printf("⚠️  Goldilocks overhead is moderate (%.1fx)\n", overhead);
    } else {
        printf("❌ Goldilocks overhead is high (%.1fx) - consider optimization\n", overhead);
    }

    printf("\n");

    /* JSON output for automated parsing */
    printf("JSON: {\"size\": %zu, \"iterations\": %zu, ", size, iterations);
    printf("\"uint64_ns\": %llu, \"goldilocks_ns\": %llu, ",
           (unsigned long long)uint64_result.total_ns,
           (unsigned long long)gold_result.total_ns);
    printf("\"overhead\": %.4f, ", overhead);
    printf("\"uint64_throughput_meps\": %.2f, ", uint64_throughput);
    printf("\"goldilocks_throughput_meps\": %.2f}\n", gold_throughput);

    return 0;
}
