/**
 * Poseidon2 S-box Benchmark
 *
 * Benchmark 2.1: Scalar Throughput
 *
 * Measures hashes per second to establish performance baseline.
 */

#include "bn254_field.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

/* ============================================================================
 * Timing Utilities
 * ============================================================================ */

#ifdef __APPLE__
#include <mach/mach_time.h>

static double get_time_ns(void) {
    static mach_timebase_info_data_t info = {0, 0};
    if (info.denom == 0) {
        mach_timebase_info(&info);
    }
    return (double)mach_absolute_time() * info.numer / info.denom;
}
#else
static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
#endif

/* ============================================================================
 * Benchmark Functions
 * ============================================================================ */

/* Prevent compiler from optimizing away the result */
static volatile uint64_t sink;

static void benchmark_sbox5(const field_params *p, int iterations) {
    printf("\n══════ Benchmark: S-box x^5 ══════\n");

    bn254_fe x, result;
    bn254_from_u64(&x, 12345, p);

    /* Warm-up */
    for (int i = 0; i < 1000; i++) {
        bn254_sbox5(&result, &x, p);
        bn254_copy(&x, &result);
    }

    /* Benchmark */
    double start = get_time_ns();

    for (int i = 0; i < iterations; i++) {
        bn254_sbox5(&result, &x, p);
        bn254_copy(&x, &result);
    }

    double end = get_time_ns();
    double total_ns = end - start;
    double per_op_ns = total_ns / iterations;
    double ops_per_sec = 1e9 / per_op_ns;

    sink = result.limbs[0];  /* Prevent optimization */

    printf("  Iterations: %d\n", iterations);
    printf("  Total time: %.3f ms\n", total_ns / 1e6);
    printf("  Per S-box:  %.1f ns\n", per_op_ns);
    printf("  Throughput: %.0f S-box/sec\n", ops_per_sec);
}

static void benchmark_full_round(const field_params *p, int iterations) {
    printf("\n══════ Benchmark: Full Round (t=3) ══════\n");

    poseidon_state_3 state;
    bn254_from_u64(&state.elem[0], 1, p);
    bn254_from_u64(&state.elem[1], 2, p);
    bn254_from_u64(&state.elem[2], 3, p);

    /* Warm-up */
    for (int i = 0; i < 1000; i++) {
        bn254_sbox5_full_round(&state, p);
    }

    /* Benchmark */
    double start = get_time_ns();

    for (int i = 0; i < iterations; i++) {
        bn254_sbox5_full_round(&state, p);
    }

    double end = get_time_ns();
    double total_ns = end - start;
    double per_round_ns = total_ns / iterations;
    double rounds_per_sec = 1e9 / per_round_ns;

    sink = state.elem[0].limbs[0];

    printf("  Iterations: %d\n", iterations);
    printf("  Total time: %.3f ms\n", total_ns / 1e6);
    printf("  Per round:  %.1f ns\n", per_round_ns);
    printf("  Throughput: %.0f rounds/sec\n", rounds_per_sec);

    /* Estimate hash rate */
    /* Poseidon2 has RF=8 full rounds + RP=56 partial rounds */
    int rf = 8, rp = 56;
    double full_round_ns = per_round_ns;
    double partial_round_ns = per_round_ns / 3;  /* Approx: 1/3 the work */
    double hash_ns = rf * full_round_ns + rp * partial_round_ns;
    double hashes_per_sec = 1e9 / hash_ns;

    printf("\n  Estimated hash rate (RF=%d, RP=%d):\n", rf, rp);
    printf("  Per hash:   %.1f us\n", hash_ns / 1e3);
    printf("  Throughput: %.0f H/s\n", hashes_per_sec);
}

static void benchmark_partial_round(const field_params *p, int iterations) {
    printf("\n══════ Benchmark: Partial Round (t=3) ══════\n");

    poseidon_state_3 state;
    bn254_from_u64(&state.elem[0], 1, p);
    bn254_from_u64(&state.elem[1], 2, p);
    bn254_from_u64(&state.elem[2], 3, p);

    /* Warm-up */
    for (int i = 0; i < 1000; i++) {
        bn254_sbox5_partial_round(&state, p);
    }

    /* Benchmark */
    double start = get_time_ns();

    for (int i = 0; i < iterations; i++) {
        bn254_sbox5_partial_round(&state, p);
    }

    double end = get_time_ns();
    double total_ns = end - start;
    double per_round_ns = total_ns / iterations;
    double rounds_per_sec = 1e9 / per_round_ns;

    sink = state.elem[0].limbs[0];

    printf("  Iterations: %d\n", iterations);
    printf("  Total time: %.3f ms\n", total_ns / 1e6);
    printf("  Per round:  %.1f ns\n", per_round_ns);
    printf("  Throughput: %.0f rounds/sec\n", rounds_per_sec);
}

static void benchmark_field_mul(const field_params *p, int iterations) {
    printf("\n══════ Benchmark: Field Multiplication ══════\n");

    bn254_fe a, b, c;
    bn254_from_u64(&a, 12345, p);
    bn254_from_u64(&b, 67890, p);

    /* Warm-up */
    for (int i = 0; i < 1000; i++) {
        bn254_mul(&c, &a, &b, p);
        bn254_copy(&a, &c);
    }

    /* Benchmark */
    double start = get_time_ns();

    for (int i = 0; i < iterations; i++) {
        bn254_mul(&c, &a, &b, p);
        bn254_copy(&a, &c);
    }

    double end = get_time_ns();
    double total_ns = end - start;
    double per_mul_ns = total_ns / iterations;
    double muls_per_sec = 1e9 / per_mul_ns;

    sink = c.limbs[0];

    printf("  Iterations: %d\n", iterations);
    printf("  Total time: %.3f ms\n", total_ns / 1e6);
    printf("  Per mul:    %.1f ns\n", per_mul_ns);
    printf("  Throughput: %.0f mul/sec\n", muls_per_sec);
}

/* ============================================================================
 * Main
 * ============================================================================ */

int main(int argc, char *argv[]) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Poseidon2 S-box Performance Benchmark\n");
    printf("  Phase Poseidon - Baseline Establishment\n");
    printf("═══════════════════════════════════════════════════════════════\n");

    /* Initialize field parameters */
    field_params p;
    bn254_init_params(&p);

    int iterations = (argc > 1) ? atoi(argv[1]) : 100000;
    printf("\nIterations: %d\n", iterations);

    /* Run benchmarks */
    benchmark_field_mul(&p, iterations);
    benchmark_sbox5(&p, iterations);
    benchmark_partial_round(&p, iterations);
    benchmark_full_round(&p, iterations);

    printf("\n═══════════════════════════════════════════════════════════════\n");
    printf("  Performance Analysis\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("\n  Expected baseline for scalar BN254 code:\n");
    printf("    - Field mul:    100-500 ns (depending on CPU)\n");
    printf("    - S-box x^5:    300-1500 ns (3 muls + overhead)\n");
    printf("    - Full round:   1-5 us (3 S-boxes)\n");
    printf("    - Hash rate:    10k-50k H/s (scalar, single core)\n");
    printf("\n  If numbers are significantly worse, check:\n");
    printf("    - Dynamic memory allocation in hot path\n");
    printf("    - Cache misses (data layout)\n");
    printf("    - Compiler optimization flags\n");
    printf("\n");

    return 0;
}
