/**
 * cached_benchmark.c - Compare NTT optimizations
 *
 * Phase 6B.1.6: Benchmark loop unrolling improvement
 *
 * Compares three implementations:
 *   1. Original: recomputes twiddles each call
 *   2. Cached: precomputed twiddles (ADR-6B-002)
 *   3. Unrolled: cached + x4 loop unrolling (ADR-6B-006)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

#include "../../generated/field_goldilocks.h"
#include "../../generated/ntt_kernel.h"
#include "../../generated/ntt_context.h"

#define GOLDILOCKS_P 0xFFFFFFFF00000001ULL

/*===========================================================================
 * Original NTT (computes twiddles every call)
 *===========================================================================*/

static inline size_t bit_reverse(size_t x, size_t log2_n) {
    size_t result = 0;
    for (size_t i = 0; i < log2_n; i++) {
        result = (result << 1) | (x & 1);
        x >>= 1;
    }
    return result;
}

static void bit_reverse_permute(lazy_goldilocks_t* data, size_t n, size_t log2_n) {
    for (size_t i = 0; i < n; i++) {
        size_t j = bit_reverse(i, log2_n);
        if (i < j) {
            lazy_goldilocks_t tmp = data[i];
            data[i] = data[j];
            data[j] = tmp;
        }
    }
}

static goldilocks_t* precompute_twiddles_full(goldilocks_t omega, size_t n) {
    size_t half = n / 2;
    if (half == 0) return NULL;

    goldilocks_t* twiddles = (goldilocks_t*)malloc(half * sizeof(goldilocks_t));
    if (!twiddles) return NULL;

    twiddles[0] = 1;
    for (size_t k = 1; k < half; k++) {
        twiddles[k] = goldilocks_mul(twiddles[k-1], omega);
    }
    return twiddles;
}

/* Original NTT - computes ALL twiddles fresh each call */
int ntt_forward_original(goldilocks_t* data, size_t n, goldilocks_t omega) {
    if (n == 0 || (n & (n - 1)) != 0) return -1;
    if (n == 1) return 0;

    size_t log2_n = 0;
    for (size_t tmp = n; tmp > 1; tmp >>= 1) log2_n++;

    lazy_goldilocks_t* work = (lazy_goldilocks_t*)malloc(n * sizeof(lazy_goldilocks_t));
    if (!work) return -1;

    for (size_t i = 0; i < n; i++) {
        work[i] = lazy_from_strict(data[i]);
    }

    bit_reverse_permute(work, n, log2_n);

    goldilocks_t* all_twiddles = precompute_twiddles_full(omega, n);
    if (!all_twiddles) { free(work); return -1; }

    for (size_t layer = 0; layer < log2_n; layer++) {
        size_t m = 1UL << (layer + 1);
        size_t half_m = m / 2;
        size_t twiddle_step = n / m;

        for (size_t k = 0; k < n; k += m) {
            for (size_t j = 0; j < half_m; j++) {
                size_t idx_a = k + j;
                size_t idx_b = k + j + half_m;
                goldilocks_t tw = all_twiddles[j * twiddle_step];
                lazy_butterfly(&work[idx_a], &work[idx_b], tw);
            }
        }

        for (size_t i = 0; i < n; i++) {
            work[i] = lazy_reduce(work[i]);
        }
    }

    for (size_t i = 0; i < n; i++) {
        data[i] = lazy_to_strict(work[i]);
    }

    free(all_twiddles);
    free(work);
    return 0;
}

/*===========================================================================
 * Cached NTT WITHOUT unrolling (baseline for comparison)
 *===========================================================================*/

int ntt_forward_cached_no_unroll(const NttContext* ctx, goldilocks_t* data) {
    if (!ctx || !data) return -1;

    const size_t n = ctx->n;
    const size_t log_n = ctx->log_n;

    if (n == 1) return 0;

    lazy_goldilocks_t* work = (lazy_goldilocks_t*)malloc(n * sizeof(lazy_goldilocks_t));
    if (!work) return -1;

    for (size_t i = 0; i < n; i++) {
        work[i] = lazy_from_strict(data[i]);
    }

    bit_reverse_permute(work, n, log_n);

    for (size_t layer = 0; layer < log_n; layer++) {
        size_t m = 1UL << (layer + 1);
        size_t half_m = m / 2;

        if (layer < ctx->cached_layers) {
            /* Cached: direct lookup */
            const goldilocks_t* layer_twiddles =
                ctx->cached_twiddles + ctx->layer_offsets[layer];

            for (size_t k = 0; k < n; k += m) {
                for (size_t j = 0; j < half_m; j++) {
                    size_t idx_a = k + j;
                    size_t idx_b = k + j + half_m;
                    goldilocks_t tw = layer_twiddles[j];
                    lazy_butterfly(&work[idx_a], &work[idx_b], tw);
                }
            }
        } else {
            /* Uncached: compute on-the-fly */
            goldilocks_t omega_m = ctx->omega_powers[layer];

            for (size_t k = 0; k < n; k += m) {
                goldilocks_t tw = 1;
                for (size_t j = 0; j < half_m; j++) {
                    size_t idx_a = k + j;
                    size_t idx_b = k + j + half_m;
                    lazy_butterfly(&work[idx_a], &work[idx_b], tw);
                    tw = goldilocks_mul(tw, omega_m);
                }
            }
        }

        for (size_t i = 0; i < n; i++) {
            work[i] = lazy_reduce(work[i]);
        }
    }

    for (size_t i = 0; i < n; i++) {
        data[i] = lazy_to_strict(work[i]);
    }

    free(work);
    return 0;
}

/*===========================================================================
 * Cached NTT WITH x4 loop unrolling (ADR-6B-006)
 *===========================================================================*/

int ntt_forward_cached_unrolled(const NttContext* ctx, goldilocks_t* data) {
    if (!ctx || !data) return -1;

    const size_t n = ctx->n;
    const size_t log_n = ctx->log_n;

    if (n == 1) return 0;

    lazy_goldilocks_t* work = (lazy_goldilocks_t*)malloc(n * sizeof(lazy_goldilocks_t));
    if (!work) return -1;

    for (size_t i = 0; i < n; i++) {
        work[i] = lazy_from_strict(data[i]);
    }

    bit_reverse_permute(work, n, log_n);

    for (size_t layer = 0; layer < log_n; layer++) {
        size_t m = 1UL << (layer + 1);
        size_t half_m = m / 2;

        if (layer < ctx->cached_layers) {
            /* Cached: direct lookup with x4 unrolling */
            const goldilocks_t* layer_twiddles =
                ctx->cached_twiddles + ctx->layer_offsets[layer];

            for (size_t k = 0; k < n; k += m) {
                size_t j = 0;

                /* Unrolled x4 main loop */
                for (; j + 4 <= half_m; j += 4) {
                    goldilocks_t tw0 = layer_twiddles[j + 0];
                    goldilocks_t tw1 = layer_twiddles[j + 1];
                    goldilocks_t tw2 = layer_twiddles[j + 2];
                    goldilocks_t tw3 = layer_twiddles[j + 3];

                    lazy_butterfly(&work[k + j + 0], &work[k + j + 0 + half_m], tw0);
                    lazy_butterfly(&work[k + j + 1], &work[k + j + 1 + half_m], tw1);
                    lazy_butterfly(&work[k + j + 2], &work[k + j + 2 + half_m], tw2);
                    lazy_butterfly(&work[k + j + 3], &work[k + j + 3 + half_m], tw3);
                }

                /* Remainder loop */
                for (; j < half_m; j++) {
                    goldilocks_t tw = layer_twiddles[j];
                    lazy_butterfly(&work[k + j], &work[k + j + half_m], tw);
                }
            }
        } else {
            /* Uncached: compute on-the-fly with x4 unrolling */
            goldilocks_t omega_m = ctx->omega_powers[layer];
            goldilocks_t omega_m2 = goldilocks_mul(omega_m, omega_m);
            goldilocks_t omega_m3 = goldilocks_mul(omega_m2, omega_m);
            goldilocks_t omega_m4 = goldilocks_mul(omega_m2, omega_m2);

            for (size_t k = 0; k < n; k += m) {
                goldilocks_t tw0 = 1;
                size_t j = 0;

                /* Unrolled x4 main loop */
                for (; j + 4 <= half_m; j += 4) {
                    goldilocks_t tw1 = goldilocks_mul(tw0, omega_m);
                    goldilocks_t tw2 = goldilocks_mul(tw0, omega_m2);
                    goldilocks_t tw3 = goldilocks_mul(tw0, omega_m3);

                    lazy_butterfly(&work[k + j + 0], &work[k + j + 0 + half_m], tw0);
                    lazy_butterfly(&work[k + j + 1], &work[k + j + 1 + half_m], tw1);
                    lazy_butterfly(&work[k + j + 2], &work[k + j + 2 + half_m], tw2);
                    lazy_butterfly(&work[k + j + 3], &work[k + j + 3 + half_m], tw3);

                    tw0 = goldilocks_mul(tw0, omega_m4);
                }

                /* Remainder loop */
                for (; j < half_m; j++) {
                    lazy_butterfly(&work[k + j], &work[k + j + half_m], tw0);
                    tw0 = goldilocks_mul(tw0, omega_m);
                }
            }
        }

        for (size_t i = 0; i < n; i++) {
            work[i] = lazy_reduce(work[i]);
        }
    }

    for (size_t i = 0; i < n; i++) {
        data[i] = lazy_to_strict(work[i]);
    }

    free(work);
    return 0;
}

/*===========================================================================
 * Benchmark
 *===========================================================================*/

static double get_time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

void benchmark_size(size_t log_n, size_t iterations) {
    size_t n = 1UL << log_n;

    goldilocks_t* data_orig = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));
    goldilocks_t* data_cached = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));
    goldilocks_t* data_unrolled = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));
    goldilocks_t* initial = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));

    /* Initialize */
    for (size_t i = 0; i < n; i++) {
        initial[i] = (i + 1) % GOLDILOCKS_P;
    }

    goldilocks_t omega = GOLDILOCKS_TWO_ADIC_ROOTS[log_n];
    NttContext* ctx = ntt_context_create(log_n);

    /* Benchmark original (recomputes twiddles) */
    double start = get_time_ms();
    for (size_t iter = 0; iter < iterations; iter++) {
        memcpy(data_orig, initial, n * sizeof(goldilocks_t));
        ntt_forward_original(data_orig, n, omega);
    }
    double time_orig = get_time_ms() - start;

    /* Benchmark cached WITHOUT unrolling */
    start = get_time_ms();
    for (size_t iter = 0; iter < iterations; iter++) {
        memcpy(data_cached, initial, n * sizeof(goldilocks_t));
        ntt_forward_cached_no_unroll(ctx, data_cached);
    }
    double time_cached = get_time_ms() - start;

    /* Benchmark cached WITH unrolling */
    start = get_time_ms();
    for (size_t iter = 0; iter < iterations; iter++) {
        memcpy(data_unrolled, initial, n * sizeof(goldilocks_t));
        ntt_forward_cached_unrolled(ctx, data_unrolled);
    }
    double time_unrolled = get_time_ms() - start;

    /* Verify all results match */
    int match_cached = 1, match_unrolled = 1;
    for (size_t i = 0; i < n; i++) {
        if (data_orig[i] != data_cached[i]) { match_cached = 0; }
        if (data_orig[i] != data_unrolled[i]) { match_unrolled = 0; }
    }

    double us_orig = time_orig * 1000.0 / iterations;
    double us_cached = time_cached * 1000.0 / iterations;
    double us_unrolled = time_unrolled * 1000.0 / iterations;

    double speedup_cached = time_orig / time_cached;
    double speedup_unrolled = time_orig / time_unrolled;
    double unroll_gain = (time_cached - time_unrolled) / time_cached * 100.0;

    printf("N=2^%-2zu: orig=%7.1f us, cached=%7.1f us (%.2fx), unrolled=%7.1f us (%.2fx) [+%.1f%%] %s\n",
           log_n, us_orig, us_cached, speedup_cached, us_unrolled, speedup_unrolled,
           unroll_gain,
           (match_cached && match_unrolled) ? "[OK]" : "[MISMATCH!]");

    ntt_context_destroy(ctx);
    free(data_orig);
    free(data_cached);
    free(data_unrolled);
    free(initial);
}

int main(void) {
    printf("╔════════════════════════════════════════════════════════════════════════════════╗\n");
    printf("║  NTT Loop Unrolling Benchmark - Phase 6B.1.6 (ADR-6B-006)                      ║\n");
    printf("╚════════════════════════════════════════════════════════════════════════════════╝\n\n");

    printf("Comparing: Original (no cache) vs Cached vs Cached+Unrolled x4\n\n");

    /* Warmup */
    printf("Warming up...\n");
    goldilocks_t warmup[256];
    for (int i = 0; i < 256; i++) warmup[i] = i;
    NttContext* ctx = ntt_context_create(8);
    for (int i = 0; i < 100; i++) {
        ntt_forward_cached_unrolled(ctx, warmup);
    }
    ntt_context_destroy(ctx);

    printf("\nResults:\n");
    printf("──────────────────────────────────────────────────────────────────────────────────\n");
    printf("Size      Original      Cached (speedup)    Unrolled (speedup) [unroll gain]\n");
    printf("──────────────────────────────────────────────────────────────────────────────────\n");

    /* Test various sizes */
    benchmark_size(8, 10000);   /* N=256 */
    benchmark_size(10, 5000);   /* N=1024 */
    benchmark_size(12, 1000);   /* N=4096 */
    benchmark_size(14, 200);    /* N=16384 */
    benchmark_size(16, 50);     /* N=65536 */
    benchmark_size(18, 10);     /* N=262144 */

    printf("──────────────────────────────────────────────────────────────────────────────────\n");
    printf("\nExpected: +10-15%% from x4 loop unrolling (ADR-6B-006)\n");
    printf("Legend:\n");
    printf("  - Original: recomputes all twiddles each call\n");
    printf("  - Cached:   reuses precomputed twiddles (no unrolling)\n");
    printf("  - Unrolled: cached twiddles + x4 loop unrolling for ILP\n");

    return 0;
}
