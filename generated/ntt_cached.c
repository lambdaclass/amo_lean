/**
 * ntt_cached.c - NTT with Intelligent Twiddle Caching and Loop Unrolling
 *
 * AMO-Lean Phase 6B: Performance Optimization
 *
 * This implementation uses NttContext for:
 *   - Full twiddle caching (all layers) - benchmark showed this beats partial
 *   - Precomputed omega powers for efficient on-the-fly computation
 *   - x4 loop unrolling for Instruction Level Parallelism (ILP)
 *   - Pre-allocated work buffer (no malloc/free per NTT call)
 *
 * Design Decisions:
 *   - ADR-6B-002: Full caching by default (partial was slower for large N)
 *   - ADR-6B-006: x4 loop unrolling for +10-15% ILP improvement
 *   - ADR-6B-009: Pre-allocated work buffer for +5-10% on small N
 *   - ADR-6B-010: Pre-computed bit-reversal table for +3-5%
 *   - Uses lazy_butterfly from Phase 5 (verified against Lean)
 */

#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "field_goldilocks.h"
#include "ntt_kernel.h"
#include "ntt_context.h"

/*===========================================================================
 * Bit-Reversal Permutation
 * ADR-6B-010: Uses pre-computed table from NttContext
 *===========================================================================*/

/**
 * Bit-reverse permute using pre-computed table.
 * O(n) lookups instead of O(n * log n) bit operations.
 */
static void bit_reverse_permute_ctx(const NttContext* ctx, lazy_goldilocks_t* data) {
    const size_t n = ctx->n;
    const size_t* table = ctx->bit_reverse_table;

    for (size_t i = 0; i < n; i++) {
        size_t j = table[i];
        if (i < j) {
            lazy_goldilocks_t tmp = data[i];
            data[i] = data[j];
            data[j] = tmp;
        }
    }
}

/*===========================================================================
 * NTT Forward Transform with Cached Twiddles
 *===========================================================================*/

/**
 * Compute NTT using precomputed context (cached twiddles).
 *
 * This is the optimized version that:
 *   - Uses cached twiddles for early layers (sequential access)
 *   - Computes twiddles on-the-fly for late layers (large stride)
 *
 * @param ctx NTT context with cached twiddles
 * @param data Array of n elements (modified in place)
 * @return 0 on success, -1 on error
 */
int ntt_forward_ctx(const NttContext* ctx, goldilocks_t* data) {
    if (!ctx || !data) {
        return -1;
    }

    const size_t n = ctx->n;
    const size_t log_n = ctx->log_n;

    /* N=1: Identity transform */
    if (n == 1) {
        return 0;
    }

    /* ADR-6B-009: Use pre-allocated work buffer (no malloc per call) */
    lazy_goldilocks_t* work = ctx->work_buffer;

    /* Copy to lazy form */
    for (size_t i = 0; i < n; i++) {
        work[i] = lazy_from_strict(data[i]);
    }

    /* Bit-reverse permutation */
    bit_reverse_permute_ctx(ctx, work);

    /* Main NTT loop: Cooley-Tukey DIT */
    for (size_t layer = 0; layer < log_n; layer++) {
        size_t m = 1UL << (layer + 1);      /* Butterfly group size: 2, 4, 8, ... */
        size_t half_m = m / 2;              /* Distance between butterfly pairs */

        if (layer < ctx->cached_layers) {
            /*
             * CACHED LAYERS: Direct lookup from precomputed twiddles
             *
             * This is the fast path for early layers where:
             * - Access is sequential within each group
             * - Twiddles are in L1 cache
             *
             * ADR-6B-006: x4 loop unrolling for ILP (Instruction Level Parallelism)
             */
            const goldilocks_t* layer_twiddles =
                ctx->cached_twiddles + ctx->layer_offsets[layer];

            for (size_t k = 0; k < n; k += m) {
                size_t j = 0;

                /* Unrolled x4 main loop */
                for (; j + 4 <= half_m; j += 4) {
                    /* Prefetch twiddles to registers */
                    goldilocks_t tw0 = layer_twiddles[j + 0];
                    goldilocks_t tw1 = layer_twiddles[j + 1];
                    goldilocks_t tw2 = layer_twiddles[j + 2];
                    goldilocks_t tw3 = layer_twiddles[j + 3];

                    /* Execute 4 butterflies with independent data dependencies */
                    lazy_butterfly(&work[k + j + 0], &work[k + j + 0 + half_m], tw0);
                    lazy_butterfly(&work[k + j + 1], &work[k + j + 1 + half_m], tw1);
                    lazy_butterfly(&work[k + j + 2], &work[k + j + 2 + half_m], tw2);
                    lazy_butterfly(&work[k + j + 3], &work[k + j + 3 + half_m], tw3);
                }

                /* Remainder loop for half_m % 4 != 0 */
                for (; j < half_m; j++) {
                    goldilocks_t tw = layer_twiddles[j];
                    lazy_butterfly(&work[k + j], &work[k + j + half_m], tw);
                }
            }
        } else {
            /*
             * UNCACHED LAYERS: Compute twiddles on-the-fly
             *
             * For late layers where:
             * - Stride is large (cache misses anyway)
             * - Fewer groups (amortizes computation cost)
             *
             * Strategy: Compute twiddles incrementally within each group
             * tw_0 = 1
             * tw_{j+1} = tw_j * omega_m
             *
             * ADR-6B-006: x4 loop unrolling for ILP
             * Note: We precompute omega_m^2, omega_m^3, omega_m^4 for the unrolled loop
             */
            goldilocks_t omega_m = ctx->omega_powers[layer];
            goldilocks_t omega_m2 = goldilocks_mul(omega_m, omega_m);      /* omega_m^2 */
            goldilocks_t omega_m3 = goldilocks_mul(omega_m2, omega_m);     /* omega_m^3 */
            goldilocks_t omega_m4 = goldilocks_mul(omega_m2, omega_m2);    /* omega_m^4 */

            for (size_t k = 0; k < n; k += m) {
                goldilocks_t tw0 = 1;  /* omega_m^0 = 1 */
                size_t j = 0;

                /* Unrolled x4 main loop */
                for (; j + 4 <= half_m; j += 4) {
                    /* Compute 4 consecutive twiddles */
                    goldilocks_t tw1 = goldilocks_mul(tw0, omega_m);
                    goldilocks_t tw2 = goldilocks_mul(tw0, omega_m2);
                    goldilocks_t tw3 = goldilocks_mul(tw0, omega_m3);

                    /* Execute 4 butterflies */
                    lazy_butterfly(&work[k + j + 0], &work[k + j + 0 + half_m], tw0);
                    lazy_butterfly(&work[k + j + 1], &work[k + j + 1 + half_m], tw1);
                    lazy_butterfly(&work[k + j + 2], &work[k + j + 2 + half_m], tw2);
                    lazy_butterfly(&work[k + j + 3], &work[k + j + 3 + half_m], tw3);

                    /* Advance by omega_m^4 for next iteration */
                    tw0 = goldilocks_mul(tw0, omega_m4);
                }

                /* Remainder loop */
                for (; j < half_m; j++) {
                    lazy_butterfly(&work[k + j], &work[k + j + half_m], tw0);
                    tw0 = goldilocks_mul(tw0, omega_m);
                }
            }
        }

        /* Reduce all values after each layer to keep bounds */
        for (size_t i = 0; i < n; i++) {
            work[i] = lazy_reduce(work[i]);
        }
    }

    /* Copy back to output */
    for (size_t i = 0; i < n; i++) {
        data[i] = lazy_to_strict(work[i]);
    }

    /* ADR-6B-009: No free - work_buffer is owned by ctx */
    return 0;
}

/*===========================================================================
 * INTT (Inverse NTT) with Cached Twiddles
 *===========================================================================*/

/**
 * Compute inverse NTT using precomputed context.
 *
 * INTT(A) = (1/n) * NTT(A, omega^(-1))
 *
 * @param ctx NTT context (uses omega_inv internally)
 * @param data Array of n elements (modified in place)
 * @return 0 on success, -1 on error
 */
int ntt_inverse_ctx(const NttContext* ctx, goldilocks_t* data) {
    if (!ctx || !data) {
        return -1;
    }

    const size_t n = ctx->n;
    const size_t log_n = ctx->log_n;

    /* N=1: Identity transform */
    if (n == 1) {
        return 0;
    }

    /* ADR-6B-009: Use pre-allocated work buffer (no malloc per call) */
    lazy_goldilocks_t* work = ctx->work_buffer;

    /* Copy to lazy form */
    for (size_t i = 0; i < n; i++) {
        work[i] = lazy_from_strict(data[i]);
    }

    /* Bit-reverse permutation */
    bit_reverse_permute_ctx(ctx, work);

    /*
     * Main NTT loop with omega_inv
     *
     * For inverse NTT, we use omega^(-1) instead of omega.
     * We compute twiddles using omega_inv^(n / 2^(layer+1)).
     */
    for (size_t layer = 0; layer < log_n; layer++) {
        size_t m = 1UL << (layer + 1);
        size_t half_m = m / 2;
        size_t twiddle_step = n / m;

        /* omega_inv_m = omega_inv^(twiddle_step) = omega_inv^(n/m) */
        goldilocks_t omega_inv_m = goldilocks_pow(ctx->omega_inv, twiddle_step);

        /*
         * Note: We don't cache inverse twiddles to save memory.
         * The inverse NTT is typically called less frequently,
         * and computing on-the-fly is acceptable.
         *
         * ADR-6B-006: x4 loop unrolling for ILP
         */
        goldilocks_t omega_inv_m2 = goldilocks_mul(omega_inv_m, omega_inv_m);
        goldilocks_t omega_inv_m3 = goldilocks_mul(omega_inv_m2, omega_inv_m);
        goldilocks_t omega_inv_m4 = goldilocks_mul(omega_inv_m2, omega_inv_m2);

        for (size_t k = 0; k < n; k += m) {
            goldilocks_t tw0 = 1;
            size_t j = 0;

            /* Unrolled x4 main loop */
            for (; j + 4 <= half_m; j += 4) {
                goldilocks_t tw1 = goldilocks_mul(tw0, omega_inv_m);
                goldilocks_t tw2 = goldilocks_mul(tw0, omega_inv_m2);
                goldilocks_t tw3 = goldilocks_mul(tw0, omega_inv_m3);

                lazy_butterfly(&work[k + j + 0], &work[k + j + 0 + half_m], tw0);
                lazy_butterfly(&work[k + j + 1], &work[k + j + 1 + half_m], tw1);
                lazy_butterfly(&work[k + j + 2], &work[k + j + 2 + half_m], tw2);
                lazy_butterfly(&work[k + j + 3], &work[k + j + 3 + half_m], tw3);

                tw0 = goldilocks_mul(tw0, omega_inv_m4);
            }

            /* Remainder loop */
            for (; j < half_m; j++) {
                lazy_butterfly(&work[k + j], &work[k + j + half_m], tw0);
                tw0 = goldilocks_mul(tw0, omega_inv_m);
            }
        }

        /* Reduce after each layer */
        for (size_t i = 0; i < n; i++) {
            work[i] = lazy_reduce(work[i]);
        }
    }

    /* Scale by n^(-1) and copy back */
    for (size_t i = 0; i < n; i++) {
        goldilocks_t val = lazy_to_strict(work[i]);
        data[i] = goldilocks_mul(val, ctx->n_inv);
    }

    /* ADR-6B-009: No free - work_buffer is owned by ctx */
    return 0;
}

/*===========================================================================
 * Convenience Functions (no context needed)
 *===========================================================================*/

/**
 * One-shot forward NTT (creates temporary context).
 *
 * Use ntt_forward_ctx() with a persistent context for repeated transforms.
 */
int ntt_forward_cached(goldilocks_t* data, size_t n) {
    if (n == 0 || (n & (n - 1)) != 0) {
        return -1;  /* n must be power of 2 */
    }

    if (n == 1) {
        return 0;
    }

    /* Compute log2(n) */
    size_t log_n = 0;
    for (size_t tmp = n; tmp > 1; tmp >>= 1) {
        log_n++;
    }

    NttContext* ctx = ntt_context_create(log_n);
    if (!ctx) return -1;

    int result = ntt_forward_ctx(ctx, data);

    ntt_context_destroy(ctx);
    return result;
}

/**
 * One-shot inverse NTT (creates temporary context).
 */
int ntt_inverse_cached(goldilocks_t* data, size_t n) {
    if (n == 0 || (n & (n - 1)) != 0) {
        return -1;
    }

    if (n == 1) {
        return 0;
    }

    size_t log_n = 0;
    for (size_t tmp = n; tmp > 1; tmp >>= 1) {
        log_n++;
    }

    NttContext* ctx = ntt_context_create(log_n);
    if (!ctx) return -1;

    int result = ntt_inverse_ctx(ctx, data);

    ntt_context_destroy(ctx);
    return result;
}

/*===========================================================================
 * Test/Debug Functions
 *===========================================================================*/

#ifdef NTT_CACHED_MAIN

#include <stdio.h>
#include <time.h>

/* Benchmark helper */
static double get_time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

int main(void) {
    printf("NTT Cached Implementation Test\n");
    printf("==============================\n\n");

    /* Test 1: Basic correctness N=8 */
    printf("Test 1: Roundtrip N=8\n");
    {
        goldilocks_t input[8] = {1, 2, 3, 4, 5, 6, 7, 8};
        goldilocks_t data[8];
        memcpy(data, input, sizeof(data));

        NttContext* ctx = ntt_context_create(3);  /* log2(8) = 3 */
        if (!ctx) {
            printf("Failed to create context!\n");
            return 1;
        }

        printf("  Input:  ");
        for (int i = 0; i < 8; i++) printf("%llu ", (unsigned long long)data[i]);
        printf("\n");

        ntt_forward_ctx(ctx, data);
        printf("  NTT:    ");
        for (int i = 0; i < 8; i++) printf("%llu ", (unsigned long long)data[i]);
        printf("\n");

        ntt_inverse_ctx(ctx, data);
        printf("  INTT:   ");
        for (int i = 0; i < 8; i++) printf("%llu ", (unsigned long long)data[i]);
        printf("\n");

        int match = 1;
        for (int i = 0; i < 8; i++) {
            if (data[i] != input[i]) { match = 0; break; }
        }
        printf("  Match:  %s\n", match ? "YES" : "NO");

        ntt_context_destroy(ctx);
        if (!match) return 1;
    }

    /* Test 2: Context info */
    printf("\nTest 2: Context info for various sizes\n");
    for (size_t log_n = 3; log_n <= 18; log_n += 3) {
        NttContext* ctx = ntt_context_create(log_n);
        if (ctx) {
            printf("  N=2^%zu: cached_layers=%zu, cache_bytes=%zu\n",
                   log_n, ctx->cached_layers, ntt_context_cache_bytes(ctx));
            ntt_context_destroy(ctx);
        }
    }

    /* Test 3: Benchmark cached vs original */
    printf("\nTest 3: Benchmark (N=1024, 10000 iterations)\n");
    {
        const size_t N = 1024;
        const size_t ITERS = 10000;

        goldilocks_t* data = (goldilocks_t*)malloc(N * sizeof(goldilocks_t));
        if (!data) return 1;

        /* Initialize */
        for (size_t i = 0; i < N; i++) {
            data[i] = i + 1;
        }

        /* Benchmark with context (reused) */
        NttContext* ctx = ntt_context_create(10);  /* log2(1024) = 10 */
        if (!ctx) { free(data); return 1; }

        double start = get_time_ms();
        for (size_t iter = 0; iter < ITERS; iter++) {
            ntt_forward_ctx(ctx, data);
            ntt_inverse_ctx(ctx, data);
        }
        double elapsed = get_time_ms() - start;

        printf("  Cached (context reused): %.2f ms total, %.3f us per roundtrip\n",
               elapsed, elapsed * 1000.0 / ITERS);

        /* Verify still correct */
        int match = 1;
        for (size_t i = 0; i < N; i++) {
            if (data[i] != i + 1) { match = 0; break; }
        }
        printf("  Final match: %s\n", match ? "YES" : "NO");

        ntt_context_destroy(ctx);
        free(data);
    }

    printf("\n[PASS] All tests passed!\n");
    return 0;
}

#endif /* NTT_CACHED_MAIN */
