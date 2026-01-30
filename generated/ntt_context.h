/**
 * ntt_context.h - NTT Context with Intelligent Twiddle Caching
 *
 * AMO-Lean Phase 6B: Twiddle Caching Optimization
 *
 * Design Decision ADR-6B-002: Partial Twiddle Caching
 *   - Cache first CACHED_LAYERS layers (~16KB, fits in L1)
 *   - Compute remaining layers on-the-fly
 *   - Prevents cache thrashing for large N (2^18)
 *
 * Rationale:
 *   - Early layers access twiddles sequentially -> benefit from cache
 *   - Late layers access with exponentially growing stride -> cache misses anyway
 *   - Computing a twiddle is cheap: one modular multiplication
 */

#ifndef NTT_CONTEXT_H
#define NTT_CONTEXT_H

#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "field_goldilocks.h"

/*===========================================================================
 * Configuration
 *===========================================================================*/

/**
 * Maximum number of layers to cache twiddles for.
 *
 * After benchmarking (Phase 6B.1.4), we found that partial caching
 * is SLOWER for large N because on-the-fly computation adds overhead.
 *
 * Options:
 *   - NTT_CACHE_MODE_PARTIAL (11 layers, ~16KB) - original QA recommendation
 *   - NTT_CACHE_MODE_FULL (all layers) - better performance, more memory
 *
 * Benchmark results showed:
 *   - N≤1024: partial caching is 9-14% faster
 *   - N≥16384: partial caching is 8-15% SLOWER
 *
 * Conclusion: Use FULL caching by default for performance.
 * The cache thrashing concern is less important than computation overhead.
 */

/* Cache mode: 0 = partial (16KB), 1 = full (all twiddles) */
#ifndef NTT_CACHE_MODE_FULL
#define NTT_CACHE_MODE_FULL 1
#endif

#if NTT_CACHE_MODE_FULL
#define NTT_CACHED_LAYERS 32  /* Effectively unlimited - will be capped by log_n */
#else
#define NTT_CACHED_LAYERS 11  /* ~16KB max */
#endif

/**
 * Maximum twiddles to cache (for layers 0 to CACHED_LAYERS-1)
 * This is sum of 2^0 + 2^1 + ... + 2^(CACHED_LAYERS-1) = 2^CACHED_LAYERS - 1
 * Plus we store them in a flat array indexed by layer, so we need 2^CACHED_LAYERS total.
 */
#define NTT_MAX_CACHED_TWIDDLES (1UL << NTT_CACHED_LAYERS)

/*===========================================================================
 * NTT Context Structure
 *===========================================================================*/

/**
 * NTT Context - holds precomputed data for a specific NTT size
 *
 * Usage:
 *   NttContext* ctx = ntt_context_create(log_n);
 *   ntt_forward_ctx(ctx, data);
 *   ntt_inverse_ctx(ctx, data);
 *   ntt_context_destroy(ctx);
 */
typedef struct {
    /* NTT parameters */
    size_t log_n;               /* log2 of NTT size */
    size_t n;                   /* NTT size = 2^log_n */

    /* Primitive roots */
    goldilocks_t omega;         /* Primitive n-th root of unity */
    goldilocks_t omega_inv;     /* omega^(-1) for inverse NTT */
    goldilocks_t n_inv;         /* 1/n for inverse NTT normalization */

    /* Twiddle caching strategy */
    size_t cached_layers;       /* Number of layers with cached twiddles */

    /**
     * Cached twiddles organized by layer.
     *
     * For layer L (0-indexed), the twiddle factors are:
     *   omega^(k * n / 2^(L+1)) for k = 0, 1, ..., 2^L - 1
     *
     * We store them in a flat array where layer L starts at index 2^L - 1:
     *   Layer 0: index 0 (1 twiddle)
     *   Layer 1: index 1-2 (2 twiddles)
     *   Layer 2: index 3-6 (4 twiddles)
     *   Layer L: index 2^L - 1 to 2^(L+1) - 2
     *
     * Actually, for simplicity, we use a 2D-like layout:
     *   cached_twiddles[layer * max_per_layer + k]
     * where max_per_layer = 2^(cached_layers-1)
     *
     * Simpler approach: store twiddles for the MAXIMUM layer count,
     * and for each layer L, store 2^L twiddles starting at offset layer_offset[L].
     */
    goldilocks_t* cached_twiddles;  /* Cached twiddles array */
    size_t* layer_offsets;          /* layer_offsets[L] = start index for layer L */

    /* For on-the-fly computation of uncached layers */
    goldilocks_t* omega_powers;     /* omega^(2^k) for k = 0, 1, ..., log_n-1 */

} NttContext;

/*===========================================================================
 * Context Creation and Destruction
 *===========================================================================*/

/**
 * Get the primitive n-th root of unity for Goldilocks field.
 *
 * The Goldilocks field has order p-1 = 2^32 * (2^32 - 1), which is divisible
 * by 2^32. So primitive 2^k-th roots exist for k <= 32.
 *
 * We use the TWO_ADIC_GENERATOR approach:
 *   g = 7 is a generator of the multiplicative group
 *   omega_n = g^((p-1)/n) is a primitive n-th root
 *
 * These values are precomputed and match Plonky3/Lean.
 */
static const goldilocks_t GOLDILOCKS_TWO_ADIC_ROOTS[] = {
    /* omega for N = 2^0 = 1 */  1ULL,
    /* Values verified against Plonky3 plonky3_get_omega() */
    /* omega for N = 2^1 = 2 */   0xFFFFFFFF00000000ULL,
    /* omega for N = 2^2 = 4 */   0x0001000000000000ULL,
    /* omega for N = 2^3 = 8 */   0xFFFFFFFEFF000001ULL,
    /* omega for N = 2^4 = 16 */  0xEFFFFFFF00000001ULL,
    /* omega for N = 2^5 = 32 */  0x00003FFFFFFFC000ULL,
    /* omega for N = 2^6 = 64 */  0x0000008000000000ULL,
    /* omega for N = 2^7 = 128 */ 0xF80007FF08000001ULL,
    /* omega for N = 2^8 = 256 */ 0xBF79143CE60CA966ULL,
    /* omega for N = 2^9 = 512 */ 0x1905D02A5C411F4EULL,
    /* omega for N = 2^10 = 1024 */ 0x9D8F2AD78BFED972ULL,
    /* omega for N = 2^11 = 2048 */ 0x0653B4801DA1C8CFULL,
    /* omega for N = 2^12 = 4096 */ 0xF2C35199959DFCB6ULL,
    /* omega for N = 2^13 = 8192 */ 0x1544EF2335D17997ULL,
    /* omega for N = 2^14 = 16384 */ 0xE0EE099310BBA1E2ULL,
    /* omega for N = 2^15 = 32768 */ 0xF6B2CFFE2306BAACULL,
    /* omega for N = 2^16 = 65536 */ 0x54DF9630BF79450EULL,
    /* omega for N = 2^17 = 131072 */ 0xABD0A6E8AA3D8A0EULL,
    /* omega for N = 2^18 = 262144 */ 0x81281A7B05F9BEACULL,
    /* omega for N = 2^19 = 524288 */ 0xCA25B9AB3C316FB6ULL,  /* TODO: verify */
    /* omega for N = 2^20 = 1048576 */ 0x1D094B0FFF3B314AULL, /* TODO: verify */
};

#define GOLDILOCKS_MAX_LOG_N 20  /* Support up to N = 2^20 = 1M elements */

/* goldilocks_inv is already defined in field_goldilocks.h */

/**
 * Create an NTT context for transforms of size 2^log_n.
 *
 * @param log_n Log base 2 of NTT size (1 <= log_n <= GOLDILOCKS_MAX_LOG_N)
 * @return Allocated context, or NULL on error. Caller must free with ntt_context_destroy.
 */
static inline NttContext* ntt_context_create(size_t log_n) {
    if (log_n < 1 || log_n > GOLDILOCKS_MAX_LOG_N) {
        return NULL;
    }

    NttContext* ctx = (NttContext*)calloc(1, sizeof(NttContext));
    if (!ctx) return NULL;

    ctx->log_n = log_n;
    ctx->n = 1UL << log_n;

    /* Get primitive root from table */
    ctx->omega = GOLDILOCKS_TWO_ADIC_ROOTS[log_n];
    ctx->omega_inv = goldilocks_pow(ctx->omega, ctx->n - 1);  /* omega^(n-1) = omega^(-1) */
    ctx->n_inv = goldilocks_inv(ctx->n);

    /* Determine how many layers to cache */
    ctx->cached_layers = (log_n < NTT_CACHED_LAYERS) ? log_n : NTT_CACHED_LAYERS;

    /* Allocate layer offsets */
    ctx->layer_offsets = (size_t*)malloc((ctx->cached_layers + 1) * sizeof(size_t));
    if (!ctx->layer_offsets) {
        free(ctx);
        return NULL;
    }

    /* Compute layer offsets and total cached twiddles needed */
    size_t total_cached = 0;
    for (size_t layer = 0; layer < ctx->cached_layers; layer++) {
        ctx->layer_offsets[layer] = total_cached;
        total_cached += (1UL << layer);  /* Layer L needs 2^L twiddles */
    }
    ctx->layer_offsets[ctx->cached_layers] = total_cached;  /* Sentinel */

    /* Allocate and compute cached twiddles */
    ctx->cached_twiddles = (goldilocks_t*)malloc(total_cached * sizeof(goldilocks_t));
    if (!ctx->cached_twiddles) {
        free(ctx->layer_offsets);
        free(ctx);
        return NULL;
    }

    /* Precompute twiddles for each cached layer */
    for (size_t layer = 0; layer < ctx->cached_layers; layer++) {
        size_t m = 1UL << (layer + 1);           /* Butterfly group size */
        size_t half_m = m / 2;                   /* Twiddles needed for this layer */
        size_t twiddle_step = ctx->n / m;       /* Step in full twiddle array */

        goldilocks_t* layer_twiddles = ctx->cached_twiddles + ctx->layer_offsets[layer];

        /* omega_m = omega^(n/m) = omega^twiddle_step */
        goldilocks_t omega_m = goldilocks_pow(ctx->omega, twiddle_step);

        /* Compute omega_m^k for k = 0, 1, ..., half_m - 1 */
        layer_twiddles[0] = 1;
        for (size_t k = 1; k < half_m; k++) {
            layer_twiddles[k] = goldilocks_mul(layer_twiddles[k - 1], omega_m);
        }
    }

    /* Precompute omega powers for on-the-fly computation */
    ctx->omega_powers = (goldilocks_t*)malloc(log_n * sizeof(goldilocks_t));
    if (!ctx->omega_powers) {
        free(ctx->cached_twiddles);
        free(ctx->layer_offsets);
        free(ctx);
        return NULL;
    }

    /* omega_powers[k] = omega^(n / 2^(k+1)) = omega^(2^(log_n - k - 1)) */
    for (size_t k = 0; k < log_n; k++) {
        size_t exp = 1UL << (log_n - k - 1);
        ctx->omega_powers[k] = goldilocks_pow(ctx->omega, exp);
    }

    return ctx;
}

/**
 * Destroy an NTT context and free all resources.
 */
static inline void ntt_context_destroy(NttContext* ctx) {
    if (ctx) {
        free(ctx->omega_powers);
        free(ctx->cached_twiddles);
        free(ctx->layer_offsets);
        free(ctx);
    }
}

/*===========================================================================
 * Twiddle Access Functions
 *===========================================================================*/

/**
 * Get twiddle factor for a specific layer and index.
 *
 * For cached layers: direct lookup
 * For uncached layers: compute on-the-fly
 *
 * @param ctx NTT context
 * @param layer Layer index (0-indexed)
 * @param k Butterfly index within layer (0 <= k < 2^layer)
 * @return Twiddle factor omega^(k * n / 2^(layer+1))
 */
static inline goldilocks_t ntt_get_twiddle(const NttContext* ctx, size_t layer, size_t k) {
    if (layer < ctx->cached_layers) {
        /* Cached: direct lookup */
        return ctx->cached_twiddles[ctx->layer_offsets[layer] + k];
    } else {
        /* Uncached: compute on-the-fly */
        /* omega_layer = omega^(n / 2^(layer+1)) */
        goldilocks_t omega_layer = ctx->omega_powers[layer];
        /* Return omega_layer^k */
        return goldilocks_pow(omega_layer, k);
    }
}

/**
 * Get the base twiddle factor (omega_m) for a layer.
 * This is omega^(n / 2^(layer+1)).
 *
 * Useful for computing twiddles incrementally in a layer.
 */
static inline goldilocks_t ntt_get_layer_omega(const NttContext* ctx, size_t layer) {
    return ctx->omega_powers[layer];
}

/*===========================================================================
 * Context Information
 *===========================================================================*/

/**
 * Get the number of cached twiddles (for diagnostics).
 */
static inline size_t ntt_context_cached_count(const NttContext* ctx) {
    return ctx->layer_offsets[ctx->cached_layers];
}

/**
 * Get the memory usage of cached twiddles in bytes.
 */
static inline size_t ntt_context_cache_bytes(const NttContext* ctx) {
    return ntt_context_cached_count(ctx) * sizeof(goldilocks_t);
}

/**
 * Print context information (for debugging).
 */
#ifdef NTT_CONTEXT_DEBUG
#include <stdio.h>
static inline void ntt_context_print(const NttContext* ctx) {
    printf("NttContext:\n");
    printf("  log_n = %zu, n = %zu\n", ctx->log_n, ctx->n);
    printf("  omega = 0x%016llx\n", (unsigned long long)ctx->omega);
    printf("  omega_inv = 0x%016llx\n", (unsigned long long)ctx->omega_inv);
    printf("  n_inv = 0x%016llx\n", (unsigned long long)ctx->n_inv);
    printf("  cached_layers = %zu / %zu\n", ctx->cached_layers, ctx->log_n);
    printf("  cached_twiddles = %zu (%zu bytes)\n",
           ntt_context_cached_count(ctx), ntt_context_cache_bytes(ctx));
}
#endif

#endif /* NTT_CONTEXT_H */
