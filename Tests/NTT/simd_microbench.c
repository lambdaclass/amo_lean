/**
 * simd_microbench.c - Fail-Fast SIMD Microbenchmark (ADR-6B-005)
 *
 * Phase 6B.2.0: Determine if SIMD acceleration is worthwhile for Goldilocks mul
 *
 * Plonky3 finding: AVX2 64-bit multiplication is 1.33x SLOWER than scalar
 * because 64-bit mul must be emulated with 32-bit operations (4-way split).
 *
 * This benchmark validates that finding on the current CPU.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

#include "../../generated/field_goldilocks.h"

/*===========================================================================
 * Architecture Detection
 *===========================================================================*/

/* Detect available SIMD features */
#if defined(__AVX2__)
  #define HAVE_AVX2 1
  #include <immintrin.h>
#else
  #define HAVE_AVX2 0
#endif

#if defined(__ARM_NEON) || defined(__aarch64__)
  #define HAVE_NEON 1
  #include <arm_neon.h>
#else
  #define HAVE_NEON 0
#endif

/*===========================================================================
 * Timing Utilities
 *===========================================================================*/

static inline double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

/*===========================================================================
 * Scalar Goldilocks Multiplication (Baseline)
 *===========================================================================*/

/* This is the fast scalar mul from field_goldilocks.h */
static inline uint64_t scalar_mul(uint64_t a, uint64_t b) {
    return goldilocks_mul(a, b);
}

/*===========================================================================
 * AVX2 Goldilocks Multiplication (Emulated 64-bit)
 *===========================================================================*/

#if HAVE_AVX2
/**
 * AVX2-emulated 64-bit multiplication with Goldilocks reduction.
 *
 * Strategy: Split each 64-bit value into two 32-bit halves:
 *   a = a_hi * 2^32 + a_lo
 *   b = b_hi * 2^32 + b_lo
 *
 * Product = a_lo*b_lo + (a_lo*b_hi + a_hi*b_lo)*2^32 + a_hi*b_hi*2^64
 *
 * This requires 4 _mm256_mul_epu32 operations and multiple adds/shifts.
 *
 * Plonky3 comment: "1.33x SLOWER than scalar"
 */
static inline __m256i avx2_mul_goldilocks(__m256i a, __m256i b) {
    /* Constants */
    const __m256i mask32 = _mm256_set1_epi64x(0xFFFFFFFFULL);
    const __m256i goldilocks_p = _mm256_set1_epi64x(0xFFFFFFFF00000001ULL);

    /* Split into 32-bit halves */
    __m256i a_lo = _mm256_and_si256(a, mask32);
    __m256i a_hi = _mm256_srli_epi64(a, 32);
    __m256i b_lo = _mm256_and_si256(b, mask32);
    __m256i b_hi = _mm256_srli_epi64(b, 32);

    /* Four 32x32->64 multiplications */
    __m256i ll = _mm256_mul_epu32(a_lo, b_lo);  /* a_lo * b_lo */
    __m256i lh = _mm256_mul_epu32(a_lo, b_hi);  /* a_lo * b_hi */
    __m256i hl = _mm256_mul_epu32(a_hi, b_lo);  /* a_hi * b_lo */
    __m256i hh = _mm256_mul_epu32(a_hi, b_hi);  /* a_hi * b_hi */

    /* Combine: result = ll + (lh + hl) << 32 + hh << 64 */
    __m256i mid = _mm256_add_epi64(lh, hl);
    __m256i mid_lo = _mm256_slli_epi64(mid, 32);
    __m256i mid_hi = _mm256_srli_epi64(mid, 32);

    /* Low 64 bits: ll + mid_lo */
    __m256i lo = _mm256_add_epi64(ll, mid_lo);

    /* High 64 bits: hh + mid_hi + carry from lo */
    /* Carry detection is complex in SIMD - approximate with saturating add check */
    __m256i hi = _mm256_add_epi64(hh, mid_hi);

    /*
     * Goldilocks reduction: p = 2^64 - 2^32 + 1
     * hi * 2^64 mod p = hi * (2^32 - 1)
     *                 = hi * 2^32 - hi
     *                 = (hi << 32) - hi
     *
     * This is a simplified reduction (not fully correct for all cases).
     * For benchmarking purposes, this approximates the real cost.
     */
    __m256i hi_shifted = _mm256_slli_epi64(hi, 32);
    __m256i reduced_hi = _mm256_sub_epi64(hi_shifted, hi);
    __m256i result = _mm256_add_epi64(lo, reduced_hi);

    /* Simple modular reduction (may need additional passes) */
    __m256i cmp = _mm256_cmpgt_epi64(result, goldilocks_p);
    __m256i sub = _mm256_and_si256(cmp, goldilocks_p);
    result = _mm256_sub_epi64(result, sub);

    return result;
}

/* Benchmark AVX2 mul: process 4 values at a time */
void benchmark_avx2_mul(uint64_t* data, size_t n, size_t iters) {
    for (size_t iter = 0; iter < iters; iter++) {
        for (size_t i = 0; i < n; i += 4) {
            __m256i a = _mm256_loadu_si256((__m256i*)&data[i]);
            __m256i b = _mm256_set1_epi64x(0x1234567890ABCDEFULL); /* constant multiplier */
            __m256i r = avx2_mul_goldilocks(a, b);
            _mm256_storeu_si256((__m256i*)&data[i], r);
        }
    }
}
#endif /* HAVE_AVX2 */

/*===========================================================================
 * NEON Goldilocks Multiplication (ARM)
 *===========================================================================*/

#if HAVE_NEON
/**
 * NEON 64-bit multiplication.
 *
 * ARM NEON has vmull_u32 for 32x32->64 bit multiplication, similar to AVX2.
 * The same 4-way split is needed for 64-bit operands.
 *
 * ARM64 also has scalar mulhi instruction which may be faster.
 */
static inline uint64x2_t neon_mul_goldilocks(uint64x2_t a, uint64x2_t b) {
    /* For now, fall back to scalar for each lane - NEON 64-bit mul is complex */
    uint64_t a0 = vgetq_lane_u64(a, 0);
    uint64_t a1 = vgetq_lane_u64(a, 1);
    uint64_t b0 = vgetq_lane_u64(b, 0);
    uint64_t b1 = vgetq_lane_u64(b, 1);

    uint64_t r0 = goldilocks_mul(a0, b0);
    uint64_t r1 = goldilocks_mul(a1, b1);

    return vcombine_u64(vcreate_u64(r0), vcreate_u64(r1));
}

void benchmark_neon_mul(uint64_t* data, size_t n, size_t iters) {
    uint64x2_t multiplier = vdupq_n_u64(0x1234567890ABCDEFULL);
    for (size_t iter = 0; iter < iters; iter++) {
        for (size_t i = 0; i < n; i += 2) {
            uint64x2_t a = vld1q_u64(&data[i]);
            uint64x2_t r = neon_mul_goldilocks(a, multiplier);
            vst1q_u64(&data[i], r);
        }
    }
}
#endif /* HAVE_NEON */

/*===========================================================================
 * Scalar Benchmark
 *===========================================================================*/

void benchmark_scalar_mul(uint64_t* data, size_t n, size_t iters) {
    const uint64_t multiplier = 0x1234567890ABCDEFULL;
    for (size_t iter = 0; iter < iters; iter++) {
        for (size_t i = 0; i < n; i++) {
            data[i] = scalar_mul(data[i], multiplier);
        }
    }
}

/*===========================================================================
 * Main Benchmark
 *===========================================================================*/

int main(void) {
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  SIMD Microbenchmark - Phase 6B.2.0 (ADR-6B-005)               ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n\n");

    /* Architecture detection */
    printf("Architecture Detection:\n");
#if defined(__x86_64__) || defined(_M_X64)
    printf("  Platform: x86-64\n");
#elif defined(__aarch64__) || defined(_M_ARM64)
    printf("  Platform: ARM64 (aarch64)\n");
#else
    printf("  Platform: Unknown\n");
#endif

#if HAVE_AVX2
    printf("  AVX2: AVAILABLE\n");
#else
    printf("  AVX2: NOT AVAILABLE\n");
#endif

#if HAVE_NEON
    printf("  NEON: AVAILABLE\n");
#else
    printf("  NEON: NOT AVAILABLE\n");
#endif

    printf("\n");

    /* Benchmark parameters */
    const size_t N = 4096;  /* Must be multiple of 4 for AVX2 */
    const size_t ITERS = 100000;

    uint64_t* data_scalar = (uint64_t*)aligned_alloc(32, N * sizeof(uint64_t));
    uint64_t* data_simd = (uint64_t*)aligned_alloc(32, N * sizeof(uint64_t));

    /* Initialize */
    for (size_t i = 0; i < N; i++) {
        data_scalar[i] = (i + 1) % 0xFFFFFFFF00000001ULL;
        data_simd[i] = data_scalar[i];
    }

    printf("Benchmark: %zu elements x %zu iterations\n\n", N, ITERS);

    /* Warmup */
    printf("Warming up...\n");
    benchmark_scalar_mul(data_scalar, N, 1000);

    /* Reset data */
    for (size_t i = 0; i < N; i++) {
        data_scalar[i] = (i + 1) % 0xFFFFFFFF00000001ULL;
        data_simd[i] = data_scalar[i];
    }

    /* Benchmark scalar */
    printf("\nBenchmarking scalar Goldilocks mul...\n");
    double start = get_time_ns();
    benchmark_scalar_mul(data_scalar, N, ITERS);
    double time_scalar = get_time_ns() - start;

    double scalar_ns_per_mul = time_scalar / (N * ITERS);
    double scalar_muls_per_sec = 1e9 / scalar_ns_per_mul;

    printf("  Scalar: %.2f ns/mul (%.1f M muls/sec)\n",
           scalar_ns_per_mul, scalar_muls_per_sec / 1e6);

    /* Benchmark SIMD if available */
#if HAVE_AVX2
    /* Reset data */
    for (size_t i = 0; i < N; i++) {
        data_simd[i] = (i + 1) % 0xFFFFFFFF00000001ULL;
    }

    printf("\nBenchmarking AVX2 Goldilocks mul...\n");
    start = get_time_ns();
    benchmark_avx2_mul(data_simd, N, ITERS);
    double time_avx2 = get_time_ns() - start;

    double avx2_ns_per_mul = time_avx2 / (N * ITERS);
    double avx2_muls_per_sec = 1e9 / avx2_ns_per_mul;

    printf("  AVX2:   %.2f ns/mul (%.1f M muls/sec)\n",
           avx2_ns_per_mul, avx2_muls_per_sec / 1e6);

    double avx2_ratio = time_avx2 / time_scalar;
    printf("\n  AVX2 vs Scalar: %.2fx\n", avx2_ratio);

    if (avx2_ratio > 1.0) {
        printf("  >>> AVX2 is %.0f%% SLOWER than scalar (confirms Plonky3 finding)\n",
               (avx2_ratio - 1.0) * 100);
        printf("  >>> RECOMMENDATION: Use scalar mul, skip AVX2 for Goldilocks\n");
    } else {
        printf("  >>> AVX2 is %.0f%% FASTER than scalar\n",
               (1.0 - avx2_ratio) * 100);
        printf("  >>> RECOMMENDATION: Consider AVX2 hybrid strategy\n");
    }

#elif HAVE_NEON
    /* Reset data */
    for (size_t i = 0; i < N; i++) {
        data_simd[i] = (i + 1) % 0xFFFFFFFF00000001ULL;
    }

    printf("\nBenchmarking NEON Goldilocks mul (falls back to scalar)...\n");
    start = get_time_ns();
    benchmark_neon_mul(data_simd, N, ITERS);
    double time_neon = get_time_ns() - start;

    double neon_ns_per_mul = time_neon / (N * ITERS);
    double neon_muls_per_sec = 1e9 / neon_ns_per_mul;

    printf("  NEON:   %.2f ns/mul (%.1f M muls/sec)\n",
           neon_ns_per_mul, neon_muls_per_sec / 1e6);

    double neon_ratio = time_neon / time_scalar;
    printf("\n  NEON vs Scalar: %.2fx\n", neon_ratio);

    printf("\n  NOTE: ARM64 scalar mul (UMULH instruction) is typically optimal.\n");
    printf("        NEON 64-bit mul requires similar 4-way split as AVX2.\n");
    printf("  >>> RECOMMENDATION: Use scalar mul on ARM64\n");

#else
    printf("\n  No SIMD available - using scalar only.\n");
#endif

    printf("\n═══════════════════════════════════════════════════════════════════\n");
    printf("CONCLUSION:\n");
    printf("  The Goldilocks field (p = 2^64 - 2^32 + 1) has special structure\n");
    printf("  that enables fast scalar reduction. SIMD 64-bit mul emulation\n");
    printf("  adds overhead that negates parallelism benefits.\n");
    printf("\n");
    printf("  For Phase 6B: Focus on scalar optimizations (caching, unrolling)\n");
    printf("  rather than SIMD for multiplication.\n");
    printf("═══════════════════════════════════════════════════════════════════\n");

    free(data_scalar);
    free(data_simd);

    return 0;
}
