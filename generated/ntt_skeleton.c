/**
 * ntt_skeleton.c - NTT Skeleton with Lazy Butterfly
 *
 * AMO-Lean Phase 5: NTT Code Generation
 *
 * This file implements the NTT loop structure (Skeleton) that calls the
 * verified lazy_butterfly kernel.
 *
 * Design Decision DD-023: Skeleton + Kernel Strategy
 *   - Skeleton (this file): Loop structure, bit-reversal, memory management
 *   - Kernel (ntt_kernel.h): lazy_butterfly verified against Lean
 *
 * Algorithm: Cooley-Tukey Decimation-in-Time (DIT) NTT
 *   1. Bit-reverse permute the input
 *   2. For each layer (log2(n) layers):
 *      - Compute twiddle factors
 *      - Apply butterflies to pairs
 *   3. Final values are in normal order
 *
 * Complexity: O(n log n) time, O(n) space
 */

#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "field_goldilocks.h"
#include "ntt_kernel.h"

/*===========================================================================
 * Bit-Reversal Permutation
 *===========================================================================*/

/**
 * Compute bit-reversed index
 *
 * @param x Index to reverse
 * @param log2_n Number of bits (log2 of array size)
 * @return Bit-reversed index
 */
static inline size_t bit_reverse(size_t x, size_t log2_n) {
    size_t result = 0;
    for (size_t i = 0; i < log2_n; i++) {
        result = (result << 1) | (x & 1);
        x >>= 1;
    }
    return result;
}

/**
 * Bit-reverse permute array in place
 *
 * @param data Array to permute
 * @param n Array size (must be power of 2)
 * @param log2_n log2(n)
 */
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

/*===========================================================================
 * Twiddle Factor Cache
 *===========================================================================*/

/**
 * Precompute twiddle factors for a given NTT size
 *
 * For NTT of size n, we need omega^k for k = 0, 1, ..., n/2-1
 * where omega is a primitive n-th root of unity.
 *
 * @param omega Primitive n-th root of unity
 * @param n NTT size (power of 2)
 * @return Array of n/2 twiddle factors, caller must free
 */
static goldilocks_t* precompute_twiddles(goldilocks_t omega, size_t n) {
    size_t half = n / 2;

    /* Edge case: n <= 1 means no twiddles needed */
    if (half == 0) {
        return NULL;  /* Caller should handle this case */
    }

    goldilocks_t* twiddles = (goldilocks_t*)malloc(half * sizeof(goldilocks_t));
    if (!twiddles) return NULL;

    /* Compute omega^k for k = 0, 1, ..., n/2-1 */
    twiddles[0] = 1;  /* omega^0 = 1 */
    for (size_t k = 1; k < half; k++) {
        twiddles[k] = goldilocks_mul(twiddles[k-1], omega);
    }

    return twiddles;
}

/*===========================================================================
 * NTT Forward Transform
 *===========================================================================*/

/**
 * Compute NTT (Number Theoretic Transform) in place
 *
 * Transforms array a of size n using primitive n-th root omega.
 * Result: A[k] = sum_{j=0}^{n-1} a[j] * omega^(jk)
 *
 * @param data Array of n elements (modified in place)
 * @param n Array size (must be power of 2)
 * @param omega Primitive n-th root of unity
 * @return 0 on success, -1 on error
 */
int ntt_forward(goldilocks_t* data, size_t n, goldilocks_t omega) {
    if (n == 0 || (n & (n - 1)) != 0) {
        return -1;  /* n must be power of 2 */
    }

    /* N=1: Identity transform, nothing to do */
    if (n == 1) {
        return 0;
    }

    /* Compute log2(n) */
    size_t log2_n = 0;
    for (size_t tmp = n; tmp > 1; tmp >>= 1) {
        log2_n++;
    }

    /* Allocate lazy working array */
    lazy_goldilocks_t* work = (lazy_goldilocks_t*)malloc(n * sizeof(lazy_goldilocks_t));
    if (!work) return -1;

    /* Copy to lazy form */
    for (size_t i = 0; i < n; i++) {
        work[i] = lazy_from_strict(data[i]);
    }

    /* Bit-reverse permutation */
    bit_reverse_permute(work, n, log2_n);

    /* Precompute all twiddle factors */
    goldilocks_t* all_twiddles = precompute_twiddles(omega, n);
    if (!all_twiddles) {
        free(work);
        return -1;
    }

    /* Main NTT loop: Cooley-Tukey DIT */
    for (size_t layer = 0; layer < log2_n; layer++) {
        size_t m = 1UL << (layer + 1);      /* Butterfly group size: 2, 4, 8, ... */
        size_t half_m = m / 2;              /* Distance between butterfly pairs */

        /* Twiddle step: n / m */
        size_t twiddle_step = n / m;

        /* For each group in this layer */
        for (size_t k = 0; k < n; k += m) {
            /* For each butterfly in the group */
            for (size_t j = 0; j < half_m; j++) {
                size_t idx_a = k + j;
                size_t idx_b = k + j + half_m;

                /* Get twiddle factor omega^(j * n/m) */
                goldilocks_t tw = all_twiddles[j * twiddle_step];

                /* Apply lazy butterfly */
                lazy_butterfly(&work[idx_a], &work[idx_b], tw);
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

    free(all_twiddles);
    free(work);
    return 0;
}

/*===========================================================================
 * INTT (Inverse NTT)
 *===========================================================================*/

/**
 * Compute inverse NTT in place
 *
 * INTT(A) = (1/n) * NTT(A) with omega^(-1)
 *
 * @param data Array of n elements (modified in place)
 * @param n Array size (must be power of 2)
 * @param omega Primitive n-th root of unity (forward direction)
 * @param n_inv Modular inverse of n
 * @return 0 on success, -1 on error
 */
int ntt_inverse(goldilocks_t* data, size_t n, goldilocks_t omega, goldilocks_t n_inv) {
    if (n == 0 || (n & (n - 1)) != 0) {
        return -1;  /* n must be power of 2 */
    }

    /* omega^(-1) = omega^(n-1) for primitive n-th root */
    goldilocks_t omega_inv = goldilocks_pow(omega, n - 1);

    /* Apply forward NTT with omega^(-1) */
    int result = ntt_forward(data, n, omega_inv);
    if (result != 0) return result;

    /* Scale by n^(-1) */
    for (size_t i = 0; i < n; i++) {
        data[i] = goldilocks_mul(data[i], n_inv);
    }

    return 0;
}

/*===========================================================================
 * Test/Debug Functions
 *===========================================================================*/

#ifdef NTT_SKELETON_MAIN

#include <stdio.h>

/* Primitive roots of unity for Goldilocks field (from Lean) */
/* omega_n = g^((p-1)/n) where g is a generator (g = 7) */

/* For testing: primitive 8th root of unity */
/* From AmoLean/NTT/Goldilocks.lean: primitiveRoot 8 */
#define OMEGA_8 0xFFFFFFFEFF000001ULL

/* Modular inverse of 8 */
/* 8^(-1) mod p */
#define N_INV_8 0xDFFFFFFF20000001ULL

int main(void) {
    printf("NTT Skeleton Test\n");
    printf("=================\n\n");

    /* Test 1: Basic NTT N=8 */
    printf("Test 1: Forward NTT N=8\n");
    goldilocks_t input[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    goldilocks_t data[8];
    memcpy(data, input, sizeof(data));

    printf("Input:  ");
    for (int i = 0; i < 8; i++) {
        printf("%llu ", (unsigned long long)data[i]);
    }
    printf("\n");

    int result = ntt_forward(data, 8, OMEGA_8);
    if (result != 0) {
        printf("NTT failed!\n");
        return 1;
    }

    printf("NTT:    ");
    for (int i = 0; i < 8; i++) {
        printf("%llu ", (unsigned long long)data[i]);
    }
    printf("\n");

    /* Test 2: Roundtrip INTT(NTT(x)) = x */
    printf("\nTest 2: Roundtrip INTT(NTT(x))\n");
    result = ntt_inverse(data, 8, OMEGA_8, N_INV_8);
    if (result != 0) {
        printf("INTT failed!\n");
        return 1;
    }

    printf("INTT:   ");
    for (int i = 0; i < 8; i++) {
        printf("%llu ", (unsigned long long)data[i]);
    }
    printf("\n");

    /* Verify roundtrip */
    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (data[i] != input[i]) {
            match = 0;
            break;
        }
    }
    printf("Match:  %s\n", match ? "YES" : "NO");

    return match ? 0 : 1;
}

#endif /* NTT_SKELETON_MAIN */
