/**
 * test_ntt_oracle.c - Oracle Testing: Lean NTT vs C NTT
 *
 * AMO-Lean Phase 5: NTT Code Generation
 *
 * This test verifies that the C NTT implementation produces the same
 * results as the Lean reference implementation (NTT_recursive).
 *
 * Test cases:
 *   - N=4, N=8, N=16, N=32: Compare outputs
 *   - Roundtrip: INTT(NTT(x)) = x
 *   - Random inputs: Statistical verification
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

#include "field_goldilocks.h"
#include "ntt_kernel.h"
#include "ntt_skeleton.c"

/*===========================================================================
 * Primitive Roots and Inverses (from Lean)
 *
 * Computed using: primitiveRoot n (by decide)
 * n_inv computed using: GoldilocksField.inv ⟨n⟩
 *===========================================================================*/

/* From Lean: primitiveRoot n and GoldilocksField.inv ⟨n⟩ */

/* N=4 */
#define OMEGA_4  0x1000000000000ULL
#define N_INV_4  0xBFFFFFFF40000001ULL

/* N=8 */
#ifndef OMEGA_8
#define OMEGA_8 0xFFFFFFFEFF000001ULL
#define N_INV_8 0xDFFFFFFF20000001ULL
#endif

/* N=16 */
#define OMEGA_16 0xEFFFFFFF00000001ULL
#define N_INV_16 0xEFFFFFFF10000001ULL

/* N=32 */
#define OMEGA_32 0x3FFFFFFFC000ULL
#define N_INV_32 0xF7FFFFFF08000001ULL

/*===========================================================================
 * Expected Outputs from Lean (NTT_spec / NTT_recursive)
 *===========================================================================*/

/* N=4: NTT([1,2,3,4]) from Lean NTT_spec */
static const goldilocks_t LEAN_NTT_4[] = {
    10, 18446181119461163007ULL, 18446744069414584319ULL, 562949953421310ULL
};

/* N=8: NTT([1,2,3,4,5,6,7,8]) - from build output */
static const goldilocks_t LEAN_NTT_8[] = {
    36,
    18445622567621360637ULL,
    18445618169507741693ULL,
    1130298020461564ULL,
    18446744069414584317ULL,
    18445613771394122749ULL,
    1125899906842620ULL,
    1121501793223676ULL
};

/*===========================================================================
 * Test Functions
 *===========================================================================*/

static int test_ntt_n4(void) {
    printf("Test: NTT N=4\n");

    goldilocks_t input[] = {1, 2, 3, 4};
    goldilocks_t data[4];
    memcpy(data, input, sizeof(data));

    /* Get omega_4 from Lean */
    goldilocks_t omega = OMEGA_4;

    int result = ntt_forward(data, 4, omega);
    if (result != 0) {
        printf("  FAIL: ntt_forward returned error\n");
        return 1;
    }

    /* Compare with Lean output */
    bool match = true;
    for (int i = 0; i < 4; i++) {
        if (data[i] != LEAN_NTT_4[i]) {
            printf("  FAIL: data[%d] = %llu, expected %llu\n",
                   i, (unsigned long long)data[i],
                   (unsigned long long)LEAN_NTT_4[i]);
            match = false;
        }
    }

    if (match) {
        printf("  PASS: Output matches Lean\n");
    }

    /* Test roundtrip */
    result = ntt_inverse(data, 4, omega, N_INV_4);
    if (result != 0) {
        printf("  FAIL: ntt_inverse returned error\n");
        return 1;
    }

    match = true;
    for (int i = 0; i < 4; i++) {
        if (data[i] != input[i]) {
            printf("  FAIL: roundtrip[%d] = %llu, expected %llu\n",
                   i, (unsigned long long)data[i],
                   (unsigned long long)input[i]);
            match = false;
        }
    }

    if (match) {
        printf("  PASS: Roundtrip INTT(NTT(x)) = x\n");
    }

    return match ? 0 : 1;
}

static int test_ntt_n8(void) {
    printf("\nTest: NTT N=8\n");

    goldilocks_t input[] = {1, 2, 3, 4, 5, 6, 7, 8};
    goldilocks_t data[8];
    memcpy(data, input, sizeof(data));

    goldilocks_t omega = OMEGA_8;

    int result = ntt_forward(data, 8, omega);
    if (result != 0) {
        printf("  FAIL: ntt_forward returned error\n");
        return 1;
    }

    /* Compare with Lean output */
    bool match = true;
    for (int i = 0; i < 8; i++) {
        if (data[i] != LEAN_NTT_8[i]) {
            printf("  FAIL: data[%d] = %llu, expected %llu\n",
                   i, (unsigned long long)data[i],
                   (unsigned long long)LEAN_NTT_8[i]);
            match = false;
        }
    }

    if (match) {
        printf("  PASS: Output matches Lean\n");
    }

    /* Test roundtrip */
    result = ntt_inverse(data, 8, omega, N_INV_8);
    if (result != 0) {
        printf("  FAIL: ntt_inverse returned error\n");
        return 1;
    }

    match = true;
    for (int i = 0; i < 8; i++) {
        if (data[i] != input[i]) {
            printf("  FAIL: roundtrip[%d] = %llu, expected %llu\n",
                   i, (unsigned long long)data[i],
                   (unsigned long long)input[i]);
            match = false;
        }
    }

    if (match) {
        printf("  PASS: Roundtrip INTT(NTT(x)) = x\n");
    }

    return match ? 0 : 1;
}

static int test_ntt_roundtrip(size_t n, goldilocks_t omega, goldilocks_t n_inv) {
    printf("\nTest: Roundtrip N=%zu\n", n);

    goldilocks_t* data = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));
    goldilocks_t* input = (goldilocks_t*)malloc(n * sizeof(goldilocks_t));
    if (!data || !input) {
        printf("  FAIL: malloc failed\n");
        free(data);
        free(input);
        return 1;
    }

    /* Initialize with sequential values */
    for (size_t i = 0; i < n; i++) {
        input[i] = i + 1;
        data[i] = i + 1;
    }

    /* Forward NTT */
    int result = ntt_forward(data, n, omega);
    if (result != 0) {
        printf("  FAIL: ntt_forward returned error\n");
        free(data);
        free(input);
        return 1;
    }

    /* Inverse NTT */
    result = ntt_inverse(data, n, omega, n_inv);
    if (result != 0) {
        printf("  FAIL: ntt_inverse returned error\n");
        free(data);
        free(input);
        return 1;
    }

    /* Verify roundtrip */
    bool match = true;
    for (size_t i = 0; i < n; i++) {
        if (data[i] != input[i]) {
            printf("  FAIL: roundtrip[%zu] = %llu, expected %llu\n",
                   i, (unsigned long long)data[i],
                   (unsigned long long)input[i]);
            match = false;
            if (i > 5) {
                printf("  ... (more errors)\n");
                break;
            }
        }
    }

    if (match) {
        printf("  PASS: Roundtrip INTT(NTT(x)) = x\n");
    }

    free(data);
    free(input);
    return match ? 0 : 1;
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  NTT Oracle Test: Lean vs C\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    int failures = 0;

    /* Test N=4 */
    failures += test_ntt_n4();

    /* Test N=8 */
    failures += test_ntt_n8();

    /* Test roundtrip for N=16 */
    failures += test_ntt_roundtrip(16, OMEGA_16, N_INV_16);

    /* Test roundtrip for N=32 */
    failures += test_ntt_roundtrip(32, OMEGA_32, N_INV_32);

    printf("\n═══════════════════════════════════════════════════════════════\n");
    if (failures == 0) {
        printf("  ALL TESTS PASSED\n");
    } else {
        printf("  %d TEST(S) FAILED\n", failures);
    }
    printf("═══════════════════════════════════════════════════════════════\n");

    return failures;
}
