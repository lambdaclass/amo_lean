/**
 * SanitizerTest.c - Memory Safety Tests with Sanitizers
 *
 * AMO-Lean Phase 5 QA: Final Audit
 *
 * Run with: -fsanitize=address,undefined -O1 -g
 *
 * Tests for:
 *   - Buffer overflows in NTT loops
 *   - Off-by-one errors in indexing
 *   - Undefined behavior (integer overflow, null dereference, etc.)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "../generated/field_goldilocks.h"
#include "../generated/ntt_kernel.h"
#include "../generated/ntt_skeleton.c"

/*===========================================================================
 * Primitive Roots (from Lean)
 *===========================================================================*/

/* N=1024 (from Lean: primitiveRoot 1024) */
#define OMEGA_1024 0x9D8F2AD78BFED972ULL
#define N_INV_1024 0xFFBFFFFF00400001ULL

/* N=4096 (from Lean: primitiveRoot 4096) */
#define OMEGA_4096 0xF2C35199959DFCB6ULL
#define N_INV_4096 0xFFEFFFFF00100001ULL

/*===========================================================================
 * Tests
 *===========================================================================*/

static int test_ntt_1024(void) {
    printf("Test: NTT N=1024 (Sanitizer Check)\n");

    goldilocks_t* data = (goldilocks_t*)malloc(1024 * sizeof(goldilocks_t));
    goldilocks_t* backup = (goldilocks_t*)malloc(1024 * sizeof(goldilocks_t));

    if (!data || !backup) {
        printf("FAIL: malloc failed\n");
        free(data);
        free(backup);
        return 1;
    }

    /* Initialize with sequential values */
    for (size_t i = 0; i < 1024; i++) {
        data[i] = i + 1;
        backup[i] = i + 1;
    }

    /* Forward NTT */
    int result = ntt_forward(data, 1024, OMEGA_1024);
    if (result != 0) {
        printf("FAIL: ntt_forward failed\n");
        free(data);
        free(backup);
        return 1;
    }

    /* Inverse NTT */
    result = ntt_inverse(data, 1024, OMEGA_1024, N_INV_1024);
    if (result != 0) {
        printf("FAIL: ntt_inverse failed\n");
        free(data);
        free(backup);
        return 1;
    }

    /* Verify roundtrip */
    int errors = 0;
    for (size_t i = 0; i < 1024; i++) {
        if (data[i] != backup[i]) {
            if (errors < 5) {
                printf("FAIL: data[%zu] = %llu, expected %llu\n",
                       i, (unsigned long long)data[i],
                       (unsigned long long)backup[i]);
            }
            errors++;
        }
    }

    free(data);
    free(backup);

    if (errors == 0) {
        printf("PASS: N=1024 roundtrip correct\n");
        return 0;
    } else {
        printf("FAIL: %d errors in roundtrip\n", errors);
        return 1;
    }
}

static int test_ntt_4096(void) {
    printf("\nTest: NTT N=4096 (Sanitizer Check)\n");

    goldilocks_t* data = (goldilocks_t*)malloc(4096 * sizeof(goldilocks_t));
    goldilocks_t* backup = (goldilocks_t*)malloc(4096 * sizeof(goldilocks_t));

    if (!data || !backup) {
        printf("FAIL: malloc failed\n");
        free(data);
        free(backup);
        return 1;
    }

    /* Initialize with sequential values */
    for (size_t i = 0; i < 4096; i++) {
        data[i] = i + 1;
        backup[i] = i + 1;
    }

    /* Forward NTT */
    int result = ntt_forward(data, 4096, OMEGA_4096);
    if (result != 0) {
        printf("FAIL: ntt_forward failed\n");
        free(data);
        free(backup);
        return 1;
    }

    /* Inverse NTT */
    result = ntt_inverse(data, 4096, OMEGA_4096, N_INV_4096);
    if (result != 0) {
        printf("FAIL: ntt_inverse failed\n");
        free(data);
        free(backup);
        return 1;
    }

    /* Verify roundtrip */
    int errors = 0;
    for (size_t i = 0; i < 4096; i++) {
        if (data[i] != backup[i]) {
            if (errors < 5) {
                printf("FAIL: data[%zu] = %llu, expected %llu\n",
                       i, (unsigned long long)data[i],
                       (unsigned long long)backup[i]);
            }
            errors++;
        }
    }

    free(data);
    free(backup);

    if (errors == 0) {
        printf("PASS: N=4096 roundtrip correct\n");
        return 0;
    } else {
        printf("FAIL: %d errors in roundtrip\n", errors);
        return 1;
    }
}

static int test_edge_sizes(void) {
    printf("\nTest: Edge Sizes (N=2, N=1)\n");

    /* N=2 */
    {
        goldilocks_t data[2] = {42, 17};
        goldilocks_t backup[2] = {42, 17};

        /* For N=2, omega = g^((p-1)/2) = -1 (since g^((p-1)/2) ≡ -1 by Fermat) */
        goldilocks_t omega_2 = GOLDILOCKS_ORDER - 1;  /* -1 mod p */
        goldilocks_t n_inv_2 = (GOLDILOCKS_ORDER + 1) / 2;  /* 2^(-1) mod p */

        int result = ntt_forward(data, 2, omega_2);
        if (result != 0) {
            printf("FAIL: ntt_forward N=2 failed\n");
            return 1;
        }

        result = ntt_inverse(data, 2, omega_2, n_inv_2);
        if (result != 0) {
            printf("FAIL: ntt_inverse N=2 failed\n");
            return 1;
        }

        if (data[0] != backup[0] || data[1] != backup[1]) {
            printf("FAIL: N=2 roundtrip incorrect\n");
            return 1;
        }

        printf("PASS: N=2 roundtrip correct\n");
    }

    /* N=1 */
    {
        goldilocks_t data[1] = {123456789};

        int result = ntt_forward(data, 1, 1);  /* omega doesn't matter for N=1 */
        if (result != 0) {
            printf("FAIL: ntt_forward N=1 failed\n");
            return 1;
        }

        if (data[0] != 123456789) {
            printf("FAIL: N=1 should be identity\n");
            return 1;
        }

        printf("PASS: N=1 identity correct\n");
    }

    return 0;
}

/*===========================================================================
 * Main
 *===========================================================================*/

int main(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Sanitizer Test: Memory Safety Check\n");
    printf("  AMO-Lean Phase 5 QA Final Audit\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    int failures = 0;
    failures += test_ntt_1024();
    failures += test_ntt_4096();
    failures += test_edge_sizes();

    printf("\n═══════════════════════════════════════════════════════════════\n");
    if (failures == 0) {
        printf("  ALL TESTS PASSED - NO SANITIZER ERRORS\n");
    } else {
        printf("  %d TEST(S) FAILED\n", failures);
    }
    printf("═══════════════════════════════════════════════════════════════\n");

    return failures;
}
