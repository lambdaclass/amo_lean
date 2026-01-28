/**
 * test_fri_fold.c - Test for generated FRI fold operations
 *
 * Compilation:
 *   Debug (with sanitizers):
 *     clang -DFIELD_NATIVE -DDEBUG -fsanitize=address,undefined -g -O0 -o test_fri_fold test_fri_fold.c
 *
 *   Release:
 *     clang -DFIELD_NATIVE -O3 -o test_fri_fold test_fri_fold.c
 *
 *   Goldilocks field:
 *     clang -DFIELD_GOLDILOCKS -DDEBUG -fsanitize=address,undefined -g -O0 -o test_fri_fold test_fri_fold.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Define FIELD_NATIVE and DEBUG via compiler flags, e.g.:
 *   -DFIELD_NATIVE -DDEBUG
 * or uncomment below for standalone compilation:
 */
#ifndef FIELD_NATIVE
#define FIELD_NATIVE  /* Use native uint64_t arithmetic for testing */
#endif
#ifndef DEBUG
#define DEBUG         /* Enable debug assertions */
#endif

#include "field_ops.h"
#include "fri_fold.h"

/* Test helper: print array */
void print_array(const char* name, const field_t* arr, size_t n) {
    printf("%s = [", name);
    for (size_t i = 0; i < n; i++) {
        if (i > 0) printf(", ");
        printf("%llu", (unsigned long long)arr[i]);
    }
    printf("]\n");
}

/* Test 1: Basic fri_fold */
int test_basic_fold(void) {
    printf("\n=== Test 1: Basic fri_fold ===\n");

    field_t even[4] = {1, 2, 3, 4};
    field_t odd[4]  = {10, 20, 30, 40};
    field_t out[4];
    field_t alpha = 2;

    print_array("even", even, 4);
    print_array("odd", odd, 4);
    printf("alpha = %llu\n", (unsigned long long)alpha);

    fri_fold(4, even, odd, out, alpha);

    print_array("out", out, 4);

    /* Verify: out[i] = even[i] + alpha * odd[i] */
    int pass = 1;
    for (size_t i = 0; i < 4; i++) {
        field_t expected = field_add(even[i], field_mul(alpha, odd[i]));
        if (out[i] != expected) {
            printf("FAIL: out[%zu] = %llu, expected %llu\n",
                   i, (unsigned long long)out[i], (unsigned long long)expected);
            pass = 0;
        }
    }

    if (pass) {
        printf("PASS: Basic fold test\n");
    }
    return pass;
}

/* Test 2: fri_fold_layer (from interleaved input) */
int test_fold_layer(void) {
    printf("\n=== Test 2: fri_fold_layer ===\n");

    /* Input: [e0, o0, e1, o1, e2, o2, e3, o3] */
    field_t input[8] = {1, 10, 2, 20, 3, 30, 4, 40};
    field_t output[4];
    field_t alpha = 3;

    print_array("input", input, 8);
    printf("alpha = %llu\n", (unsigned long long)alpha);

    fri_fold_layer(4, input, output, alpha);

    print_array("output", output, 4);

    /* Verify: output[i] = input[2*i] + alpha * input[2*i+1] */
    int pass = 1;
    for (size_t i = 0; i < 4; i++) {
        field_t even = input[2 * i];
        field_t odd = input[2 * i + 1];
        field_t expected = field_add(even, field_mul(alpha, odd));
        if (output[i] != expected) {
            printf("FAIL: output[%zu] = %llu, expected %llu\n",
                   i, (unsigned long long)output[i], (unsigned long long)expected);
            pass = 0;
        }
    }

    if (pass) {
        printf("PASS: Layer fold test\n");
    }
    return pass;
}

/* Test 3: Size-specific fri_fold_16 */
int test_fold_16(void) {
    printf("\n=== Test 3: fri_fold_16 ===\n");

    field_t even[16], odd[16], out[16];
    field_t alpha = 5;

    /* Initialize with simple values */
    for (size_t i = 0; i < 16; i++) {
        even[i] = i;
        odd[i] = i * 10;
    }

    fri_fold_16(even, odd, out, alpha);

    /* Verify first and last elements */
    int pass = 1;
    for (size_t i = 0; i < 16; i++) {
        field_t expected = field_add(even[i], field_mul(alpha, odd[i]));
        if (out[i] != expected) {
            printf("FAIL: out[%zu] = %llu, expected %llu\n",
                   i, (unsigned long long)out[i], (unsigned long long)expected);
            pass = 0;
        }
    }

    if (pass) {
        printf("PASS: fri_fold_16 test\n");
    }
    return pass;
}

/* Test 4: Larger array (256 elements) */
int test_fold_256(void) {
    printf("\n=== Test 4: fri_fold_256 ===\n");

    field_t* even = malloc(256 * sizeof(field_t));
    field_t* odd = malloc(256 * sizeof(field_t));
    field_t* out = malloc(256 * sizeof(field_t));

    if (!even || !odd || !out) {
        printf("FAIL: Memory allocation failed\n");
        free(even); free(odd); free(out);
        return 0;
    }

    field_t alpha = 7;

    /* Initialize with simple values */
    for (size_t i = 0; i < 256; i++) {
        even[i] = i;
        odd[i] = 256 - i;
    }

    fri_fold_256(even, odd, out, alpha);

    /* Verify a few elements */
    int pass = 1;
    size_t check_indices[] = {0, 1, 127, 128, 255};
    for (size_t j = 0; j < 5; j++) {
        size_t i = check_indices[j];
        field_t expected = field_add(even[i], field_mul(alpha, odd[i]));
        if (out[i] != expected) {
            printf("FAIL: out[%zu] = %llu, expected %llu\n",
                   i, (unsigned long long)out[i], (unsigned long long)expected);
            pass = 0;
        }
    }

    free(even);
    free(odd);
    free(out);

    if (pass) {
        printf("PASS: fri_fold_256 test\n");
    }
    return pass;
}

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║     FRI FOLD GENERATED CODE TEST                             ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");
    printf("Field type: %s\n", FIELD_NAME);
#ifdef DEBUG
    printf("Debug assertions: ENABLED\n");
#else
    printf("Debug assertions: DISABLED\n");
#endif

    int all_pass = 1;

    all_pass &= test_basic_fold();
    all_pass &= test_fold_layer();
    all_pass &= test_fold_16();
    all_pass &= test_fold_256();

    printf("\n");
    if (all_pass) {
        printf("══════════════════════════════════════════════════════════════\n");
        printf("ALL TESTS PASSED\n");
        printf("══════════════════════════════════════════════════════════════\n");
        return 0;
    } else {
        printf("══════════════════════════════════════════════════════════════\n");
        printf("SOME TESTS FAILED\n");
        printf("══════════════════════════════════════════════════════════════\n");
        return 1;
    }
}
