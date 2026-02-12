/**
 * oracle_test.c - Oracle Testing for FRI Fold
 *
 * This program tests that the C implementation produces the same
 * results as the Lean reference implementation.
 *
 * Input format (stdin):
 *   Line 1: size alpha
 *   Line 2: even[0] even[1] ... even[size-1]
 *   Line 3: odd[0] odd[1] ... odd[size-1]
 *
 * Output format (stdout):
 *   out[0] out[1] ... out[size-1]
 *
 * Compile:
 *   clang -DFIELD_NATIVE -O2 -o oracle_test oracle_test.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#ifndef FIELD_NATIVE
#define FIELD_NATIVE
#endif
#include "field_ops.h"
#include "fri_fold.h"

int main(int argc, char** argv) {
    size_t size;
    field_t alpha;

    /* Read size and alpha */
    if (scanf("%zu %llu", &size, (unsigned long long*)&alpha) != 2) {
        fprintf(stderr, "Error: Failed to read size and alpha\n");
        return 1;
    }

    if (size == 0 || size > 1000000) {
        fprintf(stderr, "Error: Invalid size %zu\n", size);
        return 1;
    }

    /* Allocate arrays */
    field_t* even = malloc(size * sizeof(field_t));
    field_t* odd = malloc(size * sizeof(field_t));
    field_t* out = malloc(size * sizeof(field_t));

    if (!even || !odd || !out) {
        fprintf(stderr, "Error: Memory allocation failed\n");
        return 1;
    }

    /* Read even array */
    for (size_t i = 0; i < size; i++) {
        if (scanf("%llu", (unsigned long long*)&even[i]) != 1) {
            fprintf(stderr, "Error: Failed to read even[%zu]\n", i);
            return 1;
        }
    }

    /* Read odd array */
    for (size_t i = 0; i < size; i++) {
        if (scanf("%llu", (unsigned long long*)&odd[i]) != 1) {
            fprintf(stderr, "Error: Failed to read odd[%zu]\n", i);
            return 1;
        }
    }

    /* Compute FRI fold */
    fri_fold(size, even, odd, out, alpha);

    /* Output result */
    for (size_t i = 0; i < size; i++) {
        if (i > 0) printf(" ");
        printf("%llu", (unsigned long long)out[i]);
    }
    printf("\n");

    /* Cleanup */
    free(even);
    free(odd);
    free(out);

    return 0;
}
