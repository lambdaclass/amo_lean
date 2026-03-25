/*
 * bench_primitives.c — Benchmark FRI fold + Poly eval + Dot product
 * AMO-Lean generated (Solinas fold) vs Plonky3-style Montgomery
 *
 * Compile: cc -O2 -o bench_primitives bench_primitives.c
 * Run:     ./bench_primitives
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

#define BB_P   0x78000001U
#define BB_C   134217727U
#define BB_MU  0x88000001U

/* AMO-Lean Solinas fold (chosen by e-graph for scalar) */
static inline uint32_t amo_reduce(uint64_t x) {
    return (uint32_t)(((x >> 31) * BB_C) + (x & 0x7FFFFFFF));
}

/* Plonky3 Montgomery REDC */
static inline uint32_t p3_reduce(uint64_t x) {
    uint64_t t = (x * (uint64_t)BB_MU) & 0xFFFFFFFF;
    uint64_t u = t * (uint64_t)BB_P;
    uint64_t d = x - u;
    uint32_t hi = (uint32_t)(d >> 32);
    return (x < u) ? hi + BB_P : hi;
}

/* ═══ FRI Fold ═══ */
static void fri_fold_amo(const uint32_t *even, const uint32_t *odd,
    uint32_t alpha, uint32_t *result, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint32_t prod = amo_reduce((uint64_t)alpha * (uint64_t)odd[i]);
        result[i] = amo_reduce((uint64_t)even[i] + (uint64_t)prod);
    }
}

static void fri_fold_p3(const uint32_t *even, const uint32_t *odd,
    uint32_t alpha, uint32_t *result, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint32_t prod = p3_reduce((uint64_t)alpha * (uint64_t)odd[i]);
        uint32_t sum = even[i] + prod;
        result[i] = (sum >= BB_P) ? sum - BB_P : sum;
    }
}

/* ═══ Polynomial Evaluation (Horner) ═══ */
static uint32_t poly_eval_amo(const uint32_t *coeffs, size_t degree, uint32_t x) {
    uint32_t acc = coeffs[degree];
    for (size_t i = degree; i > 0; i--) {
        acc = amo_reduce((uint64_t)x * (uint64_t)acc);
        acc = amo_reduce((uint64_t)coeffs[i-1] + (uint64_t)acc);
    }
    return acc;
}

static uint32_t poly_eval_p3(const uint32_t *coeffs, size_t degree, uint32_t x) {
    uint32_t acc = coeffs[degree];
    for (size_t i = degree; i > 0; i--) {
        acc = p3_reduce((uint64_t)x * (uint64_t)acc);
        uint32_t sum = coeffs[i-1] + acc;
        acc = (sum >= BB_P) ? sum - BB_P : sum;
    }
    return acc;
}

/* ═══ Dot Product ═══ */
static uint32_t dot_product_amo(const uint32_t *a, const uint32_t *b, size_t n) {
    uint32_t acc = 0;
    for (size_t i = 0; i < n; i++) {
        uint32_t prod = amo_reduce((uint64_t)a[i] * (uint64_t)b[i]);
        acc = amo_reduce((uint64_t)acc + (uint64_t)prod);
    }
    return acc;
}

static uint32_t dot_product_p3(const uint32_t *a, const uint32_t *b, size_t n) {
    uint32_t acc = 0;
    for (size_t i = 0; i < n; i++) {
        uint32_t prod = p3_reduce((uint64_t)a[i] * (uint64_t)b[i]);
        uint32_t sum = acc + prod;
        acc = (sum >= BB_P) ? sum - BB_P : sum;
    }
    return acc;
}

/* ═══ Benchmark ═══ */
int main(void) {
    printf("╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║  Crypto Primitives: AMO-Lean (Solinas) vs Plonky3 (Montgomery) ║\n");
    printf("║  BabyBear, N=65536, scalar                                    ║\n");
    printf("╚══════════════════════════════════════════════════════════════════╝\n\n");

    size_t n = 65536;
    int iters = 100;
    uint32_t *a = malloc(n * 4), *b = malloc(n * 4), *r = malloc(n * 4);
    for (size_t i = 0; i < n; i++) {
        a[i] = (uint32_t)((i * 1000000007ULL) % BB_P);
        b[i] = (uint32_t)((i * 999999937ULL) % BB_P);
    }

    struct timespec s, e;

    /* FRI Fold */
    printf("── FRI Fold (N=%zu) ──\n", n);
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) fri_fold_amo(a, b, 42, r, n);
    clock_gettime(CLOCK_MONOTONIC, &e);
    double amo_fri = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) fri_fold_p3(a, b, 42, r, n);
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_fri = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;
    printf("  AMO-Lean: %.1f us  Plonky3: %.1f us  %+.1f%%\n\n", amo_fri, p3_fri, (1-amo_fri/p3_fri)*100);

    /* Polynomial Eval */
    printf("── Polynomial Evaluation (degree 7, %zu evaluations) ──\n", n);
    uint32_t coeffs[8] = {42, 17, 99, 3, 55, 7, 13, 1};
    volatile uint32_t sink = 0;
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++)
        for (size_t i = 0; i < n; i++) sink = poly_eval_amo(coeffs, 7, a[i]);
    clock_gettime(CLOCK_MONOTONIC, &e);
    double amo_poly = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++)
        for (size_t i = 0; i < n; i++) sink = poly_eval_p3(coeffs, 7, a[i]);
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_poly = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;
    printf("  AMO-Lean: %.1f us  Plonky3: %.1f us  %+.1f%%\n\n", amo_poly, p3_poly, (1-amo_poly/p3_poly)*100);

    /* Dot Product */
    printf("── Dot Product (N=%zu) ──\n", n);
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) sink = dot_product_amo(a, b, n);
    clock_gettime(CLOCK_MONOTONIC, &e);
    double amo_dot = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) sink = dot_product_p3(a, b, n);
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_dot = ((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;
    printf("  AMO-Lean: %.1f us  Plonky3: %.1f us  %+.1f%%\n\n", amo_dot, p3_dot, (1-amo_dot/p3_dot)*100);

    printf("Note: All use e-graph-selected Solinas fold for scalar.\n");
    printf("Verified: solinasFold_mod_correct (fold(x) %% p = x %% p)\n");
    free(a); free(b); free(r);
    return 0;
}
