/*
 * bench_fri_fold.c — FRI Fold Benchmark: AMO-Lean vs Reference
 *
 * Benchmarks the FRI fold operation: result[i] = even[i] + alpha * odd[i] (mod p)
 * This is the core operation in each round of the FRI protocol.
 *
 * Strategies:
 *   1. Naive: (even + alpha * odd) % p
 *   2. AMO-Lean Solinas fold: fold(even + fold(alpha * odd))
 *   3. AMO-Lean Harvey: harvey_reduce(even + alpha * odd)
 *   4. Montgomery: monty_reduce(even + monty_mul(alpha, odd))
 *
 * Compile: cc -O2 -o bench_fri_fold bench_fri_fold.c
 * Run:     ./bench_fri_fold
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

#define BABYBEAR_P   2013265921ULL
#define BABYBEAR_C   134217727ULL
#define BABYBEAR_MU  0x88000001ULL

/* ═══════════════════════════════════════════════════════════════════
   Reductions (same as bench_ntt_full.c)
   ═══════════════════════════════════════════════════════════════════ */

static inline uint64_t reduce_solinas(uint64_t x) {
    return ((x >> 31) * BABYBEAR_C) + (x & 0x7FFFFFFF);
}

static inline uint64_t reduce_harvey(uint64_t x) {
    if (x >= 2 * BABYBEAR_P) x -= 2 * BABYBEAR_P;
    if (x >= BABYBEAR_P) x -= BABYBEAR_P;
    return x;
}

static inline uint32_t reduce_monty(uint64_t x) {
    uint64_t t = (x * BABYBEAR_MU) & 0xFFFFFFFF;
    uint64_t u = t * BABYBEAR_P;
    uint64_t diff = x - u;
    uint32_t hi = (uint32_t)(diff >> 32);
    return (x < u) ? hi + (uint32_t)BABYBEAR_P : hi;
}

/* ═══════════════════════════════════════════════════════════════════
   FRI fold implementations
   ═══════════════════════════════════════════════════════════════════ */

/* FRI fold: result[i] = (even[i] + alpha * odd[i]) % p */

/* Naive: full mod */
static void fri_fold_naive(const uint64_t *even, const uint64_t *odd,
    uint64_t alpha, uint64_t *result, size_t n) {
    for (size_t i = 0; i < n; i++) {
        result[i] = (even[i] + (alpha * odd[i]) % BABYBEAR_P) % BABYBEAR_P;
    }
}

/* AMO-Lean: Solinas fold (verified) */
static void fri_fold_solinas(const uint64_t *even, const uint64_t *odd,
    uint64_t alpha, uint64_t *result, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint64_t prod = alpha * odd[i];
        uint64_t prod_folded = reduce_solinas(prod);
        uint64_t sum = even[i] + prod_folded;
        result[i] = reduce_solinas(sum);
    }
}

/* AMO-Lean: Harvey lazy */
static void fri_fold_harvey(const uint64_t *even, const uint64_t *odd,
    uint64_t alpha, uint64_t *result, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint64_t prod = alpha * odd[i];
        uint64_t sum = even[i] + prod;
        result[i] = reduce_harvey(sum);
    }
}

/* Plonky3 Montgomery */
static void fri_fold_monty(const uint32_t *even, const uint32_t *odd,
    uint32_t alpha, uint32_t *result, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint32_t prod = reduce_monty((uint64_t)alpha * (uint64_t)odd[i]);
        uint32_t sum = even[i] + prod;
        if (sum >= (uint32_t)BABYBEAR_P) sum -= (uint32_t)BABYBEAR_P;
        result[i] = sum;
    }
}

/* ═══════════════════════════════════════════════════════════════════
   Benchmark
   ═══════════════════════════════════════════════════════════════════ */

typedef struct { const char *name; double us; } FRIResult;

static FRIResult bench_fri_u64(const char *name, size_t n, int iters,
    void (*fn)(const uint64_t*, const uint64_t*, uint64_t, uint64_t*, size_t)) {
    uint64_t *even = malloc(n * sizeof(uint64_t));
    uint64_t *odd = malloc(n * sizeof(uint64_t));
    uint64_t *result = malloc(n * sizeof(uint64_t));
    uint64_t alpha = 1234567891ULL % BABYBEAR_P;

    for (size_t i = 0; i < n; i++) {
        even[i] = (i * 1000000007ULL) % BABYBEAR_P;
        odd[i] = (i * 999999937ULL) % BABYBEAR_P;
    }

    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int iter = 0; iter < iters; iter++) {
        fn(even, odd, alpha, result, n);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);

    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double us = elapsed / iters * 1e6;
    double throughput = (double)n * iters / elapsed / 1e6;
    printf("  %-25s: %8.1f us  %6.1f Melem/s  [%llu]\n",
           name, us, throughput, (unsigned long long)result[0]);

    free(even); free(odd); free(result);
    return (FRIResult){name, us};
}

static FRIResult bench_fri_u32(const char *name, size_t n, int iters,
    void (*fn)(const uint32_t*, const uint32_t*, uint32_t, uint32_t*, size_t)) {
    uint32_t *even = malloc(n * sizeof(uint32_t));
    uint32_t *odd = malloc(n * sizeof(uint32_t));
    uint32_t *result = malloc(n * sizeof(uint32_t));
    uint32_t alpha = (uint32_t)(1234567891ULL % BABYBEAR_P);

    for (size_t i = 0; i < n; i++) {
        even[i] = (uint32_t)((i * 1000000007ULL) % BABYBEAR_P);
        odd[i] = (uint32_t)((i * 999999937ULL) % BABYBEAR_P);
    }

    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int iter = 0; iter < iters; iter++) {
        fn(even, odd, alpha, result, n);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);

    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double us = elapsed / iters * 1e6;
    double throughput = (double)n * iters / elapsed / 1e6;
    printf("  %-25s: %8.1f us  %6.1f Melem/s  [%u]\n",
           name, us, throughput, result[0]);

    free(even); free(odd); free(result);
    return (FRIResult){name, us};
}

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  AMO-Lean vs Plonky3: FRI Fold Benchmark (BabyBear)        ║\n");
    printf("╠══════════════════════════════════════════════════════════════╣\n");
    printf("║  Operation: result[i] = even[i] + alpha * odd[i] (mod p)  ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");

    size_t sizes[] = {1024, 4096, 16384, 65536};
    int iters[] =    {50000, 10000, 2000, 500};
    int num_sizes = sizeof(sizes) / sizeof(sizes[0]);

    for (int si = 0; si < num_sizes; si++) {
        size_t n = sizes[si];
        int it = iters[si];
        printf("══ N = %zu (%d iterations) ══\n\n", n, it);

        FRIResult r_naive   = bench_fri_u64("Naive (% p)", n, it, fri_fold_naive);
        FRIResult r_solinas = bench_fri_u64("AMO-Lean Solinas", n, it, fri_fold_solinas);
        FRIResult r_harvey  = bench_fri_u64("AMO-Lean Harvey", n, it, fri_fold_harvey);
        FRIResult r_monty   = bench_fri_u32("Plonky3 Montgomery", n, it, fri_fold_monty);

        printf("\n  vs Plonky3 Montgomery:\n");
        printf("    Solinas: %+.1f%%\n", (1.0 - r_solinas.us / r_monty.us) * 100);
        printf("    Harvey:  %+.1f%%\n", (1.0 - r_harvey.us / r_monty.us) * 100);
        printf("\n");
    }

    printf("Notes:\n");
    printf("  - FRI fold = core operation in each FRI protocol round\n");
    printf("  - Each element: 1 mul + 1 add + 1-2 reductions\n");
    printf("  - AMO-Lean Solinas fold verified: solinasFold_mod_correct\n");
    printf("  - Scalar comparison (no SIMD); Plonky3 has AVX2 variant\n");

    return 0;
}
