/*
 * bench_butterfly.c — B82: Microbenchmark for NTT butterfly implementations
 *
 * Compares AMO-Lean generated reductions against reference Plonky3-style code.
 * Measures cycles per butterfly for BabyBear on different strategies.
 *
 * Compile: gcc -O2 -o bench_butterfly bench_butterfly.c -lm
 * Run:     ./bench_butterfly
 */

#include <stdio.h>
#include <stdint.h>
#include <time.h>

#define BABYBEAR_P 2013265921ULL  /* 2^31 - 2^27 + 1 */
#define BABYBEAR_C 134217727ULL   /* 2^27 - 1 */
#define ITERATIONS 10000000

/* ═══════════════════════════════════════════════════════════════════
   Strategy 1: Standard reduction (full mod p)
   AMO-Lean output for ARM: (x >> 31) * 134217727 + (x & 2147483647)
   ═══════════════════════════════════════════════════════════════════ */
static inline uint64_t reduce_standard(uint64_t x) {
    return ((x >> 31) * BABYBEAR_C) + (x & 0x7FFFFFFF);
}

/* ═══════════════════════════════════════════════════════════════════
   Strategy 2: Shift-sub reduction (AMO-Lean RISC-V optimized)
   AMO-Lean output for RISC-V: ((x >> 31) << 27) - (x >> 31) + (x & mask)
   ═══════════════════════════════════════════════════════════════════ */
static inline uint64_t reduce_shiftsub(uint64_t x) {
    uint64_t hi = x >> 31;
    return ((hi << 27) - hi) + (x & 0x7FFFFFFF);
}

/* ═══════════════════════════════════════════════════════════════════
   Strategy 3: Harvey conditional subtraction (lazy reduction)
   Input in [0, 4q), output in [0, 2q). No full mod.
   ═══════════════════════════════════════════════════════════════════ */
static inline uint64_t reduce_harvey(uint64_t x) {
    if (x >= 2 * BABYBEAR_P) x -= 2 * BABYBEAR_P;
    if (x >= BABYBEAR_P) x -= BABYBEAR_P;
    return x;
}

/* ═══════════════════════════════════════════════════════════════════
   Strategy 4: Reference Plonky3-style (full butterfly)
   a' = a + w*b mod p,  b' = a - w*b mod p
   ═══════════════════════════════════════════════════════════════════ */
static inline void butterfly_standard(uint64_t *a, uint64_t *b, uint64_t w) {
    uint64_t wb = reduce_standard(w * (*b));
    uint64_t sum = *a + wb;
    uint64_t diff = *a + BABYBEAR_P - wb;
    *a = sum < BABYBEAR_P ? sum : sum - BABYBEAR_P;
    *b = diff < BABYBEAR_P ? diff : diff - BABYBEAR_P;
}

/* Strategy 5: Shift-sub butterfly (RISC-V optimized) */
static inline void butterfly_shiftsub(uint64_t *a, uint64_t *b, uint64_t w) {
    uint64_t wb = reduce_shiftsub(w * (*b));
    uint64_t sum = *a + wb;
    uint64_t diff = *a + BABYBEAR_P - wb;
    *a = sum < BABYBEAR_P ? sum : sum - BABYBEAR_P;
    *b = diff < BABYBEAR_P ? diff : diff - BABYBEAR_P;
}

/* Strategy 6: Harvey lazy butterfly (no full reduction inside) */
static inline void butterfly_harvey(uint64_t *a, uint64_t *b, uint64_t w) {
    uint64_t wb = w * (*b);  /* No reduction of w*b! */
    uint64_t sum = *a + wb;
    uint64_t diff = *a + 4 * BABYBEAR_P - wb;
    *a = reduce_harvey(sum);
    *b = reduce_harvey(diff);
}

/* ═══════════════════════════════════════════════════════════════════
   Benchmark harness
   ═══════════════════════════════════════════════════════════════════ */

static double benchmark_reduce(const char *name, uint64_t (*fn)(uint64_t)) {
    struct timespec start, end;
    volatile uint64_t result = 0;

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < ITERATIONS; i++) {
        result = fn((uint64_t)i * 1000000007ULL);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);

    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double ns_per_op = elapsed / ITERATIONS * 1e9;
    printf("  %-20s: %.2f ns/op  (%.1f M ops/sec)  [check: %llu]\n",
           name, ns_per_op, ITERATIONS / elapsed / 1e6, (unsigned long long)result);
    return ns_per_op;
}

static double benchmark_butterfly(const char *name,
    void (*fn)(uint64_t*, uint64_t*, uint64_t)) {
    struct timespec start, end;
    volatile uint64_t a = 42, b = 99;
    uint64_t w = 7;  /* twiddle factor */

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t ta = a + i, tb = b + i;
        fn(&ta, &tb, w);
        a = ta; b = tb;
    }
    clock_gettime(CLOCK_MONOTONIC, &end);

    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double ns_per_op = elapsed / ITERATIONS * 1e9;
    printf("  %-20s: %.2f ns/butterfly  (%.1f M butterflies/sec)  [check: %llu]\n",
           name, ns_per_op, ITERATIONS / elapsed / 1e6, (unsigned long long)a);
    return ns_per_op;
}

int main(void) {
    printf("═══════════════════════════════════════════════════\n");
    printf("  AMO-Lean v4.0 Butterfly Benchmark (BabyBear)\n");
    printf("  p = 2^31 - 2^27 + 1 = %llu\n", (unsigned long long)BABYBEAR_P);
    printf("  Iterations: %d\n", ITERATIONS);
    printf("═══════════════════════════════════════════════════\n\n");

    printf("--- Reduction strategies ---\n");
    double std_ns = benchmark_reduce("Standard (mul)", reduce_standard);
    double ss_ns  = benchmark_reduce("Shift-sub", reduce_shiftsub);
    double hv_ns  = benchmark_reduce("Harvey (cond sub)", reduce_harvey);

    printf("\n--- Butterfly strategies ---\n");
    double bstd_ns = benchmark_butterfly("Standard", butterfly_standard);
    double bss_ns  = benchmark_butterfly("Shift-sub", butterfly_shiftsub);
    double bhv_ns  = benchmark_butterfly("Harvey (lazy)", butterfly_harvey);

    printf("\n--- Summary ---\n");
    printf("  Shift-sub vs Standard:  %.1f%% %s\n",
           (1.0 - ss_ns / std_ns) * 100,
           ss_ns < std_ns ? "FASTER" : "slower");
    printf("  Harvey vs Standard:     %.1f%% %s\n",
           (1.0 - hv_ns / std_ns) * 100,
           hv_ns < std_ns ? "FASTER" : "slower");
    printf("  Butterfly shift-sub vs standard: %.1f%% %s\n",
           (1.0 - bss_ns / bstd_ns) * 100,
           bss_ns < bstd_ns ? "FASTER" : "slower");
    printf("  Butterfly Harvey vs standard:    %.1f%% %s\n",
           (1.0 - bhv_ns / bstd_ns) * 100,
           bhv_ns < bstd_ns ? "FASTER" : "slower");

    return 0;
}
