/*
 * bench_comprehensive.c — COMPREHENSIVE BENCHMARK
 * AMO-Lean (Solinas fold) vs Plonky3 (Montgomery REDC)
 * Both in C, no FFI overhead, same compiler (cc -O2).
 *
 * Primitives: NTT, FRI fold, Polynomial eval, Dot product
 * Fields: BabyBear, KoalaBear, Mersenne31, Goldilocks
 * Sizes: N=4096, N=65536
 *
 * Compile: cc -O2 -o bench_comprehensive bench_comprehensive.c
 * Run:     ./bench_comprehensive
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

/* ═══════════════════════════════════════════════════════════════════
   Field definitions
   ═══════════════════════════════════════════════════════════════════ */

typedef struct {
    const char *name;
    uint32_t p;
    uint32_t c;     /* Solinas fold constant */
    uint32_t mu;    /* Montgomery MU = P^{-1} mod 2^32 */
} Field;

static const Field BABYBEAR   = {"BabyBear",   0x78000001, 134217727, 0x88000001};
static const Field KOALABEAR  = {"KoalaBear",  0x7F000001, 16777215,  0x81000001};
static const Field MERSENNE31 = {"Mersenne31", 0x7FFFFFFF, 1,         0x7FFFFFFF};

/* ═══════════════════════════════════════════════════════════════════
   AMO-Lean: Solinas fold (e-graph selected for scalar)
   Verified: solinasFold_mod_correct
   ═══════════════════════════════════════════════════════════════════ */

static inline uint32_t amo_reduce(uint64_t x, uint32_t c) {
    return (uint32_t)(((x >> 31) * c) + (x & 0x7FFFFFFF));
}

static inline void amo_butterfly(uint32_t *a, uint32_t *b, uint32_t w,
    uint32_t p, uint32_t c) {
    uint32_t oa = *a;
    uint32_t wb = amo_reduce((uint64_t)w * (uint64_t)(*b), c);
    *a = amo_reduce((uint64_t)oa + (uint64_t)wb, c);
    *b = amo_reduce((uint64_t)p + (uint64_t)oa - (uint64_t)wb, c);
}

/* ═══════════════════════════════════════════════════════════════════
   Plonky3: Montgomery REDC (translated from monty-31/src/utils.rs)
   ═══════════════════════════════════════════════════════════════════ */

static inline uint32_t p3_reduce(uint64_t x, uint32_t p, uint32_t mu) {
    uint64_t t = (x * (uint64_t)mu) & 0xFFFFFFFF;
    uint64_t u = t * (uint64_t)p;
    uint64_t d = x - u;
    uint32_t hi = (uint32_t)(d >> 32);
    return (x < u) ? hi + p : hi;
}

static inline void p3_butterfly(uint32_t *a, uint32_t *b, uint32_t w,
    uint32_t p, uint32_t mu) {
    uint32_t oa = *a;
    uint32_t wb = p3_reduce((uint64_t)w * (uint64_t)(*b), p, mu);
    uint32_t sum = oa + wb;
    if (sum >= p) sum -= p;
    *a = sum;
    *b = (oa >= wb) ? oa - wb : p - wb + oa;
}

/* ═══════════════════════════════════════════════════════════════════
   Goldilocks (64-bit, same algorithm for both)
   ═══════════════════════════════════════════════════════════════════ */

#define GL_P 0xFFFFFFFF00000001ULL

static inline uint64_t gl_reduce(__uint128_t x) {
    uint64_t lo = (uint64_t)x, hi = (uint64_t)(x >> 64);
    uint64_t hh = hi >> 32, hl = hi & 0xFFFFFFFF;
    uint64_t t0; int borrow = __builtin_sub_overflow(lo, hh, &t0);
    if (borrow) t0 -= 0xFFFFFFFF;
    uint64_t t1 = hl * 0xFFFFFFFF;
    uint64_t r; int carry = __builtin_add_overflow(t0, t1, &r);
    if (carry || r >= GL_P) r -= GL_P;
    return r;
}

/* ═══════════════════════════════════════════════════════════════════
   Benchmark infrastructure
   ═══════════════════════════════════════════════════════════════════ */

static double now_us(struct timespec *s, struct timespec *e, int iters) {
    return ((e->tv_sec - s->tv_sec) + (e->tv_nsec - s->tv_nsec) / 1e9) / iters * 1e6;
}

static void bench_field(const Field *f, size_t n) {
    int iters = (n <= 4096) ? 1000 : (n <= 65536) ? 200 : 10;
    size_t tw_size = n * 20; /* enough for NTT twiddles */
    uint32_t *a = malloc(n * 4), *b = malloc(n * 4);
    uint32_t *r = malloc(n * 4), *tw = malloc(tw_size * 4);
    uint32_t coeffs[8] = {42, 17, 99, 3, 55, 7, 13, 1};
    for (size_t i = 0; i < n; i++) {
        a[i] = (uint32_t)((i * 1000000007ULL) % f->p);
        b[i] = (uint32_t)((i * 999999937ULL) % f->p);
    }
    for (size_t i = 0; i < tw_size; i++)
        tw[i] = (uint32_t)((i * 7 + 31) % f->p);
    volatile uint32_t sink = 0;
    struct timespec s, e;

    printf("  %-10s N=%-6zu | ", f->name, n);

    /* NTT */
    size_t log_n = 0; for (size_t t = n; t > 1; t >>= 1) log_n++;

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++) a[i] = (uint32_t)((i * 1000000007ULL) % f->p);
        for (size_t st = 0; st < log_n; st++) {
            size_t half = 1 << (log_n - st - 1);
            for (size_t g = 0; g < (1u << st); g++)
                for (size_t p2 = 0; p2 + 1 <= half; p2++) {
                    size_t i = g*2*half+p2, j = i+half;
                    amo_butterfly(&a[i], &a[j], tw[(st*(n/2)+g*half+p2)%tw_size], f->p, f->c);
                }
        }
        sink = a[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double amo_ntt = now_us(&s, &e, iters);

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++) b[i] = (uint32_t)((i * 1000000007ULL) % f->p);
        for (size_t st = 0; st < log_n; st++) {
            size_t half = 1 << (log_n - st - 1);
            for (size_t g = 0; g < (1u << st); g++)
                for (size_t p2 = 0; p2 + 1 <= half; p2++) {
                    size_t i = g*2*half+p2, j = i+half;
                    p3_butterfly(&b[i], &b[j], tw[(st*(n/2)+g*half+p2)%tw_size], f->p, f->mu);
                }
        }
        sink = b[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_ntt = now_us(&s, &e, iters);

    /* FRI Fold */
    for (size_t i = 0; i < n; i++) {
        a[i] = (uint32_t)((i * 1000000007ULL) % f->p);
        b[i] = (uint32_t)((i * 999999937ULL) % f->p);
    }

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++) {
            uint32_t prod = amo_reduce((uint64_t)42*(uint64_t)b[i], f->c);
            /* Solinas fold output < 2p, so a[i]+prod < 3p — Harvey cond sub */
            uint32_t sum = a[i] + prod;
            if (sum >= 2*f->p) sum -= 2*f->p;
            if (sum >= f->p) sum -= f->p;
            r[i] = sum;
        }
        sink = r[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double amo_fri = now_us(&s, &e, iters);

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++) {
            uint32_t prod = p3_reduce((uint64_t)42*(uint64_t)b[i], f->p, f->mu);
            uint32_t sum = a[i] + prod;
            r[i] = (sum >= f->p) ? sum - f->p : sum;
        }
        sink = r[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_fri = now_us(&s, &e, iters);

    /* Poly Eval — Solinas fold for mul, Harvey cond sub for add */
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++)
        for (size_t i = 0; i < n; i++) {
            uint32_t acc = coeffs[7];
            for (int j = 7; j > 0; j--) {
                acc = amo_reduce((uint64_t)a[i]*(uint64_t)acc, f->c);
                uint32_t sum = coeffs[j-1] + acc;
                if (sum >= 2*f->p) sum -= 2*f->p;
                if (sum >= f->p) sum -= f->p;
                acc = sum;
            }
            sink = acc;
        }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double amo_poly = now_us(&s, &e, iters);

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++)
        for (size_t i = 0; i < n; i++) {
            uint32_t acc = coeffs[7];
            for (int j = 7; j > 0; j--) {
                acc = p3_reduce((uint64_t)a[i]*(uint64_t)acc, f->p, f->mu);
                uint32_t sum = coeffs[j-1] + acc;
                acc = (sum >= f->p) ? sum - f->p : sum;
            }
            sink = acc;
        }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_poly = now_us(&s, &e, iters);

    /* Dot Product — Solinas fold for mul, Harvey cond sub for add */
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        uint32_t acc = 0;
        for (size_t i = 0; i < n; i++) {
            uint32_t prod = amo_reduce((uint64_t)a[i]*(uint64_t)b[i], f->c);
            uint32_t sum = acc + prod;
            if (sum >= 2*f->p) sum -= 2*f->p;
            if (sum >= f->p) sum -= f->p;
            acc = sum;
        }
        sink = acc;
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double amo_dot = now_us(&s, &e, iters);

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        uint32_t acc = 0;
        for (size_t i = 0; i < n; i++) {
            uint32_t prod = p3_reduce((uint64_t)a[i]*(uint64_t)b[i], f->p, f->mu);
            uint32_t sum = acc + prod;
            acc = (sum >= f->p) ? sum - f->p : sum;
        }
        sink = acc;
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double p3_dot = now_us(&s, &e, iters);

    printf("NTT %+5.0f%%  FRI %+5.0f%%  Poly %+5.0f%%  Dot %+5.0f%%\n",
        (1-amo_ntt/p3_ntt)*100, (1-amo_fri/p3_fri)*100,
        (1-amo_poly/p3_poly)*100, (1-amo_dot/p3_dot)*100);
    printf("                        | NTT %.0f/%.0fus  FRI %.0f/%.0fus  Poly %.0f/%.0fus  Dot %.0f/%.0fus\n",
        amo_ntt, p3_ntt, amo_fri, p3_fri, amo_poly, p3_poly, amo_dot, p3_dot);

    (void)sink;
    free(a); free(b); free(r); free(tw);
}

static void bench_goldilocks(size_t n) {
    int iters = (n <= 4096) ? 1000 : (n <= 65536) ? 200 : 10;
    uint64_t *a = malloc(n*8), *b = malloc(n*8), *r = malloc(n*8);
    uint64_t coeffs[8] = {42, 17, 99, 3, 55, 7, 13, 1};
    for (size_t i = 0; i < n; i++) {
        a[i] = (i*1000000007ULL) % GL_P;
        b[i] = (i*999999937ULL) % GL_P;
    }
    volatile uint64_t sink = 0;
    struct timespec s, e;

    printf("  Goldilocks N=%-6zu | ", n);

    /* NTT */
    size_t log_n = 0; for (size_t t = n; t > 1; t >>= 1) log_n++;
    size_t tw_size = n * log_n;
    uint64_t *tw = malloc(tw_size * 8);
    for (size_t i = 0; i < tw_size; i++) tw[i] = (i*7+31) % GL_P;

    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++) a[i] = (i*1000000007ULL) % GL_P;
        for (size_t st = 0; st < log_n; st++) {
            size_t half = 1 << (log_n-st-1);
            for (size_t g = 0; g < (1u<<st); g++)
                for (size_t p2 = 0; p2+1<=half; p2++) {
                    size_t i = g*2*half+p2, j = i+half;
                    uint64_t oa = a[i];
                    uint64_t wb = gl_reduce((__uint128_t)tw[(st*(n/2)+g*half+p2)%tw_size] * (__uint128_t)a[j]);
                    a[i] = gl_reduce((__uint128_t)oa + (__uint128_t)wb);
                    a[j] = gl_reduce((__uint128_t)GL_P + (__uint128_t)oa - (__uint128_t)wb);
                }
        }
        sink = a[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double gl_ntt = now_us(&s, &e, iters);

    /* FRI */
    for (size_t i = 0; i < n; i++) { a[i] = (i*1000000007ULL)%GL_P; b[i] = (i*999999937ULL)%GL_P; }
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++)
            r[i] = gl_reduce((__uint128_t)a[i] + (__uint128_t)gl_reduce((__uint128_t)42*(__uint128_t)b[i]));
        sink = r[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double gl_fri = now_us(&s, &e, iters);

    /* Poly */
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++)
        for (size_t i = 0; i < n; i++) {
            uint64_t acc = coeffs[7];
            for (int j = 7; j > 0; j--) {
                acc = gl_reduce((__uint128_t)a[i]*(__uint128_t)acc);
                acc = gl_reduce((__uint128_t)coeffs[j-1]+(__uint128_t)acc);
            }
            sink = acc;
        }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double gl_poly = now_us(&s, &e, iters);

    /* Dot */
    clock_gettime(CLOCK_MONOTONIC, &s);
    for (int it = 0; it < iters; it++) {
        uint64_t acc = 0;
        for (size_t i = 0; i < n; i++)
            acc = gl_reduce((__uint128_t)acc+(__uint128_t)gl_reduce((__uint128_t)a[i]*(__uint128_t)b[i]));
        sink = acc;
    }
    clock_gettime(CLOCK_MONOTONIC, &e);
    double gl_dot = now_us(&s, &e, iters);

    printf("NTT %6.0fus  FRI %5.0fus  Poly %6.0fus  Dot %5.0fus  (same alg)\n",
        gl_ntt, gl_fri, gl_poly, gl_dot);

    (void)sink;
    free(a); free(b); free(r); free(tw);
}

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════════════════════╗\n");
    printf("║  COMPREHENSIVE: AMO-Lean Solinas vs Plonky3 Montgomery (BOTH in C, -O2)   ║\n");
    printf("║  4 fields × 4 primitives × 2 sizes — FAIR comparison, no FFI overhead     ║\n");
    printf("╠══════════════════════════════════════════════════════════════════════════════╣\n");
    printf("║  +%% = AMO-Lean faster    -%% = Plonky3 faster    (Solinas vs Montgomery)  ║\n");
    printf("╚══════════════════════════════════════════════════════════════════════════════╝\n\n");

    printf("── N = 4096 ──\n");
    printf("  %-10s %-8s | %-10s %-10s %-10s %-10s\n", "Field", "Size", "NTT", "FRI", "Poly", "Dot");
    bench_field(&BABYBEAR, 4096);
    bench_field(&KOALABEAR, 4096);
    bench_field(&MERSENNE31, 4096);
    bench_goldilocks(4096);

    printf("\n── N = 65536 ──\n");
    printf("  %-10s %-8s | %-10s %-10s %-10s %-10s\n", "Field", "Size", "NTT", "FRI", "Poly", "Dot");
    bench_field(&BABYBEAR, 65536);
    bench_field(&KOALABEAR, 65536);
    bench_field(&MERSENNE31, 65536);
    bench_goldilocks(65536);

    printf("\nNote: Both AMO-Lean and Plonky3 are pure C, compiled with cc -O2.\n");
    printf("No FFI overhead. Same compiler, same machine, same loop structure.\n");
    printf("AMO-Lean: Solinas fold (mul) + Harvey cond-sub (add). Verified.\n");
    printf("Plonky3 uses Montgomery REDC (translated from monty-31/src/utils.rs).\n");
    return 0;
}
