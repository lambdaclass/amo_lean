/*
 * bench_ntt_interleaved.c — Interleaved vs Sequential NEON NTT Benchmark
 *
 * Compares:
 *   1. Sequential: 1 butterfly at a time (current)
 *   2. Interleaved: 2 butterflies overlapped (scheduling optimization)
 *   3. Plonky3 scalar Montgomery (baseline)
 *
 * Compile: cc -O2 -o bench_ntt_interleaved bench_ntt_interleaved.c
 * Run:     ./bench_ntt_interleaved
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <arm_neon.h>

#define P_VAL  0x78000001
#define MU_VAL ((int32_t)0x88000001)
#define BABYBEAR_P 0x78000001U

static const int32x4_t v_p  = {P_VAL, P_VAL, P_VAL, P_VAL};
static const int32x4_t v_mu = {MU_VAL, MU_VAL, MU_VAL, MU_VAL};

/* ═══ Single NEON Montgomery butterfly ═══ */
static inline void monty_bf_single(int32x4_t *a, int32x4_t *b, int32x4_t w) {
    int32x4_t orig_a = *a;
    int32x4_t wb = vmulq_s32(w, *b);
    int32x4_t mu_rhs = vmulq_s32(*b, v_mu);
    int32x4_t c_hi = vqdmulhq_s32(orig_a, wb);
    int32x4_t q = vmulq_s32(orig_a, mu_rhs);
    int32x4_t qp_hi = vqdmulhq_s32(q, v_p);
    int32x4_t d = vhsubq_s32(c_hi, qp_hi);
    uint32x4_t uf = vcltq_s32(c_hi, qp_hi);
    int32x4_t wb_red = vreinterpretq_s32_u32(
        vmlsq_u32(vreinterpretq_u32_s32(d), uf, vreinterpretq_u32_s32(v_p)));

    int32x4_t sum_raw = vaddq_s32(orig_a, wb_red);
    uint32x4_t su = vreinterpretq_u32_s32(sum_raw);
    *a = vreinterpretq_s32_u32(vminq_u32(su, vsubq_u32(su, vreinterpretq_u32_s32(v_p))));

    int32x4_t dif_raw = vsubq_s32(orig_a, wb_red);
    uint32x4_t du = vreinterpretq_u32_s32(dif_raw);
    *b = vreinterpretq_s32_u32(vminq_u32(du, vaddq_u32(du, vreinterpretq_u32_s32(v_p))));
}

/* ═══ 2-butterfly interleaved Montgomery ═══ */
static inline void monty_bf_interleaved(
    int32x4_t *a0, int32x4_t *b0, int32x4_t w0,
    int32x4_t *a1, int32x4_t *b1, int32x4_t w1) {

    int32x4_t orig_a0 = *a0, orig_a1 = *a1;

    /* Phase 1: both multiplies start (interleaved to hide latency) */
    int32x4_t wb0 = vmulq_s32(w0, *b0);
    int32x4_t wb1 = vmulq_s32(w1, *b1);
    int32x4_t mu_rhs0 = vmulq_s32(*b0, v_mu);
    int32x4_t mu_rhs1 = vmulq_s32(*b1, v_mu);

    /* Phase 2: high products */
    int32x4_t c_hi0 = vqdmulhq_s32(orig_a0, wb0);
    int32x4_t c_hi1 = vqdmulhq_s32(orig_a1, wb1);
    int32x4_t q0 = vmulq_s32(orig_a0, mu_rhs0);
    int32x4_t q1 = vmulq_s32(orig_a1, mu_rhs1);

    /* Phase 3: reduction */
    int32x4_t qp_hi0 = vqdmulhq_s32(q0, v_p);
    int32x4_t qp_hi1 = vqdmulhq_s32(q1, v_p);

    /* Phase 4: combine */
    int32x4_t d0 = vhsubq_s32(c_hi0, qp_hi0);
    int32x4_t d1 = vhsubq_s32(c_hi1, qp_hi1);
    uint32x4_t uf0 = vcltq_s32(c_hi0, qp_hi0);
    uint32x4_t uf1 = vcltq_s32(c_hi1, qp_hi1);

    int32x4_t wb_red0 = vreinterpretq_s32_u32(
        vmlsq_u32(vreinterpretq_u32_s32(d0), uf0, vreinterpretq_u32_s32(v_p)));
    int32x4_t wb_red1 = vreinterpretq_s32_u32(
        vmlsq_u32(vreinterpretq_u32_s32(d1), uf1, vreinterpretq_u32_s32(v_p)));

    /* Phase 5: butterfly add/sub */
    int32x4_t s0 = vaddq_s32(orig_a0, wb_red0);
    uint32x4_t su0 = vreinterpretq_u32_s32(s0);
    *a0 = vreinterpretq_s32_u32(vminq_u32(su0, vsubq_u32(su0, vreinterpretq_u32_s32(v_p))));
    int32x4_t df0 = vsubq_s32(orig_a0, wb_red0);
    uint32x4_t du0 = vreinterpretq_u32_s32(df0);
    *b0 = vreinterpretq_s32_u32(vminq_u32(du0, vaddq_u32(du0, vreinterpretq_u32_s32(v_p))));

    int32x4_t s1 = vaddq_s32(orig_a1, wb_red1);
    uint32x4_t su1 = vreinterpretq_u32_s32(s1);
    *a1 = vreinterpretq_s32_u32(vminq_u32(su1, vsubq_u32(su1, vreinterpretq_u32_s32(v_p))));
    int32x4_t df1 = vsubq_s32(orig_a1, wb_red1);
    uint32x4_t du1 = vreinterpretq_u32_s32(df1);
    *b1 = vreinterpretq_s32_u32(vminq_u32(du1, vaddq_u32(du1, vreinterpretq_u32_s32(v_p))));
}

/* ═══ Scalar Montgomery baseline ═══ */
static inline uint32_t reduce_monty(uint64_t x) {
    uint64_t t = (x * 0x88000001ULL) & 0xFFFFFFFF;
    uint64_t u = t * (uint64_t)BABYBEAR_P;
    uint64_t d = x - u;
    uint32_t hi = (uint32_t)(d >> 32);
    return (x < u) ? hi + BABYBEAR_P : hi;
}

static inline void bf_scalar_monty(uint32_t *a, uint32_t *b, uint32_t w) {
    uint32_t oa = *a;
    uint32_t wb = reduce_monty((uint64_t)w * (uint64_t)(*b));
    uint32_t sum = oa + wb;
    if (sum >= BABYBEAR_P) sum -= BABYBEAR_P;
    *a = sum;
    *b = (oa >= wb) ? oa - wb : BABYBEAR_P - wb + oa;
}

/* ═══ NTT implementations ═══ */

static void ntt_sequential(int32_t *data, size_t n, const int32_t *tw) {
    size_t log_n = 0;
    for (size_t t = n; t > 1; t >>= 1) log_n++;
    for (size_t s = 0; s < log_n; s++) {
        size_t half = 1 << (log_n - s - 1);
        for (size_t g = 0; g < (1u << s); g++) {
            for (size_t p = 0; p + 4 <= half; p += 4) {
                size_t i = g * 2 * half + p, j = i + half;
                int32x4_t a = vld1q_s32(&data[i]);
                int32x4_t b = vld1q_s32(&data[j]);
                int32x4_t w = vld1q_s32(&tw[s*(n/2) + g*half + p]);
                monty_bf_single(&a, &b, w);
                vst1q_s32(&data[i], a);
                vst1q_s32(&data[j], b);
            }
        }
    }
}

static void ntt_interleaved(int32_t *data, size_t n, const int32_t *tw) {
    size_t log_n = 0;
    for (size_t t = n; t > 1; t >>= 1) log_n++;
    for (size_t s = 0; s < log_n; s++) {
        size_t half = 1 << (log_n - s - 1);
        for (size_t g = 0; g < (1u << s); g++) {
            size_t p = 0;
            /* 2×4 interleaved = 8 butterflies per iteration */
            for (; p + 8 <= half; p += 8) {
                size_t i0 = g*2*half + p, j0 = i0 + half;
                size_t i1 = i0 + 4, j1 = i1 + half;
                size_t tw0 = s*(n/2) + g*half + p, tw1 = tw0 + 4;
                int32x4_t a0 = vld1q_s32(&data[i0]);
                int32x4_t b0 = vld1q_s32(&data[j0]);
                int32x4_t w0 = vld1q_s32(&tw[tw0]);
                int32x4_t a1 = vld1q_s32(&data[i1]);
                int32x4_t b1 = vld1q_s32(&data[j1]);
                int32x4_t w1 = vld1q_s32(&tw[tw1]);
                monty_bf_interleaved(&a0, &b0, w0, &a1, &b1, w1);
                vst1q_s32(&data[i0], a0);
                vst1q_s32(&data[j0], b0);
                vst1q_s32(&data[i1], a1);
                vst1q_s32(&data[j1], b1);
            }
            /* 4-wide tail */
            for (; p + 4 <= half; p += 4) {
                size_t i = g*2*half + p, j = i + half;
                int32x4_t a = vld1q_s32(&data[i]);
                int32x4_t b = vld1q_s32(&data[j]);
                int32x4_t w = vld1q_s32(&tw[s*(n/2) + g*half + p]);
                monty_bf_single(&a, &b, w);
                vst1q_s32(&data[i], a);
                vst1q_s32(&data[j], b);
            }
        }
    }
}

static void ntt_scalar(uint32_t *data, size_t n, const uint32_t *tw) {
    size_t log_n = 0;
    for (size_t t = n; t > 1; t >>= 1) log_n++;
    for (size_t s = 0; s < log_n; s++) {
        size_t half = 1 << (log_n - s - 1);
        for (size_t g = 0; g < (1u << s); g++)
            for (size_t p = 0; p < half; p++) {
                size_t i = g*2*half + p, j = i + half;
                bf_scalar_monty(&data[i], &data[j], tw[s*(n/2)+g*half+p]);
            }
    }
}

/* ═══ Benchmark ═══ */

typedef struct { const char *name; double us; } R;

static R bench(const char *name, size_t n, int iters,
    void (*fn)(int32_t*, size_t, const int32_t*)) {
    int32_t *data = malloc(n * sizeof(int32_t));
    int32_t *tw = malloc(n * sizeof(int32_t));
    for (size_t i = 0; i < n; i++) {
        tw[i] = (int32_t)((i * 7 + 31) % BABYBEAR_P);
    }
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++)
            data[i] = (int32_t)((i * 1000000007ULL) % BABYBEAR_P);
        fn(data, n, tw);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    double el = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double us = el / iters * 1e6;
    printf("  %-35s: %8.1f us  %6.1f Melem/s  [%d]\n",
           name, us, (double)n*iters/el/1e6, data[0]);
    free(data); free(tw);
    return (R){name, us};
}

static R bench_scalar(const char *name, size_t n, int iters) {
    uint32_t *data = malloc(n * sizeof(uint32_t));
    uint32_t *tw = malloc(n * sizeof(uint32_t));
    for (size_t i = 0; i < n; i++) {
        tw[i] = (uint32_t)((i * 7 + 31) % BABYBEAR_P);
    }
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int it = 0; it < iters; it++) {
        for (size_t i = 0; i < n; i++)
            data[i] = (uint32_t)((i * 1000000007ULL) % BABYBEAR_P);
        ntt_scalar(data, n, tw);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    double el = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    double us = el / iters * 1e6;
    printf("  %-35s: %8.1f us  %6.1f Melem/s  [%u]\n",
           name, us, (double)n*iters/el/1e6, data[0]);
    free(data); free(tw);
    return (R){name, us};
}

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║  NTT Scheduling Benchmark: Interleaved vs Sequential vs Scalar     ║\n");
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║  2-butterfly interleaving hides mul latency (3 cycles)             ║\n");
    printf("║  Theoretical: 50%% fewer pipeline stalls (14→7 cycles/butterfly)    ║\n");
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");

    size_t sizes[] = {256, 1024, 4096, 16384};
    int iters[] =    {10000, 5000, 1000, 200};

    for (int si = 0; si < 4; si++) {
        size_t n = sizes[si];
        int it = iters[si];
        printf("══ N = %zu ══\n\n", n);

        R r_sc = bench_scalar("Scalar Montgomery (Plonky3)", n, it);
        R r_seq = bench("NEON Sequential (current)", n, it, ntt_sequential);
        R r_int = bench("NEON Interleaved (scheduled)", n, it, ntt_interleaved);

        printf("\n");
        printf("  Interleaved vs Sequential: %+.1f%%\n", (1.0 - r_int.us/r_seq.us)*100);
        printf("  Interleaved vs Plonky3:    %+.1f%%\n", (1.0 - r_int.us/r_sc.us)*100);
        printf("  Sequential vs Plonky3:     %+.1f%%\n", (1.0 - r_seq.us/r_sc.us)*100);
        printf("\n");
    }

    printf("Legend:\n");
    printf("  Sequential:   1 NEON butterfly at a time (load→compute→store)\n");
    printf("  Interleaved:  2 NEON butterflies overlapped (A.mul ∥ B.load)\n");
    printf("  Scalar:       Plonky3-style u32 Montgomery (1 butterfly at a time)\n");
    return 0;
}
