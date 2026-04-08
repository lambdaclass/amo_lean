/*
 * Per-Stage NTT Profiler (B35-5)
 *
 * Measures the time of each NTT stage independently using the sqdmulh butterfly.
 * This avoids instrumenting generated code — we replicate the stage structure
 * and measure each stage's loop separately.
 *
 * Usage: ./bench_per_stage [logN] [iters]
 *        Default: logN=16 (N=65536), iters=100
 */
#include <arm_neon.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define P 2013265921U
#define MU 0x88000001U

/* sqdmulh butterfly (copy from generated code) */
static inline void neon_bf_dit_sq(int32_t* a_ptr, int32_t* b_ptr,
    const int32_t* tw_ptr, const int32_t* mu_tw_ptr,
    int32x4_t p_vec_s, uint32x4_t p_vec) {
  int32x4_t a = vld1q_s32(a_ptr);
  int32x4_t b = vld1q_s32(b_ptr);
  int32x4_t tw = vld1q_s32(tw_ptr);
  int32x4_t mu_tw = vld1q_s32(mu_tw_ptr);
  int32x4_t c_hi  = vqdmulhq_s32(tw, b);
  int32x4_t q     = vmulq_s32(b, mu_tw);
  int32x4_t qp_hi = vqdmulhq_s32(q, p_vec_s);
  int32x4_t d     = vhsubq_s32(c_hi, qp_hi);
  uint32x4_t uf   = vcltq_s32(c_hi, qp_hi);
  int32x4_t wb    = vreinterpretq_s32_u32(
      vmlsq_u32(vreinterpretq_u32_s32(d), uf, p_vec));
  int32x4_t sum_s = vaddq_s32(a, wb);
  uint32x4_t su   = vreinterpretq_u32_s32(sum_s);
  uint32x4_t sum_canon = vminq_u32(su, vsubq_u32(su, p_vec));
  int32x4_t dif_s = vsubq_s32(a, wb);
  uint32x4_t du   = vreinterpretq_u32_s32(dif_s);
  uint32x4_t dif_canon = vminq_u32(du, vaddq_u32(du, p_vec));
  vst1q_s32(a_ptr, vreinterpretq_s32_u32(sum_canon));
  vst1q_s32(b_ptr, vreinterpretq_s32_u32(dif_canon));
}

/* Scalar butterfly for stages with halfSize < 4 */
static inline void scalar_bf(int32_t* a_ptr, int32_t* b_ptr,
    int32_t tw, int32_t mu_tw_val) {
  int64_t a = *a_ptr, b_val = *b_ptr;
  /* Simple modular butterfly for profiling */
  int64_t wb = ((int64_t)tw * b_val) % P;
  *a_ptr = (int32_t)(((int64_t)a + wb) % P);
  *b_ptr = (int32_t)(((int64_t)a + P - wb) % P);
}

static double elapsed_us(struct timespec *t0, struct timespec *t1) {
    return (t1->tv_sec - t0->tv_sec) * 1e6 + (t1->tv_nsec - t0->tv_nsec) / 1e3;
}

int main(int argc, char **argv) {
    int logN = (argc > 1) ? atoi(argv[1]) : 16;
    int iters = (argc > 2) ? atoi(argv[2]) : 100;
    int n = 1 << logN;
    int lanes = 4;

    int32_t *data = (int32_t *)aligned_alloc(64, n * sizeof(int32_t));
    int32_t *orig = (int32_t *)aligned_alloc(64, n * sizeof(int32_t));
    int tw_sz = (n / 2) * logN;
    int32_t *tw   = (int32_t *)malloc(tw_sz * sizeof(int32_t));
    int32_t *mu_tw = (int32_t *)malloc(tw_sz * sizeof(int32_t));

    /* Init data */
    for (int i = 0; i < n; i++)
        orig[i] = (int32_t)(((uint64_t)i * 1000000007ULL) % P);

    /* Init twiddles (simplified — just needs valid values for profiling) */
    for (int i = 0; i < tw_sz; i++) {
        tw[i] = (int32_t)(((uint64_t)(i * 7 + 31)) % P);
        mu_tw[i] = (int32_t)(((uint64_t)(uint32_t)tw[i] * (uint64_t)MU) & 0xFFFFFFFFULL);
    }

    uint32x4_t p_vec = vdupq_n_u32(P);
    int32x4_t p_vec_s = vdupq_n_s32((int32_t)P);

    double stage_us[32] = {0};
    struct timespec t0, t1;

    /* Warmup */
    memcpy(data, orig, n * sizeof(int32_t));
    for (int st = 0; st < logN; st++) {
        int halfSize = n >> (st + 1);
        int numGroups = 1 << st;
        int twBase = st * (n / 2);
        for (int grp = 0; grp < numGroups; grp++) {
            if (halfSize >= lanes) {
                for (int pr = 0; pr < halfSize; pr += lanes) {
                    int i = grp * 2 * halfSize + pr;
                    int j = i + halfSize;
                    int tw_idx = twBase + grp * halfSize + pr;
                    neon_bf_dit_sq(&data[i], &data[j], &tw[tw_idx], &mu_tw[tw_idx], p_vec_s, p_vec);
                }
            } else {
                for (int pr = 0; pr < halfSize; pr++) {
                    int i = grp * 2 * halfSize + pr;
                    int j = i + halfSize;
                    int tw_idx = twBase + grp * halfSize + pr;
                    scalar_bf(&data[i], &data[j], tw[tw_idx], mu_tw[tw_idx]);
                }
            }
        }
    }

    /* Profiled runs */
    for (int it = 0; it < iters; it++) {
        memcpy(data, orig, n * sizeof(int32_t));
        for (int st = 0; st < logN; st++) {
            int halfSize = n >> (st + 1);
            int numGroups = 1 << st;
            int twBase = st * (n / 2);

            clock_gettime(CLOCK_MONOTONIC, &t0);

            for (int grp = 0; grp < numGroups; grp++) {
                if (halfSize >= lanes) {
                    for (int pr = 0; pr < halfSize; pr += lanes) {
                        int i = grp * 2 * halfSize + pr;
                        int j = i + halfSize;
                        int tw_idx = twBase + grp * halfSize + pr;
                        neon_bf_dit_sq(&data[i], &data[j], &tw[tw_idx], &mu_tw[tw_idx], p_vec_s, p_vec);
                    }
                } else {
                    for (int pr = 0; pr < halfSize; pr++) {
                        int i = grp * 2 * halfSize + pr;
                        int j = i + halfSize;
                        int tw_idx = twBase + grp * halfSize + pr;
                        scalar_bf(&data[i], &data[j], tw[tw_idx], mu_tw[tw_idx]);
                    }
                }
            }

            clock_gettime(CLOCK_MONOTONIC, &t1);
            stage_us[st] += elapsed_us(&t0, &t1);
        }
    }

    /* Report */
    double total = 0;
    for (int s = 0; s < logN; s++) {
        stage_us[s] /= iters;
        total += stage_us[s];
    }

    printf("# Per-Stage NTT Profiling: BabyBear N=2^%d (%d elements), %d iters\n", logN, n, iters);
    printf("# stage, time_us, pct, halfSize, stride_bytes, type\n");
    for (int s = 0; s < logN; s++) {
        int halfSize = n >> (s + 1);
        int stride_bytes = halfSize * 4;
        const char *stype = (halfSize >= lanes) ? "SIMD" : "scalar";
        printf("stage,%d,%.1f,%.1f,%d,%d,%s\n",
               s, stage_us[s], 100.0 * stage_us[s] / total,
               halfSize, stride_bytes, stype);
    }
    printf("total,%.1f\n", total);

    /* Group summary */
    double early = 0, mid = 0, late = 0;
    for (int s = 0; s < logN; s++) {
        int halfSize = n >> (s + 1);
        if (halfSize >= 8192) early += stage_us[s];
        else if (halfSize >= 64) mid += stage_us[s];
        else late += stage_us[s];
    }
    printf("# Group summary:\n");
    printf("# Early (halfSize>=8192): %.1f us (%.1f%%)\n", early, 100*early/total);
    printf("# Mid   (64<=hs<8192):   %.1f us (%.1f%%)\n", mid, 100*mid/total);
    printf("# Late  (hs<64):         %.1f us (%.1f%%)\n", late, 100*late/total);

    free(data); free(orig); free(tw); free(mu_tw);
    return 0;
}
