#!/usr/bin/env bash
# v3.20.b B4.5 N20.45.5 Performance Gate.
#
# Compares TRZK-loop (B4, linear layout + loop wrapping) vs TRZK-packed
# (B4.5, transpose + packed kernel + scalar fallback) at N=2^18 B=16 BabyBear.
#
# Gate criteria (from research/TRZK_b45_coder_prompt.md):
#   - Correctness: packed output = loop output (mod p) across all elements
#   - Perf: mean(packed) ≤ 0.50 × mean(loop)  [≥50% speedup, 2× amortization]
#   - CV: < 2% over 5 runs
#
# Verdict:
#   PASS    mean(packed) ≤ 0.50 × mean(loop)
#   PARTIAL 0.50 < mean(packed)/mean(loop) < 0.80  (1.25-2× amort, ESCALATE)
#   MVP     mean(packed) > 0.80 × mean(loop)  (no meaningful amort, escape)
#   FAIL    correctness issue
#
# Inputs: LOGN (default 18) and BATCH (default 16).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJECT_ROOT"

LOGN="${1:-18}"
BATCH="${2:-16}"
RUNS="${3:-5}"
FIELD=babybear
P=2013265921

TMPDIR=$(mktemp -d /tmp/trzk_packed_perf.XXXXXX)
trap "rm -rf $TMPDIR" EXIT

N=$((1 << LOGN))
echo "[B4.5 PERF GATE] field=$FIELD N=$N B=$BATCH runs=$RUNS"

# ── Emit loop path ──
echo "[B4.5 PERF GATE] Emitting loop path..."
{
  echo '#include <stdint.h>'
  echo '#include <stddef.h>'
  lake env lean --run Tests/benchmark/emit_batch_code.lean \
    $FIELD $LOGN $BATCH 2>/dev/null | \
    sed 's/babybear_ntt_batch/ntt_loop/g'
} > "$TMPDIR/loop.c"

# ── Emit packed path ──
echo "[B4.5 PERF GATE] Emitting packed path..."
{
  lake env lean --run Tests/benchmark/emit_packed_batch.lean \
    $FIELD $LOGN $BATCH 2>/dev/null | \
    sed 's/babybear_ntt_batch_packed/ntt_packed/g'
} > "$TMPDIR/packed.c"

# ── Harness with correctness + perf ──
cat > "$TMPDIR/main.c" <<MAIN_EOF
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

#define N $N
#define B $BATCH
#define P 2013265921
#define RUNS $RUNS

void ntt_loop(int32_t* data_base, const int32_t* twiddles, size_t B_);
void ntt_packed(int32_t* data_base, const int32_t* twiddles, size_t B_);

static double now_us(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3;
}

int main(void) {
  size_t total = (size_t)B * N;
  size_t tw_count = (size_t)$LOGN * N;
  int32_t* in_a = malloc(total * sizeof(int32_t));
  int32_t* in_b = malloc(total * sizeof(int32_t));
  int32_t* workbuf = malloc(total * sizeof(int32_t));
  int32_t* twiddles = malloc(tw_count * sizeof(int32_t));
  if (!in_a || !in_b || !workbuf || !twiddles) { fprintf(stderr, "malloc fail\n"); return 2; }
  for (size_t b = 0; b < B; b++)
    for (size_t i = 0; i < N; i++)
      in_a[b * N + i] = (int32_t)(((b * 7 + i * 13 + 1) % P));
  for (size_t i = 0; i < tw_count; i++)
    twiddles[i] = (int32_t)((i * 1664525 + 1013904223) % P);
  memcpy(in_b, in_a, total * sizeof(int32_t));
  /* Correctness — one-shot. */
  memcpy(workbuf, in_a, total * sizeof(int32_t));
  ntt_loop(workbuf, twiddles, B);
  int32_t* ref_out = malloc(total * sizeof(int32_t));
  memcpy(ref_out, workbuf, total * sizeof(int32_t));
  memcpy(workbuf, in_a, total * sizeof(int32_t));
  ntt_packed(workbuf, twiddles, B);
  int mismatches = 0;
  for (size_t k = 0; k < total; k++) {
    int64_t a = (uint32_t)ref_out[k], bb = (uint32_t)workbuf[k];
    int64_t diff_mod = ((a - bb) % P + P) % P;
    if (diff_mod != 0) mismatches++;
  }
  if (mismatches != 0) {
    printf("CORRECTNESS FAIL: %d mismatches / %zu\n", mismatches, total);
    return 1;
  }
  printf("CORRECTNESS OK (%zu elements)\n", total);
  /* Perf — RUNS iterations, report min-of-mins (conservative estimate). */
  double loop_times[RUNS], packed_times[RUNS];
  /* Warmup: one run each to populate caches */
  memcpy(workbuf, in_a, total * sizeof(int32_t)); ntt_loop(workbuf, twiddles, B);
  memcpy(workbuf, in_a, total * sizeof(int32_t)); ntt_packed(workbuf, twiddles, B);
  for (int r = 0; r < RUNS; r++) {
    memcpy(workbuf, in_a, total * sizeof(int32_t));
    double t0 = now_us();
    ntt_loop(workbuf, twiddles, B);
    loop_times[r] = now_us() - t0;
  }
  for (int r = 0; r < RUNS; r++) {
    memcpy(workbuf, in_a, total * sizeof(int32_t));
    double t0 = now_us();
    ntt_packed(workbuf, twiddles, B);
    packed_times[r] = now_us() - t0;
  }
  /* Stats */
  double loop_sum = 0, packed_sum = 0;
  double loop_min = loop_times[0], packed_min = packed_times[0];
  for (int r = 0; r < RUNS; r++) {
    loop_sum += loop_times[r]; packed_sum += packed_times[r];
    if (loop_times[r] < loop_min) loop_min = loop_times[r];
    if (packed_times[r] < packed_min) packed_min = packed_times[r];
  }
  double loop_mean = loop_sum / RUNS;
  double packed_mean = packed_sum / RUNS;
  /* CV */
  double loop_var = 0, packed_var = 0;
  for (int r = 0; r < RUNS; r++) {
    double dl = loop_times[r] - loop_mean, dp = packed_times[r] - packed_mean;
    loop_var += dl * dl; packed_var += dp * dp;
  }
  double loop_cv = sqrt(loop_var / RUNS) / loop_mean * 100.0;
  double packed_cv = sqrt(packed_var / RUNS) / packed_mean * 100.0;
  printf("\n--- PERF RESULTS (%d runs) ---\n", RUNS);
  printf("TRZK-loop    mean=%.1f μs  min=%.1f μs  CV=%.2f%%\n", loop_mean, loop_min, loop_cv);
  printf("TRZK-packed  mean=%.1f μs  min=%.1f μs  CV=%.2f%%\n", packed_mean, packed_min, packed_cv);
  double ratio = packed_mean / loop_mean;
  printf("Ratio (packed/loop mean): %.3f  (target ≤ 0.500)\n", ratio);
  if (ratio <= 0.50) {
    printf("VERDICT: PASS — ≥2× amortization achieved (%.1f%% of loop time)\n", ratio * 100);
    return 0;
  } else if (ratio < 0.80) {
    printf("VERDICT: PARTIAL — 1.25-2× amortization (packed is %.1f%% of loop)\n", ratio * 100);
    return 10;
  } else if (ratio < 1.0) {
    printf("VERDICT: MVP ESCAPE — marginal gain (packed is %.1f%% of loop, < 1.25× amort)\n", ratio * 100);
    return 20;
  } else {
    printf("VERDICT: REGRESSION — packed is SLOWER (%.1f%% of loop)\n", ratio * 100);
    return 30;
  }
  free(in_a); free(in_b); free(workbuf); free(twiddles); free(ref_out);
  return 0;
}
MAIN_EOF

echo "[B4.5 PERF GATE] Compiling..."
cc -O3 -mcpu=apple-m1 -o "$TMPDIR/test" \
  "$TMPDIR/loop.c" "$TMPDIR/packed.c" "$TMPDIR/main.c" -lm

echo "[B4.5 PERF GATE] Running..."
"$TMPDIR/test"
exit_code=$?

echo ""
echo "[B4.5 PERF GATE] Exit code: $exit_code"
exit $exit_code
