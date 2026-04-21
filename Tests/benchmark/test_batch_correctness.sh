#!/usr/bin/env bash
# v3.20.b B4 N20.4.5 Gate: batch emission correctness test.
#
# Emits single-vector + batch NTT for BabyBear N=2^6=64, B=4 via
# emit_batch_code.lean, writes a harness that (a) runs batch NTT on
# B*N=256 element buffer, (b) independently runs single-vector NTT on 4
# separate copies, (c) verifies byte-equivalence element-by-element.
#
# Gate passes if:
#   - lake env lean --run Tests/benchmark/emit_batch_code.lean succeeds
#   - emitted C compiles with cc -O2
#   - runtime output: "BATCH CORRECTNESS OK" + exit 0
#
# Linearity (±5% Phase 1 bridge) is trivial by construction — batch wrapper
# is a literal loop of B independent single-vector calls. A dedicated perf
# benchmark lives in B6 (`benchmark_batch.py`). This script is the
# CORRECTNESS gate for B4 closure.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJECT_ROOT"

LOGN=6    # N=64
BATCH=4   # 4 independent polys
FIELD=babybear

TMPDIR=$(mktemp -d /tmp/trzk_batch_gate.XXXXXX)
trap "rm -rf $TMPDIR" EXIT

echo "[GATE B4] Emitting batch C (field=$FIELD, logN=$LOGN, B=$BATCH)..."
{
  echo '#include <stdint.h>'
  echo '#include <stddef.h>'
  lake env lean --run Tests/benchmark/emit_batch_code.lean \
    $FIELD $LOGN $BATCH 2>/dev/null
} > "$TMPDIR/batch.c"

echo "[GATE B4] Writing test harness..."
cat > "$TMPDIR/main.c" <<'MAIN_EOF'
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define N 64
#define B 4
#define P 2013265921

void babybear_ntt_batch(int32_t* data_base, const int32_t* twiddles, size_t B_);
void babybear_ntt_batch_single(int32_t* data, const int32_t* twiddles);

int main(void) {
  /* Deterministic input: poly b element i = (b * 7 + i * 13 + 1) mod P. */
  int32_t* batch_input = malloc(B * N * sizeof(int32_t));
  int32_t* batch_output = malloc(B * N * sizeof(int32_t));
  int32_t* single_output = malloc(B * N * sizeof(int32_t));
  int32_t* twiddles = malloc(N * sizeof(int32_t));
  for (int b = 0; b < B; b++)
    for (int i = 0; i < N; i++)
      batch_input[b * N + i] = (int32_t)(((b * 7 + i * 13 + 1) % P));
  /* Twiddles: arbitrary deterministic small Montgomery values.
     Not real roots of unity — test only checks byte-equivalence, not math. */
  for (int i = 0; i < N; i++)
    twiddles[i] = (int32_t)((i * 1664525 + 1013904223) % P);
  memcpy(batch_output, batch_input, B * N * sizeof(int32_t));
  memcpy(single_output, batch_input, B * N * sizeof(int32_t));
  /* Path A: batch wrapper (one call, processes all B polys). */
  babybear_ntt_batch(batch_output, twiddles, B);
  /* Path B: B independent single-vector calls. */
  for (int b = 0; b < B; b++)
    babybear_ntt_batch_single(single_output + b * N, twiddles);
  /* Compare */
  int mismatches = 0;
  for (int i = 0; i < B * N; i++)
    if (batch_output[i] != single_output[i]) {
      if (mismatches < 5)
        printf("MISMATCH [%d]: batch=%d single=%d\n",
               i, batch_output[i], single_output[i]);
      mismatches++;
    }
  if (mismatches == 0) {
    printf("BATCH CORRECTNESS OK (%d elements verified, %d polys)\n", B * N, B);
  } else {
    printf("FAIL: %d mismatches out of %d elements\n", mismatches, B * N);
  }
  free(batch_input); free(batch_output); free(single_output); free(twiddles);
  return mismatches == 0 ? 0 : 1;
}
MAIN_EOF

echo "[GATE B4] Compiling (cc -O2)..."
cc -O2 -o "$TMPDIR/test" "$TMPDIR/batch.c" "$TMPDIR/main.c"

echo "[GATE B4] Running harness..."
"$TMPDIR/test"

echo "[GATE B4] PASS"
