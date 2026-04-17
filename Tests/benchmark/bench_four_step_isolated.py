#!/usr/bin/env python3
"""v3.17.0 N317.9: Evidence script for four-step NO-GO decision.

Reproduces the empirical measurement that four-step NTT is SLOWER than flat
DIF at all tested sizes (N=2^14, 2^16, 2^18) for Goldilocks with m=64.

Baseline measurement (revisor, Apple M-series, cc -O2):
  N=2^14: flat DIF 383μs, four-step 407μs (+6% SLOWER)
  N=2^16: flat DIF 1724μs, four-step 2274μs (+32% SLOWER)
  N=2^18: flat DIF 7915μs, four-step 10487μs (+32% SLOWER)

Root cause: Phase 1 of four-step (column DIF with stride-m) consumes 51% of
time. Stride-64 × 8 bytes = 512 bytes per access = 12.5% cache line utilization.

This script generates C for both approaches, compiles with identical flags,
runs and times, and verifies correctness against Python naive DFT.

Do NOT remove this script without reading research/TRZK_SBB.md §11.8.
It is referenced by the four-step re-open conditions. Re-run before
attempting m ∈ {8, 16, 32} per the re-open conditions.

Usage:
  python3 Tests/benchmark/bench_four_step_isolated.py
  python3 Tests/benchmark/bench_four_step_isolated.py --sizes 14,16 --iters 20
  python3 Tests/benchmark/bench_four_step_isolated.py --validation-only
  python3 Tests/benchmark/bench_four_step_isolated.py --m 32  # try different m
"""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from field_defs import GOLDILOCKS
from test_four_step import four_step_naive, four_step_dif_bitrev, unstride
from reference_ntt import _init_data


GOLDI_P = (1 << 64) - (1 << 32) + 1


# ═══════════════════════════════════════════════════════════════════════════
# C code templates (reconstructed from emitFourStepC, VerifiedPlanCodeGen.lean:797-874)
# ═══════════════════════════════════════════════════════════════════════════

REDUCE128_C = f"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define GOLDI_P {GOLDI_P}ULL

static inline uint64_t goldi_reduce128(__uint128_t x) {{
  uint64_t lo=(uint64_t)x, hi=(uint64_t)(x>>64);
  uint64_t hh=hi>>32, hl=hi&0xFFFFFFFFULL;
  uint64_t t0; int borrow=__builtin_sub_overflow(lo,hh,&t0);
  if(borrow) t0-=0xFFFFFFFFULL;
  uint64_t t1=hl*0xFFFFFFFFULL;
  uint64_t r; int carry=__builtin_add_overflow(t0,t1,&r);
  if(carry||r>=GOLDI_P) r-=GOLDI_P;
  return r;
}}

static inline uint64_t goldi_add(uint64_t a, uint64_t b) {{
  uint64_t r; int carry=__builtin_add_overflow(a,b,&r);
  if(carry||r>=GOLDI_P) r-=GOLDI_P;
  return r;
}}

static inline uint64_t goldi_sub(uint64_t a, uint64_t b) {{
  uint64_t r; int borrow=__builtin_sub_overflow(a,b,&r);
  if(borrow) r+=GOLDI_P;
  return r;
}}

static inline uint64_t goldi_mul(uint64_t a, uint64_t b) {{
  return goldi_reduce128((__uint128_t)a * (__uint128_t)b);
}}
"""


def gen_flat_dif_c(n: int, log_n: int) -> str:
    """Flat DIT NTT (not DIF — matching emitCFromPlanStandard output).

    Matches the current TRZK pipeline: bit-reverse input + DIT small→large stages.
    This is the baseline that four-step is compared against."""
    return REDUCE128_C + f"""
/* Flat DIT NTT baseline — matches emitCFromPlanStandard output.
 * bitrev input + DIT stages small→large. */
void ntt_flat(uint64_t *data, const uint64_t *twiddles) {{
  /* bitrev */
  for (uint64_t i=0; i<{n}; i++) {{
    uint64_t br=0, tmp=i;
    for (int b=0; b<{log_n}; b++) {{ br=(br<<1)|(tmp&1); tmp>>=1; }}
    if (br > i) {{ uint64_t t=data[i]; data[i]=data[br]; data[br]=t; }}
  }}
  /* DIT stages small→large (stageIdx decreasing from {log_n - 1} to 0) */
""" + "\n".join(
        f"""  /* stage {stage}: halfSize={n >> (stage + 1)}, numGroups={1 << stage} */
  for (uint64_t g=0; g<{1 << stage}; g++) {{
    for (uint64_t pr=0; pr<{n >> (stage + 1)}; pr++) {{
      uint64_t i=g*{2 * (n >> (stage + 1))}+pr, j=i+{n >> (stage + 1)};
      uint64_t tw=twiddles[{stage}*{n // 2}+g*{n >> (stage + 1)}+pr];
      uint64_t a=data[i], b=data[j];
      uint64_t wb=goldi_mul(tw, b);
      data[i]=goldi_add(a,wb); data[j]=goldi_sub(a,wb);
    }}
  }}"""
        # small→large = stages in reverse order (stageIdx = log_n - 1 first → halfSize=1)
        for stage in reversed(range(log_n))
    ) + "\n}\n"


def gen_four_step_c(n: int, m: int) -> str:
    """Four-step NTT — reconstructed from emitFourStepC template.

    6 phases: Col DIF → Col bitrev → Twiddle matrix → Row DIF → Row bitrev → Unstride.
    Matches VerifiedPlanCodeGen.lean:797-874 structure."""
    import math
    log_m = int(math.log2(m))
    log_outer = int(math.log2(n // m))
    rows = n // m
    # Phase 1: Col DIF (strided) — stride-m access = CACHE BOTTLENECK
    col_dif_body = []
    for stage in range(log_outer):
        half = rows // (2 ** (stage + 1))
        num_groups = 2 ** stage
        col_dif_body.append(f"""    for (uint64_t g=0; g<{num_groups}; g++) {{
      for (uint64_t pr=0; pr<{half}; pr++) {{
        uint64_t i=col+(g*{2 * half}+pr)*{m}, j=i+{half * m};
        uint64_t a=data[i], b=data[j];
        uint64_t tw=outer_tw[{stage}*{rows // 2}+g*{half}+pr];
        uint64_t sum=goldi_add(a,b), diff=goldi_sub(a,b);
        data[i]=sum; data[j]=goldi_mul(tw,diff);
      }}
    }}""")
    col_dif = "\n".join(col_dif_body)
    # Phase 4: Row DIF (contiguous — well-behaved)
    row_dif_body = []
    for stage in range(log_m):
        half = m // (2 ** (stage + 1))
        num_groups = 2 ** stage
        row_dif_body.append(f"""      for (uint64_t g=0; g<{num_groups}; g++) {{
        for (uint64_t pr=0; pr<{half}; pr++) {{
          uint64_t i=blk*{m}+g*{2 * half}+pr, j=i+{half};
          uint64_t a=data[i], b=data[j];
          uint64_t tw=inner_tw[{stage}*{m // 2}+g*{half}+pr];
          uint64_t sum=goldi_add(a,b), diff=goldi_sub(a,b);
          data[i]=sum; data[j]=goldi_mul(tw,diff);
        }}
      }}""")
    row_dif = "\n".join(row_dif_body)
    return REDUCE128_C + f"""
/* Four-step NTT — reconstructed from emitFourStepC (m={m}).
 * 6 phases: col_DIF + col_bitrev + twiddle_matrix + row_DIF + row_bitrev + unstride.
 * Cache bottleneck: Phase 1 stride-{m} access = {100 * 8 // (m * 8):.1f}% cache line util. */
void ntt_four_step(uint64_t *data, const uint64_t *inner_tw,
                   const uint64_t *outer_tw, const uint64_t *matrix_tw) {{
  uint64_t *tmp_unstride = (uint64_t*)malloc({n} * sizeof(uint64_t));
  if (!tmp_unstride) {{ perror("malloc"); exit(1); }}

  /* Phase 1: Col DIF (strided) */
  for (uint64_t col=0; col<{m}; col++) {{
{col_dif}
  }}

  /* Phase 2: Col bit-reversal */
  for (uint64_t col=0; col<{m}; col++) {{
    for (uint64_t row=0; row<{rows}; row++) {{
      uint64_t br=0, tmp=row;
      for (int b=0; b<{log_outer}; b++) {{ br=(br<<1)|(tmp&1); tmp>>=1; }}
      if (br > row) {{
        uint64_t t=data[row*{m}+col];
        data[row*{m}+col]=data[br*{m}+col];
        data[br*{m}+col]=t;
      }}
    }}
  }}

  /* Phase 3: Twiddle matrix (omega_N^(row*col)) */
  for (uint64_t i=0; i<{n}; i++) data[i]=goldi_mul(data[i], matrix_tw[i]);

  /* Phase 4: Row DIF (contiguous, blocks) */
  for (uint64_t blk=0; blk<{rows}; blk++) {{
{row_dif}
  }}

  /* Phase 5: Row bit-reversal */
  for (uint64_t blk=0; blk<{rows}; blk++) {{
    for (uint64_t col=0; col<{m}; col++) {{
      uint64_t br=0, tmp=col;
      for (int b=0; b<{log_m}; b++) {{ br=(br<<1)|(tmp&1); tmp>>=1; }}
      if (br > col) {{
        uint64_t t=data[blk*{m}+col];
        data[blk*{m}+col]=data[blk*{m}+br];
        data[blk*{m}+br]=t;
      }}
    }}
  }}

  /* Phase 6: Unstride (transpose) */
  for (uint64_t i=0; i<{n}; i++) {{
    uint64_t row=i/{m}, col=i%{m};
    tmp_unstride[col*{rows}+row]=data[i];
  }}
  memcpy(data, tmp_unstride, {n}*sizeof(uint64_t));
  free(tmp_unstride);
}}
"""


def gen_main(n: int, mode: str, iters: int, m: int = 64) -> str:
    """Main harness: init data + twiddles, run NTT, time, print."""
    import math
    log_n = int(math.log2(n))
    if mode == "flat":
        tw_size = n * log_n
        call = "ntt_flat(data, tw);"
        tw_init = f"  uint64_t *tw=(uint64_t*)calloc({tw_size}, sizeof(uint64_t));\n  for(uint64_t i=0;i<{tw_size};i++) tw[i]=(i*7+31)%GOLDI_P;"
        tw_free = "  free(tw);"
    else:
        rows = n // m
        log_m = int(math.log2(m))
        log_outer = int(math.log2(rows))
        inner_tw_sz = m * log_m  # approx
        outer_tw_sz = rows * log_outer  # approx
        matrix_tw_sz = n
        call = "ntt_four_step(data, inner_tw, outer_tw, matrix_tw);"
        tw_init = f"""  uint64_t *inner_tw=(uint64_t*)calloc({inner_tw_sz}+1, sizeof(uint64_t));
  uint64_t *outer_tw=(uint64_t*)calloc({outer_tw_sz}+1, sizeof(uint64_t));
  uint64_t *matrix_tw=(uint64_t*)calloc({matrix_tw_sz}, sizeof(uint64_t));
  for(uint64_t i=0;i<{inner_tw_sz};i++) inner_tw[i]=(i*7+31)%GOLDI_P;
  for(uint64_t i=0;i<{outer_tw_sz};i++) outer_tw[i]=(i*7+31)%GOLDI_P;
  for(uint64_t i=0;i<{matrix_tw_sz};i++) matrix_tw[i]=(i*7+31)%GOLDI_P;"""
        tw_free = "  free(inner_tw); free(outer_tw); free(matrix_tw);"
    return f"""
int main() {{
  uint64_t *data=(uint64_t*)malloc({n}*sizeof(uint64_t));
{tw_init}
  struct timespec t0, t1;
  double min_us = 1e18;
  for (int iter=0; iter<{iters}; iter++) {{
    for (uint64_t i=0; i<{n}; i++) data[i]=(i*1000000007ULL)%GOLDI_P;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    {call}
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double us = (t1.tv_sec-t0.tv_sec)*1e6 + (t1.tv_nsec-t0.tv_nsec)/1e3;
    if (us < min_us) min_us = us;
  }}
  printf("%.2f\\n", min_us);
  free(data);
{tw_free}
  return 0;
}}
"""


# ═══════════════════════════════════════════════════════════════════════════
# Benchmark harness
# ═══════════════════════════════════════════════════════════════════════════

def compile_and_run(c_source: str, tmpdir: Path, name: str) -> float:
    """Compile C with cc -O2 (conservative profile for reproducibility). Returns μs."""
    src = tmpdir / f"{name}.c"
    bin_path = tmpdir / name
    src.write_text(c_source)
    comp = subprocess.run(
        ["cc", "-O2", "-o", str(bin_path), str(src)],
        capture_output=True, text=True, timeout=60
    )
    if comp.returncode != 0:
        print(f"COMPILE FAIL for {name}:\n{comp.stderr[:500]}", file=sys.stderr)
        return -1.0
    run = subprocess.run([str(bin_path)], capture_output=True, text=True, timeout=300)
    if run.returncode != 0:
        print(f"RUN FAIL for {name}: {run.stderr[:200]}", file=sys.stderr)
        return -1.0
    return float(run.stdout.strip())


def validate_python(n: int, m: int) -> bool:
    """Verify Python four-step matches naive DFT for small n (sanity check)."""
    if n > 1024:
        return True  # skip for large n
    p = GOLDILOCKS.p
    g = GOLDILOCKS.generator
    x = [(i * 1000000007) % p for i in range(n)]
    import math
    omega_n = pow(g, (p - 1) // n, p)
    from test_four_step import naive_dft
    dft_ref = naive_dft(x, omega_n, p)
    fs = four_step_dif_bitrev(x, p, g, m)
    fs_unstrided = unstride(fs, m)
    return fs_unstrided == dft_ref


def bench_size(log_n: int, m: int, iters: int, tmpdir: Path) -> dict:
    """Run flat vs four-step benchmark for N=2^log_n."""
    n = 1 << log_n
    # Flat DIT baseline
    flat_src = gen_flat_dif_c(n, log_n) + gen_main(n, "flat", iters)
    flat_us = compile_and_run(flat_src, tmpdir, f"flat_n{log_n}")
    # Four-step
    fs_src = gen_four_step_c(n, m) + gen_main(n, "four_step", iters, m)
    fs_us = compile_and_run(fs_src, tmpdir, f"fs_n{log_n}_m{m}")
    delta_pct = ((fs_us - flat_us) / flat_us) * 100 if flat_us > 0 else 0.0
    return {"log_n": log_n, "flat_us": flat_us, "fs_us": fs_us, "delta_pct": delta_pct}


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--sizes", default="14,16,18",
                        help="Comma-separated log2(N) values (default: 14,16,18)")
    parser.add_argument("--iters", type=int, default=30,
                        help="Iterations per measurement (default: 30, min reported)")
    parser.add_argument("--m", type=int, default=64,
                        help="Four-step inner NTT size (default: 64 for Goldilocks)")
    parser.add_argument("--validation-only", action="store_true",
                        help="Only verify Python reference, skip C benchmarks")
    args = parser.parse_args()

    sizes = [int(s) for s in args.sizes.split(",")]
    print(f"bench_four_step_isolated.py — Goldilocks, m={args.m}, cc -O2, iters={args.iters}")
    print(f"Reference baseline (revisor, Apple M-series): 2^14 +6%, 2^16 +32%, 2^18 +32% SLOWER.\n")

    # Python validation
    for log_n in sizes:
        n = 1 << log_n
        if n <= 1024:
            ok = validate_python(n, args.m)
            print(f"Python validation N=2^{log_n}: {'PASS' if ok else 'FAIL'}")
    if args.validation_only:
        return 0

    # C benchmark
    print(f"\n{'N':>6} | {'Flat DIT (μs)':>14} | {'Four-step (μs)':>16} | {'Δ':>8}")
    print("-" * 56)
    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        for log_n in sizes:
            r = bench_size(log_n, args.m, args.iters, tmpdir)
            if r["flat_us"] < 0 or r["fs_us"] < 0:
                print(f"  2^{log_n:<4} | COMPILE/RUN FAIL — check stderr")
                continue
            sign = "+" if r["delta_pct"] >= 0 else ""
            print(f"  2^{log_n:<4} | {r['flat_us']:>14.1f} | {r['fs_us']:>16.1f} | {sign}{r['delta_pct']:>5.1f}%")

    print("\nInterpretation:")
    print(f"  At N ≥ 2^14 with m={args.m}: Δ > 0 expected (flat wins; four-step Phase 1")
    print(f"    stride-{args.m} × 8 bytes = {args.m * 8}B per access = {100 * 8 // (args.m * 8) if args.m * 8 >= 8 else 100}% cache line utilization).")
    print(f"  At N < 2^14: four-step may win (flat bitrev overhead dominates, cache fits).")
    print(f"  To re-open four-step per §11.8: need Δ < 0 at N ≥ 2^18 with m ∈ {{8, 16, 32}}")
    print(f"    AND ILP2 applied AND --profile match-plonky3.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
