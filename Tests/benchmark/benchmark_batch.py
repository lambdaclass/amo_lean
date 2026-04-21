#!/usr/bin/env python3
"""
v3.20.b B6.1 — Python benchmark harness for TRZK batch NTT emission.

Measures TRZK batch emission (via `emit_batch_code.lean`, the B4
loop-wrapping path — production default post B4.5 MVP escape) across
(field × size × batch_width) combinations. Outputs JSON matching the
structure of `v3.19_b2_batch.json` for comparability with Plonky3-batch
reference numbers (BENCHMARKS §8b).

Compile flag policy: `-mcpu=apple-m1` throughout (lesson L-769,
glearnings §5.5/§5.7). Explicit, no fallback to `-march=armv8-a`.

Protocol:
- 5 process launches (fresh-compile-resistant per L-746)
- warmup=5 iters per launch
- measure=10 iters per launch
- reports: min_us, mean_us, median_us, std_us, cv_pct per combo
- min-of-mins across 5 launches is the conservative reported value

Usage:
    python3 Tests/benchmark/benchmark_batch.py \\
        --fields babybear,goldilocks --sizes 14,18,20 \\
        --batch-widths 1,4,8,16 --warmup 5 --iters 10 --launches 5
"""

import argparse
import json
import os
import shlex
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from datetime import datetime

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent

# Field parameters (BabyBear + Goldilocks). Solinas fold constants.
FIELDS = {
    "babybear": {"k": 31, "c": 134217727, "mu": "0x88000001", "p": 2013265921},
    "goldilocks": {"k": 64, "c": 1, "mu": "0x0", "p": 18446744069414584321},
}


def emit_batch_c(field: str, log_n: int, batch_width: int, outfile: Path) -> None:
    """Invoke emit_batch_code.lean to emit batch NTT C source to outfile."""
    cmd = ["lake", "env", "lean", "--run",
           str(PROJECT_ROOT / "Tests/benchmark/emit_batch_code.lean"),
           field, str(log_n), str(batch_width)]
    result = subprocess.run(
        cmd, cwd=str(PROJECT_ROOT),
        capture_output=True, text=True, timeout=180,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"emit_batch_code failed: field={field} logN={log_n} B={batch_width}\n"
            f"stderr: {result.stderr[:500]}")
    # Prepend required headers (emit_batch_code.lean does not emit them)
    outfile.write_text(
        "#include <stdint.h>\n#include <stddef.h>\n" + result.stdout
    )


def compile_harness(batch_c: Path, harness_c: Path, binary: Path) -> None:
    """Compile batch C + timing harness with -mcpu=apple-m1 (L-769)."""
    # Detect Apple Silicon for flag; default to apple-m1 when aarch64 Darwin.
    import platform
    if platform.system() == "Darwin" and platform.machine() in ("arm64", "aarch64"):
        arch_flag = "-mcpu=apple-m1"
    elif platform.machine() in ("arm64", "aarch64"):
        arch_flag = "-mcpu=apple-m1"  # cross-compiled on ARM64 Linux target
    else:
        arch_flag = "-march=native"
    cmd = ["cc", "-O3", arch_flag, "-o", str(binary),
           str(batch_c), str(harness_c)]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        raise RuntimeError(f"Compile failed: {result.stderr[:500]}")


def write_harness(harness_c: Path, n: int, batch_width: int, warmup: int,
                  iters: int, field: str) -> None:
    """Write timing harness that calls {field}_ntt_batch and measures
    iters timings in microseconds, after warmup invocations.

    Output format: one line "us" per iter on stdout."""
    p = FIELDS[field]["p"]
    elem_type = "uint64_t" if FIELDS[field]["k"] == 64 else "int32_t"
    # Twiddle count: plan has logN stages, each with N/2 twiddles → logN * N/2.
    import math
    log_n = int(math.log2(n))
    tw_count = log_n * (n // 2)
    content = f"""
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define N {n}
#define B {batch_width}
#define P {p}LL
#define WARMUP {warmup}
#define ITERS {iters}
#define TW_COUNT {tw_count}

void {field}_ntt_batch({elem_type}* data_base, const {elem_type}* twiddles, size_t B_);

static double now_us(void) {{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3;
}}

int main(void) {{
    size_t total = (size_t)B * N;
    {elem_type}* data = malloc(total * sizeof({elem_type}));
    {elem_type}* src  = malloc(total * sizeof({elem_type}));
    {elem_type}* twiddles = malloc(TW_COUNT * sizeof({elem_type}));
    if (!data || !src || !twiddles) {{ fprintf(stderr, "malloc fail\\n"); return 2; }}
    /* Deterministic input */
    for (size_t b = 0; b < B; b++)
        for (size_t i = 0; i < N; i++)
            src[b * N + i] = ({elem_type})(((b * 7 + i * 13 + 1) % P));
    for (size_t i = 0; i < TW_COUNT; i++)
        twiddles[i] = ({elem_type})((i * 1664525 + 1013904223) % P);
    /* Warmup */
    for (int w = 0; w < WARMUP; w++) {{
        memcpy(data, src, total * sizeof({elem_type}));
        {field}_ntt_batch(data, twiddles, B);
    }}
    /* Measure */
    for (int t = 0; t < ITERS; t++) {{
        memcpy(data, src, total * sizeof({elem_type}));
        double t0 = now_us();
        {field}_ntt_batch(data, twiddles, B);
        double dt = now_us() - t0;
        printf("%.3f\\n", dt);
    }}
    free(data); free(src); free(twiddles);
    return 0;
}}
"""
    harness_c.write_text(content)


def run_binary(binary: Path) -> list:
    """Run compiled binary, return list of timing samples in μs."""
    result = subprocess.run([str(binary)], capture_output=True, text=True,
                            timeout=300)
    if result.returncode != 0:
        raise RuntimeError(f"Binary failed: {result.stderr[:500]}")
    samples = []
    for line in result.stdout.strip().split("\n"):
        line = line.strip()
        if line:
            samples.append(float(line))
    return samples


def stats_of(samples: list) -> dict:
    return {
        "min_us": min(samples),
        "mean_us": statistics.mean(samples),
        "median_us": statistics.median(samples),
        "std_us": statistics.stdev(samples) if len(samples) > 1 else 0.0,
        "cv_pct": (statistics.stdev(samples) / statistics.mean(samples) * 100
                   if len(samples) > 1 and statistics.mean(samples) > 0 else 0.0),
        "samples": len(samples),
    }


def measure_combo(field: str, log_n: int, batch_width: int, warmup: int,
                  iters: int, launches: int) -> dict:
    """Run benchmark for one (field, size, width) combo across `launches`
    separate processes. Aggregates min-of-mins + full stats."""
    n = 1 << log_n
    with tempfile.TemporaryDirectory(prefix="trzk_b6_bench_") as tmp:
        tmpd = Path(tmp)
        batch_c = tmpd / "batch.c"
        harness_c = tmpd / "main.c"
        binary = tmpd / "bench"
        emit_batch_c(field, log_n, batch_width, batch_c)
        write_harness(harness_c, n, batch_width, warmup, iters, field)
        compile_harness(batch_c, harness_c, binary)
        launch_means = []
        all_samples = []
        for launch_idx in range(launches):
            samples = run_binary(binary)
            if samples:
                launch_means.append(statistics.mean(samples))
                all_samples.extend(samples)
        if not all_samples:
            raise RuntimeError("No samples collected")
        return {
            "field": field, "log_n": log_n, "n": n, "batch_width": batch_width,
            "min_of_mins_us": min(launch_means) if launch_means else 0.0,
            **stats_of(all_samples),
            "launches": launches,
            "launch_means": launch_means,
        }


def main():
    ap = argparse.ArgumentParser(description="v3.20.b B6.1 batch NTT benchmark harness")
    ap.add_argument("--fields", default="babybear",
                    help="Comma-separated: babybear, goldilocks")
    ap.add_argument("--sizes", default="14,18",
                    help="Comma-separated log2(N) values")
    ap.add_argument("--batch-widths", default="1,4,8,16",
                    help="Comma-separated batch widths")
    ap.add_argument("--warmup", type=int, default=5)
    ap.add_argument("--iters", type=int, default=10)
    ap.add_argument("--launches", type=int, default=5,
                    help="Separate process launches for fresh-compile resistance")
    ap.add_argument("--output",
                    default=str(PROJECT_ROOT / "Tests/benchmark/output/v3.20_b_batch.json"))
    args = ap.parse_args()
    fields = [f.strip() for f in args.fields.split(",")]
    sizes = [int(s.strip()) for s in args.sizes.split(",")]
    widths = [int(w.strip()) for w in args.batch_widths.split(",")]
    metadata = {
        "date": datetime.now().isoformat(timespec="seconds"),
        "hardware": f"{os.uname().machine} {os.uname().sysname}",
        "iters": args.iters,
        "warmup": args.warmup,
        "launches": args.launches,
        "compile_flag": "-O3 -mcpu=apple-m1 (L-769)",
        "fields": fields,
        "sizes": sizes,
        "widths": widths,
        "note": "v3.20.b post-MVP-escape: packed dispatch disabled; measurement "
                "reflects B4 loop-wrapping batch path (production default). "
                "See BENCHMARKS §8g for positioning vs Plonky3-batch.",
    }
    data = {}
    for field in fields:
        data[field] = {}
        for log_n in sizes:
            combos = []
            for w in widths:
                print(f"[B6.1] {field} 2^{log_n} width={w} ...", flush=True)
                try:
                    stats = measure_combo(field, log_n, w, args.warmup,
                                          args.iters, args.launches)
                    stats["width"] = w  # match v3.19_b2 schema
                    combos.append(stats)
                    print(f"   min_us={stats['min_us']:.1f} "
                          f"mean_us={stats['mean_us']:.1f} cv%={stats['cv_pct']:.2f}")
                except Exception as e:
                    print(f"   FAIL: {e}")
                    combos.append({"width": w, "error": str(e)})
            data[field][f"2^{log_n}"] = combos
    result = {"metadata": metadata, "data": data}
    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result, indent=2))
    print(f"\n[B6.1] Output: {out_path}")


if __name__ == "__main__":
    main()
