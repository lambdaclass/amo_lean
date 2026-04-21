#!/usr/bin/env python3
"""Plonky3 batch NTT benchmark — v3.19 Bloque 2 (N319.2.2).

Measures Plonky3's `dft_batch` across `width ∈ {1, 2, 4, 8, 16}` to detect when
PackedMontyField31Neon (BabyBear/KoalaBear, WIDTH=4) and Radix2DitParallel
optimisations activate. Compares batch latency-per-NTT against width=1 baseline,
and against the existing TRZK single-vector numbers in BENCHMARKS.md §1 for the
v3.19 §13.5 decision tree.

Methodology:
  * warmup_subprocess: this script is one process invocation; intra-process
    warmup loop (default 5 iters discarded) handles the cache/CPU ramp.
  * measurement: min-of-iters per (field, log_n, width). CV reported.
  * canonical sizes: log_n ∈ {14, 18} per BENCHMARKS.md §1; widths cover the
    BabyBear NEON activation threshold (>= 4).
  * **Short-task CV caveat**: for cells where w=1 latency is < 1 ms (typical
    at N ≤ 2^14), the default 30 iters can leave CV in the 10-20% range due
    to OS scheduler noise. Use `--iters 100 --warmup 10` for those sizes to
    satisfy the rubric's CV ≤ 5% requirement.

Usage:
    python3 benchmark_plonky3_batch.py [--fields babybear,goldilocks]
        [--sizes 14,18] [--widths 1,2,4,8,16] [--iters 30]
        [--warmup 5] [--output Tests/benchmark/output/batch.json]
"""

import argparse
import ctypes
import json
import platform
import statistics
import sys
import time
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from field_defs import get_field  # type: ignore  # noqa: E402

PROJECT_ROOT = Path(__file__).resolve().parents[2]


def load_shim() -> ctypes.CDLL:
    ext = "dylib" if platform.system() == "Darwin" else "so"
    lib_path = (
        PROJECT_ROOT
        / f"verification/plonky3/plonky3_shim/target/release/libplonky3_shim.{ext}"
    )
    if not lib_path.exists():
        sys.exit(
            f"ERROR: Plonky3 shim not built ({lib_path}).\n"
            f"Run: cd verification/plonky3 && make shim"
        )
    lib = ctypes.CDLL(str(lib_path))
    # Bind batch entry points (added in v3.19 N319.2.1).
    for sym, ptr in (
        ("plonky3_babybear_ntt_forward_batch", ctypes.c_uint32),
        ("plonky3_koalabear_ntt_forward_batch", ctypes.c_uint32),
        ("plonky3_goldilocks_ntt_forward_batch", ctypes.c_uint64),
    ):
        fn = getattr(lib, sym)
        fn.argtypes = [ctypes.POINTER(ptr), ctypes.c_size_t, ctypes.c_size_t]
        fn.restype = ctypes.c_int32
    return lib


def batch_fn_for(lib: ctypes.CDLL, field_name: str):
    """(fn, ctypes_elem_type) for the batch entry point of a given field."""
    if field_name == "babybear":
        return lib.plonky3_babybear_ntt_forward_batch, ctypes.c_uint32
    if field_name == "koalabear":
        return lib.plonky3_koalabear_ntt_forward_batch, ctypes.c_uint32
    if field_name == "goldilocks":
        return lib.plonky3_goldilocks_ntt_forward_batch, ctypes.c_uint64
    raise ValueError(f"unsupported field: {field_name}")


def measure_batch(
    lib: ctypes.CDLL,
    field_name: str,
    log_n: int,
    width: int,
    iters: int,
    warmup: int,
) -> dict:
    """Time a batched NTT. Returns dict with min/median/mean/std/cv_pct (μs)."""
    n = 1 << log_n
    p = get_field(field_name).p
    fn, elem_t = batch_fn_for(lib, field_name)
    total = n * width
    ArrType = elem_t * total

    # Deterministic content; varies row + col so columns are independent.
    template = [((i * 1000000007) ^ ((i // width) * 2718281)) % p for i in range(total)]

    # Warmup — discarded.
    for _ in range(warmup):
        arr = ArrType(*template)
        ret = fn(arr, n, width)
        if ret != 0:
            raise RuntimeError(f"warmup failed (ret={ret}) for {field_name} N=2^{log_n} w={width}")

    samples_us = []
    for _ in range(iters):
        arr = ArrType(*template)
        t0 = time.perf_counter()
        ret = fn(arr, n, width)
        t1 = time.perf_counter()
        if ret != 0:
            raise RuntimeError(f"iter failed (ret={ret})")
        samples_us.append((t1 - t0) * 1e6)

    min_us = min(samples_us)
    mean_us = statistics.fmean(samples_us)
    median_us = statistics.median(samples_us)
    std_us = statistics.pstdev(samples_us) if len(samples_us) > 1 else 0.0
    cv_pct = (std_us / mean_us * 100.0) if mean_us > 0 else 0.0
    return {
        "min_us": min_us,
        "mean_us": mean_us,
        "median_us": median_us,
        "std_us": std_us,
        "cv_pct": cv_pct,
        "samples": iters,
    }


def parse_csv(arg: str, cast=str) -> list:
    return [cast(x.strip()) for x in arg.split(",") if x.strip()]


def format_table(field: str, log_n: int, rows: list) -> str:
    """Markdown table with width comparison + per-NTT latency."""
    n = 1 << log_n
    header = (
        f"\n#### {field} — N=2^{log_n} ({n} elements per column)\n\n"
        f"| Width | Batch latency (μs) | μs per NTT | Throughput (NTT/s) "
        f"| CV | Speedup vs w=1 |\n"
        f"|------:|-------------------:|-----------:|-------------------:"
        f"|---:|---------------:|\n"
    )
    base_per_ntt = None
    out = [header]
    for r in rows:
        per_ntt = r["min_us"] / r["width"]
        throughput = r["width"] / (r["min_us"] * 1e-6) if r["min_us"] > 0 else 0
        if base_per_ntt is None:
            base_per_ntt = per_ntt
            speedup = "1.00x"
        else:
            speedup = f"{base_per_ntt / per_ntt:.2f}x"
        out.append(
            f"| {r['width']:>5} | {r['min_us']:>18.2f} | {per_ntt:>10.2f} "
            f"| {throughput:>17.0f} | {r['cv_pct']:>3.1f}% | {speedup:>14} |\n"
        )
    return "".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--fields", default="babybear,goldilocks",
                    help="Comma-separated fields (babybear, goldilocks, koalabear)")
    ap.add_argument("--sizes", default="14,18",
                    help="Comma-separated log_n values")
    ap.add_argument("--widths", default="1,2,4,8,16",
                    help="Comma-separated batch widths")
    ap.add_argument("--iters", type=int, default=30, help="Measurement iters")
    ap.add_argument("--warmup", type=int, default=5, help="Warmup iters (discarded)")
    ap.add_argument("--output", type=Path, default=None,
                    help="Optional JSON dump path")
    args = ap.parse_args()

    fields = parse_csv(args.fields)
    sizes = parse_csv(args.sizes, int)
    widths = parse_csv(args.widths, int)

    lib = load_shim()
    print(f"# Plonky3 Batch Benchmark (v3.19 N319.2.2)")
    print(f"# Date: {datetime.now().isoformat(timespec='seconds')}")
    print(f"# Hardware: {platform.machine()} {platform.system()}")
    print(f"# Fields: {fields} | Sizes: {sizes} | Widths: {widths}")
    print(f"# Iters: {args.iters} measurement + {args.warmup} warmup")

    results = {
        "metadata": {
            "date": datetime.now().isoformat(timespec="seconds"),
            "hardware": f"{platform.machine()} {platform.system()}",
            "iters": args.iters,
            "warmup": args.warmup,
            "fields": fields,
            "sizes": sizes,
            "widths": widths,
        },
        "data": {},
    }

    for field in fields:
        results["data"][field] = {}
        for log_n in sizes:
            rows = []
            for width in widths:
                m = measure_batch(lib, field, log_n, width, args.iters, args.warmup)
                m["width"] = width
                rows.append(m)
                print(
                    f"  {field:>10} N=2^{log_n:>2} w={width:>2}: "
                    f"min={m['min_us']:>10.2f}μs cv={m['cv_pct']:>4.1f}%"
                )
            results["data"][field][f"2^{log_n}"] = rows
            print(format_table(field, log_n, rows))

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(results, indent=2))
        print(f"\nResults written to {args.output}")


if __name__ == "__main__":
    main()
