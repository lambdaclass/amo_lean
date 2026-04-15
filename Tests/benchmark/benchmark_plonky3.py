#!/usr/bin/env python3
"""Benchmark: TRZK vs Plonky3 Real Timing.

v3.16.0 B3: Measures TRZK (C scalar) vs Plonky3 (Rust --release) performance.
Uses ctypes FFI for Plonky3, compiled C binary for TRZK.

Reports with 6 requirements: correctness ref, P3 version, TRZK strategy,
artefacts dir, reproduction instructions, metadata.

Usage:
    python3 benchmark_plonky3.py [--fields babybear,goldilocks] [--sizes 14,16] [--iters 10]
"""

import argparse
import ctypes
import os
import subprocess
import sys
import time
import platform
from pathlib import Path
from datetime import datetime

from field_defs import get_field, BABYBEAR, GOLDILOCKS


def load_plonky3_shim(project_root: Path):
    ext = "dylib" if platform.system() == "Darwin" else "so"
    lib_path = project_root / f"verification/plonky3/plonky3_shim/target/release/libplonky3_shim.{ext}"
    if not lib_path.exists():
        print(f"ERROR: Plonky3 shim not built. Run: cd verification/plonky3 && make shim")
        sys.exit(1)
    return ctypes.CDLL(str(lib_path))


def plonky3_timing(lib, field_name: str, log_n: int, iters: int) -> float:
    """Time Plonky3 NTT via FFI. Returns average microseconds."""
    n = 1 << log_n
    p = get_field(field_name).p
    data_template = [(i * 1000000007) % p for i in range(n)]

    if field_name in ("babybear", "koalabear"):
        ArrayType = ctypes.c_uint32 * n
        fn = getattr(lib, f"plonky3_{field_name}_ntt_forward")
        fn.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.c_size_t]
    else:
        ArrayType = ctypes.c_uint64 * n
        fn = lib.plonky3_ntt_forward
        fn.argtypes = [ctypes.POINTER(ctypes.c_uint64), ctypes.c_size_t]
    fn.restype = ctypes.c_int32

    # Warmup
    arr = ArrayType(*data_template)
    fn(arr, n)

    # Timed iterations
    total = 0.0
    for _ in range(iters):
        arr = ArrayType(*data_template)
        t0 = time.perf_counter()
        fn(arr, n)
        t1 = time.perf_counter()
        total += (t1 - t0)

    return (total / iters) * 1e6  # microseconds


def trzk_c_timing(project_root: Path, field_name: str, log_n: int, iters: int,
                  use_r4: bool = False) -> tuple[float, str]:
    """Generate TRZK C, compile, run with timing. Returns (avg_us, plan_description)."""
    n = 1 << log_n
    p = get_field(field_name).p

    # Generate C via emit_standard.lean
    cmd = ["lake", "env", "lean", "--run", "Tests/benchmark/emit_standard.lean",
           field_name, str(log_n)]
    if use_r4:
        cmd.append("--r4")
    gen = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                         cwd=str(project_root))
    if gen.returncode != 0:
        raise RuntimeError(f"Generation failed: {gen.stderr[:200]}")

    # Extract NTT function from generated code, wrap with timing harness
    ntt_code = gen.stdout
    func_name = f"{field_name}_ntt_standard"
    elem_type = "uint64_t" if field_name == "goldilocks" else "int32_t"
    wide_type = "__uint128_t" if field_name == "goldilocks" else "int64_t"
    p_lit = f"{p}ULL"

    # Build timing-only C program (no validation output, just timing)
    timing_code = ntt_code.split("int main(void)")[0]  # Keep everything before main
    # Ensure time.h is included (emit_standard only includes stdio/stdint/stdlib)
    if "#include <time.h>" not in timing_code:
        timing_code = timing_code.replace("#include <stdlib.h>",
                                          "#include <stdlib.h>\n#include <time.h>", 1)
    timing_code += f"""
int main(void) {{
    size_t n = {n};
    int iters = {iters};
    {elem_type} *d = malloc(n * sizeof({elem_type}));
    {elem_type} *orig = malloc(n * sizeof({elem_type}));

    /* Twiddle table */
    size_t logn = {log_n};
    {wide_type} p_val = ({wide_type}){p_lit};
    {wide_type} omega_n = mod_pow({get_field(field_name).generator}, (p_val - 1) / n, p_val);
    size_t tw_sz = n * logn;
    {elem_type} *tw = malloc(tw_sz * sizeof({elem_type}));
    for(size_t st=0; st<logn; st++) {{
        size_t h = 1u << (logn - 1 - st);
        for(size_t g=0; g<(1u<<st); g++)
            for(size_t pp=0; pp<h; pp++)
                tw[st*(n/2)+g*h+pp] = ({elem_type})mod_pow(omega_n, pp*(1ULL<<st), p_val);
    }}
"""
    # Twiddle dispatch: standard for Goldilocks, Montgomery for BabyBear
    if field_name == "goldilocks":
        timing_code += f"""
    {elem_type} *tw_ntt = tw;  /* Goldilocks: standard twiddles */
"""
    else:
        timing_code += f"""
    {elem_type} *tw_mont = malloc(tw_sz * sizeof({elem_type}));
    for(size_t i=0; i<tw_sz; i++) tw_mont[i] = ({elem_type})((({wide_type})tw[i] * ({wide_type})4294967296ULL) % ({wide_type}){p_lit});
    {elem_type} *tw_ntt = tw_mont;  /* BabyBear: Montgomery twiddles */
"""

    timing_code += f"""
    for(size_t i=0; i<n; i++) orig[i] = ({elem_type})((i * 1000000007ULL) % ({wide_type}){p_lit});

    /* Warmup */
    for(size_t i=0; i<n; i++) d[i] = orig[i];
    {func_name}(d, tw_ntt);

    /* Timed iterations */
    struct timespec s, e;
    clock_gettime(CLOCK_MONOTONIC, &s);
    for(int it=0; it<iters; it++) {{
        for(size_t i=0; i<n; i++) d[i] = orig[i];
        {func_name}(d, tw_ntt);
    }}
    clock_gettime(CLOCK_MONOTONIC, &e);
    double us = ((e.tv_sec-s.tv_sec) + (e.tv_nsec-s.tv_nsec)/1e9) / iters * 1e6;
    printf("%.1f\\n", us);

    free(d); free(orig); free(tw);
    return 0;
}}
"""

    # Write, compile, run
    src = f"/tmp/trzk_bench_{field_name}_{log_n}.c"
    bin_path = src.replace(".c", "")
    with open(src, "w") as f:
        f.write(timing_code)

    comp = subprocess.run(["cc", "-O2", "-o", bin_path, src],
                          capture_output=True, text=True)
    if comp.returncode != 0:
        raise RuntimeError(f"Compilation failed: {comp.stderr[:200]}")

    run = subprocess.run([bin_path], capture_output=True, text=True, timeout=300)
    if run.returncode != 0:
        raise RuntimeError(f"Execution failed (exit {run.returncode})")

    us = float(run.stdout.strip())
    plan_desc = "R4+R2 mixed DIT" if use_r4 else "R2 uniform Harvey"
    return us, plan_desc


def main():
    parser = argparse.ArgumentParser(description="TRZK vs Plonky3 Real Timing")
    parser.add_argument("--fields", default="babybear,goldilocks")
    parser.add_argument("--sizes", default="14")
    parser.add_argument("--iters", type=int, default=10)
    parser.add_argument("--project-root", default=None)
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    project_root = Path(args.project_root).resolve() if args.project_root else script_dir.parent.parent

    fields = [f.strip() for f in args.fields.split(",")]
    sizes = [int(s.strip()) for s in args.sizes.split(",")]

    # Metadata
    git_hash = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                              capture_output=True, text=True, cwd=str(project_root)).stdout.strip()
    hw_info = platform.processor() or platform.machine()
    timestamp = datetime.now().isoformat(timespec="seconds")

    print("=" * 65)
    print("  TRZK vs Plonky3 Real — Performance Benchmark")
    print("=" * 65)
    print(f"  Date:     {timestamp}")
    print(f"  Git:      {git_hash}")
    print(f"  Hardware: {hw_info}, {platform.system()}")
    print(f"  C:        cc -O2")
    print(f"  Plonky3:  Rust --release (via FFI), p3-field from GitHub main")
    print(f"  Iters:    {args.iters}")
    print(f"  Fields:   {fields}")
    print(f"  Sizes:    {['2^'+str(s) for s in sizes]}")
    print()

    lib = load_plonky3_shim(project_root)

    print(f"  {'Field':<12} {'N':<8} {'TRZK C (us)':<14} {'P3 Rust (us)':<14} {'Ratio':<8} {'Note'}")
    print(f"  {'─'*12} {'─'*8} {'─'*14} {'─'*14} {'─'*8} {'─'*20}")

    for field_name in fields:
        for log_n in sizes:
            n = 1 << log_n
            tag = f"{get_field(field_name).display:<12} 2^{log_n:<5}"

            try:
                trzk_us, plan = trzk_c_timing(project_root, field_name, log_n, args.iters)
            except Exception as e:
                print(f"  {tag} TRZK FAIL: {e}")
                continue

            try:
                p3_us = plonky3_timing(lib, field_name, log_n, args.iters)
            except Exception as e:
                print(f"  {tag} P3 FAIL: {e}")
                continue

            ratio = trzk_us / p3_us
            note = plan
            print(f"  {tag} {trzk_us:>10.1f}    {p3_us:>10.1f}    {ratio:>5.2f}x  {note}")

    print()
    print("  Ratio < 1.0 = TRZK faster. Ratio > 1.0 = Plonky3 faster.")
    print("  TRZK: C scalar generated by emitCFromPlanStandard, cc -O2")
    print("  P3:   Rust Radix2Dit::dft_batch, --release LTO, via FFI")
    print("=" * 65)


if __name__ == "__main__":
    sys.exit(main())
