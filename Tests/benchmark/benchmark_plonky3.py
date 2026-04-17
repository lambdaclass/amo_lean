#!/usr/bin/env python3
"""Benchmark: TRZK vs Plonky3 Real Timing.

v3.16.0 B3: Measures TRZK (C scalar) vs Plonky3 (Rust --release) performance.
Uses ctypes FFI for Plonky3, compiled C binary for TRZK.

Reports with 6 requirements: correctness ref, P3 version, TRZK strategy,
artefacts dir, reproduction instructions, metadata.

Usage:
    python3 benchmark_plonky3.py [--fields babybear,goldilocks] [--sizes 14,18,20] [--iters 10]
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
from compiler import (compile_c, compile_rust, describe_profile_c,
                      describe_profile_rust, PLONKY3_PROFILE_DESCRIPTION)


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

    # v3.17.0 post-B6: multi-iter warmup + min-of-iters (matches TRZK harness
    # methodology). Single warmup + average was biased by cold-cache outliers.
    for _ in range(5):
        arr = ArrayType(*data_template)
        fn(arr, n)

    # Timed iterations — report MIN (matches TRZK harness `min_us`)
    min_us = float("inf")
    for _ in range(iters):
        arr = ArrayType(*data_template)
        t0 = time.perf_counter()
        fn(arr, n)
        t1 = time.perf_counter()
        us = (t1 - t0) * 1e6
        if us < min_us:
            min_us = us
    return min_us


def trzk_c_timing(project_root: Path, field_name: str, log_n: int, iters: int,
                  use_r4: bool = False, profile: str = "conservative") -> tuple[float, str]:
    """Generate TRZK C, compile, run with timing. Returns (avg_us, plan_description).

    v3.17.0 N317.8: `profile` threads through to compile_c for flag parity with Plonky3.
    """
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

    # v3.17.0 N317.8: use compile_c from compiler.py (profile-aware) instead of
    # hardcoded cc -O2. field_k lets compile_c emit -Wno-implicitly-unsigned-literal
    # for Goldilocks (k=64) where p > INT64_MAX.
    field_k = get_field(field_name).k
    cr = compile_c(Path(src), Path(bin_path), hardware="arm-scalar",
                   field_k=field_k, profile=profile)
    if not cr.success:
        raise RuntimeError(f"Compilation failed ({profile}): {cr.error[:200]}")

    # v3.17.0 post-B6 fix: process-level warmup. Fresh-compile + first run hits
    # cold iTLB/cache/thermal state; binary's internal `min of 30 iters` still
    # reflects the cold window. Run binary N_WARMUP times discarding results,
    # then N_MEASURE times keeping the minimum across all measurement runs.
    # See /tmp/bb_inv investigation in conversation log.
    N_WARMUP = 2
    N_MEASURE = 3
    for _ in range(N_WARMUP):
        subprocess.run([bin_path], capture_output=True, text=True, timeout=300)
    measured = []
    for _ in range(N_MEASURE):
        run = subprocess.run([bin_path], capture_output=True, text=True, timeout=300)
        if run.returncode != 0:
            raise RuntimeError(f"Execution failed (exit {run.returncode})")
        measured.append(float(run.stdout.strip()))
    us = min(measured)
    plan_desc = "R4+R2 mixed DIT" if use_r4 else "R2 uniform Harvey"
    return us, plan_desc


def trzk_rust_timing(project_root: Path, field_name: str, log_n: int, iters: int,
                     use_r4: bool = False, profile: str = "conservative") -> tuple[float, str]:
    """Generate TRZK Rust, compile, run with timing. Returns (avg_us, plan_description).

    v3.17.0 B5.5: Rust-vs-Rust comparison to eliminate compiler variable (clang vs rustc)
    from TRZK-vs-Plonky3 gap measurements.
    """
    n = 1 << log_n
    fd = get_field(field_name)
    p = fd.p
    g = fd.generator

    # Generate Rust via emit_standard_rust.lean (emits NTT function + preambles only)
    cmd = ["lake", "env", "lean", "--run", "Tests/benchmark/emit_standard_rust.lean",
           field_name, str(log_n)]
    if use_r4:
        cmd.append("--r4")
    gen = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                         cwd=str(project_root))
    if gen.returncode != 0:
        raise RuntimeError(f"Rust generation failed: {gen.stderr[:200]}")
    ntt_rust = gen.stdout
    func_name = f"{field_name}_ntt_standard"

    # Rust type widths per field (mirrors emitRustFromPlanStandard conventions)
    if field_name == "goldilocks":
        elem_type = "u64"   # data array
        wide_type = "u128"  # products / p_val
    else:
        # BabyBear/KoalaBear use u32 data + u64 wide; but emitRustFromPlanStandard
        # emits i32/i64 for these. Conservative: let Lean-generated code define types,
        # use u64 at harness level for portability (the NTT function signature uses u32
        # for 32-bit fields per the emitter).
        elem_type = "u32"
        wide_type = "u64"

    # Emitted fn signature (verified against emitRustFromPlanStandard):
    #   Goldilocks:    fn <name>(data: &mut [u64], twiddles: &[u64])
    #   BabyBear/K/M31: fn <name>(data: &mut [u32], twiddles: &[u32])
    if field_name == "goldilocks":
        data_elem = "u64"
    else:
        data_elem = "u32"

    # Montgomery R for twiddle conversion (BabyBear uses Montgomery, Goldilocks doesn't)
    # For Goldilocks: standard twiddles (no Montgomery). For BabyBear: R = 2^32.
    p_lit = f"{p}_{wide_type}"

    # Build Rust timing harness
    harness = f"""
use std::time::Instant;

fn mod_pow(mut base: {wide_type}, mut exp: {wide_type}, m: {wide_type}) -> {wide_type} {{
    let mut result: {wide_type} = 1;
    base %= m;
    while exp > 0 {{
        if exp & 1 == 1 {{
            result = ((result as u128 * base as u128) % m as u128) as {wide_type};
        }}
        base = ((base as u128 * base as u128) % m as u128) as {wide_type};
        exp >>= 1;
    }}
    result
}}

fn main() {{
    let n: usize = {n};
    let logn: usize = {log_n};
    let iters: usize = {iters};
    let p: {wide_type} = {p_lit};
    let omega_n = mod_pow({g} as {wide_type}, (p - 1) / (n as {wide_type}), p);
    let tw_sz = n * logn;
    let mut tw: Vec<{data_elem}> = vec![0; tw_sz];
    for st in 0..logn {{
        let h = 1usize << (logn - 1 - st);
        for grp in 0..(1usize << st) {{
            for pp in 0..h {{
                let exp = (pp * (1usize << st)) as {wide_type};
                tw[st * (n / 2) + grp * h + pp] = mod_pow(omega_n, exp, p) as {data_elem};
            }}
        }}
    }}
"""
    if field_name == "goldilocks":
        # Goldilocks: standard twiddles (no Montgomery)
        harness += f"""
    let tw_ntt: Vec<{data_elem}> = tw.clone();
"""
    else:
        # BabyBear: Montgomery twiddles (R = 2^32)
        harness += f"""
    let r_val: {wide_type} = 4294967296_{wide_type};
    let tw_mont: Vec<{data_elem}> = tw.iter()
        .map(|&t| ((t as {wide_type} * r_val) % p) as {data_elem})
        .collect();
    let tw_ntt: Vec<{data_elem}> = tw_mont;
"""
    # Direct call — both Goldilocks and BabyBear use unsigned types in Rust emitter
    # (signature: `&mut [u64]`/`&[u64]` for Goldilocks, `&mut [u32]`/`&[u32]` for BabyBear).
    call_block = f"{func_name}(&mut d, &tw_ntt);"

    harness += f"""
    let orig: Vec<{data_elem}> = (0..n)
        .map(|i| ((i as u128 * 1000000007u128) % p as u128) as {data_elem}).collect();
    let mut d: Vec<{data_elem}> = orig.clone();

    // Warmup
    {{
        {call_block}
    }}

    // Timed iterations — min of iters
    let mut min_us = f64::MAX;
    for _ in 0..iters {{
        d.copy_from_slice(&orig);
        let t0 = Instant::now();
        {{
            {call_block}
        }}
        let us = t0.elapsed().as_secs_f64() * 1e6;
        if us < min_us {{ min_us = us; }}
    }}
    println!("{{:.1}}", min_us);
}}
"""
    rust_source = ntt_rust + "\n" + harness

    # Write, compile with profile, run
    src = Path(f"/tmp/trzk_bench_{field_name}_{log_n}.rs")
    bin_path = Path(f"/tmp/trzk_bench_{field_name}_{log_n}")
    src.write_text(rust_source)
    cr = compile_rust(src, bin_path, profile=profile)
    if not cr.success:
        raise RuntimeError(f"Rust compile failed ({profile}): {cr.error[:400]}")
    # Process-level warmup (see trzk_c_timing comment for rationale)
    N_WARMUP = 2
    N_MEASURE = 3
    for _ in range(N_WARMUP):
        subprocess.run([str(bin_path)], capture_output=True, text=True, timeout=300)
    measured = []
    for _ in range(N_MEASURE):
        run = subprocess.run([str(bin_path)], capture_output=True, text=True, timeout=300)
        if run.returncode != 0:
            raise RuntimeError(f"Rust execution failed (exit {run.returncode}): {run.stderr[:200]}")
        measured.append(float(run.stdout.strip()))
    us = min(measured)
    plan_desc = "R4+R2 mixed DIT" if use_r4 else "R2 uniform Harvey"
    return us, plan_desc


def main():
    parser = argparse.ArgumentParser(description="TRZK vs Plonky3 Real Timing")
    parser.add_argument("--fields", default="babybear,goldilocks")
    parser.add_argument("--sizes", default="14,18,20",
                        help="Comma-separated log2(N). Canonical: small/medium/large = "
                             "14 (cache-resident), 18 (cache-pressured), 20 (cache-miss-dominant).")
    parser.add_argument("--iters", type=int, default=10)
    parser.add_argument("--project-root", default=None)
    parser.add_argument("--profile", default="conservative",
                        choices=["conservative", "match-plonky3"],
                        help="Compilation profile. conservative = cc -O2 (historical). "
                             "match-plonky3 = -O3 -flto + CPU target (fair comparison).")
    parser.add_argument("--lang", default="c",
                        choices=["c", "rust", "both"],
                        help="Which TRZK backend to benchmark. "
                             "rust eliminates compiler variable vs Plonky3 (both rustc).")
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
    print(f"  Profile:  {args.profile}")
    print(f"  Lang:     {args.lang}")
    if args.lang in ("c", "both"):
        print(f"  TRZK C:   {describe_profile_c(args.profile)}")
    if args.lang in ("rust", "both"):
        print(f"  TRZK Rs:  {describe_profile_rust(args.profile)}")
        print(f"  NOTE:     Rust-vs-Rust comparison eliminates compiler variable (both rustc+LLVM).")
    print(f"  Plonky3:  {PLONKY3_PROFILE_DESCRIPTION}")
    if args.profile == "conservative" and args.lang != "rust":
        print(f"  NOTE:     Asymmetric — TRZK uses -O2, Plonky3 uses -O3+LTO.")
        print(f"            For fair comparison, re-run with --profile match-plonky3.")
    # SIMD mode asymmetry note (v3.17.0 N317.8)
    for f in fields:
        if f in ("babybear", "koalabear"):
            print(f"  WARN:     {f} TRZK runs SCALAR, Plonky3 may use NEON (p3-{f} packing).")
            print(f"            BabyBear NEON-vs-NEON comparison requires v3.18 SIMD migration.")
            break
    print(f"  Iters:    {args.iters}")
    print(f"  Fields:   {fields}")
    print(f"  Sizes:    {['2^'+str(s) for s in sizes]}")
    print()

    lib = load_plonky3_shim(project_root)

    # Column layout depends on --lang
    if args.lang == "c":
        header = f"  {'Field':<12} {'N':<8} {'TRZK C (us)':<14} {'P3 Rust (us)':<14} {'Ratio':<8} {'Note'}"
    elif args.lang == "rust":
        header = f"  {'Field':<12} {'N':<8} {'TRZK Rs (us)':<14} {'P3 Rust (us)':<14} {'Ratio':<8} {'Note'}"
    else:  # both
        header = f"  {'Field':<12} {'N':<8} {'TRZK C (us)':<13} {'TRZK Rs (us)':<14} {'P3 (us)':<12} {'C/P3':<7} {'Rs/P3':<7} {'Note'}"
    print(header)
    print(f"  {'─'*(len(header)-2)}")

    for field_name in fields:
        for log_n in sizes:
            n = 1 << log_n
            tag = f"{get_field(field_name).display:<12} 2^{log_n:<5}"

            trzk_c_us = trzk_rs_us = None
            plan = ""

            if args.lang in ("c", "both"):
                try:
                    trzk_c_us, plan = trzk_c_timing(project_root, field_name, log_n,
                                                    args.iters, profile=args.profile)
                except Exception as e:
                    print(f"  {tag} TRZK C FAIL: {str(e)[:80]}")
                    if args.lang == "c":
                        continue

            if args.lang in ("rust", "both"):
                try:
                    trzk_rs_us, plan = trzk_rust_timing(project_root, field_name, log_n,
                                                        args.iters, profile=args.profile)
                except Exception as e:
                    print(f"  {tag} TRZK Rust FAIL: {str(e)[:80]}")
                    if args.lang == "rust":
                        continue

            try:
                p3_us = plonky3_timing(lib, field_name, log_n, args.iters)
            except Exception as e:
                print(f"  {tag} P3 FAIL: {e}")
                continue

            if args.lang == "c":
                ratio = trzk_c_us / p3_us
                print(f"  {tag} {trzk_c_us:>10.1f}    {p3_us:>10.1f}    {ratio:>5.2f}x  {plan}")
            elif args.lang == "rust":
                ratio = trzk_rs_us / p3_us
                print(f"  {tag} {trzk_rs_us:>10.1f}    {p3_us:>10.1f}    {ratio:>5.2f}x  {plan}")
            else:  # both
                c_us_str = f"{trzk_c_us:>9.1f}" if trzk_c_us is not None else "     FAIL"
                rs_us_str = f"{trzk_rs_us:>10.1f}" if trzk_rs_us is not None else "      FAIL"
                c_ratio = f"{trzk_c_us/p3_us:>5.2f}x" if trzk_c_us is not None else "  n/a"
                rs_ratio = f"{trzk_rs_us/p3_us:>5.2f}x" if trzk_rs_us is not None else "  n/a"
                print(f"  {tag} {c_us_str}    {rs_us_str}    {p3_us:>8.1f}    {c_ratio}  {rs_ratio}  {plan}")

    print()
    print("  Ratio < 1.0 = TRZK faster. Ratio > 1.0 = Plonky3 faster.")
    if args.lang in ("c", "both"):
        print(f"  TRZK C:   emitCFromPlanStandard, {describe_profile_c(args.profile)}")
    if args.lang in ("rust", "both"):
        print(f"  TRZK Rs:  emitRustFromPlanStandard, {describe_profile_rust(args.profile)}")
    print(f"  P3:       Rust Radix2Dit::dft_batch via FFI — {PLONKY3_PROFILE_DESCRIPTION}")
    if args.lang == "both":
        print(f"  Rust-vs-Rust (Rs/P3) eliminates compiler variable — isolates algorithm/design gap.")
    print("=" * 65)


if __name__ == "__main__":
    sys.exit(main())
