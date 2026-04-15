#!/usr/bin/env python3
"""Pipeline Value Benchmark: Baseline R2 vs Competition Winner.

v3.16.0 B4: Measures how much value the ultra pipeline adds
(R4, ILP2, bound-aware) by comparing a uniform R2 Harvey plan
against the competition winner (typically R4 mixed + ILP2).

Usage:
    python3 benchmark_pipeline.py [--fields babybear,goldilocks] [--sizes 14] [--iters 10]
"""

import argparse
import subprocess
import sys
import time
import platform
from pathlib import Path
from datetime import datetime

from field_defs import get_field


def trzk_c_timing(project_root: Path, field_name: str, log_n: int, iters: int,
                  use_r4: bool = False) -> float:
    """Generate TRZK C, compile with timing harness, run. Returns avg microseconds."""
    n = 1 << log_n
    fdef = get_field(field_name)
    p = fdef.p

    cmd = ["lake", "env", "lean", "--run", "Tests/benchmark/emit_standard.lean",
           field_name, str(log_n)]
    if use_r4:
        cmd.append("--r4")
    gen = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                         cwd=str(project_root))
    if gen.returncode != 0:
        raise RuntimeError(f"Generation failed: {gen.stderr[:200]}")

    ntt_code = gen.stdout
    func_name = f"{field_name}_ntt_standard"
    elem_type = "uint64_t" if field_name == "goldilocks" else "int32_t"
    wide_type = "__uint128_t" if field_name == "goldilocks" else "int64_t"
    p_lit = f"{p}ULL"

    timing_code = ntt_code.split("int main(void)")[0]
    if "#include <time.h>" not in timing_code:
        timing_code = timing_code.replace("#include <stdlib.h>",
                                          "#include <stdlib.h>\n#include <time.h>", 1)

    timing_code += f"""
int main(void) {{
    size_t n = {n};
    int iters = {iters};
    {elem_type} *d = malloc(n * sizeof({elem_type}));
    {elem_type} *orig = malloc(n * sizeof({elem_type}));
    size_t logn = {log_n};
    {wide_type} p_val = ({wide_type}){p_lit};
    {wide_type} omega_n = mod_pow({fdef.generator}, (p_val - 1) / n, p_val);
    size_t tw_sz = n * logn;
    {elem_type} *tw = malloc(tw_sz * sizeof({elem_type}));
    for(size_t st=0; st<logn; st++) {{
        size_t h = 1u << (logn - 1 - st);
        for(size_t g=0; g<(1u<<st); g++)
            for(size_t pp=0; pp<h; pp++)
                tw[st*(n/2)+g*h+pp] = ({elem_type})mod_pow(omega_n, pp*(1ULL<<st), p_val);
    }}
"""
    if field_name == "goldilocks":
        timing_code += f"    {elem_type} *tw_ntt = tw;\n"
    else:
        timing_code += f"""    {elem_type} *tw_mont = malloc(tw_sz * sizeof({elem_type}));
    for(size_t i=0; i<tw_sz; i++) tw_mont[i] = ({elem_type})((({wide_type})tw[i] * ({wide_type})4294967296ULL) % ({wide_type}){p_lit});
    {elem_type} *tw_ntt = tw_mont;
"""

    timing_code += f"""
    for(size_t i=0; i<n; i++) orig[i] = ({elem_type})((i * 1000000007ULL) % ({wide_type}){p_lit});
    for(size_t i=0; i<n; i++) d[i] = orig[i];
    {func_name}(d, tw_ntt);
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

    tag = "r4" if use_r4 else "r2"
    src = f"/tmp/trzk_pipe_{field_name}_{log_n}_{tag}.c"
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

    return float(run.stdout.strip())


def main():
    parser = argparse.ArgumentParser(description="Pipeline Value Benchmark")
    parser.add_argument("--fields", default="babybear,goldilocks")
    parser.add_argument("--sizes", default="14")
    parser.add_argument("--iters", type=int, default=10)
    parser.add_argument("--project-root", default=None)
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    project_root = Path(args.project_root).resolve() if args.project_root else script_dir.parent.parent

    fields = [f.strip() for f in args.fields.split(",")]
    sizes = [int(s.strip()) for s in args.sizes.split(",")]

    git_hash = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                              capture_output=True, text=True, cwd=str(project_root)).stdout.strip()

    print("=" * 70)
    print("  Pipeline Value Benchmark: Baseline R2 vs Competition Winner")
    print("=" * 70)
    print(f"  Git: {git_hash}, {platform.machine()}, cc -O2, {args.iters} iters")
    print()
    print(f"  {'Field':<12} {'N':<7} {'Baseline (us)':<15} {'Winner (us)':<14} {'Speedup':<9} {'Winner description'}")
    print(f"  {'─'*12} {'─'*7} {'─'*15} {'─'*14} {'─'*9} {'─'*30}")

    for field_name in fields:
        for log_n in sizes:
            tag = f"{get_field(field_name).display:<12} 2^{log_n:<4}"
            try:
                base_us = trzk_c_timing(project_root, field_name, log_n, args.iters, use_r4=False)
                win_us = trzk_c_timing(project_root, field_name, log_n, args.iters, use_r4=True)
                speedup = base_us / win_us
                # Describe the winner
                if field_name == "goldilocks":
                    desc = "R4+R2 mixed, ILP2, PZT reduce, standard tw"
                else:
                    desc = "R4+R2 mixed, Monty REDC, Montgomery tw"
                print(f"  {tag} {base_us:>11.1f}    {win_us:>10.1f}    {speedup:>5.2f}x   {desc}")
            except Exception as e:
                print(f"  {tag} FAIL: {e}")

    print()
    print("  Baseline: mkUniformPlan .r2 .harvey (no pipeline optimizations)")
    print("  Winner:   mkMixedRadixPlan (R4 early + R2 late, competition winner)")
    print("  Speedup > 1.0 = pipeline adds value")
    print("=" * 70)


if __name__ == "__main__":
    sys.exit(main())
