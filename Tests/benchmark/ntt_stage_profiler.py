#!/usr/bin/env python3
"""
NTT Per-Stage Profiler (B35-5)

Takes a generated NTT C file, inserts clock_gettime between stages,
compiles, runs, and reports per-stage timing.

Usage:
    python3 ntt_stage_profiler.py <field> <logN>
    # Generates, instruments, compiles, and runs the profiled NTT.
"""
import subprocess, tempfile, re, sys, os

def main():
    field = sys.argv[1] if len(sys.argv) > 1 else "babybear"
    logN = sys.argv[2] if len(sys.argv) > 2 else "16"
    n = 1 << int(logN)
    iters = 100  # enough iterations for stable timing

    project_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

    # Step 1: Generate NTT C code
    print(f"Generating {field} N=2^{logN} C (arm-neon)...", flush=True)
    gen = subprocess.run(
        ["lake", "env", "lean", "--run", "Tests/benchmark/emit_code.lean",
         field, logN, "c", "arm-neon"],
        capture_output=True, text=True, cwd=project_root, timeout=300
    )
    if gen.returncode != 0:
        print(f"Generation failed: {gen.stderr[:200]}")
        return

    source = gen.stdout

    # Step 2: Extract NTT function and instrument with per-stage timing
    # Find all "/* Stage N: ..." comments and insert clock_gettime before/after
    stage_pattern = re.compile(r'(/\* Stage (\d+):.*?\*/)')
    matches = list(stage_pattern.finditer(source))
    num_stages = len(matches)

    if num_stages == 0:
        print("No stages found in generated code!")
        return

    print(f"Found {num_stages} stages. Instrumenting...", flush=True)

    # Insert timing code. Work backwards to preserve positions.
    instrumented = source

    # Find the NTT function body start (after constant declarations, before first stage)
    func_match = re.search(r'(void \w+_ntt_ultra\([^)]+\)\s*\{)', source)
    if not func_match:
        print("Cannot find NTT function!")
        return

    # Insert timer declarations after the function opening
    # Find the first stage comment
    first_stage_pos = matches[0].start()
    timer_decl = f"""
  struct timespec _ts0, _ts1;
  static double _stage_us[{num_stages}];
  static int _prof_count = 0;
  _prof_count++;
"""
    instrumented = instrumented[:first_stage_pos] + timer_decl + instrumented[first_stage_pos:]

    # Recompute positions after insertion
    offset = len(timer_decl)

    # For each stage, wrap with clock_gettime
    # Process in reverse to preserve positions
    for idx in range(num_stages - 1, -1, -1):
        m = matches[idx]
        stage_num = int(m.group(2))
        pos = m.start() + offset

        # Insert clock_gettime BEFORE the stage comment
        before = f"  clock_gettime(CLOCK_MONOTONIC, &_ts0);\n"
        instrumented = instrumented[:pos] + before + instrumented[pos:]
        offset += len(before)

        # Find the end of this stage's code block (next stage comment or function end)
        if idx < num_stages - 1:
            next_pos = matches[idx + 1].start() + offset
        else:
            # Last stage: find the closing } of the function
            # Look for the "}\n" that ends the NTT function
            next_pos = instrumented.find("\n}\n", pos) + 1

        after = f"""  clock_gettime(CLOCK_MONOTONIC, &_ts1);
  _stage_us[{stage_num}] += (_ts1.tv_sec - _ts0.tv_sec) * 1e6 + (_ts1.tv_nsec - _ts0.tv_nsec) / 1e3;
"""
        instrumented = instrumented[:next_pos] + after + instrumented[next_pos:]
        offset += len(after)

    # Insert profiling output in main() — after the benchmark loop
    # Find "printf(" in main and insert profiling dump before it
    printf_pos = instrumented.rfind('printf(')
    if printf_pos > 0:
        prof_dump = f"""
    /* === Per-stage profiling (B35-5) === */
    fprintf(stderr, "# Per-stage profiling: {field} N=2^{logN}, %d iterations\\n", {iters});
    double _total = 0;
    for (int _s = 0; _s < {num_stages}; _s++) _total += _stage_us[_s];
    for (int _s = 0; _s < {num_stages}; _s++)
        fprintf(stderr, "stage,%d,%.1f,%.1f\\n", _s, _stage_us[_s]/{iters}, 100.0 * _stage_us[_s] / _total);
    fprintf(stderr, "total,%.1f\\n", _total/{iters});

"""
        instrumented = instrumented[:printf_pos] + prof_dump + instrumented[printf_pos:]

    # Step 3: Write, compile, run
    with tempfile.TemporaryDirectory(prefix="ntt_prof_") as tmpdir:
        src_path = f"{tmpdir}/ntt_profiled.c"
        bin_path = f"{tmpdir}/ntt_profiled"

        with open(src_path, 'w') as f:
            f.write(instrumented)

        print("Compiling...", flush=True)
        cc = subprocess.run(
            ["cc", "-O2", "-o", bin_path, src_path, "-lm"],
            capture_output=True, text=True
        )
        if cc.returncode != 0:
            print(f"Compile error: {cc.stderr[:500]}")
            # Save the source for debugging
            debug_path = f"/tmp/ntt_profiled_debug.c"
            with open(debug_path, 'w') as f:
                f.write(instrumented)
            print(f"Source saved to {debug_path}")
            return

        print(f"Running ({iters} iterations)...", flush=True)
        run = subprocess.run(
            [bin_path], capture_output=True, text=True, timeout=120
        )

        if run.returncode != 0:
            print(f"Runtime error: {run.stderr[:200]}")
            return

        # Parse profiling output from stderr
        print()
        print(f"{'='*60}")
        print(f"Per-Stage Profiling: {field} N=2^{logN} (NEON sqdmulh)")
        print(f"{'='*60}")
        print(f"{'Stage':>6} {'Time(μs)':>10} {'%Total':>8} {'halfSize':>10} {'Type':>8}")
        print(f"{'-'*6:>6} {'-'*10:>10} {'-'*8:>8} {'-'*10:>10} {'-'*8:>8}")

        total_us = 0
        stages_data = []
        for line in run.stderr.strip().split('\n'):
            if line.startswith('stage,'):
                parts = line.split(',')
                s = int(parts[1])
                us = float(parts[2])
                pct = float(parts[3])
                halfSize = n >> (s + 1)
                stype = "SIMD" if halfSize >= 4 else "scalar"
                stages_data.append((s, us, pct, halfSize, stype))
                print(f"{s:>6} {us:>10.1f} {pct:>7.1f}% {halfSize:>10} {stype:>8}")
            elif line.startswith('total,'):
                total_us = float(line.split(',')[1])

        print(f"{'TOTAL':>6} {total_us:>10.1f}")
        print()

        # Group analysis
        if stages_data:
            early = sum(us for s,us,_,hs,_ in stages_data if hs >= 8192)
            mid = sum(us for s,us,_,hs,_ in stages_data if 64 <= hs < 8192)
            late = sum(us for s,us,_,hs,_ in stages_data if hs < 64)
            print(f"Early (halfSize>=8192): {early:.1f} μs ({100*early/total_us:.1f}%)")
            print(f"Mid   (64<=halfSize<8192): {mid:.1f} μs ({100*mid/total_us:.1f}%)")
            print(f"Late  (halfSize<64):    {late:.1f} μs ({100*late/total_us:.1f}%)")


if __name__ == "__main__":
    main()
