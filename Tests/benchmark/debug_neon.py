#!/usr/bin/env python3
"""NEON butterfly debug harness (ND.1-ND.5).

Generates debug-instrumented C validation programs for both scalar and NEON
paths, compiles them, runs them, and diffs the output to find the divergence.

Usage:
    python3 debug_neon.py [--field babybear] [--logn 4]

Requires: Lean environment (lake env lean) to generate the C code.
"""

import argparse
import os
import subprocess
import sys
import tempfile

# Add parent paths
sys.path.insert(0, os.path.dirname(__file__))
from field_defs import BABYBEAR, KOALABEAR, MERSENNE31, GOLDILOCKS

FIELDS = {
    "babybear": BABYBEAR,
    "koalabear": KOALABEAR,
    "mersenne31": MERSENNE31,
    "goldilocks": GOLDILOCKS,
}

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))


def generate_c_code(field_name: str, logn: int, hardware: str) -> str:
    """Generate C code from Lean for the given field and hardware.

    Bench.lean writes C to /tmp/amobench.c. We run it and read the file.
    """
    cmd = [
        "lake", "env", "lean", "--run", "Bench.lean", "--",
        "--pipeline", "ultra",
        "--hardware", hardware,
        "--field", field_name,
        "--size", str(logn),
        "--lang", "c",
        "--primitive", "ntt",
    ]
    # Bench.lean writes C to /tmp/amobench.c, then tries to compile+run.
    # We only care about the C file — ignore compile/run errors (NEON may
    # not compile on this host, and that's fine).
    result = subprocess.run(cmd, cwd=PROJECT_ROOT, capture_output=True, text=True,
                            timeout=300)
    # Read the generated C file regardless of exit code
    c_path = "/tmp/amobench.c"
    if not os.path.exists(c_path):
        print(f"ERROR: {c_path} not generated (Lean exit={result.returncode})",
              file=sys.stderr)
        if result.stderr:
            print(f"  stderr: {result.stderr[:500]}", file=sys.stderr)
        sys.exit(1)
    with open(c_path) as f:
        return f.read()


def build_debug_program(c_source: str, field, logn: int) -> str:
    """Build a debug-instrumented validation program from generated C."""
    from code_splitter import split_at_main, _detect_ntt_func_name, build_debug_validation_c

    kernel, _ = split_at_main(c_source, "c")
    func_name = _detect_ntt_func_name(kernel, "c")
    return build_debug_validation_c(kernel, field, logn, func_name)


def compile_and_run(c_program: str, label: str, is_neon: bool) -> str:
    """Compile C program and run it, returning stdout."""
    with tempfile.NamedTemporaryFile(suffix=".c", mode="w", delete=False) as f:
        f.write(c_program)
        c_path = f.name

    binary = c_path.replace(".c", "")
    # Use -O0 to avoid optimizations that might hide bugs
    flags = ["-O0", "-lm"]
    if is_neon:
        flags.extend(["-march=armv8-a"])

    try:
        compile_cmd = ["cc"] + flags + [c_path, "-o", binary]
        result = subprocess.run(compile_cmd, capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            print(f"COMPILE ERROR ({label}):\n{result.stderr[:1000]}", file=sys.stderr)
            # Save the C file for inspection
            debug_c = os.path.join(PROJECT_ROOT, f"Tests/benchmark/output/debug_{label}.c")
            os.makedirs(os.path.dirname(debug_c), exist_ok=True)
            with open(debug_c, "w") as out:
                out.write(c_program)
            print(f"  Saved C source to {debug_c}", file=sys.stderr)
            return ""

        run_result = subprocess.run([binary], capture_output=True, text=True, timeout=30)
        return run_result.stdout
    finally:
        for path in [c_path, binary]:
            if os.path.exists(path):
                os.unlink(path)


def main():
    parser = argparse.ArgumentParser(description="NEON butterfly debug harness")
    parser.add_argument("--field", default="babybear", choices=FIELDS.keys())
    parser.add_argument("--logn", type=int, default=4, help="log2(N), default=4 for N=16")
    parser.add_argument("--generate-only", action="store_true",
                        help="Only generate C files, don't compile/run")
    args = parser.parse_args()

    field = FIELDS[args.field]
    logn = args.logn

    print(f"=== NEON Debug: {field.display} N=2^{logn}={1<<logn} ===")

    # Step 1: Generate C code from Lean for both paths
    print("\n[1/5] Generating scalar C code from Lean...")
    scalar_c = generate_c_code(args.field, logn, "arm-scalar")
    print(f"  Generated {len(scalar_c)} chars")

    print("[2/5] Generating NEON C code from Lean...")
    neon_c = generate_c_code(args.field, logn, "arm-neon")
    print(f"  Generated {len(neon_c)} chars")

    # Step 2: Build debug-instrumented programs
    print("[3/5] Injecting debug printf...")
    scalar_debug = build_debug_program(scalar_c, field, logn)
    neon_debug = build_debug_program(neon_c, field, logn)

    # Save C files for inspection
    out_dir = os.path.join(PROJECT_ROOT, "Tests/benchmark/output")
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "debug_scalar.c"), "w") as f:
        f.write(scalar_debug)
    with open(os.path.join(out_dir, "debug_neon.c"), "w") as f:
        f.write(neon_debug)
    print(f"  Saved to {out_dir}/debug_{{scalar,neon}}.c")

    if args.generate_only:
        print("\n--generate-only: skipping compile/run")
        return

    # Step 3: Compile and run both
    print("[4/5] Compiling and running scalar...")
    scalar_out = compile_and_run(scalar_debug, "scalar", is_neon=False)

    print("[5/5] Compiling and running NEON...")
    neon_out = compile_and_run(neon_debug, "neon", is_neon=True)

    if not scalar_out or not neon_out:
        print("\nERROR: One or both paths failed to compile/run.")
        print("Check the saved C files in Tests/benchmark/output/")
        return

    # Save outputs
    with open(os.path.join(out_dir, "debug_scalar.out"), "w") as f:
        f.write(scalar_out)
    with open(os.path.join(out_dir, "debug_neon.out"), "w") as f:
        f.write(neon_out)

    # Step 4: Compare outputs (ND.5 diagnosis)
    print("\n=== DIAGNOSIS ===")

    scalar_lines = scalar_out.strip().split("\n")
    neon_lines = neon_out.strip().split("\n")

    # Find first divergence in debug lines
    debug_scalar = [l for l in scalar_lines if l.startswith("SCALAR_BF") or
                    l.startswith("=== ") or l.startswith("tw_mont") or
                    l.startswith("data[")]
    debug_neon = [l for l in neon_lines if l.startswith("NEON_BF") or
                  l.startswith("=== ") or l.startswith("tw_mont") or
                  l.startswith("data[")]

    print(f"\nScalar debug lines: {len(debug_scalar)}")
    print(f"NEON debug lines: {len(debug_neon)}")

    # Print twiddle comparison
    tw_scalar = [l for l in scalar_lines if l.startswith("tw_mont")]
    tw_neon = [l for l in neon_lines if l.startswith("tw_mont")]
    if tw_scalar == tw_neon:
        print("\nTwiddles: MATCH")
    else:
        print("\nTwiddles: MISMATCH!")
        for s, n in zip(tw_scalar, tw_neon):
            marker = " <<<" if s != n else ""
            print(f"  S: {s}")
            print(f"  N: {n}{marker}")

    # Print data comparison
    data_scalar = [l for l in scalar_lines if l.startswith("data[")]
    data_neon = [l for l in neon_lines if l.startswith("data[")]
    if data_scalar == data_neon:
        print("Input data: MATCH")
    else:
        print("Input data: MISMATCH!")

    # Print butterfly intermediates
    bf_scalar = [l for l in scalar_lines if l.startswith("SCALAR_BF")]
    bf_neon = [l for l in neon_lines if l.startswith("NEON_BF")]

    if bf_scalar:
        print("\n--- Scalar butterfly (first call) ---")
        for l in bf_scalar:
            print(f"  {l}")

    if bf_neon:
        print("\n--- NEON butterfly lane 0 (first call) ---")
        for l in bf_neon:
            print(f"  {l}")

    # Compare NTT outputs (last N lines = NTT result mod p)
    n = 1 << logn
    ntt_scalar = scalar_lines[-n:] if len(scalar_lines) >= n else []
    ntt_neon = neon_lines[-n:] if len(neon_lines) >= n else []

    diffs = 0
    for i, (s, ne) in enumerate(zip(ntt_scalar, ntt_neon)):
        if s != ne:
            if diffs < 5:
                print(f"\nOUTPUT DIFF at element {i}: scalar={s} neon={ne}")
            diffs += 1

    if diffs == 0:
        print(f"\n=== RESULT: MATCH ({n}/{n} elements) ===")
    else:
        print(f"\n=== RESULT: {diffs}/{n} elements DIFFER ===")


if __name__ == "__main__":
    main()
