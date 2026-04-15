#!/usr/bin/env python3
"""Oracle Validation: TRZK C generated vs Plonky3 real (via FFI).

v3.16.0 B1: Element-by-element comparison of TRZK standard DFT output
against Plonky3's Radix2Dit::dft_batch() via libplonky3_shim FFI.

Usage:
    python3 oracle_validate.py [--fields babybear,goldilocks] [--sizes 3,4,5,6,7,8,10]

Prerequisites:
    cd verification/plonky3 && make shim  # builds libplonky3_shim
"""

import argparse
import ctypes
import subprocess
import sys
import tempfile
from pathlib import Path

from field_defs import BABYBEAR, GOLDILOCKS, get_field


def load_plonky3_shim(project_root: Path):
    """Load libplonky3_shim dynamic library."""
    import platform
    ext = "dylib" if platform.system() == "Darwin" else "so"
    lib_path = project_root / f"verification/plonky3/plonky3_shim/target/release/libplonky3_shim.{ext}"
    if not lib_path.exists():
        print(f"ERROR: Plonky3 shim not built. Run: cd verification/plonky3 && make shim")
        sys.exit(1)
    return ctypes.CDLL(str(lib_path))


def plonky3_ntt(lib, field_name: str, data: list[int]) -> list[int]:
    """Run Plonky3 NTT via FFI. Returns output in canonical form."""
    n = len(data)
    if field_name in ("babybear", "koalabear", "mersenne31"):
        arr = (ctypes.c_uint32 * n)(*data)
        fn_name = f"plonky3_{field_name}_ntt_forward"
        fn = getattr(lib, fn_name)
        fn.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.c_size_t]
        fn.restype = ctypes.c_int32
        ret = fn(arr, n)
        if ret != 0:
            raise RuntimeError(f"Plonky3 {field_name} NTT failed (ret={ret})")
        return [arr[i] for i in range(n)]
    else:  # goldilocks
        arr = (ctypes.c_uint64 * n)(*data)
        fn = lib.plonky3_ntt_forward
        fn.argtypes = [ctypes.POINTER(ctypes.c_uint64), ctypes.c_size_t]
        fn.restype = ctypes.c_int32
        ret = fn(arr, n)
        if ret != 0:
            raise RuntimeError(f"Plonky3 goldilocks NTT failed (ret={ret})")
        return [arr[i] for i in range(n)]


def trzk_ntt(project_root: Path, field_name: str, log_n: int, use_r4: bool = False) -> list[int]:
    """Generate TRZK C, compile, run, parse output."""
    cmd = ["lake", "env", "lean", "--run", "Tests/benchmark/emit_standard.lean",
           field_name, str(log_n)]
    if use_r4:
        cmd.append("--r4")
    gen = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                         cwd=str(project_root))
    if gen.returncode != 0:
        raise RuntimeError(f"TRZK generation failed: {gen.stderr[:200]}")

    with tempfile.NamedTemporaryFile(suffix=".c", mode="w", delete=False) as f:
        f.write(gen.stdout)
        src_path = f.name
    bin_path = src_path.replace(".c", "")

    comp = subprocess.run(["cc", "-O2", "-o", bin_path, src_path],
                          capture_output=True, text=True)
    if comp.returncode != 0:
        raise RuntimeError(f"TRZK compilation failed: {comp.stderr[:200]}")

    run = subprocess.run([bin_path], capture_output=True, text=True, timeout=30)
    if run.returncode != 0:
        raise RuntimeError(f"TRZK execution failed (exit {run.returncode})")

    return [int(x) for x in run.stdout.strip().split("\n") if x.strip()]


def main():
    parser = argparse.ArgumentParser(description="Oracle Validation: TRZK vs Plonky3")
    parser.add_argument("--fields", default="babybear,goldilocks")
    parser.add_argument("--sizes", default="3,4,5,6,7,8,10")
    parser.add_argument("--project-root", default=None)
    parser.add_argument("--r4", action="store_true", help="Use R4 plans")
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    project_root = Path(args.project_root).resolve() if args.project_root else script_dir.parent.parent

    fields = [f.strip() for f in args.fields.split(",")]
    sizes = [int(s.strip()) for s in args.sizes.split(",")]

    print("TRZK Oracle Validation: TRZK C vs Plonky3 Real (FFI)")
    print(f"  Fields: {fields}")
    print(f"  Sizes:  {['2^'+str(s) for s in sizes]}")
    print(f"  R4:     {args.r4}")
    print()

    lib = load_plonky3_shim(project_root)
    print("Plonky3 shim loaded.\n")

    results = []
    for field_name in fields:
        fdef = get_field(field_name)
        p = fdef.p
        for log_n in sizes:
            n = 1 << log_n
            tag = f"{fdef.display} N={n:5d}"

            # Same deterministic data as benchmark harness
            data = [(i * 1000000007) % p for i in range(n)]

            # Run Plonky3
            try:
                p3_out = plonky3_ntt(lib, field_name, data)
            except Exception as e:
                print(f"  {tag}: P3 FAIL — {e}")
                results.append(False)
                continue

            # Run TRZK
            try:
                trzk_out = trzk_ntt(project_root, field_name, log_n, use_r4=args.r4)
            except Exception as e:
                print(f"  {tag}: TRZK FAIL — {e}")
                results.append(False)
                continue

            # Compare element-by-element mod p
            if len(trzk_out) != n:
                print(f"  {tag}: SIZE MISMATCH (trzk={len(trzk_out)}, expected={n})")
                results.append(False)
                continue

            mismatches = []
            for i in range(n):
                tv = trzk_out[i] % p
                pv = p3_out[i] % p
                if tv != pv:
                    mismatches.append((i, tv, pv))

            if mismatches:
                i, tv, pv = mismatches[0]
                print(f"  {tag}: FAIL at [{i}] TRZK={tv} P3={pv} ({len(mismatches)} total)")
                results.append(False)
            else:
                print(f"  {tag}: PASS ({n}/{n})")
                results.append(True)

    n_pass = sum(results)
    n_fail = len(results) - n_pass
    print(f"\nOracle Validation: {n_pass} PASS, {n_fail} FAIL out of {len(results)}")
    return 1 if n_fail > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
