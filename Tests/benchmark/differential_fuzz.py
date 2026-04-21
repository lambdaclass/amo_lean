#!/usr/bin/env python3
"""Triangular differential fuzzing: TRZK vs Plonky3 vs Python naive.

v3.18.0: replaces single-point oracle (v3.16.0 B1, 14-24 test points) with
thousands of random + edge-case inputs. Reuses ~70% of existing infrastructure.

3-way comparison (N ≤ 1024): TRZK == Plonky3 == Python naive (ground truth).
2-way comparison (N > 1024): TRZK == Plonky3 (Python O(N²) too slow).

Modes:
    fast   : 100 random inputs + ~15 edge cases per (field × size). ~30-60s.
    medium : 1000 random + edges. ~3 min.
    full   : 10000 random + edges. ~10-30 min.

Usage:
    python3 Tests/benchmark/differential_fuzz.py --mode fast
    python3 Tests/benchmark/differential_fuzz.py --mode full --seed 42
    python3 Tests/benchmark/differential_fuzz.py --fields goldilocks --sizes 3,6,8,10
"""

import argparse
import json
import os
import random
import subprocess
import sys
import tempfile
from pathlib import Path

# Add benchmark dir to path for sibling imports
sys.path.insert(0, str(Path(__file__).resolve().parent))

from oracle_validate import load_plonky3_shim, plonky3_ntt
from field_defs import get_field
from test_four_step import naive_dft
from compiler import compile_c


# ═══════════════════════════════════════════════════════════════════
# N318.3 — Edge cases (~15 patterns)
# ═══════════════════════════════════════════════════════════════════

def edge_cases(field_name: str, n: int) -> list[tuple[str, list[int]]]:
    """~15 structured inputs that stress specific code paths.

    Deterministic: no randomness, same output every call.
    Patterns target bugs like L-732 (int64 overflow), L-733 (DIT/DIF mix),
    L-739 (codegen emission gap) — boundary values that the linear oracle
    pattern (i * 1000000007 % p) never reaches.
    """
    p = get_field(field_name).p
    return [
        ("all-zero",          [0] * n),
        ("all-p-minus-1",     [p - 1] * n),
        ("all-half-p",        [p // 2] * n),
        ("single-1-at-0",     [1] + [0] * (n - 1)),
        ("single-max-at-0",   [p - 1] + [0] * (n - 1)),
        ("single-max-middle", [0] * (n // 2) + [p - 1] + [0] * (n // 2 - 1)),
        ("alt-0-max",         [(i % 2) * (p - 1) for i in range(n)]),
        ("alt-1-max",         [1 if i % 2 == 0 else p - 1 for i in range(n)]),
        ("powers-of-2",       [pow(2, i % 32, p) for i in range(n)]),
        ("ascending",         [i % p for i in range(n)]),
        ("descending",        [(p - 1 - i) % p for i in range(n)]),
        ("near-2^32",         [min((1 << 32) - 1 + (i % 3), p - 1) for i in range(n)]),
        ("near-2^63",         [min((1 << 63) + i, p - 1) for i in range(n)]),
        ("small-values",      [i % 17 for i in range(n)]),
        ("palindrome",        [i if i < n // 2 else n - 1 - i for i in range(n)]),
    ]


# ═══════════════════════════════════════════════════════════════════
# N318.2 — trzk_ntt_with_input (stdin-driven harness, binary cache)
# ═══════════════════════════════════════════════════════════════════

def _compile_trzk_binary(project_root: Path, field_name: str, log_n: int,
                         work_dir: Path) -> Path:
    """Generate NTT function via emit_standard.lean, wrap with stdin harness, compile."""
    n = 1 << log_n
    fd = get_field(field_name)
    p, g, k = fd.p, fd.generator, fd.k
    elem_type = "uint64_t" if k > 32 else "int32_t"
    wide_type = "__uint128_t" if k > 32 else "int64_t"
    p_lit = f"{p}ULL"

    # Step 1: generate NTT function + preambles via Lean
    cmd = ["lake", "env", "lean", "--run", "Tests/benchmark/emit_standard.lean",
           field_name, str(log_n)]
    gen = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                         cwd=str(project_root))
    if gen.returncode != 0:
        raise RuntimeError(f"emit_standard.lean failed: {gen.stderr[:300]}")

    # Step 2: extract NTT function (everything before `int main`)
    full_code = gen.stdout
    main_idx = full_code.find("int main(void)")
    if main_idx == -1:
        raise RuntimeError("Cannot find 'int main(void)' in generated code")
    ntt_code = full_code[:main_idx]

    # Step 3: build stdin-driven harness
    func_name = f"{field_name}_ntt_standard"
    r_lit = "(__uint128_t)1<<64" if k > 32 else "4294967296ULL"

    # ntt_code already includes #include headers and mod_pow from emit_standard.lean.
    # We only need to append a new main() that reads from stdin instead of hardcoded data.
    harness = ntt_code + "\n"

    harness += "int main(void) {\n"
    harness += f"  size_t n = {n}, logn = {log_n};\n"
    harness += f"  {wide_type} p_val = ({wide_type}){p_lit};\n"
    harness += f"  {wide_type} omega_n = mod_pow({g}, (p_val - 1) / n, p_val);\n"
    harness += f"  size_t tw_sz = n * logn;\n"
    harness += f"  {elem_type} *tw = malloc(tw_sz * sizeof({elem_type}));\n"
    harness += "  for(size_t st=0; st<logn; st++) {\n"
    harness += "    size_t h = 1u << (logn - 1 - st);\n"
    harness += "    for(size_t gg=0; gg<(1u<<st); gg++)\n"
    harness += "      for(size_t pp=0; pp<h; pp++)\n"
    harness += f"        tw[st*(n/2)+gg*h+pp] = ({elem_type})mod_pow(omega_n, pp*(1ULL<<st), p_val);\n"
    harness += "  }\n"

    if k > 32:
        # Goldilocks: standard twiddles
        harness += f"  {elem_type} *tw_ntt = tw;\n"
    else:
        # BabyBear: Montgomery twiddles
        harness += f"  {elem_type} *tw_mont = malloc(tw_sz * sizeof({elem_type}));\n"
        harness += f"  for(size_t i=0; i<tw_sz; i++) tw_mont[i] = ({elem_type})((({wide_type})tw[i] * ({wide_type}){r_lit}) % ({wide_type}){p_lit});\n"
        harness += f"  {elem_type} *tw_ntt = tw_mont;\n"

    # Read input from stdin
    harness += f"  {elem_type} *d = malloc(n * sizeof({elem_type}));\n"
    harness += "  for(size_t i=0; i<n; i++) {\n"
    harness += "    unsigned long long v; scanf(\"%llu\", &v);\n"
    harness += f"    d[i] = ({elem_type})v;\n"
    harness += "  }\n"
    harness += f"  {func_name}(d, tw_ntt);\n"
    # Print output (canonical mod p)
    harness += f"  for(size_t i=0; i<n; i++) printf(\"%llu\\n\", (unsigned long long)(({wide_type})d[i] % ({wide_type}){p_lit}));\n"
    harness += "  free(d); free(tw);\n"
    if k <= 32:
        harness += "  free(tw_mont);\n"
    harness += "  return 0;\n}\n"

    # Step 4: compile
    src_path = work_dir / f"trzk_fuzz_{field_name}_{log_n}.c"
    bin_path = work_dir / f"trzk_fuzz_{field_name}_{log_n}"
    src_path.write_text(harness)

    cr = compile_c(src_path, bin_path, hardware="arm-scalar",
                   field_k=k, profile="conservative")
    if not cr.success:
        raise RuntimeError(f"Compilation failed: {cr.error[:300]}")

    return bin_path


def trzk_ntt_with_input(project_root: Path, field_name: str, log_n: int,
                        input_data: list[int], binary_cache: dict,
                        work_dir: Path = None) -> list[int]:
    """Run TRZK NTT with arbitrary input via stdin-driven cached binary.

    binary_cache: dict {(field, log_n): Path(binary)} — compiles ONCE, reuses N times.
    """
    key = (field_name, log_n)
    if key not in binary_cache:
        if work_dir is None:
            raise RuntimeError("work_dir required for first compilation")
        binary_cache[key] = _compile_trzk_binary(project_root, field_name, log_n, work_dir)

    # Run binary with input from stdin
    stdin_data = "\n".join(str(x) for x in input_data) + "\n"
    run = subprocess.run(
        [str(binary_cache[key])],
        input=stdin_data, capture_output=True, text=True, timeout=30
    )
    if run.returncode != 0:
        raise RuntimeError(f"TRZK binary failed: {run.stderr[:200]}")

    lines = [l.strip() for l in run.stdout.strip().split("\n") if l.strip()]
    return [int(x) for x in lines]


# ═══════════════════════════════════════════════════════════════════
# N318.4 — fuzz_one (3-way / 2-way) + main orchestration
# ═══════════════════════════════════════════════════════════════════

def fuzz_one(lib, project_root: Path, field_name: str, log_n: int,
             input_data: list[int], binary_cache: dict,
             work_dir: Path) -> tuple[bool, str, dict]:
    """Single fuzz iteration. 3-way for N ≤ 1024, 2-way for N > 1024."""
    n = 1 << log_n
    p = get_field(field_name).p
    g = get_field(field_name).generator

    trzk_out = trzk_ntt_with_input(project_root, field_name, log_n,
                                    input_data, binary_cache, work_dir)
    p3_out = plonky3_ntt(lib, field_name, input_data)

    # Canonicalize both outputs mod p
    trzk_out = [x % p for x in trzk_out]
    p3_out = [x % p for x in p3_out]

    if n <= 1024:
        omega_n = pow(g, (p - 1) // n, p)
        py_out = naive_dft(input_data, omega_n, p)
        py_out = [x % p for x in py_out]
        if trzk_out == p3_out == py_out:
            return True, "3-way PASS", {}
        # Diagnose which disagrees
        detail = {}
        if trzk_out != p3_out:
            for i in range(n):
                if trzk_out[i] != p3_out[i]:
                    detail["first_diff_idx"] = i
                    detail["trzk"] = trzk_out[i]
                    detail["p3"] = p3_out[i]
                    break
            detail["type"] = "TRZK != Plonky3"
        elif trzk_out != py_out:
            for i in range(n):
                if trzk_out[i] != py_out[i]:
                    detail["first_diff_idx"] = i
                    detail["trzk"] = trzk_out[i]
                    detail["py"] = py_out[i]
                    break
            detail["type"] = "TRZK != Python naive (Plonky3 agrees with TRZK)"
        return False, "3-way FAIL", detail
    else:
        if trzk_out == p3_out:
            return True, "2-way PASS", {}
        for i in range(n):
            if trzk_out[i] != p3_out[i]:
                return False, "2-way FAIL", {
                    "first_diff_idx": i,
                    "trzk": trzk_out[i],
                    "p3": p3_out[i],
                }
        return True, "2-way PASS", {}  # shouldn't reach


def _batch_mode_run(project_root: Path, fields: list, sizes: list,
                     batch_widths: list, iters: int, seed: int) -> int:
    """v3.20.b B6.2 — batch mode: differentially fuzz TRZK-batch (from
    emit_batch_code.lean, B4 loop-wrapping path) vs B independent
    single-vector invocations (via `{field}_ntt_batch_single`, emitted
    in the SAME C binary). Same-C-binary comparison avoids cross-language
    variance; tests the offset arithmetic in `batchOffsetAssign` +
    outer for-loop semantics in `lowerNTTFromPlanBatch`.

    Target: iters/iters PASS across (field × size × width) combos.
    Fails only on offset arithmetic bugs or outer loop termination issues.
    """
    import math, ctypes
    rng = random.Random(seed)
    total, passed = 0, 0
    print(f"[B6.2 batch] seed={seed} iters={iters}/combo")
    with tempfile.TemporaryDirectory(prefix="trzk_fuzz_batch_") as tmp:
        tmpd = Path(tmp)
        for field_name in fields:
            p = get_field(field_name).p
            elem_type = "uint64_t" if field_name == "goldilocks" else "int32_t"
            ctype_elem = ctypes.c_uint64 if field_name == "goldilocks" else ctypes.c_int32
            for log_n in sizes:
                n = 1 << log_n
                tw_count = log_n * (n // 2)
                for B in batch_widths:
                    combo_tag = f"{field_name} N=2^{log_n} B={B}"
                    # Emit + compile batch C with a tiny harness that
                    # exposes run_batch(data, tw, B) and run_single(data, tw)
                    # entry points from the emitted C.
                    batch_c = tmpd / f"batch_{field_name}_{log_n}_{B}.c"
                    # emit with includes prepended
                    emit_cmd = ["lake", "env", "lean", "--run",
                                str(project_root / "Tests/benchmark/emit_batch_code.lean"),
                                field_name, str(log_n), str(B)]
                    result = subprocess.run(emit_cmd, cwd=str(project_root),
                                            capture_output=True, text=True, timeout=180)
                    if result.returncode != 0:
                        print(f"  [FAIL-emit] {combo_tag}: {result.stderr[:200]}")
                        continue
                    batch_c.write_text(
                        "#include <stdint.h>\n#include <stddef.h>\n" + result.stdout)
                    # Compile to shared library
                    so_path = tmpd / f"batch_{field_name}_{log_n}_{B}.so"
                    cc_cmd = ["cc", "-O3", "-mcpu=apple-m1", "-shared", "-fPIC",
                              "-o", str(so_path), str(batch_c)]
                    cc_result = subprocess.run(cc_cmd, capture_output=True, text=True, timeout=120)
                    if cc_result.returncode != 0:
                        print(f"  [FAIL-compile] {combo_tag}: {cc_result.stderr[:200]}")
                        continue
                    lib = ctypes.CDLL(str(so_path))
                    batch_fn = getattr(lib, f"{field_name}_ntt_batch")
                    single_fn = getattr(lib, f"{field_name}_ntt_batch_single")
                    batch_fn.restype = None
                    single_fn.restype = None
                    batch_fn.argtypes = [ctypes.POINTER(ctype_elem),
                                         ctypes.POINTER(ctype_elem), ctypes.c_size_t]
                    single_fn.argtypes = [ctypes.POINTER(ctype_elem),
                                          ctypes.POINTER(ctype_elem)]
                    # Shared twiddle table (deterministic per combo)
                    TwArr = ctype_elem * tw_count
                    tw_seed_rng = random.Random(seed ^ (log_n << 8) ^ B)
                    tw_arr = TwArr(*[tw_seed_rng.randrange(p) for _ in range(tw_count)])
                    combo_pass = 0
                    DataArr = ctype_elem * (B * n)
                    SingleArr = ctype_elem * n
                    for i in range(iters):
                        # Random batch input
                        input_vals = [rng.randrange(p) for _ in range(B * n)]
                        batch_data = DataArr(*input_vals)
                        batch_fn(batch_data, tw_arr, B)
                        # Reference: B independent single-vector calls
                        ok = True
                        mismatch_idx = -1
                        for b_idx in range(B):
                            single_data = SingleArr(*input_vals[b_idx * n:(b_idx + 1) * n])
                            single_fn(single_data, tw_arr)
                            for j in range(n):
                                bv = int(batch_data[b_idx * n + j]) & ((1 << (64 if field_name == "goldilocks" else 32)) - 1)
                                sv = int(single_data[j]) & ((1 << (64 if field_name == "goldilocks" else 32)) - 1)
                                if bv != sv:
                                    ok = False
                                    mismatch_idx = b_idx * n + j
                                    break
                            if not ok:
                                break
                        total += 1
                        if ok:
                            passed += 1
                            combo_pass += 1
                        else:
                            if total - passed <= 3:
                                print(f"  [MISMATCH] {combo_tag} iter={i} idx={mismatch_idx}")
                    print(f"  {combo_tag}: {combo_pass}/{iters} PASS")
    print(f"\n[B6.2 batch] TOTAL: {passed}/{total} PASS ({passed*100/max(total,1):.2f}%)")
    return 0 if passed == total else 1


def main():
    parser = argparse.ArgumentParser(
        description="TRZK Differential Fuzzing (v3.18.0 + v3.20.b batch mode)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="Modes:\n  fast   100 random + edges (~30-60s)\n"
               "  medium 1000 random + edges (~3min)\n"
               "  full   10000 random + edges (~10-30min)\n"
               "  batch  v3.20.b B6.2 — batch vs B×single, same C binary")
    parser.add_argument("--mode", default="fast",
                        choices=["fast", "medium", "full", "batch"])
    parser.add_argument("--fields", default="goldilocks,babybear")
    parser.add_argument("--sizes", default="3,6,8,10,14",
                        help="Comma-separated log2(N). Default: 3,6,8,10,14")
    parser.add_argument("--seed", type=int, default=None,
                        help="Random seed (logged for reproducibility)")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--fail-fast", action="store_true",
                        help="Stop on first failure")
    parser.add_argument("--save-failures", default="/tmp/trzk_fuzz_failures",
                        help="Directory for counterexample dumps")
    parser.add_argument("--batch-width", default="4,16",
                        help="(batch mode) comma-separated batch widths")
    parser.add_argument("--iters", type=int, default=1000,
                        help="(batch mode) iterations per (field × size × width)")
    args = parser.parse_args()

    # v3.20.b B6.2 — batch mode dispatch
    if args.mode == "batch":
        script_dir = Path(__file__).resolve().parent
        project_root = script_dir.parent.parent
        fields = [f.strip() for f in args.fields.split(",") if f.strip() == "babybear"]
        if not fields:
            fields = ["babybear"]  # batch mode BabyBear-only in Phase 1
        sizes = [int(s.strip()) for s in args.sizes.split(",")
                 if int(s.strip()) >= 3]  # min N=8 for meaningful batch
        widths = [int(w.strip()) for w in args.batch_width.split(",")]
        seed = args.seed if args.seed is not None else random.randrange(2**32)
        print(f"=== TRZK Differential Fuzz v3.20.b B6.2 (batch mode) ===")
        print(f"Seed:     {seed}")
        print(f"Fields:   {fields}")
        print(f"Sizes:    {sizes}")
        print(f"Widths:   {widths}")
        print(f"Iters:    {args.iters}/combo")
        print()
        return _batch_mode_run(project_root, fields, sizes, widths,
                               args.iters, seed)

    n_random = {"fast": 100, "medium": 1000, "full": 10000}[args.mode]
    seed = args.seed if args.seed is not None else random.randrange(2**32)
    rng = random.Random(seed)

    script_dir = Path(__file__).resolve().parent
    project_root = script_dir.parent.parent

    print(f"=== TRZK Differential Fuzzing v3.18.0 ({args.mode} mode) ===")
    print(f"Seed:     {seed}")
    print(f"Random:   {n_random} per (field × size)")
    print(f"Edge:     ~{len(edge_cases('babybear', 8))} per (field × size)")
    print(f"Fields:   {args.fields}")
    print(f"Sizes:    {args.sizes}")
    print(f"Project:  {project_root}")
    print()

    lib = load_plonky3_shim(project_root)
    binary_cache = {}
    total, passed, failures = 0, 0, []

    with tempfile.TemporaryDirectory(prefix="trzk_fuzz_") as tmpdir:
        work_dir = Path(tmpdir)

        for field_name in args.fields.split(","):
            for log_n in [int(s) for s in args.sizes.split(",")]:
                n = 1 << log_n
                way = "3-way" if n <= 1024 else "2-way"
                tag = f"{field_name:12} N=2^{log_n:<2} ({n:>5}) [{way}]"
                field_pass = 0
                field_total = 0

                # Edge cases
                for name, inp in edge_cases(field_name, n):
                    ok, msg, detail = fuzz_one(lib, project_root, field_name,
                                                log_n, inp, binary_cache, work_dir)
                    total += 1
                    field_total += 1
                    if ok:
                        passed += 1
                        field_pass += 1
                    else:
                        failures.append({
                            "field": field_name, "log_n": log_n,
                            "desc": f"edge:{name}", "msg": msg,
                            "detail": detail, "input_head": inp[:5],
                        })
                        if args.fail_fast:
                            break
                    if args.verbose:
                        status = "PASS" if ok else f"FAIL ({msg})"
                        print(f"    edge:{name:20} {status}")

                if args.fail_fast and failures:
                    break

                # Random iterations
                for i in range(n_random):
                    inp = [rng.randrange(get_field(field_name).p) for _ in range(n)]
                    ok, msg, detail = fuzz_one(lib, project_root, field_name,
                                                log_n, inp, binary_cache, work_dir)
                    total += 1
                    field_total += 1
                    if ok:
                        passed += 1
                        field_pass += 1
                    else:
                        failures.append({
                            "field": field_name, "log_n": log_n,
                            "desc": f"random:{i}", "msg": msg,
                            "detail": detail, "input_head": inp[:5],
                            "seed": seed, "iter": i,
                        })
                        if args.fail_fast:
                            break

                print(f"  {tag}: {field_pass}/{field_total} PASS")
                if args.fail_fast and failures:
                    break
            if args.fail_fast and failures:
                break

    # Summary
    print(f"\n{'=' * 65}")
    pct = 100 * passed / total if total > 0 else 0
    print(f"TOTAL: {passed}/{total} PASS ({pct:.2f}%)")
    print(f"Seed: {seed} (re-run with --seed {seed} to reproduce)")

    if failures:
        print(f"\nFAILURES ({len(failures)}):")
        for f in failures[:10]:
            print(f"  {f['field']} N=2^{f['log_n']} {f['desc']}: {f['msg']}")
            if f.get('detail'):
                print(f"    {f['detail']}")
        # Save counterexamples
        save_dir = Path(args.save_failures)
        save_dir.mkdir(parents=True, exist_ok=True)
        for i, f in enumerate(failures[:20]):
            fp = save_dir / f"failure_{i}_{f['field']}_{f['log_n']}_{f['desc'].replace(':','_')}.json"
            fp.write_text(json.dumps(f, indent=2, default=str))
        print(f"\nCounterexamples saved to {save_dir}")
        return 1

    print("\nAll tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
