#!/usr/bin/env python3
"""AMO-Lean NTT Benchmark Harness.

Validates correctness BEFORE measuring performance.
Independent Python NTT reference for cross-validation.

Usage:
    python3 benchmark.py --fields babybear --sizes 14 --langs c --hardware arm-scalar
    python3 benchmark.py --fields all --sizes 14,16,18 --langs c,rust
    python3 benchmark.py --fields babybear --sizes 14 --validation-only
"""

import argparse
import sys
import tempfile
from pathlib import Path

from field_defs import ALL_FIELDS, get_field
from lean_driver import generate_program, LeanGenerationError
from validator import validate
from benchmarker import run_benchmark
from cost_explainer import format_explanation
from reporter import generate_report


def main():
    parser = argparse.ArgumentParser(description="AMO-Lean NTT Benchmark Harness")
    parser.add_argument("--fields", default="babybear,koalabear,mersenne31",
                        help="Comma-separated fields or 'all'")
    parser.add_argument("--sizes", default="14,16",
                        help="Comma-separated log2(N) values")
    parser.add_argument("--langs", default="c",
                        help="Comma-separated: c, rust, or both")
    parser.add_argument("--hardware", default="arm-scalar",
                        help="arm-scalar, arm-neon, x86-avx2")
    parser.add_argument("--pipeline", default="ultra", choices=["legacy", "ultra"])
    parser.add_argument("--output-dir", default=None,
                        help="Output directory (default: Tests/benchmark/output)")
    parser.add_argument("--project-root", default=None,
                        help="Project root (default: auto-detect)")
    parser.add_argument("--validation-only", action="store_true",
                        help="Only validate correctness, skip performance")
    parser.add_argument("--skip-validation", action="store_true",
                        help="Skip validation, only measure (DANGEROUS)")
    args = parser.parse_args()

    # Resolve paths
    script_dir = Path(__file__).resolve().parent
    if args.project_root:
        project_root = Path(args.project_root).resolve()
    else:
        project_root = script_dir.parent.parent  # Tests/benchmark/../../

    if args.output_dir:
        output_dir = Path(args.output_dir)
    else:
        output_dir = script_dir / "output"

    # Parse field list
    if args.fields == "all":
        fields = list(ALL_FIELDS.keys())
    else:
        fields = [f.strip() for f in args.fields.split(",")]

    sizes = [int(s.strip()) for s in args.sizes.split(",")]
    langs = [l.strip() for l in args.langs.split(",")]
    hardware = args.hardware

    print(f"AMO-Lean NTT Benchmark Harness")
    print(f"  Fields:   {fields}")
    print(f"  Sizes:    {['2^'+str(s) for s in sizes]}")
    print(f"  Langs:    {langs}")
    print(f"  Hardware: {hardware}")
    print(f"  Pipeline: {args.pipeline}")
    print(f"  Project:  {project_root}")
    print()

    validations = []
    benchmarks = []
    explanations = []

    with tempfile.TemporaryDirectory(prefix="amobench_") as tmpdir:
        work_dir = Path(tmpdir)

        for field_name in fields:
            field = get_field(field_name)
            for log_n in sizes:
                for lang in langs:
                    tag = f"{field_name}/2^{log_n}/{lang}/{hardware}"

                    # Phase 1: Generate
                    print(f"[GEN] {tag} ... ", end="", flush=True)
                    try:
                        program = generate_program(
                            project_root, field_name, log_n, lang,
                            hardware, args.pipeline
                        )
                        print("OK")
                    except LeanGenerationError as e:
                        print(f"FAIL: {e}")
                        continue
                    except Exception as e:
                        print(f"ERROR: {e}")
                        continue

                    # Phase 2: Validate
                    if not args.skip_validation:
                        print(f"[VAL] {tag} ... ", end="", flush=True)
                        vr = validate(program, field, work_dir)
                        validations.append(vr)
                        if vr.passed:
                            print(f"PASS ({vr.num_checked} elements)")
                        else:
                            print(f"FAIL: {vr.error}")
                            continue  # Don't benchmark if validation failed

                    # Phase 3: Benchmark (unless validation-only)
                    if not args.validation_only:
                        print(f"[RUN] {tag} ... ", end="", flush=True)
                        br = run_benchmark(program, work_dir)
                        benchmarks.append(br)
                        if not br.error:
                            print(f"{br.amo_us:.1f}us (P3: {br.p3_us:.1f}us, {br.diff_pct:+.1f}%)")
                        else:
                            print(f"ERROR: {br.error}")

                    # Phase 4: Explain (once per field/size, not per lang)
                    if lang == langs[0]:
                        explanations.append(format_explanation(program))

    # Phase 5: Report
    print()
    report_path = generate_report(validations, benchmarks, explanations, output_dir)
    print(f"Report written to: {report_path}")

    # Summary
    n_pass = sum(1 for v in validations if v.passed)
    n_fail = sum(1 for v in validations if not v.passed)
    print(f"\nValidation: {n_pass} PASS, {n_fail} FAIL")
    if benchmarks:
        valid_b = [b for b in benchmarks if not b.error]
        print(f"Benchmarks: {len(valid_b)} completed, {len(benchmarks) - len(valid_b)} errors")

    return 1 if n_fail > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
