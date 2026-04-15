"""Generate Markdown and CSV reports from benchmark results."""

import csv
import datetime
import platform
from pathlib import Path
from dataclasses import dataclass

from validator import ValidationResult
from benchmarker import BenchmarkResult


def generate_report(
    validations: list[ValidationResult],
    benchmarks: list[BenchmarkResult],
    explanations: list[str],
    output_dir: Path,
) -> Path:
    """Generate the full benchmark report."""
    output_dir.mkdir(parents=True, exist_ok=True)
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    arch = f"{platform.system()} {platform.machine()}"

    md_path = output_dir / "bench_report.md"
    csv_path = output_dir / "bench_results.csv"

    # CSV
    with open(csv_path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(["field", "log_n", "lang", "hardware", "validated",
                     "strategy", "amo_us", "p3_naive_us", "melem",
                     "vs_p3_naive_pct", "p3_real_us", "vs_p3_real_pct", "error"])
        for b in benchmarks:
            val = next((v for v in validations
                       if v.field == b.field and v.log_n == b.log_n
                       and v.lang == b.lang and v.hardware == b.hardware), None)
            validated = val.passed if val else False
            p3_real = f"{b.p3_real_us:.1f}" if b.p3_real_us > 0 else "N/A"
            vs_real = f"{b.vs_p3_real_pct:+.1f}" if b.p3_real_us > 0 else "N/A"
            w.writerow([b.field, b.log_n, b.lang, b.hardware, validated,
                       b.strategy, f"{b.amo_us:.1f}", f"{b.p3_us:.1f}",
                       f"{b.melem:.1f}", f"{b.diff_pct:+.1f}",
                       p3_real, vs_real, b.error])

    # Markdown
    lines = [
        f"# TRZK NTT Benchmark Report",
        f"**Date:** {now}",
        f"**Platform:** {arch}",
        "",
        "## Column Legend",
        "",
        "| Column | Description |",
        "|--------|-------------|",
        "| **Lang** | Output language: `c` = compiled C, `rust` = compiled Rust |",
        "| **HW** | Hardware target: `arm-scalar` = no SIMD, `arm-neon` = ARM NEON 4-lane SIMD |",
        "| **AMO** | TRZK Ultra pipeline: verified codegen with e-graph optimization |",
        "| **P3 naive** | Scalar reference using naive `% p` modular reduction (NOT actual Plonky3) |",
        "| **P3 real** | Actual Plonky3 library via FFI (when available) |",
        "| **vs P3 naive** | `(P3_naive - AMO) / P3_naive × 100%` — positive = AMO faster |",
        "| **vs P3 real** | `(P3_real - AMO) / P3_real × 100%` — positive = AMO faster |",
        "",
        "## Validation Summary",
        "",
        "| Field | N | Lang | HW | Status | Details |",
        "|-------|---|------|----|--------|---------|",
    ]
    for v in validations:
        status = "PASS" if v.passed else "**FAIL**"
        detail = f"{v.num_checked} elements" if v.passed else v.error[:60]
        lines.append(f"| {v.field} | 2^{v.log_n} | {v.lang} | {v.hardware} | {status} | {detail} |")

    lines += ["", "## Performance Results", ""]

    # Only show results where validation passed
    valid_set = {(v.field, v.log_n, v.lang, v.hardware) for v in validations if v.passed}
    valid_benchmarks = [b for b in benchmarks
                       if (b.field, b.log_n, b.lang, b.hardware) in valid_set and not b.error]

    has_p3_real = any(b.p3_real_us > 0 for b in valid_benchmarks)

    if valid_benchmarks:
        if has_p3_real:
            lines += [
                "| Field | N | Lang | HW | AMO (μs) | P3 naive (μs) | vs naive | P3 real (μs) | vs real |",
                "|-------|---|------|----|----------|---------------|----------|--------------|---------|",
            ]
            for b in valid_benchmarks:
                p3r = f"{b.p3_real_us:.1f}" if b.p3_real_us > 0 else "—"
                vsr = f"{b.vs_p3_real_pct:+.1f}%" if b.p3_real_us > 0 else "—"
                lines.append(
                    f"| {b.field} | 2^{b.log_n} | {b.lang} | {b.hardware} | "
                    f"{b.amo_us:.1f} | {b.p3_us:.1f} | {b.diff_pct:+.1f}% | {p3r} | {vsr} |"
                )
        else:
            lines += [
                "| Field | N | Lang | HW | AMO (μs) | P3 naive (μs) | vs naive |",
                "|-------|---|------|----|----------|---------------|----------|",
            ]
            for b in valid_benchmarks:
                lines.append(
                    f"| {b.field} | 2^{b.log_n} | {b.lang} | {b.hardware} | "
                    f"{b.amo_us:.1f} | {b.p3_us:.1f} | {b.diff_pct:+.1f}% |"
                )
    else:
        lines.append("*No valid benchmark results.*")

    # Notes on what was tested and what was not
    lines += ["", "## Notes", ""]
    tested_combos = {(b.lang, b.hardware) for b in valid_benchmarks}
    all_combos = {("c", "arm-scalar"), ("c", "arm-neon"), ("rust", "arm-scalar"), ("rust", "arm-neon")}
    missing = all_combos - tested_combos
    if tested_combos:
        lines.append("**Configurations tested:**")
        for lang, hw in sorted(tested_combos):
            hw_desc = "ARM scalar (no SIMD)" if hw == "arm-scalar" else "ARM NEON (4-lane uint32 SIMD)"
            lines.append(f"- `{lang}` / `{hw}`: {hw_desc}")
    if missing:
        lines.append("")
        lines.append("**Configurations not tested in this run:**")
        for lang, hw in sorted(missing):
            lines.append(f"- `{lang}` / `{hw}`")
    if not has_p3_real:
        lines.append("")
        lines.append("**P3 real (Plonky3 via FFI):** Not available in this run. "
                     "The P3 naive column uses scalar `% p` modular reduction — "
                     "it is NOT representative of actual Plonky3 performance which uses "
                     "Montgomery SIMD (sqdmulh on NEON, vpmuludq on AVX2).")

    # Errors
    errors = [b for b in benchmarks if b.error]
    failed_vals = [v for v in validations if not v.passed]
    if errors or failed_vals:
        lines += ["", "## Errors", ""]
        for v in failed_vals:
            lines.append(f"- **VALIDATION FAIL** {v.field}/2^{v.log_n}/{v.lang}/{v.hardware}: {v.error}")
        for b in errors:
            lines.append(f"- **BENCH ERROR** {b.field}/2^{b.log_n}/{b.lang}/{b.hardware}: {b.error}")

    # Explanations
    if explanations:
        lines += ["", "## Cost Model Explanations", ""]
        for exp in explanations:
            lines.append(f"```\n{exp}\n```")

    md_path.write_text('\n'.join(lines) + '\n')
    return md_path
