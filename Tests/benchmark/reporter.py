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
                     "strategy", "amo_us", "p3_us", "melem", "diff_pct", "error"])
        for b in benchmarks:
            val = next((v for v in validations
                       if v.field == b.field and v.log_n == b.log_n
                       and v.lang == b.lang and v.hardware == b.hardware), None)
            validated = val.passed if val else False
            w.writerow([b.field, b.log_n, b.lang, b.hardware, validated,
                       b.strategy, f"{b.amo_us:.1f}", f"{b.p3_us:.1f}",
                       f"{b.melem:.1f}", f"{b.diff_pct:+.1f}", b.error])

    # Markdown
    lines = [
        f"# AMO-Lean NTT Benchmark Report",
        f"**Date:** {now}",
        f"**Platform:** {arch}",
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

    if valid_benchmarks:
        lines += [
            "| Field | N | Lang | HW | AMO (us) | P3 (us) | Melem/s | vs P3 |",
            "|-------|---|------|----|----------|---------|---------|-------|",
        ]
        for b in valid_benchmarks:
            lines.append(
                f"| {b.field} | 2^{b.log_n} | {b.lang} | {b.hardware} | "
                f"{b.amo_us:.1f} | {b.p3_us:.1f} | {b.melem:.1f} | {b.diff_pct:+.1f}% |"
            )
    else:
        lines.append("*No valid benchmark results.*")

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
