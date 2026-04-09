"""Performance measurement: compile and run the full benchmark program, parse CSV."""

import subprocess
from pathlib import Path
from dataclasses import dataclass

from lean_driver import GeneratedProgram
from compiler import compile_c, compile_rust


@dataclass
class BenchmarkResult:
    field: str
    log_n: int
    lang: str
    hardware: str
    strategy: str          # "ultra" or e-graph result
    amo_us: float          # AMO time in microseconds
    p3_us: float           # P3 reference time in microseconds
    melem: float           # Million elements/second
    diff_pct: float        # % difference (positive = AMO faster)
    error: str = ""


def run_benchmark(
    program: GeneratedProgram,
    work_dir: Path,
    timeout: int = 300,
) -> BenchmarkResult:
    """Compile and run the full benchmark program, parse CSV output.

    The generated program includes:
    - Internal correctness check (Ultra vs P3, exits 1 on mismatch)
    - Warmup + timing for both implementations
    - CSV output: "FieldName,strategy,amo_us,p3_us,melem,diff_pct"
    """
    tag = f"{program.field}_{program.log_n}_{program.lang}_{program.hardware}"
    ext = ".c" if program.lang == "c" else ".rs"
    src_path = work_dir / f"bench_{tag}{ext}"
    bin_path = work_dir / f"bench_{tag}"
    src_path.write_text(program.source)

    # Compile
    if program.lang == "c":
        cr = compile_c(src_path, bin_path, program.hardware)
    else:
        cr = compile_rust(src_path, bin_path)

    if not cr.success:
        return BenchmarkResult(program.field, program.log_n, program.lang,
                               program.hardware, "", 0, 0, 0, 0,
                               f"Compile error: {cr.error}")

    # Run
    try:
        result = subprocess.run(
            [str(bin_path)], capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return BenchmarkResult(program.field, program.log_n, program.lang,
                               program.hardware, "", 0, 0, 0, 0, "Timeout")

    if result.returncode != 0:
        return BenchmarkResult(program.field, program.log_n, program.lang,
                               program.hardware, "", 0, 0, 0, 0,
                               f"Runtime error (code {result.returncode}): {result.stderr[:200]}")

    # Parse CSV — find the line matching FieldName pattern
    for line in result.stdout.strip().split('\n'):
        parts = line.strip().split(',')
        if len(parts) >= 6:
            try:
                return BenchmarkResult(
                    field=program.field,
                    log_n=program.log_n,
                    lang=program.lang,
                    hardware=program.hardware,
                    strategy=parts[1].strip(),
                    amo_us=float(parts[2]),
                    p3_us=float(parts[3]),
                    melem=float(parts[4]),
                    diff_pct=float(parts[5]),
                )
            except (ValueError, IndexError):
                continue

    return BenchmarkResult(program.field, program.log_n, program.lang,
                           program.hardware, "", 0, 0, 0, 0,
                           f"No CSV output found in: {result.stdout[:200]}")
