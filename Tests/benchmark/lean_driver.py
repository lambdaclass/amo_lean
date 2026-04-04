"""Invokes lake env lean --run Bench.lean to generate C/Rust benchmark programs."""

import subprocess
from pathlib import Path
from dataclasses import dataclass


@dataclass
class GeneratedProgram:
    source: str
    lang: str        # "c" or "rust"
    field: str       # "babybear", etc.
    log_n: int
    hardware: str    # "arm-scalar", "arm-neon", "x86-avx2"
    pipeline: str    # "ultra" or "legacy"


class LeanGenerationError(Exception):
    pass


def generate_program(
    project_root: Path,
    field: str,
    log_n: int,
    lang: str = "c",
    hardware: str = "arm-scalar",
    pipeline: str = "ultra",
    timeout: int = 300,
) -> GeneratedProgram:
    """Invoke emit_code.lean to generate raw C/Rust source code."""
    cmd = [
        "lake", "env", "lean", "--run",
        "Tests/benchmark/emit_code.lean",
        field, str(log_n), lang, hardware,
    ]
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        cwd=str(project_root),
        timeout=timeout,
    )
    if result.returncode != 0:
        raise LeanGenerationError(
            f"Lean generation failed for {field}/{log_n}/{lang}/{hardware}:\n{result.stderr[:500]}"
        )
    # Filter out Lean warnings from stdout (they start with filename:line:col)
    lines = result.stdout.split('\n')
    source_lines = [l for l in lines if not (l.strip().startswith('Note:') or
                    ':' in l[:40] and ('warning' in l or 'linter' in l))]
    source = '\n'.join(source_lines)
    if not source.strip():
        raise LeanGenerationError(
            f"Lean produced empty output for {field}/{log_n}/{lang}/{hardware}"
        )
    return GeneratedProgram(
        source=source,
        lang=lang,
        field=field,
        log_n=log_n,
        hardware=hardware,
        pipeline=pipeline,
    )
