"""Compile C and Rust source files."""

import subprocess
import platform
from pathlib import Path
from dataclasses import dataclass


@dataclass
class CompileResult:
    success: bool
    binary: Path
    error: str = ""


def compile_c(source: Path, output: Path, hardware: str = "arm-scalar") -> CompileResult:
    """Compile C source with cc -O2. Adds NEON/AVX2 flags as needed."""
    flags = ["-O2", "-lm"]
    arch = platform.machine()
    if hardware == "arm-neon":
        if arch not in ("arm64", "aarch64"):
            return CompileResult(False, output, f"NEON requires ARM, got {arch}")
    elif hardware == "x86-avx2":
        if arch not in ("x86_64", "AMD64"):
            return CompileResult(False, output, f"AVX2 requires x86_64, got {arch}")
        flags.append("-mavx2")

    cmd = ["cc"] + flags + [str(source), "-o", str(output)]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if result.returncode != 0:
        return CompileResult(False, output, result.stderr[:500])
    return CompileResult(True, output)


def compile_rust(source: Path, output: Path) -> CompileResult:
    """Compile Rust source with rustc -O."""
    cmd = ["rustc", "-O", str(source), "-o", str(output)]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if result.returncode != 0:
        return CompileResult(False, output, result.stderr[:500])
    return CompileResult(True, output)
