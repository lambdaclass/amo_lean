"""Compile C and Rust source files.

v3.17.0 N317.8: `profile` parameter for benchmark fairness.
  conservative  — default, cc -O2 (TRZK historical)
  match-plonky3 — -O3 + LTO + CPU target, matches Plonky3 release profile
"""

import subprocess
import platform
from pathlib import Path
from dataclasses import dataclass


@dataclass
class CompileResult:
    success: bool
    binary: Path
    error: str = ""


# v3.17.0 N317.8: profile presets.
# match-plonky3 aligns with Plonky3 Cargo.toml:20-24 (lto=true, opt-level=3,
# codegen-units=1, panic=abort). On Apple Silicon use -mcpu=apple-m1 (INV1
# measured -march=native outliers 560μs); on other ARM64 use generic; on
# x86_64 use -march=native.
def _cpu_flag(arch: str) -> list[str]:
    """Return CPU-specific optimization flag for match-plonky3 profile."""
    system = platform.system()
    if arch in ("arm64", "aarch64"):
        if system == "Darwin":
            return ["-mcpu=apple-m1"]
        return ["-mcpu=native"]
    if arch in ("x86_64", "AMD64"):
        return ["-march=native"]
    return []  # unknown arch — skip cpu-specific flag


def compile_c(source: Path, output: Path, hardware: str = "arm-scalar",
              field_k: int = 31, profile: str = "conservative") -> CompileResult:
    """Compile C source.

    Args:
      profile: "conservative" → cc -O2 (historical).
               "match-plonky3" → -O3 -flto + CPU target (paridad con Plonky3 release).
    """
    arch = platform.machine()
    if profile == "match-plonky3":
        flags = ["-O3", "-flto"] + _cpu_flag(arch) + ["-lm"]
    else:  # conservative
        flags = ["-O2", "-lm"]
    # Suppress unsigned literal warnings only for 64-bit fields (Goldilocks)
    # where p > INT64_MAX. Don't hide for 32-bit fields where such warnings
    # would indicate a real bug.
    if field_k > 32:
        flags.append("-Wno-implicitly-unsigned-literal")
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


def compile_rust(source: Path, output: Path, profile: str = "conservative") -> CompileResult:
    """Compile Rust source.

    Args:
      profile: "conservative" → rustc -O (opt-level=2, historical).
               "match-plonky3" → rustc -C opt-level=3 -C lto=yes -C target-cpu=native.
    """
    if profile == "match-plonky3":
        cmd = ["rustc", "-C", "opt-level=3", "-C", "lto=yes",
               "-C", "target-cpu=native", str(source), "-o", str(output)]
    else:
        cmd = ["rustc", "-O", str(source), "-o", str(output)]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if result.returncode != 0:
        return CompileResult(False, output, result.stderr[:500])
    return CompileResult(True, output)


def describe_profile_c(profile: str = "conservative") -> str:
    """Human-readable summary of C flags for reporting."""
    arch = platform.machine()
    if profile == "match-plonky3":
        cpu = " ".join(_cpu_flag(arch)) or "(no cpu flag)"
        return f"cc -O3 -flto {cpu}"
    return "cc -O2"


def describe_profile_rust(profile: str = "conservative") -> str:
    """Human-readable summary of Rust flags for reporting."""
    if profile == "match-plonky3":
        return "rustc -C opt-level=3 -C lto=yes -C target-cpu=native"
    return "rustc -O (opt-level=2)"


PLONKY3_PROFILE_DESCRIPTION = "rustc --release (Cargo.toml: lto=true, opt-level=3, codegen-units=1, panic=abort)"
