"""Correctness validation: compare compiled C/Rust output against Python reference."""

import subprocess
import tempfile
from pathlib import Path
from dataclasses import dataclass

from field_defs import FieldDef, get_field
from reference_ntt import compute_reference_ntt, compute_reference_standard_ntt
from lean_driver import GeneratedProgram
from code_splitter import generate_validation_program
from compiler import compile_c, compile_rust


@dataclass
class ValidationResult:
    passed: bool
    field: str
    log_n: int
    lang: str
    hardware: str
    num_checked: int
    first_mismatch: int          # -1 if passed
    compiled_val: int             # value from compiled code at mismatch
    python_val: int               # value from Python at mismatch
    error: str = ""               # non-empty if compile/runtime error


def validate(
    program: GeneratedProgram,
    field: FieldDef,
    work_dir: Path,
    timeout: int = 120,
    scalar_program: "GeneratedProgram | None" = None,
    rust_simd: bool = False,
    use_standard: bool = True,  # v3.17.0 N317.8: aligned with generator default
) -> ValidationResult:
    """Full validation pipeline:
    1. Build validation program (prints NTT output elements)
    2. Compile
    3. Run, capture stdout
    4. Compute Python reference
    5. Compare element-by-element mod p
    """
    n = 1 << program.log_n
    tag = f"{program.field}_{program.log_n}_{program.lang}_{program.hardware}"

    # Step 1: Generate validation source
    # With real roots of unity, R4 and R2 produce the same NTT result.
    # No need for scalar fallback — validate the actual generated code directly.
    val_prog = program
    try:
        val_source = generate_validation_program(val_prog, field, rust_simd=rust_simd)
    except Exception as e:
        return ValidationResult(False, program.field, program.log_n, program.lang,
                                program.hardware, 0, -1, 0, 0, f"Split error: {e}")

    # Step 2: Write and compile
    ext = ".c" if program.lang == "c" else ".rs"
    src_path = work_dir / f"val_{tag}{ext}"
    bin_path = work_dir / f"val_{tag}"
    src_path.write_text(val_source)

    if program.lang == "c":
        cr = compile_c(src_path, bin_path, program.hardware, field_k=field.k)
    else:
        cr = compile_rust(src_path, bin_path)

    if not cr.success:
        return ValidationResult(False, program.field, program.log_n, program.lang,
                                program.hardware, 0, -1, 0, 0, f"Compile error: {cr.error}")

    # Step 3: Run validation binary
    try:
        result = subprocess.run(
            [str(bin_path)], capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return ValidationResult(False, program.field, program.log_n, program.lang,
                                program.hardware, 0, -1, 0, 0, "Timeout")
    except Exception as e:
        return ValidationResult(False, program.field, program.log_n, program.lang,
                                program.hardware, 0, -1, 0, 0, f"Runtime error: {e}")

    if result.returncode != 0:
        return ValidationResult(False, program.field, program.log_n, program.lang,
                                program.hardware, 0, -1, 0, 0,
                                f"Exit code {result.returncode}: {result.stderr[:200]}")

    # Step 4: Parse compiled output
    lines = result.stdout.strip().split('\n')
    try:
        compiled_output = [int(line.strip()) for line in lines if line.strip()]
    except ValueError as e:
        return ValidationResult(False, program.field, program.log_n, program.lang,
                                program.hardware, 0, -1, 0, 0, f"Parse error: {e}")

    if len(compiled_output) != n:
        return ValidationResult(False, program.field, program.log_n, program.lang,
                                program.hardware, len(compiled_output), -1, 0, 0,
                                f"Expected {n} elements, got {len(compiled_output)}")

    # Step 5: Compute Python reference
    # v3.15.0: use standard DFT reference (bitrev + DIT small→large) when --use-standard
    if use_standard:
        python_output = compute_reference_standard_ntt(field, program.log_n)
    else:
        python_output = compute_reference_ntt(field, program.log_n)

    # Step 6: Compare mod p
    p = field.p
    for i in range(n):
        cv = compiled_output[i] % p
        pv = python_output[i] % p
        if cv != pv:
            return ValidationResult(False, program.field, program.log_n, program.lang,
                                    program.hardware, i, i, cv, pv,
                                    f"Mismatch at [{i}]: compiled={cv}, python={pv}")

    return ValidationResult(True, program.field, program.log_n, program.lang,
                            program.hardware, n, -1, 0, 0)
