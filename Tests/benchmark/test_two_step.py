#!/usr/bin/env python3
"""v3.13.0 H.7-H.9: Two-step NTT validation — shift-based twiddle optimization.

Validates that using shifts (goldi_mul_tw) for power-of-2 twiddles produces
IDENTICAL output to the standard multiply-reduce path.

The two-step optimization in v3.13.0 uses the STANDARD DIT NTT algorithm but
marks stages with `useShift=true` where goldi_butterfly4_shift (via goldi_mul_tw)
is used instead of goldi_butterfly4. goldi_mul_tw detects power-of-2 twiddles
at runtime (popcnt==1) and uses shift instead of full multiply.

The four-step factorization (inner blocks + twiddle matrix + outer strided)
is deferred to v3.14.0 due to DIT bit-reversal permutation complexity.

Usage:
  python3 Tests/benchmark/test_two_step.py
"""

import math
import sys

sys.path.insert(0, "Tests/benchmark")
from field_defs import GOLDILOCKS, BABYBEAR
from reference_ntt import _init_data, _init_twiddles_real, reference_dit_ntt


# ══════════════════════════════════════════════════════════════════
# Section 1: Shift-based twiddle multiply (Python equivalent of goldi_mul_tw)
# ══════════════════════════════════════════════════════════════════

def is_power_of_2(n: int) -> bool:
    """Equivalent to __builtin_popcountll(n) == 1."""
    return n > 0 and (n & (n - 1)) == 0


def goldi_mul_tw_py(val: int, tw: int, p: int) -> int:
    """Python equivalent of goldi_mul_tw: shift when power-of-2, else full mul."""
    if is_power_of_2(tw):
        shift = tw.bit_length() - 1  # __builtin_ctzll(tw)
        return ((val << shift) % (p * p)) % p  # goldi_reduce128(val << shift)
    return (tw * val) % p


def ntt_with_shift(data: list[int], twiddles: list[int], p: int, log_n: int) -> list[int]:
    """DIT NTT using goldi_mul_tw_py for twiddle multiply (shift when pow2)."""
    n = len(data)
    out = list(data)

    for stage in range(log_n):
        half = n >> (stage + 1)
        num_groups = 1 << stage
        for group in range(num_groups):
            for pair in range(half):
                i = group * 2 * half + pair
                j = i + half
                tw_idx = stage * (n // 2) + group * half + pair
                w = twiddles[tw_idx % len(twiddles)]

                a = out[i]
                b = out[j]
                # goldi_mul_tw: shift when power-of-2, else full multiply
                wb = goldi_mul_tw_py(b, w, p)
                out[i] = (a + wb) % p
                out[j] = (a + p - wb) % p

    return out


# ══════════════════════════════════════════════════════════════════
# Section 2: Power-of-2 twiddle analysis per stage
# ══════════════════════════════════════════════════════════════════

def analyze_pow2_twiddles(twiddles: list[int], n: int, log_n: int):
    """Analyze what fraction of twiddles are powers of 2 per stage."""
    results = []
    for stage in range(log_n):
        half = n >> (stage + 1)
        num_groups = 1 << stage
        pow2_count = 0
        total = 0
        for group in range(num_groups):
            for pair in range(half):
                tw_idx = stage * (n // 2) + group * half + pair
                w = twiddles[tw_idx]
                total += 1
                if is_power_of_2(w):
                    pow2_count += 1
        results.append((stage, pow2_count, total))
    return results


# ══════════════════════════════════════════════════════════════════
# Section 3: Twiddle table for two-step plan (standard layout, shift-aware)
# ══════════════════════════════════════════════════════════════════

def _init_twiddles_two_step(n: int, p: int, g: int) -> list[int]:
    """Generate standard twiddle table (same as _init_twiddles_real).
    For two-step v3.13.0, the table is IDENTICAL to standard — the optimization
    is in the COST MODEL (useShift stages are cheaper) and CODEGEN
    (goldi_butterfly4_shift uses goldi_mul_tw). No separate twiddle layout needed.
    """
    log_n = int(math.log2(n))
    return _init_twiddles_real(n, log_n, p, g)


# ══════════════════════════════════════════════════════════════════
# Section 4: Exhaustive validation
# ══════════════════════════════════════════════════════════════════

def init_data_typed(N: int, p: int, input_type: str) -> list[int]:
    """Generate test data of various types."""
    if input_type == "zeros":
        return [0] * N
    elif input_type == "ones":
        return [1] * N
    elif input_type == "sequential":
        return [i % p for i in range(N)]
    elif input_type == "max_vals":
        return [p - 1] * N
    elif input_type == "random_42":
        return [(i * 1000000007 + 42) % p for i in range(N)]
    else:
        return _init_data(N, p)


def validate_shift_ntt():
    """Validate that shift-based NTT (goldi_mul_tw) == standard NTT for all inputs.
    Gate: ZERO tolerance — 100% match for ALL sizes x inputs x fields.
    """
    fields = [
        ("Goldilocks", GOLDILOCKS),
        ("BabyBear", BABYBEAR),
    ]
    input_types = ["zeros", "ones", "sequential", "max_vals", "random_42"]
    log_sizes = [7, 8, 10, 14]
    total = 0
    passed = 0

    for field_name, field in fields:
        p, g = field.p, field.generator
        print(f"\n=== {field_name} (p={p}) ===")

        for logN in log_sizes:
            N = 1 << logN

            # Analyze power-of-2 twiddles
            tw = _init_twiddles_real(N, logN, p, g)
            analysis = analyze_pow2_twiddles(tw, N, logN)
            pow2_total = sum(c for _, c, _ in analysis)
            tw_total = sum(t for _, _, t in analysis)
            print(f"  N=2^{logN}: {pow2_total}/{tw_total} pow2 twiddles ({100*pow2_total//tw_total}%)")
            for stage, pc, tc in analysis:
                if tc > 0:
                    pct = 100 * pc // tc
                    marker = " <<<" if pct > 90 else ""
                    print(f"    Stage {stage:>2}: {pc:>5}/{tc:>5} ({pct:>3}%){marker}")

            for input_type in input_types:
                total += 1
                data = init_data_typed(N, p, input_type)
                tw = _init_twiddles_real(N, logN, p, g)

                # Standard NTT
                out_std = reference_dit_ntt(data[:], tw, p, logN)

                # Shift-based NTT (goldi_mul_tw equivalent)
                out_shift = ntt_with_shift(data[:], tw, p, logN)

                if out_std == out_shift:
                    passed += 1
                else:
                    print(f"    FAIL: {input_type} N=2^{logN}")
                    for idx in range(N):
                        if out_std[idx] != out_shift[idx]:
                            print(f"      mismatch at [{idx}]: std={out_std[idx]} shift={out_shift[idx]}")
                            break

    print(f"\n{'='*50}")
    print(f"Results: {passed}/{total} PASSED")
    if passed == total:
        print("=== SHIFT NTT VALIDATION: ALL PASS ===")
        return 0
    else:
        print(f"=== SHIFT NTT VALIDATION: {total - passed} FAILURES ===")
        return 1


if __name__ == "__main__":
    sys.exit(validate_shift_ntt())
