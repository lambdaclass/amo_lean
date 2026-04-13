#!/usr/bin/env python3
"""v3.14.0 Eje 2a: Four-step NTT mathematical verification.

Verifies that the Cooley-Tukey four-step decomposition produces the correct
DFT (up to stride permutation). Tests with naive O(N²) DFT as ground truth.

Three variants tested:
  1. Naive four-step (col DFTs + twiddle + row DFTs) — REFERENCE
  2. DIF inner + DIT outer (Opción B from TRZK_spiral_idea.md §3.8)
  3. Stage-split of ref_dit (trivial — preserves stage order)

Gate: 100% match for ALL sizes. If DIF+DIT fails → fallback to Opción A.

Usage:
  python3 Tests/benchmark/test_four_step.py
"""

import math
import sys

sys.path.insert(0, "Tests/benchmark")
from field_defs import GOLDILOCKS, BABYBEAR


# ══════════════════════════════════════════════════════════════════
# Building blocks
# ══════════════════════════════════════════════════════════════════

def naive_dft(x, omega, p):
    """O(N²) DFT: X[k] = Σ x[n] * omega^(nk)."""
    N = len(x)
    return [sum(x[n] * pow(omega, n * k, p) for n in range(N)) % p for k in range(N)]


def bit_reverse(k, bits):
    r = 0
    for _ in range(bits):
        r = (r << 1) | (k & 1); k >>= 1
    return r


def ref_dit(data, omega, p, log_n):
    """TRZK reference DIT NTT (same as reference_ntt.py)."""
    n = len(data); out = list(data)
    for stage in range(log_n):
        half = n >> (stage + 1)
        for group in range(1 << stage):
            for pair in range(half):
                i = group * 2 * half + pair; j = i + half
                w = pow(omega, pair * (1 << stage), p)
                a, b = out[i], out[j]; wb = (w * b) % p
                out[i] = (a + wb) % p; out[j] = (a + p - wb) % p
    return out


def dif_ntt(data, omega, p, log_n):
    """DIF NTT: add/sub first, then multiply. Same stage ordering as ref_dit."""
    n = len(data); out = list(data)
    for stage in range(log_n):
        half = n >> (stage + 1)
        for group in range(1 << stage):
            for pair in range(half):
                i = group * 2 * half + pair; j = i + half
                w = pow(omega, pair * (1 << stage), p)
                a, b = out[i], out[j]
                out[i] = (a + b) % p
                out[j] = ((a - b + p) * w) % p
    return out


# ══════════════════════════════════════════════════════════════════
# Variant 1: Naive four-step (ground truth for decomposition)
# ══════════════════════════════════════════════════════════════════

def four_step_naive(x, p, g, m):
    """Four-step NTT using naive O(m²) and O((N/m)²) DFTs.
    Returns DFT in stride-permuted order: result[row*m+col] = DFT[col*(N/m)+row].
    """
    N = len(x)
    omega_N = pow(g, (p - 1) // N, p)
    omega_m = pow(g, (p - 1) // m, p)
    omega_outer = pow(g, (p - 1) // (N // m), p)

    data = list(x)
    rows, cols = N // m, m

    # Step 1: DFT each column (size N/m)
    for col in range(cols):
        col_data = [data[row * cols + col] for row in range(rows)]
        col_dft = naive_dft(col_data, omega_outer, p)
        for row in range(rows):
            data[row * cols + col] = col_dft[row]

    # Step 2: Twiddle: data[row*m+col] *= omega_N^(row*col)
    for row in range(rows):
        for col in range(cols):
            data[row * cols + col] = (data[row * cols + col] * pow(omega_N, row * col, p)) % p

    # Step 3: DFT each row (size m)
    for row in range(rows):
        row_data = [data[row * cols + col] for col in range(cols)]
        row_dft = naive_dft(row_data, omega_m, p)
        for col in range(cols):
            data[row * cols + col] = row_dft[col]

    return data


def unstride(data, m):
    """Apply inverse stride permutation: result[col*(N/m)+row] = data[row*m+col]."""
    N = len(data)
    rows = N // m
    result = [0] * N
    for row in range(rows):
        for col in range(m):
            result[col * rows + row] = data[row * m + col]
    return result


# ══════════════════════════════════════════════════════════════════
# Variant 2: DIF inner + DIT outer (Opción B)
# ══════════════════════════════════════════════════════════════════

def four_step_dif_bitrev(x, p, g, m):
    """Four-step using DIF butterflies + per-dimension bit-reversal.
    Correct pipeline (verified for Goldilocks N=128,256,1024):
      col_DIF → col_bitrev → twiddle(ω^(r·c)) → row_DIF → row_bitrev → unstride = DFT

    The row DIF uses omega_m (e.g., omega_64=8 for Goldilocks m=64) where
    100% of twiddles are powers of 2 → shift optimization applies!
    """
    N = len(x)
    omega_N = pow(g, (p - 1) // N, p)
    omega_m = pow(g, (p - 1) // m, p)
    omega_outer = pow(g, (p - 1) // (N // m), p)
    logM = int(math.log2(m))
    logOuter = int(math.log2(N // m))
    rows, cols = N // m, m

    data = list(x)

    # Step 1: Col DIF (strided) — outer NTT, uses omega_{N/m} twiddles
    for col in range(cols):
        col_data = [data[row * cols + col] for row in range(rows)]
        col_out = dif_ntt(col_data, omega_outer, p, logOuter)
        for row in range(rows):
            data[row * cols + col] = col_out[row]

    # Step 2: Per-column bit-reversal (corrects DIF output permutation)
    for col in range(cols):
        col_data = [data[row * cols + col] for row in range(rows)]
        br_col = [col_data[bit_reverse(row, logOuter)] for row in range(rows)]
        for row in range(rows):
            data[row * cols + col] = br_col[row]

    # Step 3: Twiddle matrix — ω_N^(row * col)
    for row in range(rows):
        for col in range(cols):
            data[row * cols + col] = (data[row * cols + col] * pow(omega_N, row * col, p)) % p

    # Step 4: Row DIF (contiguous) — inner NTT, uses omega_m twiddles
    # For Goldilocks m=64: omega_64=8, ALL twiddles are powers of 2 → shifts!
    for row in range(rows):
        row_data = [data[row * cols + col] for col in range(cols)]
        row_out = dif_ntt(row_data, omega_m, p, logM)
        for col in range(cols):
            data[row * cols + col] = row_out[col]

    # Step 5: Per-row bit-reversal (corrects DIF output permutation)
    for row in range(rows):
        row_data = [data[row * cols + col] for col in range(cols)]
        br_row = [row_data[bit_reverse(col, logM)] for col in range(cols)]
        for col in range(cols):
            data[row * cols + col] = br_row[col]

    return data


# ══════════════════════════════════════════════════════════════════
# Validation
# ══════════════════════════════════════════════════════════════════

def validate():
    fields = [
        ("Small (p=97)", 97, 5),
        ("Goldilocks", GOLDILOCKS.p, GOLDILOCKS.generator),
    ]

    test_configs = [
        # (logN, m) pairs
        (3, 2),   # N=8, m=2
        (3, 4),   # N=8, m=4
        (6, 4),   # N=64, m=4
        (7, 4),   # N=128, m=4
        (8, 4),   # N=256, m=4
        (10, 4),  # N=1024, m=4
    ]

    total = 0
    passed = 0

    for field_name, p, g in fields:
        print(f"\n=== {field_name} (p={p}) ===")

        for logN, m in test_configs:
            N = 1 << logN
            if N < 2 * m:
                continue

            omega_N = pow(g, (p - 1) // N, p)
            x = [(i * 1000000007 + 42) % p for i in range(N)]

            # Ground truth: naive DFT
            dft = naive_dft(x, omega_N, p)

            # Variant 1: Naive four-step
            total += 1
            fs = four_step_naive(x, p, g, m)
            fs_unstrided = unstride(fs, m)
            if fs_unstrided == dft:
                passed += 1
                status1 = "PASS"
            else:
                status1 = "FAIL"

            # Variant 2: DIF + bitrev (Opción B corrected)
            total += 1
            try:
                fs_dif = four_step_dif_bitrev(x, p, g, m)
                fs_dif_unstrided = unstride(fs_dif, m)
                if fs_dif_unstrided == dft:
                    passed += 1
                    status2 = "PASS"
                else:
                    status2 = "FAIL"
            except Exception as e:
                status2 = f"ERROR: {e}"

            print(f"  N=2^{logN}, m={m}: naive-4step={status1}  DIF+DIT={status2}")

    print(f"\n{'='*50}")
    print(f"Results: {passed}/{total} PASSED")
    if passed == total:
        print("=== FOUR-STEP VERIFICATION: ALL PASS ===")
        return 0
    else:
        print(f"=== FOUR-STEP VERIFICATION: {total - passed} FAILURES ===")
        return 1


if __name__ == "__main__":
    sys.exit(validate())
