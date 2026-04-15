"""Independent Python NTT reference for validation.

Implements the EXACT same DIT butterfly as the generated C/Rust code,
using Python arbitrary-precision integers. No Montgomery form — operates
on standard twiddles, reduces with % p.

The generated code uses FAKE twiddles: tw[i] = (i*7+31) % p.
The Ultra path converts to Montgomery: tw_mont[i] = (tw[i] * R) % p.
The butterfly does REDC(tw_mont * b) = tw * b mod p, then sum/diff.

For the Python reference, we skip Montgomery and directly compute:
  wb = (tw[idx] * b) % p
  sum = (a + wb) % p
  diff = (a + p - wb) % p
This produces the SAME mathematical result as the Ultra C/Rust code.

Usage:
  from reference_ntt import compute_reference_ntt
  output = compute_reference_ntt(field_def, log_n)
"""

from field_defs import FieldDef


def _init_data(n: int, p: int) -> list[int]:
    """Same deterministic init as generated code: orig[i] = (i * 1000000007) % p."""
    return [(i * 1000000007) % p for i in range(n)]


def _init_twiddles_real(n: int, log_n: int, p: int, g: int) -> list[int]:
    """Real roots of unity: omega_n = g^((p-1)/n) mod p.
    tw[st*(n/2) + group*halfSize + pair] = omega_n^(pair * 2^st) mod p.
    This matches the DIT butterfly twiddle convention in VerifiedPlanCodeGen."""
    tw_sz = n * log_n
    omega_n = pow(g, (p - 1) // n, p)
    tw = [0] * tw_sz
    for st in range(log_n):
        h = n >> (st + 1)  # halfSize = n / 2^(st+1)
        num_groups = 1 << st
        for grp in range(num_groups):
            for pair in range(h):
                exp = pair * (1 << st)
                tw[st * (n // 2) + grp * h + pair] = pow(omega_n, exp, p)
    return tw


def reference_dit_ntt(data: list[int], twiddles: list[int], p: int, log_n: int) -> list[int]:
    """DIT NTT using standard % p reduction.

    Matches the butterfly in VerifiedPlanCodeGen.lean lowerDIFButterflyByReduction:
      wb = (tw * b) % p  (REDC in C, but mathematically equivalent to % p)
      sum = (a + wb) % p
      diff = (a + p - wb) % p

    Twiddle indexing: tw[stage * (n/2) + group * halfSize + pair]
    This matches nttTwiddleIndex in VerifiedPlanCodeGen.lean:166-172.
    """
    n = len(data)
    out = list(data)  # copy
    tw_sz = len(twiddles)

    for stage in range(log_n):
        half = n >> (stage + 1)
        num_groups = 1 << stage
        for group in range(num_groups):
            for pair in range(half):
                i = group * 2 * half + pair
                j = i + half
                tw_idx = (stage * (n // 2) + group * half + pair) % tw_sz
                w = twiddles[tw_idx]

                a = out[i]
                b = out[j]
                wb = (w * b) % p
                out[i] = (a + wb) % p
                out[j] = (a + p - wb) % p

    return out


def compute_reference_ntt(field: FieldDef, log_n: int) -> list[int]:
    """Compute the reference NTT for validation (legacy pipeline).

    Uses real roots of unity: omega_n = g^((p-1)/n) mod p.
    Same DIT butterfly structure as the generated C/Rust code.
    Returns list of output elements mod p.
    """
    n = 1 << log_n
    data = _init_data(n, field.p)
    twiddles = _init_twiddles_real(n, log_n, field.p, field.generator)
    return reference_dit_ntt(data, twiddles, field.p, log_n)


# ═══════════════════════════════════════════════════════════════════
# v3.15.0: Standard DFT reference (bitrev input + DIT small→large)
# Matches ntt_skeleton.c and Plonky3. NOT the same as reference_dit_ntt.
# ═══════════════════════════════════════════════════════════════════


def _bit_reverse(x: int, log_n: int) -> int:
    """Compute bit-reversed index. Pattern: ntt_skeleton.c:42-49."""
    result = 0
    for _ in range(log_n):
        result = (result << 1) | (x & 1)
        x >>= 1
    return result


def reference_standard_ntt(data: list[int], p: int, g: int, log_n: int) -> list[int]:
    """Standard DFT: bitrev input → DIT small→large → DFT output.

    Matches ntt_skeleton.c:144-180 and Plonky3.
    Uses standalone twiddle computation (omega^(j * N/m)) — does NOT use
    the per-stage twiddle table from _init_twiddles_real.

    v3.15.0 N315.1: Verified 7/7 PASS (Goldilocks+BabyBear, N=8..1024).
    """
    n = len(data)
    omega = pow(g, (p - 1) // n, p)
    out = list(data)

    # Bit-reverse input permutation
    for i in range(n):
        j = _bit_reverse(i, log_n)
        if i < j:
            out[i], out[j] = out[j], out[i]

    # Stages small→large: layer 0 → m=2,half=1; layer logN-1 → m=N,half=N/2
    for layer in range(log_n):
        m = 1 << (layer + 1)
        half_m = m >> 1
        tw_step = n // m
        for k in range(0, n, m):
            for j in range(half_m):
                w = pow(omega, j * tw_step, p)
                a, b = out[k + j], out[k + j + half_m]
                wb = (w * b) % p
                out[k + j] = (a + wb) % p
                out[k + j + half_m] = (a + p - wb) % p

    return out


def _naive_dft(data: list[int], p: int, g: int) -> list[int]:
    """O(N^2) naive DFT for cross-validation. A[k] = sum_j data[j]*omega^(jk)."""
    n = len(data)
    omega = pow(g, (p - 1) // n, p)
    result = []
    for k in range(n):
        s = 0
        for j in range(n):
            s = (s + data[j] * pow(omega, j * k, p)) % p
        result.append(s)
    return result


def compute_reference_standard_ntt(field: FieldDef, log_n: int) -> list[int]:
    """Compute standard DFT reference for v3.15.0 validation.

    Uses bitrev input + DIT small→large. Matches Plonky3.
    """
    n = 1 << log_n
    data = _init_data(n, field.p)
    return reference_standard_ntt(data, field.p, field.generator, log_n)


# ═══════════════════════════════════════════════════════════════════
# v3.15.0 B3.5: R4 standard DFT reference (bitrev + R4 inverted + .reverse)
# R4 inverted: inner=L+1, outer=L (swapped from original R4 which is inner=L, outer=L+1)
# ═══════════════════════════════════════════════════════════════════


def reference_standard_r4_ntt(data: list[int], p: int, g: int, log_n: int) -> list[int]:
    """Standard DFT using R4 inverted butterflies + .reverse.

    Stages grouped into R4 pairs (covering 2 levels each) + optional trailing R2.
    All stages reversed (small→large). R4 butterflies use inverted decomposition:
    inner=level L+1, outer=level L (swapped from the original DIT R4).

    v3.15.0 N315.15: Verified against naive DFT O(N^2).
    """
    n = len(data)
    omega = pow(g, (p - 1) // n, p)
    out = list(data)

    # Bit-reverse input
    for i in range(n):
        j = _bit_reverse(i, log_n)
        if i < j:
            out[i], out[j] = out[j], out[i]

    # Per-stage twiddle table (same layout as _init_twiddles_real)
    tw = [0] * (n * log_n)
    for st in range(log_n):
        h = n >> (st + 1)
        for grp in range(1 << st):
            for pair in range(h):
                tw[st * (n // 2) + grp * h + pair] = pow(omega, pair * (1 << st), p)

    # Build stage list: R4 pairs + optional trailing R2
    stages = []  # (stageIdx, radix) tuples
    level = 0
    while level + 1 < log_n:
        stages.append((level, "r4"))
        level += 2
    if level < log_n:
        stages.append((level, "r2"))

    # Execute ALL stages in REVERSE order (small→large for standard DFT)
    for L, radix in reversed(stages):
        if radix == "r4":
            quarter = n // (2 ** (L + 2))
            half_L = 2 * quarter
            num_groups = 2 ** L
            for grp in range(num_groups):
                for pair in range(quarter):
                    base = grp * 4 * quarter + pair
                    i0, i1 = base, base + quarter
                    i2, i3 = base + 2 * quarter, base + 3 * quarter

                    a, b, c, d = out[i0], out[i1], out[i2], out[i3]

                    # Twiddle indices (same as lowerStageR4 L303-307)
                    tw2_idx = L * (n // 2) + grp * half_L + pair
                    tw3_idx = tw2_idx + quarter
                    tw1_idx = (L + 1) * (n // 2) + grp * half_L + pair
                    tw1p_idx = tw1_idx + quarter
                    w1, w1p = tw[tw1_idx], tw[tw1p_idx]
                    w2, w3 = tw[tw2_idx], tw[tw3_idx]

                    # INVERTED R4: inner=L+1 first, outer=L second
                    # Inner (level L+1): bf2(a,b,w1), bf2(c,d,w1p)
                    wb1 = (w1 * b) % p
                    r0, r1 = (a + wb1) % p, (a + p - wb1) % p
                    wb1p = (w1p * d) % p
                    r2, r3 = (c + wb1p) % p, (c + p - wb1p) % p

                    # Outer (level L): bf2(r0,r2,w2), bf2(r1,r3,w3)
                    wb2 = (w2 * r2) % p
                    out0, out2 = (r0 + wb2) % p, (r0 + p - wb2) % p
                    wb3 = (w3 * r3) % p
                    out1, out3 = (r1 + wb3) % p, (r1 + p - wb3) % p

                    out[i0], out[i1], out[i2], out[i3] = out0, out1, out2, out3
        else:  # r2
            half = n >> (L + 1)
            num_groups = 1 << L
            for grp in range(num_groups):
                for pair in range(half):
                    i = grp * 2 * half + pair
                    j = i + half
                    tw_idx = L * (n // 2) + grp * half + pair
                    w = tw[tw_idx]
                    a, b = out[i], out[j]
                    wb = (w * b) % p
                    out[i] = (a + wb) % p
                    out[j] = (a + p - wb) % p

    return out


def compute_reference_standard_r4_ntt(field: FieldDef, log_n: int) -> list[int]:
    """Compute standard DFT using R4 inverted + .reverse for v3.15.0 B3.5 validation."""
    n = 1 << log_n
    data = _init_data(n, field.p)
    return reference_standard_r4_ntt(data, field.p, field.generator, log_n)


if __name__ == "__main__":
    from field_defs import BABYBEAR, GOLDILOCKS

    # === Legacy self-test (unchanged) ===
    p = BABYBEAR.p
    g = BABYBEAR.generator
    log_n = 3
    n = 8
    data = _init_data(n, p)
    tw = _init_twiddles_real(n, log_n, p, g)
    out = reference_dit_ntt(data, tw, p, log_n)
    assert len(out) == n
    assert all(0 <= x < p for x in out), "Output out of range!"
    assert out != data, "NTT output should differ from input"
    print("Legacy self-test PASSED")

    # === v3.15.0: Standard DFT vs naive DFT validation ===
    print("\nv3.15.0 Standard DFT validation:")
    for field in [BABYBEAR, GOLDILOCKS]:
        for log_n in [3, 4, 5, 6, 7, 8, 9, 10]:
            n = 1 << log_n
            data = _init_data(n, field.p)
            standard = reference_standard_ntt(data, field.p, field.generator, log_n)
            naive = _naive_dft(data, field.p, field.generator)
            assert standard == naive, (
                f"FAIL {field.name} N={n}: standard[0]={standard[0]}, naive[0]={naive[0]}"
            )
            print(f"  {field.display} N={n:5d}: PASS")
    print("\nAll standard DFT validations PASSED")

    # === v3.15.0 B3.5: R4 standard DFT vs naive DFT validation ===
    print("\nv3.15.0 B3.5 R4 Standard DFT validation:")
    for field in [BABYBEAR, GOLDILOCKS]:
        for log_n in [2, 3, 4, 5, 6, 7, 8, 10]:
            n = 1 << log_n
            data = _init_data(n, field.p)
            r4_std = reference_standard_r4_ntt(data, field.p, field.generator, log_n)
            naive = _naive_dft(data, field.p, field.generator)
            assert r4_std == naive, (
                f"FAIL {field.name} N={n}: r4[0]={r4_std[0]}, naive[0]={naive[0]}"
            )
            # Also cross-check R4 == R2 standard (both should equal DFT)
            r2_std = reference_standard_ntt(data, field.p, field.generator, log_n)
            assert r4_std == r2_std, (
                f"R4/R2 MISMATCH {field.name} N={n}"
            )
            print(f"  {field.display} N={n:5d}: PASS (R4==naive, R4==R2)")
    print("\nAll R4 standard DFT validations PASSED")
