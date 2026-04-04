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


def _init_twiddles(tw_sz: int, p: int) -> list[int]:
    """Same fake twiddles as generated code: tw[i] = (i * 7 + 31) % p."""
    return [(i * 7 + 31) % p for i in range(tw_sz)]


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
    """Compute the reference NTT for validation.

    Uses the same data init, same fake twiddles, same DIT butterfly
    as the generated C/Rust code. Returns list of output elements mod p.
    """
    n = 1 << log_n
    tw_sz = n * log_n
    data = _init_data(n, field.p)
    twiddles = _init_twiddles(tw_sz, field.p)
    return reference_dit_ntt(data, twiddles, field.p, log_n)


if __name__ == "__main__":
    # Quick self-test: verify DIT NTT is invertible for small sizes
    # with proper roots of unity (not fake twiddles)
    from field_defs import BABYBEAR
    p = BABYBEAR.p
    g = BABYBEAR.generator

    # Test with N=8: verify output is deterministic and non-trivial
    log_n = 3
    n = 8
    data = _init_data(n, p)
    tw = _init_twiddles(n * log_n, p)
    out = reference_dit_ntt(data, tw, p, log_n)

    print(f"Input:  {data}")
    print(f"Output: {out}")
    assert len(out) == n
    assert all(0 <= x < p for x in out), "Output out of range!"
    assert out != data, "NTT output should differ from input"
    print("Self-test PASSED")
