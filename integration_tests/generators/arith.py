#!/usr/bin/env python3
"""Generate random ArithExpr test vectors.

Emits `x0 [x1 ...] : y` per line. The reference output `y` is computed in
Python to match the spec being exercised. Unseeded by default (the checked-in
vectors are frozen artifacts).

    ./arith.py --op add0 [-n COUNT]
"""

import argparse
import itertools
import random
import sys

# arity per op. Future ops (sar) add rows here.
# Note: `shr` arity is 1 because the spec reduces to `x0` after saturation.
ARITY = {
    "add0": 1,
    "mul": 2,
    "mul0": 1,
    "idiv1": 1,
    "shl": 2,
    "shr": 1,
}

I64_MIN = -(2**63)
I64_MOD = 2**64

ISIZE_BITS = 64
ISIZE_MIN = -(2 ** (ISIZE_BITS - 1))
ISIZE_MAX = (2 ** (ISIZE_BITS - 1)) - 1


def _wrap_i64(v: int) -> int:
    v &= I64_MOD - 1
    if v >= 2**63:
        v -= I64_MOD
    return v


def _to_signed(n: int, bits: int) -> int:
    mask = (1 << bits) - 1
    n &= mask
    if n & (1 << (bits - 1)):
        n -= 1 << bits
    return n


def _unbounded_shl_isize(a: int, b: int) -> int:
    # Rust: isize::unbounded_shl(self, rhs: u32). The shift count comes from
    # `<isize> as u32`, i.e. wrap modulo 2^32. If the wrapped count is >= BITS
    # the result is 0; otherwise it's `(a << count)` truncated to isize.
    count = b & 0xFFFFFFFF
    if count >= ISIZE_BITS:
        return 0
    return _to_signed(a << count, ISIZE_BITS)


def reference(op: str, xs: list[int]) -> int:
    if op == "add0":
        # arith_spec_add0: y = x0 + 0 = x0.
        return xs[0]
    if op == "mul":
        # arith_spec_mul: y = (x0 * 1) * x1 → x0 * x1, with i64 wrapping.
        return _wrap_i64(xs[0] * xs[1])
    if op == "mul0":
        # arith_spec_mul0: y = x0 * 0 = 0. The optimizer eliminates x0; the
        # generated function preserves arity 1 (input is unused).
        return 0
    if op == "idiv1":
        # arith_spec_idiv1: y = x0 / 1 = x0. Divisor is baked into the spec.
        return xs[0]
    if op == "shl":
        # arith_spec_shl: y = x0.unbounded_shl(x1 as u32).
        return _unbounded_shl_isize(xs[0], xs[1])
    if op == "shr":
        # arith_spec_shr: y = x0 >> 0 = x0.
        return xs[0]
    raise ValueError(f"unknown op: {op}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--op", required=True, choices=sorted(ARITY))
    parser.add_argument("-n", "--count", type=int, default=None)
    args = parser.parse_args()

    arity = ARITY[args.op]
    # Per-op input ranges. Narrower than full i64 for mul so a healthy fraction
    # of vectors stay in-range; wraps still occur and are part of the spec.
    lo_hi = {
        "add0": (-(2**62), 2**62 - 1),
        "mul": (-(2**40), 2**40 - 1),
        "mul0": (-(2**62), 2**62 - 1),
        "idiv1": (-(2**62), 2**62 - 1),
        "shl": (-(2**62), 2**62 - 1),
        "shr": (-(2**62), 2**62 - 1),
    }
    lo, hi = lo_hi[args.op]
    it = range(args.count) if args.count is not None else itertools.count()
    try:
        for _ in it:
            xs = [random.randint(lo, hi) for _ in range(arity)]
            if args.op == "shl":
                # Bias the shift count: small in-range values exercise the real
                # shift, the rest cover the saturating-to-0 branch.
                xs[1] = (
                    random.randint(0, ISIZE_BITS - 1)
                    if random.random() < 0.7
                    else xs[1]
                )
            y = reference(args.op, xs)
            print(" ".join(str(v) for v in xs) + " : " + str(y), flush=True)
    except BrokenPipeError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
