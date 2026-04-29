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

# arity per op. Future ops (idiv, shl, shr, sar) add rows here.
ARITY = {
    "add0": 1,
    "mul": 2,
}

I64_MIN = -(2**63)
I64_MOD = 2**64


def _wrap_i64(v: int) -> int:
    v &= I64_MOD - 1
    if v >= 2**63:
        v -= I64_MOD
    return v


def reference(op: str, xs: list[int]) -> int:
    if op == "add0":
        # arith_spec_add0: y = x0 + 0 = x0.
        return xs[0]
    if op == "mul":
        # arith_spec_mul: y = (x0 * 1) * x1 → x0 * x1, with i64 wrapping.
        return _wrap_i64(xs[0] * xs[1])
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
    }
    lo, hi = lo_hi[args.op]
    it = range(args.count) if args.count is not None else itertools.count()
    try:
        for _ in it:
            xs = [random.randint(lo, hi) for _ in range(arity)]
            y = reference(args.op, xs)
            print(" ".join(str(v) for v in xs) + " : " + str(y), flush=True)
    except BrokenPipeError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
