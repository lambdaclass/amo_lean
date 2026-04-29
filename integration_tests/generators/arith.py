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

# arity per op. Future ops (mul, idiv, shl, shr, sar) add rows here.
ARITY = {
    "add0": 1,
}


def reference(op: str, xs: list[int]) -> int:
    if op == "add0":
        # arith_spec_add0: y = x0 + 0 = x0.
        return xs[0]
    raise ValueError(f"unknown op: {op}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--op", required=True, choices=sorted(ARITY))
    parser.add_argument("-n", "--count", type=int, default=None)
    args = parser.parse_args()

    arity = ARITY[args.op]
    lo, hi = -(2**62), 2**62 - 1
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
