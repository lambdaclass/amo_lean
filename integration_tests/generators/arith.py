#!/usr/bin/env python3
"""Generate random ArithExpr test vectors.

Emits `x0 [x1 ...] : y` per line. For arith_spec_1 the kernel computes x0,
so y := x0. Unseeded by default (the checked-in vectors are frozen artifacts).

    ./arith.py --arity 1 [-n COUNT]
"""

import argparse
import itertools
import random
import sys


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--arity", type=int, required=True)
    parser.add_argument("-n", "--count", type=int, default=None)
    args = parser.parse_args()

    if args.arity < 1:
        print(f"--arity must be >= 1, got {args.arity}", file=sys.stderr)
        return 2

    lo, hi = -(2**62), 2**62 - 1
    it = range(args.count) if args.count is not None else itertools.count()
    try:
        for _ in it:
            xs = [random.randint(lo, hi) for _ in range(args.arity)]
            # arith_spec_1: y = x0.
            y = xs[0]
            print(" ".join(str(v) for v in xs) + " : " + str(y), flush=True)
    except BrokenPipeError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
