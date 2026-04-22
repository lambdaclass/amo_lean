# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "numpy>=2.4.0,<2.5.0",
#   "scipy>=1.17.1,<1.18",
# ]
# ///
"""Generate random WHT_N test vectors.

Emits lines of the form `x0 x1 ... : y0 y1 ...` to stdout, where the
right-hand side is `hadamard(N) @ x`. N must be a power of 2.

Run with uv so the PEP-723 inline dependency block is honored:

    uv run wht.py --size N [-n COUNT] [--min M] [--max M] [--seed S]
"""

import argparse
import itertools
import sys

import numpy as np
from scipy.linalg import hadamard


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--size",
        type=int,
        required=True,
        help="transform size N (must be a power of 2)",
    )
    parser.add_argument(
        "-n",
        "--count",
        type=int,
        default=None,
        help="number of cases to generate (default: infinite)",
    )
    parser.add_argument("--min", type=int, default=-100, help="min input value (inclusive)")
    parser.add_argument("--max", type=int, default=100, help="max input value (inclusive)")
    parser.add_argument("--seed", type=int, default=None, help="RNG seed")
    args = parser.parse_args()

    if args.size < 1 or args.size & (args.size - 1):
        print(f"--size must be a power of 2, got {args.size}", file=sys.stderr)
        return 2

    rng = np.random.default_rng(args.seed)
    H = hadamard(args.size)

    it = range(args.count) if args.count is not None else itertools.count()
    try:
        for _ in it:
            x = rng.integers(args.min, args.max + 1, size=args.size)
            y = H @ x
            print(
                " ".join(str(v) for v in x) + " : " + " ".join(str(v) for v in y),
                flush=True,
            )
    except BrokenPipeError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
