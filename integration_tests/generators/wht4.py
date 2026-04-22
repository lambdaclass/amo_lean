# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "numpy>=2.4.0,<2.5.0",
#   "scipy>=1.17.1,<1.18",
# ]
# ///
"""Generate random WHT_4 test vectors.

Emits lines of the form `a b c d : A B C D` to stdout, where the right-hand
side is `hadamard(4) @ [a, b, c, d]`.

Run with uv so the PEP-723 inline dependency block is honored:

    uv run wht4.py [-n N] [--min M] [--max M] [--seed S]
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

    rng = np.random.default_rng(args.seed)
    H = hadamard(4)

    it = range(args.count) if args.count is not None else itertools.count()
    try:
        for _ in it:
            x = rng.integers(args.min, args.max + 1, size=4)
            y = H @ x
            print(
                f"{x[0]} {x[1]} {x[2]} {x[3]} : {y[0]} {y[1]} {y[2]} {y[3]}",
                flush=True,
            )
    except BrokenPipeError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
