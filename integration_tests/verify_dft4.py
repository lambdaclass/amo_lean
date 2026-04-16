#!/usr/bin/env python3
"""verify_dft4.py — Verify AMO-Lean generated DFT_4 binaries.

Usage:
    python3 verify_dft4.py --binary ./dft4 test_vectors.txt
    python3 verify_dft4.py --binary ./dft4_rs test_vectors.txt
"""

import subprocess
import sys

# The DFT_4 kernel in AMO-Lean (real case, no twiddle factors)
# computes the Walsh-Hadamard Transform of size 4:
#
#   WHT_4 = [[1,  1,  1,  1],
#            [1, -1,  1, -1],
#            [1,  1, -1, -1],
#            [1, -1, -1,  1]]
#
# Expected outputs are stored directly in test_vectors.txt alongside inputs.


def load_vectors(path):
    """Load (input, expected) pairs from test_vectors.txt.

    Format per non-comment, non-empty line:
        a b c d : e f g h
    """
    pairs = []
    with open(path) as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            if ':' not in line:
                print(f"WARNING: line {lineno} missing ':' separator, skipping: {line}", file=sys.stderr)
                continue
            left, right = line.split(':', 1)
            left_parts = left.split()
            right_parts = right.split()
            if len(left_parts) != 4 or len(right_parts) != 4:
                print(f"WARNING: line {lineno} expected 4:4 values, skipping: {line}", file=sys.stderr)
                continue
            pairs.append(([int(x) for x in left_parts], [int(x) for x in right_parts]))
    return pairs


def verify_with_binary(binary, pairs):
    passed = 0
    failed = 0
    print(f"\n══ Verification ({binary}) — {len(pairs)} test vectors ═══════════")
    for i, (vec, expected) in enumerate(pairs):
        args = [binary] + [str(x) for x in vec]
        result = subprocess.run(args, capture_output=True, text=True)
        if result.returncode != 0:
            failed += 1
            print(f"  FAIL test {i}: binary returned {result.returncode}")
            if result.stderr:
                print(f"    stderr: {result.stderr.strip()}")
            continue
        try:
            output = [int(x) for x in result.stdout.split()]
        except ValueError:
            failed += 1
            print(f"  FAIL test {i}: could not parse output: {result.stdout.strip()}")
            continue
        if len(output) != 4:
            failed += 1
            print(f"  FAIL test {i}: expected 4 values, got {len(output)}")
            continue
        ok = output == expected
        if ok:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL test {i}: input={vec}")
            print(f"    output   = {output}")
            print(f"    expected = {expected}")
    print(f"\n  Results: {passed}/{len(pairs)} passed, {failed} failed")
    if failed == 0:
        print(f"  PASS: All {len(pairs)} test vectors match WHT_4")
    return failed == 0


def main():
    binary = None
    vectors_path = None

    args = sys.argv[1:]
    i = 0
    while i < len(args):
        if args[i] == "--binary" and i + 1 < len(args):
            binary = args[i + 1]
            i += 2
        else:
            vectors_path = args[i]
            i += 1

    if not vectors_path or not binary:
        print(f"Usage: {sys.argv[0]} --binary <path> <test_vectors.txt>", file=sys.stderr)
        print(f"  e.g.: {sys.argv[0]} --binary generated/dft4 test_vectors.txt", file=sys.stderr)
        print(f"        {sys.argv[0]} --binary generated/dft4_rs test_vectors.txt", file=sys.stderr)
        sys.exit(1)

    pairs = load_vectors(vectors_path)
    if not pairs:
        print(f"No vectors loaded from {vectors_path}", file=sys.stderr)
        sys.exit(1)

    ok = verify_with_binary(binary, pairs)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
