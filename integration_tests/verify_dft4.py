#!/usr/bin/env python3
"""verify_dft4.py — Verify AMO-Lean generated DFT_4 binaries.

Usage:
    python3 verify_dft4.py --binary ./dft4 test_vectors.txt
    python3 verify_dft4.py --binary ./dft4_rs test_vectors.txt
    python3 verify_dft4.py test_vectors.txt   # standalone self-test
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

WHT_4 = [
    [1,  1,  1,  1],
    [1, -1,  1, -1],
    [1,  1, -1, -1],
    [1, -1, -1,  1],
]

def load_vectors(path):
    """Load test vectors from a text file (one 4-element vector per line)."""
    vectors = []
    with open(path) as f:
        for line in f:
            parts = line.split()
            if len(parts) == 0:
                continue
            if len(parts) != 4:
                print(f"WARNING: skipping line with {len(parts)} values: {line.strip()}", file=sys.stderr)
                continue
            vectors.append([int(x) for x in parts])
    return vectors

def mat_vec_mul(matrix, vec):
    """Multiply a matrix by a vector."""
    return [sum(row[j] * vec[j] for j in range(len(vec))) for row in matrix]

def verify_with_binary(binary, vectors):
    """Run binary on each test vector and verify output matches WHT_4."""
    passed = 0
    failed = 0
    print(f"\n══ Verification ({binary}) — {len(vectors)} test vectors ═══════════")
    for i, vec in enumerate(vectors):
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
        expected = mat_vec_mul(WHT_4, vec)
        ok = output == expected
        if ok:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL test {i}: input={vec}")
            print(f"    output   = {output}")
            print(f"    expected = {expected}")
    print(f"\n  Results: {passed}/{len(vectors)} passed, {failed} failed")
    if failed == 0:
        print(f"  PASS: All {len(vectors)} test vectors match WHT_4")
    return failed == 0

def self_test(vectors):
    """Standalone self-test: verify WHT_4 roundtrip property on input vectors."""
    print(f"DFT_4 (Walsh-Hadamard Transform) — standalone self-test ({len(vectors)} vectors)")
    print("=" * 60)
    all_ok = True
    for v in vectors:
        out = mat_vec_mul(WHT_4, v)
        roundtrip = mat_vec_mul(WHT_4, out)
        expected_rt = [4 * x for x in v]
        ok = roundtrip == expected_rt
        status = "ok" if ok else "FAIL"
        print(f"  {v} -> {out}  (roundtrip: {status})")
        if not ok:
            all_ok = False
    print()
    if all_ok:
        print(f"  Self-test PASSED ({len(vectors)} vectors, roundtrip verified)")
    else:
        print("  Self-test FAILED")
    return all_ok

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

    if not vectors_path:
        print(f"Usage: {sys.argv[0]} [--binary <path>] <test_vectors.txt>", file=sys.stderr)
        sys.exit(1)

    vectors = load_vectors(vectors_path)
    if not vectors:
        print(f"No vectors loaded from {vectors_path}", file=sys.stderr)
        sys.exit(1)

    if binary:
        ok = verify_with_binary(binary, vectors)
    else:
        ok = self_test(vectors)
        print()
        print("To verify generated code:")
        print(f"  python3 integration_tests/verify_dft4.py --binary generated/dft4 {vectors_path}")
        print(f"  python3 integration_tests/verify_dft4.py --binary generated/dft4_rs {vectors_path}")

    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
