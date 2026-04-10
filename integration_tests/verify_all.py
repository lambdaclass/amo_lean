#!/usr/bin/env python3
"""verify_all.py — Verify all trzk-generated binaries against reference implementations.

Usage:
    python3 verify_all.py --test <test_name> --binary <path> [--vectors <path>]
    python3 verify_all.py --test dft4 --binary ./dft4
    python3 verify_all.py --test identity4 --binary ./identity4
    python3 verify_all.py --test ntt_babybear_16 --ntt-binary <path>
    python3 verify_all.py --test poseidon_sbox --sbox-binary <path>
"""

import subprocess
import sys
import random

# ══════════════════════════════════════════════════════
# Reference implementations
# ══════════════════════════════════════════════════════

def wht(n):
    """Build the n×n Walsh-Hadamard matrix recursively."""
    if n == 1:
        return [[1]]
    half = wht(n // 2)
    size = len(half)
    top = [row + row for row in half]
    bot = [row + [-x for x in row] for row in half]
    return top + bot

def mat_vec_mul(matrix, vec):
    """Multiply a matrix by a vector."""
    return [sum(row[j] * vec[j] for j in range(len(vec))) for row in matrix]

def identity_matrix(n):
    """n×n identity matrix."""
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]

def kron_matrix(a, b):
    """Kronecker product of two matrices."""
    ma, na = len(a), len(a[0])
    mb, nb = len(b), len(b[0])
    result = [[0] * (na * nb) for _ in range(ma * mb)]
    for i1 in range(ma):
        for j1 in range(na):
            for i2 in range(mb):
                for j2 in range(nb):
                    result[i1 * mb + i2][j1 * nb + j2] = a[i1][j1] * b[i2][j2]
    return result

def compose_matrix(a, b):
    """Matrix product A · B."""
    m, k1 = len(a), len(a[0])
    k2, n = len(b), len(b[0])
    assert k1 == k2
    result = [[0] * n for _ in range(m)]
    for i in range(m):
        for j in range(n):
            result[i][j] = sum(a[i][p] * b[p][j] for p in range(k1))
    return result

def bit_reverse(x, bits):
    """Reverse the lowest `bits` bits of x."""
    result = 0
    for _ in range(bits):
        result = (result << 1) | (x & 1)
        x >>= 1
    return result

def bit_reverse_permute(data, n):
    """Apply bit-reversal permutation to data."""
    logn = n.bit_length() - 1
    result = [0] * n
    for i in range(n):
        result[bit_reverse(i, logn)] = data[i]
    return result

def ntt_reference(data, p, g, n):
    """Reference NTT (DIT radix-2) over Z_p.
    Standard Cooley-Tukey DIT with omega = g^((p-1)/n)."""
    result = [x % p for x in data]
    logn = n.bit_length() - 1
    omega_n = pow(g, (p - 1) // n, p)
    m = 1
    for s in range(logn):
        wm = pow(omega_n, n // (2 * m), p)
        for k in range(0, n, 2 * m):
            w = 1
            for j in range(m):
                t = (w * result[k + j + m]) % p
                u = result[k + j]
                result[k + j] = (u + t) % p
                result[k + j + m] = (u - t + p) % p
                w = (w * wm) % p
        m *= 2
    return result

# ══════════════════════════════════════════════════════
# Test definitions
# ══════════════════════════════════════════════════════

# Each test: (name, size, reference_matrix_fn, test_vectors)
MATRIX_TESTS = {}

def generate_int_vectors(n, count=15):
    """Generate test vectors for size n."""
    vecs = []
    # Basis vectors
    for i in range(min(n, 4)):
        v = [0] * n
        v[i] = 1
        vecs.append(v)
    # Special vectors
    vecs.append([1] * n)
    vecs.append(list(range(1, n + 1)))
    vecs.append(list(range(n, 0, -1)))
    vecs.append([(-1)**i for i in range(n)])
    # Random vectors
    random.seed(42)
    while len(vecs) < count:
        vecs.append([random.randint(-100, 100) for _ in range(n)])
    return vecs[:count]

def register_matrix_test(name, size, matrix_fn):
    MATRIX_TESTS[name] = (size, matrix_fn, generate_int_vectors(size))

# Register all matrix tests
register_matrix_test("dft2", 2, lambda: wht(2))
register_matrix_test("dft4", 4, lambda: wht(4))
register_matrix_test("dft8", 8, lambda: wht(8))
register_matrix_test("identity4", 4, lambda: identity_matrix(4))
register_matrix_test("kron_i3_dft2", 6, lambda: kron_matrix(identity_matrix(3), wht(2)))
register_matrix_test("compose_ct4", 4, lambda: compose_matrix(
    kron_matrix(wht(2), identity_matrix(2)),
    kron_matrix(identity_matrix(2), wht(2))
))

# ══════════════════════════════════════════════════════
# Verification functions
# ══════════════════════════════════════════════════════

def run_binary(binary, args):
    """Run a binary with arguments, return parsed output."""
    cmd = [binary] + [str(x) for x in args]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        return None, f"binary returned {result.returncode}: {result.stderr.strip()}"
    try:
        return [int(x) for x in result.stdout.split()], None
    except ValueError:
        return None, f"could not parse output: {result.stdout.strip()}"

def verify_matrix_test(name, binary):
    """Verify a matrix transform binary against reference."""
    if name not in MATRIX_TESTS:
        print(f"Unknown test: {name}")
        return False
    size, matrix_fn, vectors = MATRIX_TESTS[name]
    matrix = matrix_fn()
    passed = 0
    failed = 0
    print(f"\n  {name} ({size}×{size}, {len(vectors)} vectors)")
    for i, vec in enumerate(vectors):
        output, err = run_binary(binary, vec)
        if err:
            failed += 1
            print(f"    FAIL vector {i}: {err}")
            continue
        expected = mat_vec_mul(matrix, vec)
        if output == expected:
            passed += 1
        else:
            failed += 1
            print(f"    FAIL vector {i}: input={vec}")
            print(f"      got      = {output}")
            print(f"      expected = {expected}")
    if failed == 0:
        print(f"    PASS ({passed}/{len(vectors)})")
    else:
        print(f"    {passed}/{len(vectors)} passed, {failed} FAILED")
    return failed == 0

def verify_ntt(name, binary, p, g, n):
    """Verify NTT binary against reference implementation."""
    random.seed(42)
    vectors = []
    # Basis-like vectors
    for i in range(min(n, 4)):
        v = [0] * n
        v[i] = 1
        vectors.append(v)
    # All ones
    vectors.append([1] * n)
    # Sequential
    vectors.append([i % p for i in range(1, n + 1)])
    # Random values mod p
    while len(vectors) < 15:
        vectors.append([random.randint(0, min(p - 1, 10000)) for _ in range(n)])

    passed = 0
    failed = 0
    print(f"\n  {name} (NTT size {n}, p={p}, {len(vectors)} vectors)")
    for i, vec in enumerate(vectors):
        output, err = run_binary(binary, vec)
        if err:
            failed += 1
            print(f"    FAIL vector {i}: {err}")
            continue
        expected = ntt_reference(vec, p, g, n)
        if output == expected:
            passed += 1
        else:
            failed += 1
            print(f"    FAIL vector {i}: input={vec[:4]}...")
            print(f"      got      = {output[:4]}...")
            print(f"      expected = {expected[:4]}...")
    if failed == 0:
        print(f"    PASS ({passed}/{len(vectors)})")
    else:
        print(f"    {passed}/{len(vectors)} passed, {failed} FAILED")
    return failed == 0

def verify_sbox(binary, p=18446744069414584321, exp=5):
    """Verify Poseidon S-box: output should be x^exp mod p."""
    test_values = [0, 1, 2, 3, 7, 42, 100, 999, 2013265921, 123456789]
    passed = 0
    failed = 0
    print(f"\n  poseidon_sbox (x^{exp} mod p, {len(test_values)} values)")
    for x in test_values:
        output, err = run_binary(binary, [x])
        if err:
            failed += 1
            print(f"    FAIL x={x}: {err}")
            continue
        expected = pow(x, exp, p)
        if output == [expected]:
            passed += 1
        else:
            failed += 1
            print(f"    FAIL x={x}: got={output[0] if output else '?'}, expected={expected}")
    if failed == 0:
        print(f"    PASS ({passed}/{len(test_values)})")
    else:
        print(f"    {passed}/{len(test_values)} passed, {failed} FAILED")
    return failed == 0

# ══════════════════════════════════════════════════════
# CLI
# ══════════════════════════════════════════════════════

def main():
    args = sys.argv[1:]
    test_name = None
    binary = None

    i = 0
    while i < len(args):
        if args[i] == "--test" and i + 1 < len(args):
            test_name = args[i + 1]; i += 2
        elif args[i] == "--binary" and i + 1 < len(args):
            binary = args[i + 1]; i += 2
        else:
            i += 1

    if not test_name or not binary:
        print(f"Usage: {sys.argv[0]} --test <name> --binary <path>")
        print(f"Matrix tests: {', '.join(MATRIX_TESTS.keys())}")
        print(f"Other tests: poseidon_sbox")
        sys.exit(1)

    if test_name == "poseidon_sbox":
        ok = verify_sbox(binary)
    elif test_name == "ntt_babybear_16":
        ok = verify_ntt(test_name, binary, p=2013265921, g=31, n=16)
    elif test_name in MATRIX_TESTS:
        ok = verify_matrix_test(test_name, binary)
    else:
        print(f"Unknown test: {test_name}")
        sys.exit(1)

    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
