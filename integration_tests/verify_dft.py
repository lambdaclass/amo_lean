#!/usr/bin/env python3
"""verify_dft.py — Verify AMO-Lean generated DFT_N binaries.

Reads test vectors from stdin, line by line, so infinite generators work.

Usage:
    cat test_vectors/wht4/*.txt | python3 verify_dft.py --binary ./dft4 --size 4
    ./generators/wht.py --size 4 | python3 verify_dft.py --binary ./dft4 --size 4

Fuzz mode (--fuzz): exit non-zero on the first mismatch, printing input,
expected and actual output. Intended to pair with an infinite generator.

The generated DFT_N kernel in AMO-Lean (real case, no twiddle factors)
computes the Walsh-Hadamard Transform of size N, so expected vectors must
come from `scipy.linalg.hadamard(N) @ x`.
"""

import signal
import subprocess
import sys


def parse_line(line, lineno, size):
    """Parse one `x0 .. : y0 ..` line with `size` values on each side."""
    line = line.strip()
    if not line or line.startswith('#'):
        return None
    if ':' not in line:
        print(f"WARNING: line {lineno} missing ':' separator, skipping: {line}", file=sys.stderr)
        return None
    left, right = line.split(':', 1)
    left_parts = left.split()
    right_parts = right.split()
    if len(left_parts) != size or len(right_parts) != size:
        print(
            f"WARNING: line {lineno} expected {size}:{size} values, skipping: {line}",
            file=sys.stderr,
        )
        return None
    try:
        return [int(x) for x in left_parts], [int(x) for x in right_parts]
    except ValueError:
        print(f"WARNING: line {lineno} non-integer value, skipping: {line}", file=sys.stderr)
        return None


def run_one(binary, vec, expected, size):
    """Run binary on vec, compare to expected.

    Returns None on pass, a list[int] with the actual output on mismatch,
    or a str describing any other failure (non-zero exit, parse error, etc.).
    """
    args = [binary] + [str(x) for x in vec]
    result = subprocess.run(args, capture_output=True, text=True)
    if result.returncode != 0:
        msg = f"binary returned {result.returncode}"
        if result.stderr:
            msg += f"; stderr: {result.stderr.strip()}"
        return msg
    try:
        output = [int(x) for x in result.stdout.split()]
    except ValueError:
        return f"could not parse output: {result.stdout.strip()}"
    if len(output) != size:
        return f"expected {size} values, got {len(output)}: {output}"
    if output != expected:
        return output
    return None


def main():
    binary = None
    size = None
    fuzz = False
    args = sys.argv[1:]
    i = 0
    while i < len(args):
        if args[i] == "--binary" and i + 1 < len(args):
            binary = args[i + 1]
            i += 2
        elif args[i] == "--size" and i + 1 < len(args):
            try:
                size = int(args[i + 1])
            except ValueError:
                print(f"--size must be an integer, got {args[i + 1]}", file=sys.stderr)
                sys.exit(2)
            if size < 1 or size & (size - 1):
                print(f"--size must be a power of 2, got {size}", file=sys.stderr)
                sys.exit(2)
            i += 2
        elif args[i] == "--fuzz":
            fuzz = True
            i += 1
        else:
            print(f"Unknown argument: {args[i]}", file=sys.stderr)
            sys.exit(2)

    if not binary or size is None:
        print(
            f"Usage: {sys.argv[0]} --binary <path> --size <N> [--fuzz]  (test vectors on stdin)",
            file=sys.stderr,
        )
        sys.exit(1)

    print(f"\n══ Verification ({binary}, N={size}) — reading stdin ═══════════")
    stats = {"passed": 0, "failed": 0, "total": 0, "interrupted": False}

    def summarize_and_exit():
        total = stats["total"]
        passed = stats["passed"]
        failed = stats["failed"]
        if stats["interrupted"]:
            print("\n  Interrupted — partial results follow")
        if total == 0:
            print("No vectors read from stdin", file=sys.stderr)
            sys.exit(1)
        print(f"\n  Results: {passed}/{total} passed, {failed} failed")
        if failed == 0 and not stats["interrupted"]:
            print(f"  PASS: All {total} test vectors match WHT_{size}")
        sys.exit(0 if failed == 0 and not stats["interrupted"] else 1)

    def on_signal(signum, _frame):
        stats["interrupted"] = True
        print(f"\n  Received signal {signal.Signals(signum).name}, shutting down...",
              file=sys.stderr)
        summarize_and_exit()

    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT):
        try:
            signal.signal(sig, on_signal)
        except (ValueError, OSError):
            pass

    try:
        for lineno, line in enumerate(sys.stdin, 1):
            parsed = parse_line(line, lineno, size)
            if parsed is None:
                continue
            vec, expected = parsed
            stats["total"] += 1
            idx = stats["total"] - 1
            result = run_one(binary, vec, expected, size)
            if result is None:
                stats["passed"] += 1
                continue
            stats["failed"] += 1
            if fuzz:
                print(f"\n  FUZZ FAIL on test {idx}:")
                print(f"    input    = {vec}")
                print(f"    expected = {expected}")
                if isinstance(result, list):
                    print(f"    actual   = {result}")
                else:
                    print(f"    error    = {result}")
                sys.exit(1)
            if isinstance(result, list):
                print(f"  FAIL test {idx}: input={vec}")
                print(f"    output   = {result}")
                print(f"    expected = {expected}")
            else:
                print(f"  FAIL test {idx}: {result}")
    except KeyboardInterrupt:
        stats["interrupted"] = True

    summarize_and_exit()


if __name__ == "__main__":
    main()
