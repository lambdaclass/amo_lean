#!/usr/bin/env python3
"""verify_arith.py — Verify trzk-generated ArithExpr binaries.

Reads test vectors from stdin, line by line (streaming).

Format per line:
    <x0> [x1 ...] : <y0>

Usage:
    cat test_vectors/arith_add/*.txt | python3 verify_arith.py --binary ./arith_add --arity 1
    ./generators/arith.py --op add | python3 verify_arith.py --binary ./arith_add --arity 1 --fuzz

Fuzz mode: exit non-zero on the first mismatch.
"""

import signal
import subprocess
import sys


def parse_line(line, lineno, arity):
    line = line.strip()
    if not line or line.startswith('#'):
        return None
    if ':' not in line:
        print(f"WARNING: line {lineno} missing ':', skipping: {line}", file=sys.stderr)
        return None
    left, right = line.split(':', 1)
    left_parts = left.split()
    right_parts = right.split()
    if len(left_parts) != arity or len(right_parts) != 1:
        print(
            f"WARNING: line {lineno} expected {arity}:1 values, skipping: {line}",
            file=sys.stderr,
        )
        return None
    try:
        return [int(x) for x in left_parts], int(right_parts[0])
    except ValueError:
        print(f"WARNING: line {lineno} non-integer, skipping: {line}", file=sys.stderr)
        return None


def run_one(binary, vec, expected):
    args = [binary] + [str(x) for x in vec]
    result = subprocess.run(args, capture_output=True, text=True)
    if result.returncode != 0:
        msg = f"binary returned {result.returncode}"
        if result.stderr:
            msg += f"; stderr: {result.stderr.strip()}"
        return msg
    try:
        output = int(result.stdout.strip())
    except ValueError:
        return f"could not parse output: {result.stdout.strip()}"
    if output != expected:
        return output
    return None


def main():
    binary = None
    arity = None
    fuzz = False
    args = sys.argv[1:]
    i = 0
    while i < len(args):
        if args[i] == "--binary" and i + 1 < len(args):
            binary = args[i + 1]; i += 2
        elif args[i] == "--arity" and i + 1 < len(args):
            try:
                arity = int(args[i + 1])
            except ValueError:
                print(f"--arity must be int, got {args[i + 1]}", file=sys.stderr)
                sys.exit(2)
            i += 2
        elif args[i] == "--fuzz":
            fuzz = True; i += 1
        else:
            print(f"Unknown arg: {args[i]}", file=sys.stderr); sys.exit(2)

    if not binary or arity is None:
        print(
            f"Usage: {sys.argv[0]} --binary <path> --arity <N> [--fuzz]",
            file=sys.stderr,
        )
        sys.exit(1)

    print(f"\n== Verification ({binary}, arity={arity}) ==")
    stats = {"passed": 0, "failed": 0, "total": 0, "interrupted": False}

    def summarize_and_exit():
        total = stats["total"]
        if stats["interrupted"]:
            print("\n  Interrupted — partial results follow")
        if total == 0:
            print("No vectors read from stdin", file=sys.stderr)
            sys.exit(1)
        print(f"\n  Results: {stats['passed']}/{total} passed, {stats['failed']} failed")
        if stats["failed"] == 0 and not stats["interrupted"]:
            print(f"  PASS: All {total} vectors match")
        sys.exit(0 if stats["failed"] == 0 and not stats["interrupted"] else 1)

    def on_signal(signum, _frame):
        stats["interrupted"] = True
        summarize_and_exit()

    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT):
        try:
            signal.signal(sig, on_signal)
        except (ValueError, OSError):
            pass

    try:
        for lineno, line in enumerate(sys.stdin, 1):
            parsed = parse_line(line, lineno, arity)
            if parsed is None:
                continue
            vec, expected = parsed
            stats["total"] += 1
            idx = stats["total"] - 1
            result = run_one(binary, vec, expected)
            if result is None:
                stats["passed"] += 1
                continue
            stats["failed"] += 1
            if fuzz:
                print(f"\n  FUZZ FAIL test {idx}:")
                print(f"    input    = {vec}")
                print(f"    expected = {expected}")
                print(f"    actual   = {result}")
                sys.exit(1)
            print(f"  FAIL test {idx}: input={vec}, expected={expected}, got={result}")
    except KeyboardInterrupt:
        stats["interrupted"] = True

    summarize_and_exit()


if __name__ == "__main__":
    main()
