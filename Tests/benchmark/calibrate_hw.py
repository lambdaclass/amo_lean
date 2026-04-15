#!/usr/bin/env python3
"""v3.14.0 M.4: Empirical calibration of HardwareCost for the current machine.

SPIRAL approach: measure, don't guess.

Generates C microbenchmarks, compiles with -O2, measures cycles,
and compares against hardcoded values in CostModelDef.lean.

Usage:
  python3 Tests/benchmark/calibrate_hw.py [--iters 100000000]

Output: Calibrated HardwareCost values + divergence report.
"""

import subprocess
import sys
import tempfile
import os
from pathlib import Path

ITERS = 100_000_000

MICROBENCH_C = """
#include <stdio.h>
#include <stdint.h>
#include <time.h>

#define ITERS {iters}

static inline double elapsed_ns(struct timespec start, struct timespec end) {{
    return (end.tv_sec - start.tv_sec) * 1e9 + (end.tv_nsec - start.tv_nsec);
}}

int main() {{
    volatile uint64_t a = 0x123456789ABCDEF0ULL;
    volatile uint64_t b = 0xFEDCBA9876543210ULL;
    volatile uint64_t c = 0;
    struct timespec start, end;

    // 1. Multiply latency
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (long i = 0; i < ITERS; i++) c = a * b;
    clock_gettime(CLOCK_MONOTONIC, &end);
    double mul_ns = elapsed_ns(start, end) / ITERS;

    // 2. Shift latency
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (long i = 0; i < ITERS; i++) c = a << 3;
    clock_gettime(CLOCK_MONOTONIC, &end);
    double shift_ns = elapsed_ns(start, end) / ITERS;

    // 3. Add latency
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (long i = 0; i < ITERS; i++) c = a + b;
    clock_gettime(CLOCK_MONOTONIC, &end);
    double add_ns = elapsed_ns(start, end) / ITERS;

    // 4. Branch cost (50% taken)
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (long i = 0; i < ITERS; i++) {{
        if (__builtin_popcountll(a + i) == 1) c = a; else c = b;
    }}
    clock_gettime(CLOCK_MONOTONIC, &end);
    double branch_ns = elapsed_ns(start, end) / ITERS;

    // 5. Popcnt cost
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (long i = 0; i < ITERS; i++) c = __builtin_popcountll(a + i);
    clock_gettime(CLOCK_MONOTONIC, &end);
    double popcnt_ns = elapsed_ns(start, end) / ITERS;

    // 6. 128-bit multiply (Goldilocks product)
    volatile __uint128_t x128 = (__uint128_t)a * (__uint128_t)b;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (long i = 0; i < ITERS; i++) x128 = (__uint128_t)a * (__uint128_t)(b + i);
    clock_gettime(CLOCK_MONOTONIC, &end);
    double mul128_ns = elapsed_ns(start, end) / ITERS;

    printf("mul64_ns=%.2f\\n", mul_ns);
    printf("shift_ns=%.2f\\n", shift_ns);
    printf("add_ns=%.2f\\n", add_ns);
    printf("branch_ns=%.2f\\n", branch_ns);
    printf("popcnt_ns=%.2f\\n", popcnt_ns);
    printf("mul128_ns=%.2f\\n", mul128_ns);

    // Normalize to cycles (assume ~3GHz for Apple Silicon)
    double ghz = 3.2;
    printf("\\n--- Estimated cycles (%.1f GHz) ---\\n", ghz);
    printf("mul64:   %.1f cycles\\n", mul_ns * ghz);
    printf("shift:   %.1f cycles\\n", shift_ns * ghz);
    printf("add:     %.1f cycles\\n", add_ns * ghz);
    printf("branch:  %.1f cycles\\n", branch_ns * ghz);
    printf("popcnt:  %.1f cycles\\n", popcnt_ns * ghz);
    printf("mul128:  %.1f cycles\\n", mul128_ns * ghz);

    printf("\\n--- HardwareCost comparison (arm_cortex_a76) ---\\n");
    printf("  mul32:  hardcoded=3  measured=%.1f\\n", mul_ns * ghz);
    printf("  shift:  hardcoded=1  measured=%.1f\\n", shift_ns * ghz);
    printf("  add:    hardcoded=1  measured=%.1f\\n", add_ns * ghz);
    printf("  branchPenalty: hardcoded=1  measured=%.1f (branch - popcnt)\\n",
           (branch_ns - popcnt_ns) * ghz);
    return 0;
}}
"""


def main():
    iters = ITERS
    if len(sys.argv) > 1 and sys.argv[1] == "--iters":
        iters = int(sys.argv[2])

    with tempfile.NamedTemporaryFile(suffix=".c", mode="w", delete=False) as f:
        f.write(MICROBENCH_C.format(iters=iters))
        c_path = f.name

    bin_path = c_path.replace(".c", "")
    try:
        r = subprocess.run(["cc", "-O2", "-o", bin_path, c_path],
                           capture_output=True, text=True)
        if r.returncode != 0:
            print(f"Compile error: {r.stderr}")
            return 1

        r = subprocess.run([bin_path], capture_output=True, text=True, timeout=60)
        print(r.stdout)

        if r.returncode != 0:
            print(f"Run error: {r.stderr}")
            return 1
    finally:
        os.unlink(c_path)
        if os.path.exists(bin_path):
            os.unlink(bin_path)

    return 0


if __name__ == "__main__":
    sys.exit(main())
