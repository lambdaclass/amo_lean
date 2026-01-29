# Plonky3 Verification Suite

Phase 6A: AMO-Lean as Plonky3 Verifier

## Overview

This directory contains tools to verify that AMO-Lean's NTT implementation
produces identical results to Plonky3's implementation for the Goldilocks field.

## Structure

```
plonky3/
├── Makefile                    # Build orchestrator
├── README.md                   # This file
├── plonky3_shim/              # Rust → C wrapper
│   ├── Cargo.toml
│   └── src/lib.rs
├── plonky3_source/            # Cloned Plonky3 (reference)
├── shim_test.c                # Basic shim loading test
├── oracle_test.c              # Equivalence tests (6A.4)
└── benchmark.c                # Performance comparison (6A.5)
```

## Quick Start

```bash
# Build everything
make all

# Run basic shim test
make test

# Run Rust unit tests
make test-rust

# See all targets
make help
```

## Exported Functions

The shim exports these C-compatible functions:

| Function | Description |
|----------|-------------|
| `plonky3_ntt_forward(data, len)` | In-place forward NTT |
| `plonky3_ntt_inverse(data, len)` | In-place inverse NTT |
| `plonky3_goldilocks_prime()` | Returns p = 2^64 - 2^32 + 1 |
| `plonky3_get_omega(log_n)` | Returns primitive 2^log_n-th root |
| `plonky3_is_montgomery()` | Returns 0 (standard representation) |
| `plonky3_add(a, b)` | Field addition |
| `plonky3_mul(a, b)` | Field multiplication |
| `plonky3_sub(a, b)` | Field subtraction |
| `plonky3_shim_version()` | Returns version (100 = 0.1.0) |

## Usage from C

```c
#include <dlfcn.h>
#include <stdint.h>

// Load library
void* lib = dlopen("./plonky3_shim/target/release/libplonky3_shim.dylib", RTLD_NOW);

// Get function pointer
typedef int (*ntt_fn)(uint64_t*, size_t);
ntt_fn ntt = dlsym(lib, "plonky3_ntt_forward");

// Use it
uint64_t data[8] = {1, 2, 3, 4, 5, 6, 7, 8};
ntt(data, 8);

dlclose(lib);
```

## Compatibility Findings

| Aspect | Plonky3 | AMO-Lean | Compatible |
|--------|---------|----------|------------|
| Representation | Standard | Standard | ✅ |
| Order I/O | RN | RN | ✅ |
| Butterfly | (a+tw*b, a-tw*b) | Same | ✅ |
| Omega values | TWO_ADIC_GENERATORS | primitiveRoot | ✅ |

## Requirements

- Rust toolchain (cargo)
- GCC or Clang
- macOS or Linux

## Test Results

### Phase 6A.2 Shim Test: 28/28 passed
```
- Symbol loading: 9/9
- Basic functions: 3/3
- Omega values: 4/4
- Field arithmetic: 5/5
- NTT roundtrip: 4/4
- Error handling: 3/3
```

### Phase 6A.4 Oracle Tests: 64/64 passed (100%)
```
Sizes tested: N=8, 16, 32, 64, 128, 256, 512, 1024
Test types: sequential, zeros, ones, impulse, max, random (50 per size)

  *** ALL TESTS PASSED ***
  Plonky3 and AMO-Lean produce IDENTICAL NTT results!
```

### Phase 6A.5 Benchmark Results

| Size | Plonky3 (us) | AMO-Lean (us) | Ratio |
|------|--------------|---------------|-------|
| N=256 | 4.9 | 9.4 | 1.90x Plonky3 |
| N=1024 | 15.4 | 29.6 | 1.92x Plonky3 |
| N=4096 | 63.2 | 135.3 | 2.14x Plonky3 |
| N=16384 | 281.2 | 637.5 | 2.27x Plonky3 |
| N=65536 | 1396.2 | 2907.5 | 2.08x Plonky3 |

**Average: Plonky3 is ~2x faster** (expected due to twiddle caching and SIMD)

AMO-Lean throughput: ~23 million elements/second for large sizes

---

## Hardening Audit (Phase 6A.6)

Complete robustness audit of the FFI integration.

### Test Summary

| Test | Status | Result |
|------|--------|--------|
| FFI Torture Test (1M iter) | ✅ PASS | 0 errors in 3M+ FFI calls |
| Panic Safety Audit | ✅ PASS | `panic = "abort"` configured |
| Deep Fuzzing (120 vectors) | ✅ PASS | 120/120 bit-exact match |
| ABI Layout Audit | ✅ PASS | All offsets identical |
| FFI Overhead | ✅ PASS | **0.03%** (< 5% threshold) |

**VERDICT: PRODUCTION READY**

### FFI Stress Results
```
NTT Roundtrip:     1,000,000 iter - 0 errors - 289K calls/sec
Field Operations:  1,000,000 iter - 0 errors - 378M calls/sec
Omega Queries:       100,000 iter - 0 errors - 1B queries/sec
Varying Sizes:       100,000 iter - 0 errors
```

### Pathological Vectors Tested
- Sparse: `[P-1, 0, ..., 0, 1]`
- Geometric: `[1, ω, ω², ω³, ...]`
- Max entropy: `[P-1, P-2, P-3, ...]`
- Boundary: `[0, 1, P-1, P-2, ...]`
- Alternating: `[0, P-1, 0, P-1, ...]`
- Powers of 2, Impulse, Fibonacci, Random high bits...

All 120 vectors match bit-for-bit across 8 sizes (N=8 to N=1024).

### FFI Overhead Analysis
```
Pure FFI call (noop):  1.08 ns
Total NTT (N=256):     3316.79 ns
Overhead / Total:      0.03%

VERDICT: [EXCELLENT] Granularity is optimal
```

### Running Hardening Tests

```bash
cd ../../Tests/Plonky3/Hardening

# Build all tests
make all

# Run individual tests
make stress      # 1M iterations FFI stress
make deepfuzz    # 120 pathological vectors
make layout      # ABI compatibility
make bench       # FFI overhead measurement

# Run all tests
make test

# Generate full report
make report
```

### Hardening Files
```
Tests/Plonky3/
├── Hardening/
│   ├── FFI_Stress.c         # 1M iterations
│   ├── PanicTest.c          # Panic safety
│   ├── DeepFuzz.c           # 120 vectors
│   ├── LayoutTest.c         # ABI audit
│   ├── Makefile
│   └── HARDENING_REPORT.md  # Full report
└── Bench/
    └── FFI_Overhead.c       # Call cost
```
