# Phase 0: FRI Fold Benchmark Report

**Generated: 2026-01-28**

## Overview

This benchmark compares the performance of FRI fold operation:
- **Lean implementation**: `Array.zipWith` based reference
- **C implementation**: Generated code with `-O3 -march=native`

Operation: `out[i] = even[i] + alpha * odd[i]`

## Results

| Size | Iterations | Lean (ns) | C (ns) | Speedup |
|------|------------|-----------|--------|---------|
| 16 | 100,000 | 28,458,167 | 673,000 | **42.3x** |
| 64 | 50,000 | 36,833,958 | 1,033,000 | **35.7x** |
| 256 | 10,000 | 24,049,709 | 832,000 | **28.9x** |
| 1,024 | 5,000 | 44,471,458 | 1,630,000 | **27.3x** |
| 4,096 | 1,000 | 36,084,667 | 1,316,000 | **27.4x** |

## Summary

- **Average Speedup: 32.3x**
- **C is 32.3x faster than Lean**

## Analysis

### Performance Characteristics
- Speedup decreases slightly with larger sizes (42x → 27x)
- This is expected: overhead becomes less dominant for larger workloads
- C maintains consistent ~27x advantage at scale

### Methodology
- 10 warmup iterations before measurement
- Checksum computed to prevent dead code elimination
- Same pseudo-random number generator (LCG) for both
- Timing via `IO.monoNanosNow` (Lean) and `clock_gettime` (C)

### Compilation
- **Lean**: Interpreted via `Array.zipWith`
- **C**: `clang -DFIELD_NATIVE -O3 -march=native`

## Reproduction

```bash
# Run benchmark
lake build phase0-bench
./.lake/build/bin/phase0-bench
```

---

*This report validates that Option A (Lean→C code generation) provides significant performance benefits while maintaining correctness (verified by oracle testing).*
