# AMO-Lean NTT Benchmark Report
**Date:** 2026-04-04 17:16:56
**Platform:** Darwin arm64

## Validation Summary

| Field | N | Lang | HW | Status | Details |
|-------|---|------|----|--------|---------|
| babybear | 2^14 | c | arm-neon | PASS | 16384 elements |
| babybear | 2^16 | c | arm-neon | PASS | 65536 elements |
| koalabear | 2^14 | c | arm-neon | PASS | 16384 elements |
| koalabear | 2^16 | c | arm-neon | PASS | 65536 elements |
| mersenne31 | 2^14 | c | arm-neon | PASS | 16384 elements |
| mersenne31 | 2^16 | c | arm-neon | PASS | 65536 elements |

## Performance Results

*No valid benchmark results.*

## Errors

- **BENCH ERROR** babybear/2^14/c/arm-neon: Runtime error (code 1): MISMATCH at i=0: ultra=566522597 p3=1985467746

- **BENCH ERROR** babybear/2^16/c/arm-neon: Runtime error (code 1): MISMATCH at i=0: ultra=480824204 p3=1175019578

- **BENCH ERROR** koalabear/2^14/c/arm-neon: Runtime error (code 1): MISMATCH at i=0: ultra=27915256 p3=1991295706

- **BENCH ERROR** koalabear/2^16/c/arm-neon: Runtime error (code 1): MISMATCH at i=0: ultra=1807885591 p3=598487797

- **BENCH ERROR** mersenne31/2^14/c/arm-neon: Runtime error (code 1): MISMATCH at i=0: ultra=746312323 p3=1956697661

- **BENCH ERROR** mersenne31/2^16/c/arm-neon: Runtime error (code 1): MISMATCH at i=0: ultra=457248859 p3=274413186


## Cost Model Explanations

```
=== Cost Model Explanation: babybear N=2^14 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: BabyBear (p = 2013265921)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2013265921, N=16384
HW: mul32=3 add=1 simd=true, Target color: 2
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: babybear N=2^16 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: BabyBear (p = 2013265921)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2013265921, N=65536
HW: mul32=3 add=1 simd=true, Target color: 2
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: koalabear N=2^14 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: KoalaBear (p = 2130706433)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2130706433, N=16384
HW: mul32=3 add=1 simd=true, Target color: 2
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: koalabear N=2^16 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: KoalaBear (p = 2130706433)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2130706433, N=65536
HW: mul32=3 add=1 simd=true, Target color: 2
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: mersenne31 N=2^14 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: Mersenne31 (p = 2147483647)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2147483647, N=16384
HW: mul32=3 add=1 simd=true, Target color: 2
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: mersenne31 N=2^16 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: Mersenne31 (p = 2147483647)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2147483647, N=65536
HW: mul32=3 add=1 simd=true, Target color: 2
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
