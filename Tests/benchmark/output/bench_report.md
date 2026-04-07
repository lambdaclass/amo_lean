# AMO-Lean NTT Benchmark Report
**Date:** 2026-04-05 18:06:11
**Platform:** Darwin arm64

## Validation Summary

| Field | N | Lang | HW | Status | Details |
|-------|---|------|----|--------|---------|
| babybear | 2^14 | c | arm-scalar | PASS | 16384 elements |
| babybear | 2^16 | c | arm-scalar | PASS | 65536 elements |
| koalabear | 2^14 | c | arm-scalar | PASS | 16384 elements |
| koalabear | 2^16 | c | arm-scalar | PASS | 65536 elements |
| mersenne31 | 2^14 | c | arm-scalar | PASS | 16384 elements |
| mersenne31 | 2^16 | c | arm-scalar | PASS | 65536 elements |

## Performance Results

| Field | N | Lang | HW | AMO (us) | P3 (us) | Melem/s | vs P3 |
|-------|---|------|----|----------|---------|---------|-------|
| babybear | 2^14 | c | arm-scalar | 286.4 | 273.0 | 57.2 | -4.9% |
| babybear | 2^16 | c | arm-scalar | 1424.0 | 1280.8 | 46.0 | -11.2% |
| koalabear | 2^14 | c | arm-scalar | 286.4 | 273.1 | 57.2 | -4.9% |
| koalabear | 2^16 | c | arm-scalar | 1424.9 | 1279.5 | 46.0 | -11.4% |
| mersenne31 | 2^14 | c | arm-scalar | 253.6 | 351.7 | 64.6 | +27.9% |
| mersenne31 | 2^16 | c | arm-scalar | 1095.4 | 1373.2 | 59.8 | +20.2% |

## Cost Model Explanations

```
=== Cost Model Explanation: babybear N=2^14 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: BabyBear (p = 2013265921)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2013265921, N=16384
HW: mul32=3 add=1 simd=false, Target color: 1
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: babybear N=2^16 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: BabyBear (p = 2013265921)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2013265921, N=65536
HW: mul32=3 add=1 simd=false, Target color: 1
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: koalabear N=2^14 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: KoalaBear (p = 2130706433)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2130706433, N=16384
HW: mul32=3 add=1 simd=false, Target color: 1
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: koalabear N=2^16 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: KoalaBear (p = 2130706433)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2130706433, N=65536
HW: mul32=3 add=1 simd=false, Target color: 1
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: mersenne31 N=2^14 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: Mersenne31 (p = 2147483647)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2147483647, N=16384
HW: mul32=3 add=1 simd=false, Target color: 1
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
```
=== Cost Model Explanation: mersenne31 N=2^16 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: Mersenne31 (p = 2147483647)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2147483647, N=65536
HW: mul32=3 add=1 simd=false, Target color: 1
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
