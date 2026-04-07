# AMO-Lean NTT Benchmark Report
**Date:** 2026-04-07 16:04:57
**Platform:** Darwin arm64

## Validation Summary

| Field | N | Lang | HW | Status | Details |
|-------|---|------|----|--------|---------|
| babybear | 2^16 | c | arm-scalar | PASS | 65536 elements |
| babybear | 2^20 | c | arm-scalar | PASS | 1048576 elements |
| koalabear | 2^16 | c | arm-scalar | PASS | 65536 elements |
| koalabear | 2^20 | c | arm-scalar | PASS | 1048576 elements |

## Performance Results

| Field | N | Lang | HW | AMO (us) | P3 (us) | Melem/s | vs P3 |
|-------|---|------|----|----------|---------|---------|-------|
| babybear | 2^16 | c | arm-scalar | 841.7 | 959.5 | 77.9 | +12.3% |
| babybear | 2^20 | c | arm-scalar | 16856.0 | 21067.0 | 62.2 | +20.0% |
| koalabear | 2^16 | c | arm-scalar | 837.2 | 978.4 | 78.3 | +14.4% |
| koalabear | 2^20 | c | arm-scalar | 16890.7 | 21105.2 | 62.1 | +20.0% |

## Cost Model Explanations

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
=== Cost Model Explanation: babybear N=2^20 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: BabyBear (p = 2013265921)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2013265921, N=1048576
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
=== Cost Model Explanation: koalabear N=2^20 (arm-scalar) ===
AMO-Lean Ultra NTT Benchmark
Field: KoalaBear (p = 2130706433)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2130706433, N=1048576
HW: mul32=3 add=1 simd=false, Target color: 1
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
