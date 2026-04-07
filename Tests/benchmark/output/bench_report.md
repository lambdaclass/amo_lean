# AMO-Lean NTT Benchmark Report
**Date:** 2026-04-07 15:24:12
**Platform:** Darwin arm64

## Validation Summary

| Field | N | Lang | HW | Status | Details |
|-------|---|------|----|--------|---------|
| babybear | 2^16 | c | arm-neon | PASS | 65536 elements |
| babybear | 2^20 | c | arm-neon | PASS | 1048576 elements |
| koalabear | 2^16 | c | arm-neon | PASS | 65536 elements |
| koalabear | 2^20 | c | arm-neon | PASS | 1048576 elements |

## Performance Results

| Field | N | Lang | HW | AMO (us) | P3 (us) | Melem/s | vs P3 |
|-------|---|------|----|----------|---------|---------|-------|
| babybear | 2^16 | c | arm-neon | 888.2 | 994.5 | 73.8 | +10.7% |
| babybear | 2^20 | c | arm-neon | 18376.2 | 22405.0 | 57.1 | +18.0% |
| koalabear | 2^16 | c | arm-neon | 862.5 | 988.8 | 76.0 | +12.8% |
| koalabear | 2^20 | c | arm-neon | 17868.8 | 22186.9 | 58.7 | +19.5% |

## Cost Model Explanations

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
=== Cost Model Explanation: babybear N=2^20 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: BabyBear (p = 2013265921)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2013265921, N=1048576
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
=== Cost Model Explanation: koalabear N=2^20 (arm-neon) ===
AMO-Lean Ultra NTT Benchmark
Field: KoalaBear (p = 2130706433)
Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
   === Truth Ultra Report ===
Field: p=2130706433, N=1048576
HW: mul32=3 add=1 simd=true, Target color: 2
--- Phase 22: Bounds ---
Saturation: 20 iterations
/

```
