# AMO-Lean NTT Benchmark Report
**Date:** 2026-04-08 10:21:24
**Platform:** Darwin arm64

## Column Legend

| Column | Description |
|--------|-------------|
| **Lang** | Output language: `c` = compiled C, `rust` = compiled Rust |
| **HW** | Hardware target: `arm-scalar` = no SIMD, `arm-neon` = ARM NEON 4-lane SIMD |
| **AMO** | AMO-Lean Ultra pipeline: verified codegen with e-graph optimization |
| **P3 naive** | Scalar reference using naive `% p` modular reduction (NOT actual Plonky3) |
| **P3 real** | Actual Plonky3 library via FFI (when available) |
| **vs P3 naive** | `(P3_naive - AMO) / P3_naive × 100%` — positive = AMO faster |
| **vs P3 real** | `(P3_real - AMO) / P3_real × 100%` — positive = AMO faster |

## Validation Summary

| Field | N | Lang | HW | Status | Details |
|-------|---|------|----|--------|---------|
| babybear | 2^16 | c | arm-scalar | PASS | 65536 elements |

## Performance Results

| Field | N | Lang | HW | AMO (μs) | P3 naive (μs) | vs naive |
|-------|---|------|----|----------|---------------|----------|
| babybear | 2^16 | c | arm-scalar | 1459.7 | 1449.4 | -0.7% |

## Notes

**Configurations tested:**
- `c` / `arm-scalar`: ARM scalar (no SIMD)

**Configurations not tested in this run:**
- `c` / `arm-neon`
- `rust` / `arm-neon`
- `rust` / `arm-scalar`

**P3 real (Plonky3 via FFI):** Not available in this run. The P3 naive column uses scalar `% p` modular reduction — it is NOT representative of actual Plonky3 performance which uses Montgomery SIMD (sqdmulh on NEON, vpmuludq on AVX2).

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
