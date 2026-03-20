# AMO-Lean vs Plonky3: Definitive Rust Benchmark Report

**Date**: 2026-03-20
**Platform**: Apple Silicon (ARM64), macOS Darwin 24.6.0
**Compiler**: rustc (stable), `--release` with LTO, codegen-units=1, opt-level=3
**Comparison**: AMO-Lean (e-graph + cost-model optimized) vs Plonky3-style (Montgomery REDC)

## 1. Benchmark Conditions

| Aspect | AMO-Lean | Plonky3-style |
|--------|----------|---------------|
| Language | Rust | Rust (same binary) |
| Profile | `--release`, LTO, opt-level=3 | Same |
| Loop structure | Identical DIT NTT | Identical DIT NTT |
| Data type | `u32` / `u64` | `u32` / `u64` |
| SIMD | None (scalar only) | None (scalar only) |
| Clone per iteration | `Vec::clone()` | `Vec::clone()` (symmetric) |

Same binary, same compiler, same optimization flags. The ONLY difference is the NTT butterfly reduction.

### E-graph strategy (identical to C benchmark)

| Primitive | AMO mul strategy | AMO add strategy | Rationale |
|-----------|-----------------|-----------------|-----------|
| **NTT** | Solinas fold (6 cyc) | Solinas fold (6 cyc) | Multi-stage butterfly, cheaper per-op |
| **Poly/FRI/Dot** | Montgomery (7 cyc) | Harvey 1-branch (2 cyc) | `solinasWinsForMulAdd = false` |

## 2. Raw Data

| field | log_n | n | primitive | amo_us | p3_us | diff_pct | amo_strategy | p3_strategy |
|-------|-------|---|-----------|--------|-------|----------|-------------|-------------|
| BabyBear | 12 | 4096 | NTT | 46.2 | 55.7 | +16.9 | Solinas | Montgomery |
| BabyBear | 12 | 4096 | Poly | 49.7 | 50.0 | +0.5 | Montgomery+1br | Montgomery+1br |
| BabyBear | 12 | 4096 | FRI | 1.6 | 1.6 | +0.1 | Montgomery+1br | Montgomery+1br |
| BabyBear | 12 | 4096 | Dot | 8.1 | 8.0 | -0.7 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 12 | 4096 | NTT | 47.9 | 56.9 | +15.7 | Solinas | Montgomery |
| KoalaBear | 12 | 4096 | Poly | 49.9 | 49.4 | -0.9 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 12 | 4096 | FRI | 1.6 | 1.6 | -0.2 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 12 | 4096 | Dot | 8.1 | 8.1 | +0.7 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 12 | 4096 | NTT | 48.9 | 54.5 | +10.2 | Solinas | Montgomery |
| Mersenne31 | 12 | 4096 | Poly | 47.9 | 47.9 | +0.0 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 12 | 4096 | FRI | 1.5 | 1.5 | -0.1 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 12 | 4096 | Dot | 7.7 | 7.8 | +0.3 | Montgomery+1br | Montgomery+1br |
| BabyBear | 14 | 16384 | NTT | 213.0 | 248.6 | +14.3 | Solinas | Montgomery |
| BabyBear | 14 | 16384 | Poly | 191.5 | 191.7 | +0.1 | Montgomery+1br | Montgomery+1br |
| BabyBear | 14 | 16384 | FRI | 6.1 | 6.1 | -0.3 | Montgomery+1br | Montgomery+1br |
| BabyBear | 14 | 16384 | Dot | 31.1 | 32.3 | +3.7 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 14 | 16384 | NTT | 217.9 | 256.6 | +15.1 | Solinas | Montgomery |
| KoalaBear | 14 | 16384 | Poly | 191.6 | 191.7 | +0.1 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 14 | 16384 | FRI | 6.1 | 6.1 | +0.0 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 14 | 16384 | Dot | 31.1 | 31.1 | +0.2 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 14 | 16384 | NTT | 213.0 | 254.6 | +16.4 | Solinas | Montgomery |
| Mersenne31 | 14 | 16384 | Poly | 211.6 | 191.7 | -10.4 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 14 | 16384 | FRI | 6.1 | 6.1 | -0.1 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 14 | 16384 | Dot | 31.1 | 31.0 | -0.4 | Montgomery+1br | Montgomery+1br |
| BabyBear | 16 | 65536 | NTT | 971.2 | 1137.9 | +14.7 | Solinas | Montgomery |
| BabyBear | 16 | 65536 | Poly | 768.3 | 766.3 | -0.3 | Montgomery+1br | Montgomery+1br |
| BabyBear | 16 | 65536 | FRI | 24.3 | 24.2 | -0.4 | Montgomery+1br | Montgomery+1br |
| BabyBear | 16 | 65536 | Dot | 124.3 | 124.4 | +0.1 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 16 | 65536 | NTT | 971.9 | 1137.4 | +14.6 | Solinas | Montgomery |
| KoalaBear | 16 | 65536 | Poly | 765.6 | 766.5 | +0.1 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 16 | 65536 | FRI | 24.2 | 24.2 | +0.0 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 16 | 65536 | Dot | 124.1 | 125.8 | +1.4 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 16 | 65536 | NTT | 971.4 | 1135.8 | +14.5 | Solinas | Montgomery |
| Mersenne31 | 16 | 65536 | Poly | 798.4 | 842.2 | +5.2 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 16 | 65536 | FRI | 25.8 | 25.2 | -2.5 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 16 | 65536 | Dot | 129.7 | 129.1 | -0.5 | Montgomery+1br | Montgomery+1br |
| BabyBear | 18 | 262144 | NTT | 4550.5 | 5232.9 | +13.0 | Solinas | Montgomery |
| BabyBear | 18 | 262144 | Poly | 3087.1 | 3093.0 | +0.2 | Montgomery+1br | Montgomery+1br |
| BabyBear | 18 | 262144 | FRI | 101.9 | 102.4 | +0.5 | Montgomery+1br | Montgomery+1br |
| BabyBear | 18 | 262144 | Dot | 499.8 | 500.4 | +0.1 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 18 | 262144 | NTT | 4475.2 | 5148.0 | +13.1 | Solinas | Montgomery |
| KoalaBear | 18 | 262144 | Poly | 3066.4 | 3068.2 | +0.1 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 18 | 262144 | FRI | 97.4 | 97.2 | -0.1 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 18 | 262144 | Dot | 496.8 | 497.3 | +0.1 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 18 | 262144 | NTT | 4370.9 | 5103.1 | +14.3 | Solinas | Montgomery |
| Mersenne31 | 18 | 262144 | Poly | 3063.8 | 3066.4 | +0.1 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 18 | 262144 | FRI | 98.2 | 98.4 | +0.2 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 18 | 262144 | Dot | 502.3 | 496.8 | -1.1 | Montgomery+1br | Montgomery+1br |
| BabyBear | 20 | 1048576 | NTT | 19726.2 | 22909.8 | +13.9 | Solinas | Montgomery |
| BabyBear | 20 | 1048576 | Poly | 12370.2 | 12329.2 | -0.3 | Montgomery+1br | Montgomery+1br |
| BabyBear | 20 | 1048576 | FRI | 407.4 | 398.4 | -2.3 | Montgomery+1br | Montgomery+1br |
| BabyBear | 20 | 1048576 | Dot | 2014.6 | 1997.4 | -0.9 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 20 | 1048576 | NTT | 19637.8 | 22955.5 | +14.5 | Solinas | Montgomery |
| KoalaBear | 20 | 1048576 | Poly | 12274.4 | 12376.1 | +0.8 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 20 | 1048576 | FRI | 399.1 | 409.2 | +2.5 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 20 | 1048576 | Dot | 1996.7 | 1994.5 | -0.1 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 20 | 1048576 | NTT | 19647.5 | 22984.8 | +14.5 | Solinas | Montgomery |
| Mersenne31 | 20 | 1048576 | Poly | 12442.3 | 12340.8 | -0.8 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 20 | 1048576 | FRI | 416.8 | 397.2 | -4.9 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 20 | 1048576 | Dot | 1997.0 | 1989.3 | -0.4 | Montgomery+1br | Montgomery+1br |
| BabyBear | 22 | 4194304 | NTT | 90460.6 | 101223.1 | +10.6 | Solinas | Montgomery |
| BabyBear | 22 | 4194304 | Poly | 49414.9 | 49075.2 | -0.7 | Montgomery+1br | Montgomery+1br |
| BabyBear | 22 | 4194304 | FRI | 1784.2 | 1570.3 | -13.6 | Montgomery+1br | Montgomery+1br |
| BabyBear | 22 | 4194304 | Dot | 7966.7 | 8000.3 | +0.4 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 22 | 4194304 | NTT | 87999.3 | 103750.9 | +15.2 | Solinas | Montgomery |
| KoalaBear | 22 | 4194304 | Poly | 50021.0 | 49122.9 | -1.8 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 22 | 4194304 | FRI | 1569.4 | 1591.7 | +1.4 | Montgomery+1br | Montgomery+1br |
| KoalaBear | 22 | 4194304 | Dot | 8088.4 | 7973.8 | -1.4 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 22 | 4194304 | NTT | 87202.1 | 102166.9 | +14.6 | Solinas | Montgomery |
| Mersenne31 | 22 | 4194304 | Poly | 49898.2 | 49188.7 | -1.4 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 22 | 4194304 | FRI | 1565.2 | 1566.4 | +0.1 | Montgomery+1br | Montgomery+1br |
| Mersenne31 | 22 | 4194304 | Dot | 7980.8 | 7970.9 | -0.1 | Montgomery+1br | Montgomery+1br |

## 3. NTT Summary (the only primitive where strategies differ)

| Field | 2^12 | 2^14 | 2^16 | 2^18 | 2^20 | 2^22 |
|-------|------|------|------|------|------|------|
| BabyBear | +16.9% | +14.3% | +14.7% | +13.0% | +13.9% | +10.6% |
| KoalaBear | +15.7% | +15.1% | +14.6% | +13.1% | +14.5% | +15.2% |
| Mersenne31 | +10.2% | +16.4% | +14.5% | +14.3% | +14.5% | +14.6% |

**Average NTT advantage: +14.1%** across all 18 data points.

## 4. Cross-Language Comparison (C vs Rust)

| Primitive | C (-O2) avg | Rust (--release LTO) avg | Notes |
|-----------|------------|--------------------------|-------|
| NTT | +19.2% | +14.1% | C compiler optimizes Solinas fold better |
| Poly eval | ~0% | ~0% | Same algorithm, same performance |
| FRI fold | ~0% | ~0% | Same algorithm |
| Dot product | ~0% | ~0% | Same algorithm |

The C compiler (Apple clang) extracts ~5% more NTT advantage than Rust's LLVM backend, likely because clang more aggressively optimizes the `multiply-by-compile-time-constant` pattern in the Solinas fold (`(x >> 31) * 134217727` becomes shift+sub).

## 5. Formal Verification Status

All reduction strategies used in this benchmark are formally verified in Lean 4:

| Theorem | Covers | Status |
|---------|--------|--------|
| `solinasFold_mod_correct` | Solinas fold in NTT butterfly | 0 sorry |
| `monty_reduce_spec` | Montgomery REDC in Poly/FRI/Dot | 0 sorry |
| `harveyReduce_mod` | Harvey conditional subtract | 0 sorry |
| `combinedMulAddCost` | Cost model selection logic | Computable, `native_decide` |
| `solinasWinsForMulAdd` | Strategy decision function | Computable, `native_decide` |

Project: `lake build` 3140 jobs, 0 errors, 0 axioms in active code.
