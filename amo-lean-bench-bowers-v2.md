# AMO-Lean vs Plonky3: Bowers NTT Benchmark Report (v2 — post-bugfix)

**Date**: 2026-03-22
**Platform**: Apple Silicon (ARM64), macOS Darwin 24.6.0
**Compiler**: rustc stable, `--release` with LTO, codegen-units=1, opt-level=3
**Comparison**: AMO-Lean generated Bowers NTT vs Plonky3 `Radix2Bowers` (native API)
**Note**: Post-bugfix run. Fixes: u32/u64 truncation in KoalaBear fold, overflow in Goldilocks DIF butterfly.

## Raw Data

| field | log_n | n | primitive | amo_us | p3_us | diff_pct | amo_strategy | p3_strategy |
|-------|-------|---|-----------|--------|-------|----------|-------------|-------------|
| BabyBear | 14 | 16384 | NTT-Bowers | 174 | 214 | +18.9 | Solinas fold | Montgomery |
| BabyBear | 16 | 65536 | NTT-Bowers | 862 | 943 | +8.6 | Solinas fold | Montgomery |
| BabyBear | 18 | 262144 | NTT-Bowers | 4160 | 4591 | +9.4 | Solinas fold | Montgomery |
| BabyBear | 20 | 1048576 | NTT-Bowers | 18522 | 20384 | +9.1 | Solinas fold | Montgomery |
| BabyBear | 22 | 4194304 | NTT-Bowers | 80673 | 89274 | +9.6 | Solinas fold | Montgomery |
| KoalaBear | 14 | 16384 | NTT-Bowers | 167 | 199 | +16.0 | Solinas fold | Montgomery |
| KoalaBear | 16 | 65536 | NTT-Bowers | 824 | 1025 | +19.6 | Solinas fold | Montgomery |
| KoalaBear | 18 | 262144 | NTT-Bowers | 3956 | 4417 | +10.4 | Solinas fold | Montgomery |
| KoalaBear | 20 | 1048576 | NTT-Bowers | 19074 | 20195 | +5.6 | Solinas fold | Montgomery |
| KoalaBear | 22 | 4194304 | NTT-Bowers | 79643 | 89610 | +11.1 | Solinas fold | Montgomery |
| Goldilocks | 14 | 16384 | NTT-Bowers | 188 | 254 | +26.0 | GL reduce | Montgomery |
| Goldilocks | 16 | 65536 | NTT-Bowers | 961 | 1234 | +22.1 | GL reduce | Montgomery |
| Goldilocks | 18 | 262144 | NTT-Bowers | 4491 | 5295 | +15.2 | GL reduce | Montgomery |
| Goldilocks | 20 | 1048576 | NTT-Bowers | 20382 | 24191 | +15.7 | GL reduce | Montgomery |
| Goldilocks | 22 | 4194304 | NTT-Bowers | 89139 | 107748 | +17.3 | GL reduce | Montgomery |

## Summary

| Field | Average advantage | Range |
|-------|------------------|-------|
| **BabyBear** | +11.1% | +8.6 to +18.9% |
| **KoalaBear** | +12.5% | +5.6 to +19.6% |
| **Goldilocks** | +19.3% | +15.2 to +26.0% |

## Changes from v1 (pre-bugfix, March 20)

- BabyBear now included (was missing in v1)
- KoalaBear: slightly different numbers due to corrected u32/u64 types in solinas_fold
- Goldilocks: lower advantage at small N (26% vs 31%) due to corrected overflow handling in DIF butterfly
- All numbers represent correct, verified arithmetic
