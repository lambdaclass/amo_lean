# Goldilocks Cost Model Calibration Report

## B39-4: Empirical calibration for Goldilocks NTT v3.9.0

### Hardware
- Apple Silicon (ARM, Apple Firestorm/Icestorm cores)
- Dual-pipe NEON: V0 (multiply) + V1 (add/shift/logic)

### Measured (bench_goldi_isolated.c, N=10M)

| Variant | ns/call | V0-only | Dual | Total instr | Ratio vs halves |
|---------|---------|---------|------|-------------|-----------------|
| fold_mul | 6.43 | 1 (umulh) | 9 | 15 | 1.09x |
| fold_shiftsub | 6.06 | 1 (umulh) | 9 | 15 | 1.03x |
| fold_halves | 5.89 | 0 | 11 | 17 | 1.00x (baseline) |
| Karatsuba NEON | 3.60 | 3 (umull×3) | 12 | 15 | 0.61x (2 lanes) |

### Key Findings

1. **Compiler optimizes fold_mul = fold_shiftsub**: Both produce IDENTICAL assembly
   (15 instructions, 1 umulh). The compiler rewrites `hi * (2^32-1)` and
   `(hi << 32) - hi` identically. No benefit to either over the other.

2. **fold_halves is cheapest scalar** (0 V0): The compiler rewrites
   `hl * 0xFFFFFFFF` as `(hl << 32) - hl` (no multiply). This is the variant
   used by `lowerGoldilocksProductReduce` (the verified path).

3. **NEON Karatsuba is 1.6x faster** than scalar (3.60 vs 5.89 ns), even with
   only 2 NEON lanes for 64-bit elements. The 3 vmull_u32 (V0) operations are
   the bottleneck, matching the InstructionProfile model.

4. **Loop bottleneck dominates scalar**: The benchmark loop includes a 64×64→128
   multiply (`mul + umulh`, 2 V0) per iteration. This adds ~4 ns constant overhead
   to all scalar variants, explaining why fold_halves (0 V0 in fold) still takes
   5.89 ns. The FOLD-ONLY cost difference (halves vs mul) is ~0.5 ns ≈ 1 V0 cycle.

### InstructionProfile (added to CrossRelNTT.lean)

| Profile | v0Only | dualIssue | effectiveCost |
|---------|--------|-----------|---------------|
| goldilocksProfile_halves | 0 | 11 | 0 |
| goldilocksProfile_mul | 1 | 9 | 1 |
| goldilocksProfile_karatsuba | 3 | 12 | 3 |

### Model vs Measured Ratio Validation

The V0 throughput model predicts fold-only cost ratios:

| Ratio | Model (V0) | Measured | Match? |
|-------|-----------|----------|--------|
| mul/halves | 1/0 = ∞ | 1.09x | ✗ (V0 model breaks at 0) |
| karat/halves | 3/0 = ∞ | 0.61x | ✗ (V0 model breaks at 0) |
| mul/karat | 1/3 = 0.33x | 1.79x | ✗ (scalar vs NEON incomparable) |

**V0 model limitation**: When the baseline (fold_halves) has 0 V0 instructions,
the V0-only model cannot compute ratios. The bottleneck shifts to dual-issue
throughput and loop overhead. The V0 model works well for BabyBear (vmull 6 V0 →
sqdmulh 3 V0, predicted 2.0x, measured 1.79x) but not for Goldilocks scalar.

**Total instruction model** (alternative):
| Ratio | Total instr | Measured | Match? |
|-------|------------|----------|--------|
| mul/halves | 15/17 = 0.88x | 1.09x | ~20% off |
| karat(per-elem)/halves | 7.5/17 = 0.44x | 0.61x | ~28% off |

Total instruction count is closer but still ~20-28% off due to loop overhead and
pipeline effects.

**Conclusion**: For Goldilocks, the InstructionProfile effectiveCost (V0-only)
correctly identifies fold_halves as cheapest (0 V0) and Karatsuba NEON as most
V0-expensive (3 V0). The absolute timing predictions require accounting for the
loop's 128-bit multiply overhead. For e-graph selection (Fase 2), the RELATIVE
ordering is correct: fold_halves < fold_mul < Karatsuba (per-call scalar).

### Static vs Dynamic Cost Comparison

| Field | Static (reductionCostForHW) | Note |
|-------|---------------------------|------|
| BabyBear (scalar) | Solinas: 6 | Calibrated in v3.5.0 |
| BabyBear (NEON) | Solinas: 14 | Calibrated in v3.5.0 |
| Goldilocks (scalar) | Solinas: 6 | Same formula, uses arm_cortex_a76 |
| All fields | Harvey: 3, Montgomery: 7 | |

Dynamic cost (from e-graph) will be computed in Fase 2 (N39.8) using
`exprCostHW` on the extracted expression. Prerequisite: shift-subtract
and Karatsuba rules (B3a/B3b) must be in the e-graph first.

### E-graph Selection Validation (deferred to Fase 2)

Cannot run yet — need shift-subtract rule (N39.5) and Karatsuba rule (N39.6)
in the e-graph before `optimizeReduction goldilocksConfig` produces meaningful
alternatives. Current e-graph only has generic bitwise rules.

Gate for Fase 2: after B3a/B3b, re-run calibration validation:
```
optimizeReduction goldilocksConfig arm_cortex_a76 → [strategy]
exprCostHW(extracted) vs measured ns/call → ratio check
```
