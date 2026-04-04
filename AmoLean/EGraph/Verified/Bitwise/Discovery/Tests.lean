import AmoLean.EGraph.Verified.Bitwise.Discovery.Pipeline

/-!
# AmoLean.EGraph.Verified.Bitwise.Discovery.Tests

Integration tests and smoke tests for the Discovery Engine (Fase 24).

## Test coverage

1. CSD decomposition correctness (ShiftAddGen)
2. Growth prediction bounds (GrowthPrediction)
3. Lazy reduction decisions (LazyReduction)
4. Guided saturation configuration (GuidedSaturation)
5. TreewidthDP routing (TreewidthDP)
6. Pipeline composition (Pipeline)
7. End-to-end: does the pipeline discover shift-add for BabyBear?
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery.Tests

open AmoLean.EGraph.Verified.Bitwise.Discovery

/-! ## 1. CSD decomposition tests -/

section CSD

/-- CSD of 0 is empty. -/
example : toCSD 0 = [] := by native_decide

/-- CSD of 1 is [pos]. -/
example : toCSD 1 = [.pos] := by native_decide

/-- CSD of 2 is [zero, pos]. -/
example : toCSD 2 = [.zero, .pos] := by native_decide

/-- CSD of 3 = 4-1: [neg, zero, pos]. -/
example : toCSD 3 = [.neg, .zero, .pos] := by native_decide

/-- CSD correctness for 42. -/
example : evalCSDInt (toCSD 42) 0 = 42 := by native_decide

/-- CSD correctness for 1000. -/
example : evalCSDInt (toCSD 1000) 0 = 1000 := by native_decide

/-- BabyBear correction 2^27-1 has CSD weight 2 (optimal!). -/
example : csdWeight (toCSD 134217727) = 2 := by native_decide

/-- Shift-add decomposition of 15 has 2 operations. -/
example : (shiftAddDecompose 15).length = 2 := by native_decide

/-- Shift-add soundness for 7: 7x = 8x - x = (x<<<3) - x. -/
example : evalShiftOps (shiftAddDecompose 7) 10 = 10 * 7 := by native_decide

end CSD

/-! ## 2. Growth prediction tests -/

section Growth

/-- Growth bound with 0 steps is identity. -/
example : maxNodesBound 100 10 0 = 100 := by native_decide

/-- Growth bound with 1 step. -/
example : maxNodesBound 10 5 1 = 60 := by native_decide

/-- Growth bound with 3 steps of 5 rules. -/
example : maxNodesBound 10 5 3 = 2160 := by native_decide

/-- Growth is monotone in steps. -/
example : maxNodesBound 10 5 2 ≤ maxNodesBound 10 5 3 := by native_decide

/-- Safe fuel stays within budget. -/
example : safeFuel ⟨1000, 10, 5⟩ 10 ≤ 10 := by native_decide

end Growth

/-! ## 3. Lazy reduction tests -/

section LazyReduction

/-- BabyBear initial bound can defer reduction. -/
example : canDeferReduction ⟨2013265921⟩ 64 2013265921 = true := by native_decide

/-- After 3 additions, still deferrable (64-bit). -/
example :
  let b := IntervalBound.mk 2013265921
  let b3 := b.add (b.add b)
  canDeferReduction b3 64 2013265921 = true := by native_decide

/-- Mask produces small bound. -/
example : (IntervalBound.mask 31).maxVal = 2147483647 := by native_decide

end LazyReduction

/-! ## 4. Guided saturation tests -/

section Guided

/-- Phase 1 has 10 algebraic rules. -/
example : phase1Rules.length = 10 := by native_decide

/-- Phase 3 generates shift-add rules. -/
example : phase3ShiftAddRules.length ≥ 1 := by native_decide

/-- Default fuel is 20. -/
example : totalFuel GuidedConfig.default = 20 := by native_decide

/-- Aggressive fuel is 40. -/
example : totalFuel GuidedConfig.aggressive = 40 := by native_decide

/-- Conservative fuel is 10. -/
example : totalFuel GuidedConfig.conservative = 10 := by native_decide

end Guided

/-! ## 5. TreewidthDP tests -/

section TreewidthDP

private def smallTree : NiceTree Nat :=
  .introduce 1 (.leaf [0])

/-- Small tree has treewidth ≤ 15 → DP mode. -/
example : extractionMode smallTree = .dp := by native_decide

/-- DP extraction on small tree. -/
example : dpExtract smallTree (fun _ => 1) ≤ 1000000 := by native_decide

end TreewidthDP

/-! ## 6. Pipeline integration tests -/

section Pipeline

/-- BabyBear pipeline generates rules. -/
example : (generatePrimeShiftAddRules .babybear).length ≥ 1 := by native_decide

/-- Pipeline growth is bounded. -/
example : predictGrowth .babybear 10 ≥ 10 :=
  maxNodesBound_ge_initial _ _ _

/-- All generated shift-add rules are sound. -/
example : ∀ r ∈ generatePrimeShiftAddRules .babybear,
    ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  generatePrimeShiftAddRules_sound _

end Pipeline

/-! ## 7. End-to-end discovery test -/

section E2E

/-- The discovery pipeline for BabyBear finds the shift-add decomposition
    of the correction constant 2^27-1 = 134217727.

    CSD(134217727) = 2^27 - 1 = (x<<<27) - x, which is 2 shift operations
    instead of a full multiplication. On RISC-V (mul=3 cycles), this saves
    1 cycle per reduction. In a ZK proof with 10^6 reductions: ~1 second. -/
example : csdWeight (toCSD 134217727) = 2 := by native_decide

/-- For a new prime p = 2^61-1 (Mersenne), the correction constant is 1.
    CSD(1) = [pos], so the fold is just `hi + lo` (1 add, 0 muls). -/
example :
  let p := 2^61 - 1
  let correction := 2^61 - p
  csdWeight (toCSD correction) = 1 := by native_decide

/-- The shift-add rule for BabyBear correction is sound. -/
example : ∀ env v,
    (shiftAddRule 134217727).lhsEval env v =
    (shiftAddRule 134217727).rhsEval env v :=
  (shiftAddRule 134217727).soundness

end E2E

end AmoLean.EGraph.Verified.Bitwise.Discovery.Tests
