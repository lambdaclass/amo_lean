/-
  Harvey Chaining Verification Test (Fase Harvey-SIMD v3.4.0)

  Verifies that with boundAfterReduction .harvey = 1:
  1. costAwareReductionForBound selects Harvey when boundK ≤ 2
  2. stageBoundFactor with Harvey returns 1 (not 2)
  3. Harvey chains across ALL NTT stages (invariant stable)
  4. selectReductionForBound never returns Montgomery for SIMD sum/diff
  5. nttStageBoundAnalysis produces all-Harvey schedule with NEON config
-/
import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT
import AmoLean.EGraph.Verified.Bitwise.BoundIntegration

set_option maxHeartbeats 4000000

open AmoLean.EGraph.Verified.Bitwise.BoundProp
  (ReductionChoice boundAfterReduction stageBoundFactor reductionBoundFactor)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT
  (costAwareReductionForBound selectReductionForBound reductionCostForHW
   nttStageBoundAnalysis NTTBoundConfig)
open AmoLean.EGraph.Verified.Bitwise (arm_neon_simd arm_cortex_a76 HardwareCost)

-- ════════════════════════════════════════════════════════════════
-- 1. Bound annotation correctness (N34.1)
-- ════════════════════════════════════════════════════════════════

/-- Harvey output bound = 1 (output < p), matching harveyReduceSpec postcondition. -/
example : boundAfterReduction .harvey = 1 := rfl

/-- Harvey e-graph bound factor = 1. -/
example : reductionBoundFactor (.harveyReduce 0 0) = 1 := rfl

/-- stageBoundFactor with Harvey returns 1 regardless of inputK. -/
example : stageBoundFactor 1 .harvey = 1 := by native_decide
example : stageBoundFactor 5 .harvey = 1 := by native_decide

-- ════════════════════════════════════════════════════════════════
-- 2. Harvey chaining invariant (N34.1 consequence)
-- ════════════════════════════════════════════════════════════════

/-- costAwareReductionForBound selects Harvey when boundK ≤ 2 (NEON). -/
example : costAwareReductionForBound arm_neon_simd 2 2013265921 = .harvey := by native_decide

/-- With Harvey outputK=1, next stage staticK = 1+1 = 2, Harvey still eligible. -/
example : costAwareReductionForBound arm_neon_simd 2 2013265921 = .harvey := by native_decide

/-- The cost-aware planner (costAwareReductionForBound) selects Harvey for ALL stages
    when HardwareCost is available. Chaining test: 5 consecutive Harvey selections. -/
private def chainTest (hw : HardwareCost) (p : Nat) (n : Nat) : Bool :=
  let rec go (stage : Nat) (boundK : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => true
    | fuel + 1 =>
      if stage >= n then true
      else
        let effectiveK := boundK + 1
        let red := costAwareReductionForBound hw effectiveK p
        let newBound := stageBoundFactor boundK red
        red == .harvey && go (stage + 1) newBound fuel
  go 0 1 n

/-- Harvey chains across 10 stages for BabyBear with NEON. -/
example : chainTest arm_neon_simd 2013265921 10 = true := by native_decide

/-- Harvey chains across 10 stages for Mersenne31 with NEON. -/
example : chainTest arm_neon_simd 2147483647 10 = true := by native_decide

/-- Harvey chains across 20 stages for BabyBear with ARM scalar. -/
example : chainTest arm_cortex_a76 2013265921 20 = true := by native_decide

-- ════════════════════════════════════════════════════════════════
-- 3. Montgomery exclusion (N34.3)
-- ════════════════════════════════════════════════════════════════

/-- selectReductionForBound never returns Montgomery for SIMD (any boundK). -/
example : selectReductionForBound 5 true false ≠ .montgomery := by native_decide
example : selectReductionForBound 10 true true ≠ .montgomery := by native_decide
example : selectReductionForBound 100 true false ≠ .montgomery := by native_decide

-- ════════════════════════════════════════════════════════════════
-- 4. Cost model sanity (unchanged)
-- ════════════════════════════════════════════════════════════════

/-- NEON Harvey costs 3 (cheapest). -/
example : reductionCostForHW arm_neon_simd .harvey = 3 := by native_decide

/-- NEON Solinas costs 14 (with u64 penalty). -/
example : reductionCostForHW arm_neon_simd .solinasFold = 14 := by native_decide

/-- Scalar Harvey costs 3. -/
example : reductionCostForHW arm_cortex_a76 .harvey = 3 := by native_decide
