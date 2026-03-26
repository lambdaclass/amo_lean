/-
  Tests.VerifiedPipeline.StageSimE2E

  N18.7: Integration test for the NTT stage simulation pipeline.

  Verifies that:
  1. stagePairs generates correct indices for N=8, 16
  2. applyStage/applyAllStages preserve list length
  3. butterflyAt writes correct values (spot checks)
  4. The full pipeline compiles and the theorem statements are well-typed
-/
import AmoLean.NTT.StageSimulation

open AmoLean.NTT.StageSimulation

-- ══════════════════════════════════════════════════════════════════
-- Test 1: Index structure for N=8 (3 stages)
-- ══════════════════════════════════════════════════════════════════

-- Stage 0: half=4, pairs (0,4)(1,5)(2,6)(3,7) — 1 group
#eval (stagePairs 3 0).map fun p => (p.i, p.j)
-- Stage 1: half=2, pairs (0,2)(1,3)(4,6)(5,7) — 2 groups
#eval (stagePairs 3 1).map fun p => (p.i, p.j)
-- Stage 2: half=1, pairs (0,1)(2,3)(4,5)(6,7) — 4 groups
#eval (stagePairs 3 2).map fun p => (p.i, p.j)

-- Every index 0..7 appears exactly once per stage
example : (stagePairs 3 0).map (·.i) ++ (stagePairs 3 0).map (·.j) =
    [0, 1, 2, 3, 4, 5, 6, 7] := by native_decide
example : ((stagePairs 3 1).map (·.i) ++ (stagePairs 3 1).map (·.j)).mergeSort (· ≤ ·) =
    [0, 1, 2, 3, 4, 5, 6, 7] := by native_decide
example : ((stagePairs 3 2).map (·.i) ++ (stagePairs 3 2).map (·.j)).mergeSort (· ≤ ·) =
    [0, 1, 2, 3, 4, 5, 6, 7] := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Test 2: Index structure for N=16 (4 stages)
-- ══════════════════════════════════════════════════════════════════

-- Stage 0: half=8, 1 group, 8 pairs
example : (stagePairs 4 0).length = 8 := by native_decide
-- Stage 3: half=1, 8 groups, 1 pair each
example : (stagePairs 4 3).length = 8 := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Test 3: Length preservation (type-checks = pass)
-- ══════════════════════════════════════════════════════════════════

example (data : List ℚ) (tw : Nat → ℚ) : (applyStage data tw 3 0).length = data.length :=
  applyStage_length data tw 3 0

example (data : List ℚ) (tw : Nat → ℚ) : (applyAllStages data tw 3).length = data.length :=
  applyAllStages_length data tw 3

-- ══════════════════════════════════════════════════════════════════
-- Test 4: Butterfly correctness (concrete)
-- ══════════════════════════════════════════════════════════════════

-- butterflyAt on [1, 2, 3, 4] at (0, 2) with w=1:
-- result[0] = 1 + 1*3 = 4, result[2] = 1 - 1*3 = -2
-- result[1] = 2 (unchanged), result[3] = 4 (unchanged)
example : butterflyAt [(1:ℚ), 2, 3, 4] 0 2 1 = [4, 2, -2, 4] := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Test 5: Pipeline theorem statement well-typedness
-- ══════════════════════════════════════════════════════════════════

-- The theorem compiles (with sorry) — this confirms the statement is well-typed
#check @applyAllStages_eq_ntt_generic
#check @applyAllStages_eq_ntt_spec
