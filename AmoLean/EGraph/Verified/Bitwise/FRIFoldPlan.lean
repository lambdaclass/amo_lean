import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT

/-!
# FRIFoldPlan — Bound-Aware Reduction for FRI Fold Operations

FRI fold computes `alpha * f_odd[i] + f_even[i]` per element. After mul+add,
the bound is ~2p (same as an NTT butterfly). This module instantiates the
existing bound-aware reduction infrastructure for FRI fold operations.

Key insight: `selectReductionForBound` and `reductionCost` are generic —
they take bounds and return reductions. FRI fold just provides different
initial bounds than NTT.

Node N25.1 in Fase 25 (FRI/Poseidon Integration).
Consumed by: N25.3 PrimitivesIntegration.
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.FRIFoldPlan

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice stageBoundFactor
  lazyReductionSafe boundAfterReduction)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound reductionCost)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: FRI Fold Configuration
-- ══════════════════════════════════════════════════════════════════

/-- Configuration for FRI fold bound analysis.
    FRI fold = `alpha * f_odd[i] + f_even[i]` where alpha is a challenge value.
    After multiplication: bound ≤ p * p (if both inputs < p).
    After addition: bound ≤ 2 * p^2. But in practice, inputs are already reduced,
    so bound after mul+add is ~2p (same as NTT butterfly). -/
structure FRIFoldConfig where
  /-- Field prime p -/
  prime : Nat
  /-- Number of FRI fold rounds (log₂(degree) typically) -/
  numRounds : Nat
  /-- Bound factor of input elements (1 = fully reduced, i.e., < p) -/
  inputBoundK : Nat := 1
  /-- Hardware SIMD flag -/
  hwIsSimd : Bool := false
  /-- Large array flag -/
  arrayIsLarge : Bool := false
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Section 2: FRI Fold Reduction Selection
-- ══════════════════════════════════════════════════════════════════

/-- Bound factor after a FRI fold operation (mul + add).
    alpha * f_odd produces bound ~inputK * inputK (mul doubles the representation).
    Adding f_even increases by inputK. For fully reduced inputs (inputK=1):
    result bound = 1 * 1 + 1 = 2. -/
def friFoldOutputBound (inputK : Nat) : Nat :=
  inputK * inputK + inputK

/-- Select the optimal reduction after a FRI fold operation. -/
def selectFRIReduction (cfg : FRIFoldConfig) : ReductionChoice :=
  let outputBound := friFoldOutputBound cfg.inputBoundK
  selectReductionForBound outputBound cfg.hwIsSimd cfg.arrayIsLarge

/-- Cost of one FRI fold element (mul + add + reduction). -/
def friFoldElementCost (cfg : FRIFoldConfig) (mulCost addCost : Nat) : Nat :=
  let reduction := selectFRIReduction cfg
  let outputBound := friFoldOutputBound cfg.inputBoundK
  mulCost + addCost + reductionCost reduction outputBound cfg.hwIsSimd

/-- Total cost of a FRI fold round (N/2 elements per round).
    N halves each round: N, N/2, N/4, ..., so total elements = N-1. -/
def friFoldRoundCost (cfg : FRIFoldConfig) (elementsInRound : Nat)
    (mulCost addCost : Nat) : Nat :=
  elementsInRound * friFoldElementCost cfg mulCost addCost

/-- Analyze all FRI rounds: for each round, return (roundIdx, reduction, cost). -/
def friFoldAnalysis (cfg : FRIFoldConfig) (initialN : Nat)
    (mulCost addCost : Nat) : List (Nat × ReductionChoice × Nat) :=
  List.range cfg.numRounds |>.map fun round =>
    let elementsInRound := initialN / (2 ^ (round + 1))
    let reduction := selectFRIReduction cfg
    let cost := friFoldRoundCost cfg elementsInRound mulCost addCost
    (round, reduction, cost)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- FRI fold with fully reduced inputs has output bound = 2. -/
theorem friFoldOutputBound_reduced : friFoldOutputBound 1 = 2 := rfl

/-- FRI fold with reduced inputs selects Harvey (bound ≤ 2, cheapest). -/
theorem friFoldReduction_scalar_reduced :
    selectFRIReduction { prime := 2013265921, numRounds := 10 } = .harvey := rfl

/-- FRI fold with SIMD + reduced inputs still selects Harvey (bound ≤ 2 wins). -/
theorem friFoldReduction_simd_reduced :
    selectFRIReduction { prime := 2013265921, numRounds := 10, hwIsSimd := true }
    = .harvey := rfl

/-- FRI fold with SIMD + unreduced inputs (inputK=3) selects Montgomery. -/
theorem friFoldReduction_simd_unreduced :
    selectFRIReduction { prime := 2013265921, numRounds := 10, hwIsSimd := true, inputBoundK := 3 }
    = .montgomery := rfl

/-- FRI fold cost is computable. -/
theorem friFoldElementCost_babybear_scalar :
    friFoldElementCost { prime := 2013265921, numRounds := 10 } 3 1 = 7 := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- FRI fold bound for reduced inputs. -/
example : friFoldOutputBound 1 = 2 := rfl

/-- Scalar BabyBear FRI fold uses Harvey. -/
example : selectFRIReduction { prime := 2013265921, numRounds := 10 } = .harvey := rfl

/-- SIMD BabyBear FRI fold with reduced inputs still uses Harvey (bound ≤ 2 priority). -/
example : selectFRIReduction { prime := 2013265921, numRounds := 10, hwIsSimd := true }
    = .harvey := rfl

/-- SIMD with unreduced inputs (inputK=3) → bound=12 → Montgomery. -/
example : selectFRIReduction { prime := 2013265921, numRounds := 10, hwIsSimd := true, inputBoundK := 3 }
    = .montgomery := rfl

/-- Goldilocks FRI fold uses Harvey (scalar, reduced inputs). -/
example : selectFRIReduction { prime := 18446744069414584321, numRounds := 10 }
    = .harvey := rfl

/-- FRI fold analysis produces correct number of rounds. -/
example : (friFoldAnalysis { prime := 2013265921, numRounds := 5 } 1024 3 1).length = 5 := rfl

/-- FRI fold element cost: mul(3) + add(1) + harvey(3) = 7. -/
example : friFoldElementCost { prime := 2013265921, numRounds := 10 } 3 1 = 7 := rfl

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.FRIFoldPlan
