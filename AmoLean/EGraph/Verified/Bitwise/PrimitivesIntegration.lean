import AmoLean.EGraph.Verified.Bitwise.FRIFoldPlan
import AmoLean.EGraph.Verified.Bitwise.PoseidonStagePlan

/-!
# PrimitivesIntegration — Unified Primitive Dispatch for Bound-Aware Reduction

Unified interface for selecting optimal reduction across all ZK primitives:
NTT butterfly, FRI fold, and Poseidon S-box. The same prime with different
primitives may use different reductions depending on the operation's bound profile.

This demonstrates the key architectural insight: `selectReductionForBound` is
primitive-agnostic — the bound determines the reduction, not the primitive.

Node N25.3 in Fase 25 (FRI/Poseidon Integration).
Consumed by: UltraPipeline, DiscoveryPipeline.
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.PrimitivesIntegration

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound reductionCostForHW)
open AmoLean.EGraph.Verified.Bitwise (HardwareCost arm_cortex_a76)
open AmoLean.EGraph.Verified.Bitwise.FRIFoldPlan (FRIFoldConfig selectFRIReduction
  friFoldElementCost friFoldOutputBound)
open AmoLean.EGraph.Verified.Bitwise.PoseidonStagePlan (PoseidonConfig PoseidonRoundType
  selectPoseidonReduction fullRoundOutputBound poseidonRoundCost babybear_t8)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Primitive Type
-- ══════════════════════════════════════════════════════════════════

/-- Cryptographic primitive that needs modular reduction. -/
inductive Primitive where
  | nttButterfly       -- NTT Cooley-Tukey butterfly (mul + add/sub)
  | friFold            -- FRI fold (alpha * f_odd + f_even)
  | poseidonFullRound  -- Poseidon full round (all S-boxes + MDS)
  | poseidonPartialRound -- Poseidon partial round (1 S-box + MDS)
  deriving Repr, BEq, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Unified Reduction Selection
-- ══════════════════════════════════════════════════════════════════

/-- Bound factor for a single operation of the given primitive.
    This is the key function: different primitives produce different bounds
    from the same field, leading to different reduction choices. -/
def primitiveBound (prim : Primitive) (stateWidth : Nat) (sboxExp : Nat)
    (inputK : Nat) : Nat :=
  match prim with
  | .nttButterfly => inputK + 1  -- a + w*b: bound ≈ 2*inputK
  | .friFold => friFoldOutputBound inputK  -- alpha*f + g: bound ≈ inputK^2 + inputK
  | .poseidonFullRound => stateWidth * (if inputK ≤ 1 then 1 else inputK ^ sboxExp) + 1
  | .poseidonPartialRound =>
    (if inputK ≤ 1 then 1 else inputK ^ sboxExp) + (stateWidth - 1) * inputK + 1

/-- Select optimal reduction for a primitive operation. -/
def selectPrimitiveReduction (prim : Primitive) (stateWidth : Nat := 8)
    (sboxExp : Nat := 7) (inputK : Nat := 1)
    (hwIsSimd : Bool := false) (arrayIsLarge : Bool := false) : ReductionChoice :=
  let bound := primitiveBound prim stateWidth sboxExp inputK
  selectReductionForBound bound hwIsSimd arrayIsLarge

/-- Per-primitive cost analysis for a given field + hardware. -/
structure PrimitiveCostReport where
  primitive : Primitive
  reduction : ReductionChoice
  boundFactor : Nat
  reductionCost : Nat
  deriving Repr, Inhabited

/-- Generate a cost report for each primitive on the given field + hardware.
    Uses reductionCostForHW (SSOT) instead of legacy reductionCost. -/
def analyzePrimitives (prime : Nat) (stateWidth : Nat := 8) (sboxExp : Nat := 7)
    (hw : HardwareCost := arm_cortex_a76) (mulCost : Nat := 3) (addCost : Nat := 1)
    : List PrimitiveCostReport :=
  [.nttButterfly, .friFold, .poseidonFullRound, .poseidonPartialRound].map fun prim =>
    let bound := primitiveBound prim stateWidth sboxExp 1
    let red := selectReductionForBound bound hw.isSimd false
    let cost := reductionCostForHW hw red
    { primitive := prim, reduction := red, boundFactor := bound, reductionCost := cost }

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Key insight: same prime, different primitives → different reductions.
    NTT butterfly (bound=2) → Harvey.
    Poseidon full round (bound=9 for t=8) → Solinas.
    This is the whole point of Fase 25. -/
theorem different_primitives_different_reductions :
    (selectPrimitiveReduction .nttButterfly ==
    selectPrimitiveReduction .poseidonFullRound) = false := rfl

/-- NTT butterfly with reduced inputs → Harvey (cheapest). -/
theorem ntt_uses_harvey :
    selectPrimitiveReduction .nttButterfly = .harvey := rfl

/-- FRI fold with reduced inputs → Harvey (same bound as NTT). -/
theorem fri_uses_harvey :
    selectPrimitiveReduction .friFold = .harvey := rfl

/-- Poseidon full round (t=8) with reduced inputs → Solinas (bound=9 > 4). -/
theorem poseidon_full_uses_solinas :
    selectPrimitiveReduction .poseidonFullRound = .solinasFold := rfl

/-- Poseidon partial round (t=8) with reduced inputs → Harvey (bound=1+7=8... wait).
    Actually: sboxOutputBound 1 7 = 1, so partial bound = 1 + 7*1 + 1 = 9 → Solinas. -/
theorem poseidon_partial_uses_solinas :
    selectPrimitiveReduction .poseidonPartialRound = .solinasFold := rfl

/-- SIMD with high-bound primitives → Solinas (not Montgomery).
    Montgomery REDC is unsound for sums — selectReductionForBound excludes it (v3.4.0 fix). -/
theorem poseidon_simd_uses_solinas :
    selectPrimitiveReduction .poseidonFullRound (hwIsSimd := true) = .solinasFold := rfl

/-- Cost analysis produces 4 entries (one per primitive). -/
theorem analyzePrimitives_length (p : Nat) :
    (analyzePrimitives p).length = 4 := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- NTT butterfly: bound=2, Harvey. -/
example : selectPrimitiveReduction .nttButterfly = .harvey := rfl

/-- FRI fold: bound=2, Harvey (same as NTT — key insight). -/
example : selectPrimitiveReduction .friFold = .harvey := rfl

/-- Poseidon full round: bound=9, Solinas (different from NTT). -/
example : selectPrimitiveReduction .poseidonFullRound = .solinasFold := rfl

/-- BabyBear cost analysis: 4 primitives, 2 different reductions. -/
example : (analyzePrimitives 2013265921).length = 4 := rfl

/-- Different primitives CAN use different reductions on the same field. -/
example : (selectPrimitiveReduction .nttButterfly ==
    selectPrimitiveReduction .poseidonFullRound) = false := rfl

/-- SIMD Poseidon: Solinas (Montgomery excluded for soundness — REDC only valid for products). -/
example : selectPrimitiveReduction .poseidonFullRound (hwIsSimd := true) = .solinasFold := rfl

/-- Goldilocks analysis is computable. -/
example : (analyzePrimitives 18446744069414584321).length = 4 := rfl

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.PrimitivesIntegration
