/-
  AmoLean.EGraph.Verified.Bitwise.MixedSaturationSpec — Saturation preserves ConsistentValuation

  B64 (CRITICO capstone): Fuel-based saturation loop for the MixedNodeOp EGraph.
  Composes PreservesCV steps to produce the end-to-end soundness theorem.

  Key insight: this module is INDEPENDENT of the specific rewrite rules —
  it only needs PreservesCV from B61. The concrete rule soundness (B65+B66)
  plugs in via the PreservesCV interface.

  Deliverables:
  - saturateMixedF: fuel-based saturation loop
  - saturateMixedF_preserves_consistent: capstone soundness theorem
  - phasedSaturateMixedF: two-phase saturation
  - phasedSaturateMixedF_preserves_consistent: phased soundness
-/
import AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.MixedSaturationSpec

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv)
open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec (MGraph CId)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (VPMI)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (CV PreservesCV ShapeHashconsInv)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Fuel-based saturation loop
-- ══════════════════════════════════════════════════════════════════

/-- Total saturation loop: each iteration applies a step function.
    No rebuild needed — the simpler VerifiedExtraction EGraph doesn't require it. -/
def saturateMixedF (step : MGraph → MGraph) (maxIter : Nat)
    (g : MGraph) : MGraph :=
  match maxIter with
  | 0 => g
  | n + 1 =>
    let g' := step g
    saturateMixedF step n g'

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Saturation soundness (capstone)
-- ══════════════════════════════════════════════════════════════════

/-- **Main soundness theorem**: saturateMixedF preserves ConsistentValuation
    when the step function preserves the (CV, PMI) pair.
    The existential witness comes from the step function. -/
theorem saturateMixedF_preserves_consistent (step : MGraph → MGraph)
    (maxIter : Nat) (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
    (h_step : PreservesCV env step) :
    ∃ v', CV (saturateMixedF step maxIter g) env v' := by
  induction maxIter generalizing g v with
  | zero => exact ⟨v, hcv⟩
  | succ n ih =>
    unfold saturateMixedF
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h_step g v hcv hpmi hshi
    exact ih (step g) v1 hcv1 hpmi1 hshi1

/-- saturateMixedF preserves the full (CV, PMI) pair (needed for composition). -/
theorem saturateMixedF_preserves_triple (step : MGraph → MGraph)
    (maxIter : Nat) (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
    (h_step : PreservesCV env step) :
    ∃ v', CV (saturateMixedF step maxIter g) env v' ∧
          VPMI (saturateMixedF step maxIter g) ∧
          ShapeHashconsInv (saturateMixedF step maxIter g) := by
  induction maxIter generalizing g v with
  | zero => exact ⟨v, hcv, hpmi, hshi⟩
  | succ n ih =>
    unfold saturateMixedF
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h_step g v hcv hpmi hshi
    exact ih (step g) v1 hcv1 hpmi1 hshi1

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Two-phase saturation
-- ══════════════════════════════════════════════════════════════════

/-- Two-phase saturation: run step1 for phase1Fuel iterations, then step2 for phase2Fuel. -/
def phasedSaturateMixedF (step1 step2 : MGraph → MGraph)
    (phase1Fuel phase2Fuel : Nat) (g : MGraph) : MGraph :=
  let g1 := saturateMixedF step1 phase1Fuel g
  saturateMixedF step2 phase2Fuel g1

/-- **Phased soundness**: if both step functions preserve (CV, PMI),
    the two-phase composition also preserves CV. -/
theorem phasedSaturateMixedF_preserves_consistent
    (step1 step2 : MGraph → MGraph)
    (phase1Fuel phase2Fuel : Nat) (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
    (h_step1 : PreservesCV env step1)
    (h_step2 : PreservesCV env step2) :
    ∃ v', CV (phasedSaturateMixedF step1 step2 phase1Fuel phase2Fuel g) env v' := by
  unfold phasedSaturateMixedF
  obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := saturateMixedF_preserves_triple step1 phase1Fuel g env v
    hcv hpmi hshi h_step1
  exact saturateMixedF_preserves_consistent step2 phase2Fuel _ env v1 hcv1 hpmi1 hshi1 h_step2

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: saturateMixedF with id is a no-op. -/
example (g : MGraph) : saturateMixedF id 0 g = g := rfl

/-- Smoke: saturateMixedF with id for any fuel preserves the graph. -/
theorem saturate_id_preserves (g : MGraph) (n : Nat) :
    saturateMixedF id n g = g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => unfold saturateMixedF; simp [ih]

end AmoLean.EGraph.Verified.Bitwise.MixedSaturationSpec
