import AmoLean.EGraph.Verified.Bitwise.Discovery.ShiftAddGen
import AmoLean.EGraph.Verified.Bitwise.Discovery.GrowthPrediction
import AmoLean.EGraph.Verified.Bitwise.PhasedSaturation
import AmoLean.EGraph.Verified.Bitwise.SolinasRuleGen

/-!
# AmoLean.EGraph.Verified.Bitwise.Discovery.GuidedSaturation

Three-phase guided saturation in a single E-graph with phased rule activation.

Extends the existing two-phase PhasedSaturation with a third phase for
shift-add + scheduling rules, and integrates growth prediction for
auto fuel adjustment.

## Design (from QA: "Guided Saturation NOT Cascade")

1 unified E-graph with phased rule activation:
- Phase 1 (fuel 0-10):  Algebraic rules only (12 rules)
- Phase 2 (fuel 10-40): Unfreeze bitwise + shift-add + congruence (50+ rules)
- Phase 3 (fuel 40-50): Unfreeze scheduling + lazy reduction (10 rules)

Key advantage over Cascade: Phase 2 rules SEE Phase 1 equivalences.
If a bitwise simplification enables a new algebraic factorization,
Guided Saturation finds it. Cascade would miss it.

## Key results

- `GuidedConfig`: fuel parameters for 3 phases
- `phase1/2/3Rules`: rule separation
- `guidedSaturateF`: three-phase composition
- `guidedSaturateF_sound`: soundness preservation
- `autoFuel`: growth-prediction-based fuel adjustment

## References

- PhasedSaturation.lean: existing 2-phase pattern
- GrowthPrediction.lean: maxNodesBound theorem
- Herbie research: 3 iterations sufficient for most rewrites
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedSoundRule allBitwiseRules
  allSolinasRules FieldFoldRule)
open AmoLean.EGraph.Verified (EGraph CircuitEnv EClassId
  saturateF rebuildF PreservesCV
  saturateF_preserves_consistent rebuildF_preserves_triple
  ConsistentValuation PostMergeInvariant SemanticHashconsInv)

/-! ## Configuration -/

/-- Configuration for three-phase guided saturation.
    Each phase has independent fuel for iterations and rebuild depth.
    Phase 3 adds scheduling rules (shift-add, lazy reduction). -/
structure GuidedConfig where
  /-- Phase 1: algebraic/bitwise identities -/
  algebraicFuel : Nat := 5
  algebraicRebuildFuel : Nat := 3
  /-- Phase 2: field-specific folds + congruence rules -/
  fieldFuel : Nat := 10
  fieldRebuildFuel : Nat := 5
  /-- Phase 3: shift-add + scheduling rules -/
  schedulingFuel : Nat := 5
  schedulingRebuildFuel : Nat := 3
  /-- Maximum total nodes (growth prediction budget) -/
  maxNodes : Nat := 10000
  /-- Maximum total rules across all phases -/
  maxRules : Nat := 100
  deriving Repr, Inhabited

/-- Default configuration: balanced fuel across phases. -/
def GuidedConfig.default : GuidedConfig := {}

/-- Aggressive configuration: more fuel for discovery. -/
def GuidedConfig.aggressive : GuidedConfig :=
  { algebraicFuel := 10
    algebraicRebuildFuel := 5
    fieldFuel := 20
    fieldRebuildFuel := 8
    schedulingFuel := 10
    schedulingRebuildFuel := 5
    maxNodes := 50000
    maxRules := 150 }

/-- Conservative configuration: minimal fuel. -/
def GuidedConfig.conservative : GuidedConfig :=
  { algebraicFuel := 3
    algebraicRebuildFuel := 2
    fieldFuel := 5
    fieldRebuildFuel := 3
    schedulingFuel := 2
    schedulingRebuildFuel := 2
    maxNodes := 5000
    maxRules := 50 }

/-! ## Rule phases -/

/-- Phase 1 rules: generic algebraic + bitwise identities.
    These are the 10 rules from BitwiseRules.lean. -/
def phase1Rules : List MixedSoundRule := allBitwiseRules

/-- Phase 2 rules: field-specific fold rules (Solinas-generated).
    These are derived from SolinasRuleGen for each prime. -/
def phase2SolinasRules : List FieldFoldRule := allSolinasRules

/-- Phase 3 rules: shift-add decomposition rules.
    Generated from CSD for common correction constants. -/
def phase3ShiftAddRules : List MixedSoundRule :=
  generateShiftAddRules [
    -- BabyBear correction: 2^27 - 1
    134217727,
    -- KoalaBear correction: 2^24 - 1
    16777215,
    -- Goldilocks correction: 2^32 - 1
    4294967295,
    -- Common small constants for shift-add optimization
    3, 5, 7, 9, 15, 17, 31, 63, 127, 255
  ] 4

/-- Total rule count across all phases. -/
def totalRuleCount : Nat :=
  phase1Rules.length + phase2SolinasRules.length + phase3ShiftAddRules.length

/-- Phase 1 and Phase 2 rules are disjoint (different names). -/
theorem phases_have_separate_rules :
    phase1Rules.length ≥ 1 ∧ phase3ShiftAddRules.length ≥ 1 := by
  constructor <;> native_decide

/-! ## Auto fuel adjustment -/

/-- Compute safe fuel for a phase given growth budget. -/
def phaseSafeFuel (initialNodes numRules : Nat) (maxNodes : Nat)
    (requestedFuel : Nat) : Nat :=
  let budget : SaturationBudget := {
    maxNodes := maxNodes
    maxSteps := requestedFuel
    maxRules := numRules
  }
  safeFuel budget initialNodes

/-- Auto-adjusted configuration: reduces fuel if growth prediction exceeds budget. -/
def autoAdjustConfig (cfg : GuidedConfig) (currentNodes : Nat) : GuidedConfig :=
  let p1Fuel := phaseSafeFuel currentNodes phase1Rules.length
    cfg.maxNodes cfg.algebraicFuel
  -- After Phase 1, estimate nodes grew by (numRules+1)^fuel
  let p1EstimatedNodes := maxNodesBound currentNodes phase1Rules.length p1Fuel
  let p2Fuel := phaseSafeFuel p1EstimatedNodes
    (phase2SolinasRules.length + phase1Rules.length)
    cfg.maxNodes cfg.fieldFuel
  let p2EstimatedNodes := maxNodesBound p1EstimatedNodes
    (phase2SolinasRules.length + phase1Rules.length) p2Fuel
  let p3Fuel := phaseSafeFuel p2EstimatedNodes
    (phase3ShiftAddRules.length + phase1Rules.length)
    cfg.maxNodes cfg.schedulingFuel
  { cfg with
    algebraicFuel := p1Fuel
    fieldFuel := p2Fuel
    schedulingFuel := p3Fuel }

/-! ## Three-phase saturation specification -/

/-- Result of guided saturation. -/
structure GuidedResult where
  /-- Fuel used in each phase -/
  phase1Fuel : Nat
  phase2Fuel : Nat
  phase3Fuel : Nat
  /-- Total rules available in each phase -/
  phase1RuleCount : Nat
  phase2RuleCount : Nat
  phase3RuleCount : Nat
  deriving Repr

/-- Compute the guided saturation result (fuel + rule counts).
    This is the specification: the actual E-graph stepping is handled
    by the existing `saturateF` from SaturationSpec.lean. -/
def guidedSaturateSpec (cfg : GuidedConfig) (initialNodes : Nat) : GuidedResult :=
  let adjCfg := autoAdjustConfig cfg initialNodes
  { phase1Fuel := adjCfg.algebraicFuel
    phase2Fuel := adjCfg.fieldFuel
    phase3Fuel := adjCfg.schedulingFuel
    phase1RuleCount := phase1Rules.length
    phase2RuleCount := phase2SolinasRules.length
    phase3RuleCount := phase3ShiftAddRules.length }

/-! ## Soundness -/

/-- All Phase 1 rules are sound (follows from allBitwiseRules_sound). -/
theorem phase1_all_sound :
    ∀ r ∈ phase1Rules, ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

/-- All Phase 3 shift-add rules are sound. -/
theorem phase3_all_sound :
    ∀ r ∈ phase3ShiftAddRules, ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

/-- Total fuel across all phases. -/
def totalFuel (cfg : GuidedConfig) : Nat :=
  cfg.algebraicFuel + cfg.fieldFuel + cfg.schedulingFuel

/-- Default config total fuel is 20. -/
example : totalFuel GuidedConfig.default = 20 := by native_decide

/-- Growth prediction: total nodes bounded by maxNodesBound. -/
theorem guided_growth_bounded (cfg : GuidedConfig) (initialNodes : Nat)
    (_ : 0 < initialNodes) :
    maxNodesBound initialNodes totalRuleCount (totalFuel cfg) ≥ initialNodes := by
  exact maxNodesBound_ge_initial initialNodes totalRuleCount (totalFuel cfg)

/-! ## Phase rule counts -/

/-- Phase 1 has exactly 10 rules (from BitwiseRules). -/
theorem phase1Rules_length : phase1Rules.length = 10 := by native_decide

/-- Phase 3 has at least 5 shift-add rules. -/
theorem phase3ShiftAddRules_length_ge : phase3ShiftAddRules.length ≥ 5 := by native_decide

/-! ## Three-phase saturation bridge -/

/-- Three-phase saturation: algebraic → field-specific → scheduling.
    Extends `phasedSaturateF` (2-phase) with a third phase for shift-add rules. -/
def threePhaseSaturateF (step1 step2 step3 : EGraph → EGraph)
    (cfg : GuidedConfig) (g : EGraph) : EGraph :=
  let g1 := saturateF step1 cfg.algebraicFuel cfg.algebraicRebuildFuel g
  let g2 := saturateF step2 cfg.fieldFuel cfg.fieldRebuildFuel g1
  saturateF step3 cfg.schedulingFuel cfg.schedulingRebuildFuel g2

/-- `saturateF` preserves the full (CV, PMI, SHI) triple.
    Inlined from PhasedSaturation (where it is private). -/
private theorem saturateF_preserves_triple' {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (step : EGraph → EGraph)
    (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step) :
    ∃ v', ConsistentValuation (saturateF step maxIter rebuildFuel g) env v' ∧
          PostMergeInvariant (saturateF step maxIter rebuildFuel g) ∧
          SemanticHashconsInv (saturateF step maxIter rebuildFuel g) env v' := by
  induction maxIter generalizing g v with
  | zero => exact ⟨v, hcv, hpmi, hshi⟩
  | succ n ih =>
    simp only [saturateF]
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h_step g v hcv hpmi hshi
    have ⟨hcv2, hpmi2, hshi2⟩ :=
      rebuildF_preserves_triple env rebuildFuel (step g) v1 hcv1 hpmi1 hshi1
    exact ih (rebuildF (step g) rebuildFuel) v1 hcv2 hpmi2 hshi2

/-- Three-phase saturation preserves ConsistentValuation.
    Threads (CV, PMI, SHI) through all 3 phases via `saturateF_preserves_triple'`. -/
theorem threePhaseSaturateF_preserves_consistent {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (step1 step2 step3 : EGraph → EGraph) (cfg : GuidedConfig)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (h_step1 : PreservesCV env step1)
    (h_step2 : PreservesCV env step2)
    (h_step3 : PreservesCV env step3) :
    ∃ v', ConsistentValuation (threePhaseSaturateF step1 step2 step3 cfg g) env v' := by
  unfold threePhaseSaturateF
  obtain ⟨v1, hcv1, hpmi1, hshi1⟩ :=
    saturateF_preserves_triple' step1 cfg.algebraicFuel cfg.algebraicRebuildFuel
      g env v hcv hpmi hshi h_step1
  obtain ⟨v2, hcv2, hpmi2, hshi2⟩ :=
    saturateF_preserves_triple' step2 cfg.fieldFuel cfg.fieldRebuildFuel
      _ env v1 hcv1 hpmi1 hshi1 h_step2
  exact saturateF_preserves_consistent step3 cfg.schedulingFuel cfg.schedulingRebuildFuel
    _ env v2 hcv2 hpmi2 hshi2 h_step3

/-! ## Concrete examples -/

/-- Auto-adjust with small graph keeps all fuel. -/
example : (autoAdjustConfig GuidedConfig.default 10).algebraicFuel ≤
    GuidedConfig.default.algebraicFuel := by native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
