/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.ExplosionControl

  B109 (N26.3 GATE): 4-phase spec-driven saturation with dynamic pruning.
  Defines `specDrivenSaturateF` that threads ConsistentValuation through
  spec-insertion, algebraic, reduction, and extraction phases.
  Fuel is dynamically bounded via GrowthPrediction's `safeFuel`.
-/
import AmoLean.EGraph.Verified.Bitwise.Discovery.ReduceSpecAxiom
import AmoLean.EGraph.Verified.Bitwise.Discovery.BitwiseVocabulary
import AmoLean.EGraph.Verified.Bitwise.Discovery.GrowthPrediction

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec (MGraph CId ShapeHashconsInv)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (CV VPMI PreservesCV)
open AmoLean.EGraph.Verified.Bitwise (MixedEnv)

-- ════════════════════════════════════════════════════════════════
-- Section 1: SpecDrivenConfig
-- ════════════════════════════════════════════════════════════════

/-- Configuration for 4-phase spec-driven saturation.
    Each phase has its own fuel budget:
    - `specFuel`: Phase 0 — insert the reduce(x) ≡ x % p spec axiom
    - `algebraicFuel`: Phase 1 — algebraic simplification rules
    - `reductionFuel`: Phase 2 — reduction equivalence discovery
    - `extractFuel`: Phase 3 — extraction preparation (class merging, etc.) -/
structure SpecDrivenConfig where
  specFuel : Nat := 1
  algebraicFuel : Nat := 10
  reductionFuel : Nat := 5
  extractFuel : Nat := 3
  deriving Repr

/-- Default configuration: 1 + 10 + 5 + 3 = 19 total steps. -/
def SpecDrivenConfig.default : SpecDrivenConfig := {}

/-- Conservative: minimal fuel for each phase. -/
def SpecDrivenConfig.conservative : SpecDrivenConfig where
  specFuel := 1
  algebraicFuel := 3
  reductionFuel := 2
  extractFuel := 1

/-- Aggressive: high fuel for algebraic and reduction phases. -/
def SpecDrivenConfig.aggressive : SpecDrivenConfig where
  specFuel := 1
  algebraicFuel := 20
  reductionFuel := 10
  extractFuel := 5

-- ════════════════════════════════════════════════════════════════
-- Section 2: iterateStep + preservation
-- ════════════════════════════════════════════════════════════════

/-- Apply a step function `fuel` times. -/
def iterateStep (step : MGraph → MGraph) : Nat → MGraph → MGraph
  | 0, g => g
  | n + 1, g => iterateStep step n (step g)

/-- Iterating a CV-preserving step preserves the consistency triple. -/
theorem iterateStep_preserves_cv (env : MixedEnv) (step : MGraph → MGraph)
    (h : PreservesCV env step) (fuel : Nat) :
    PreservesCV env (iterateStep step fuel) := by
  induction fuel with
  | zero =>
    intro g v hcv hpmi hshi
    exact ⟨v, hcv, hpmi, hshi⟩
  | succ n ih =>
    intro g v hcv hpmi hshi
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h g v hcv hpmi hshi
    exact ih (step g) v1 hcv1 hpmi1 hshi1

-- ════════════════════════════════════════════════════════════════
-- Section 3: specDrivenSaturateF
-- ════════════════════════════════════════════════════════════════

/-- 4-phase spec-driven saturation pipeline.
    Composes spec insertion → algebraic → reduction → extraction phases,
    each iterated according to the config's fuel budget. -/
def specDrivenSaturateF
    (specStep : MGraph → MGraph)
    (algStep : MGraph → MGraph)
    (redStep : MGraph → MGraph)
    (extStep : MGraph → MGraph)
    (cfg : SpecDrivenConfig) (g : MGraph) : MGraph :=
  let g0 := iterateStep specStep cfg.specFuel g
  let g1 := iterateStep algStep cfg.algebraicFuel g0
  let g2 := iterateStep redStep cfg.reductionFuel g1
  iterateStep extStep cfg.extractFuel g2

-- ════════════════════════════════════════════════════════════════
-- Section 4: specDrivenSaturateF_preserves_consistent
-- ════════════════════════════════════════════════════════════════

/-- The 4-phase saturation preserves ConsistentValuation, threading
    the CV witness through all phases via `iterateStep_preserves_cv`. -/
theorem specDrivenSaturateF_preserves_consistent
    (env : MixedEnv)
    (specStep algStep redStep extStep : MGraph → MGraph)
    (cfg : SpecDrivenConfig)
    (g : MGraph) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
    (h_spec : PreservesCV env specStep)
    (h_alg : PreservesCV env algStep)
    (h_red : PreservesCV env redStep)
    (h_ext : PreservesCV env extStep) :
    ∃ v', CV (specDrivenSaturateF specStep algStep redStep extStep cfg g) env v' := by
  unfold specDrivenSaturateF
  -- Phase 0: spec insertion
  have h0 := iterateStep_preserves_cv env specStep h_spec cfg.specFuel
  obtain ⟨v0, hcv0, hpmi0, hshi0⟩ := h0 g v hcv hpmi hshi
  -- Phase 1: algebraic rules
  have h1 := iterateStep_preserves_cv env algStep h_alg cfg.algebraicFuel
  obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h1 _ v0 hcv0 hpmi0 hshi0
  -- Phase 2: reduction equivalence
  have h2 := iterateStep_preserves_cv env redStep h_red cfg.reductionFuel
  obtain ⟨v2, hcv2, hpmi2, hshi2⟩ := h2 _ v1 hcv1 hpmi1 hshi1
  -- Phase 3: extraction prep
  have h3 := iterateStep_preserves_cv env extStep h_ext cfg.extractFuel
  obtain ⟨v3, hcv3, _, _⟩ := h3 _ v2 hcv2 hpmi2 hshi2
  exact ⟨v3, hcv3⟩

-- ════════════════════════════════════════════════════════════════
-- Section 5: Growth-aware fuel cap
-- ════════════════════════════════════════════════════════════════

/-- Compute safe fuel for a phase given initial node count and a budget.
    Delegates to `safeFuel` from GrowthPrediction. -/
def specPhaseSafeFuel (initialNodes : Nat) (budget : SaturationBudget) : Nat :=
  safeFuel budget initialNodes

/-- `specPhaseSafeFuel` respects the budget's step limit. -/
theorem specPhaseSafeFuel_le_maxSteps (initialNodes : Nat) (budget : SaturationBudget) :
    specPhaseSafeFuel initialNodes budget ≤ budget.maxSteps :=
  safeFuel_le_maxSteps budget initialNodes

/-- `specPhaseSafeFuel` keeps the predicted node count within the budget. -/
theorem specPhaseSafeFuel_bound (initialNodes : Nat) (budget : SaturationBudget)
    (hInit : initialNodes ≤ budget.maxNodes) :
    maxNodesBound initialNodes budget.maxRules (specPhaseSafeFuel initialNodes budget) ≤
    budget.maxNodes :=
  safeFuel_bound budget initialNodes hInit

-- ════════════════════════════════════════════════════════════════
-- Section 6: autoAdjustConfig
-- ════════════════════════════════════════════════════════════════

/-- Dynamically adjust saturation config based on a ReduceSpec and budget.
    Each phase's fuel is capped by `min defaultCap (specPhaseSafeFuel estimatedNodes budget)`.
    The estimated node count grows conservatively across phases. -/
def autoAdjustConfig (_spec : ReduceSpec) (budget : SaturationBudget) : SpecDrivenConfig where
  specFuel := 1
  algebraicFuel := min 10 (specPhaseSafeFuel 2 budget)
  reductionFuel := min 5 (specPhaseSafeFuel (2 + 10 * budget.maxRules) budget)
  extractFuel := min 3 (specPhaseSafeFuel (2 + 15 * budget.maxRules) budget)

-- ════════════════════════════════════════════════════════════════
-- Section 7: totalFuel + bound theorem
-- ════════════════════════════════════════════════════════════════

/-- Total fuel across all 4 phases. -/
def totalFuel (cfg : SpecDrivenConfig) : Nat :=
  cfg.specFuel + cfg.algebraicFuel + cfg.reductionFuel + cfg.extractFuel

/-- The auto-adjusted config always uses at most 1 + 10 + 5 + 3 = 19 fuel. -/
theorem autoAdjust_fuel_bounded (_spec : ReduceSpec) (budget : SaturationBudget) :
    totalFuel (autoAdjustConfig _spec budget) ≤ 1 + 10 + 5 + 3 := by
  simp [totalFuel, autoAdjustConfig]
  omega

-- ════════════════════════════════════════════════════════════════
-- Section 8: Smoke tests
-- ════════════════════════════════════════════════════════════════

-- Default config has reasonable total fuel
#eval totalFuel SpecDrivenConfig.default  -- 19

example : totalFuel SpecDrivenConfig.default ≤ 100 := by native_decide

-- Conservative config is within bounds
example : totalFuel SpecDrivenConfig.conservative ≤ 19 := by native_decide

-- Aggressive config total
example : totalFuel SpecDrivenConfig.aggressive = 36 := by native_decide

-- autoAdjust with babybearSpec stays bounded
example : totalFuel (autoAdjustConfig babybearSpec SaturationBudget.default) ≤ 19 := by
  native_decide

-- autoAdjust with mersenne31Spec stays bounded
example : totalFuel (autoAdjustConfig mersenne31Spec SaturationBudget.default) ≤ 19 := by
  native_decide

-- autoAdjust with small budget is even tighter
example : totalFuel (autoAdjustConfig babybearSpec SaturationBudget.small) ≤ 19 := by
  native_decide

-- iterateStep 0 is identity
example : ∀ g : MGraph, iterateStep id 0 g = g := fun _ => rfl

-- iterateStep 1 applies step once
example : ∀ g : MGraph, iterateStep id 1 g = id g := fun _ => rfl

-- specPhaseSafeFuel with default budget doesn't exceed maxSteps
example : specPhaseSafeFuel 2 SaturationBudget.default ≤ 100 := by native_decide

-- specPhaseSafeFuel with small budget is conservative
example : specPhaseSafeFuel 2 SaturationBudget.small ≤ 10 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
