/-
  AmoLean.EGraph.Verified.Bitwise.GuidedMixedSaturation — UCB1-guided saturation

  Integrates RuleScoring (UCB1 selectTopK) with MixedSaturation's operational
  e-graph loop. Each iteration selects top-K rules by score, applies them with
  merge counting, feeds stats back to the scorer, and rebuilds.

  Also integrates GrowthPrediction for adaptive fuel control.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedSaturation
import AmoLean.EGraph.Verified.Bitwise.Discovery.RuleScoring
import AmoLean.EGraph.Verified.Bitwise.Discovery.GrowthPrediction

namespace GuidedMixedSaturation

open AmoLean.EGraph.VerifiedExtraction
open MixedEMatch (RewriteRule)
open MixedSaturation (applyRulesF_counted rebuildF saturateMixedF)
open AmoLean.EGraph.Verified.Bitwise.Discovery (RuleScorer RuleStats
  selectTopK isqrt SaturationBudget safeFuel budgetExceeded maxNodesBound)

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Guided saturation step
-- ══════════════════════════════════════════════════════════════════

/-- One iteration of guided saturation:
    1. Select top-K rules by UCB1 score
    2. Apply selected rules with merge counting
    3. Update scorer with feedback
    4. Rebuild -/
def guidedSatStep (ematchFuel rebuildFuel : Nat)
    (g : EGraph Op) (allRules : List (RewriteRule Op))
    (scorer : RuleScorer) : (EGraph Op × RuleScorer) :=
  -- Step 1: Select top-K rules
  let allNames := allRules.map (fun (r : RewriteRule Op) => r.name)
  let selectedNames := selectTopK scorer allNames
  let selectedRules := allRules.filter (fun (r : RewriteRule Op) => selectedNames.contains r.name)
  -- Step 2: Apply with counting
  let (g', stats) := applyRulesF_counted ematchFuel g selectedRules
  -- Step 3: Update scorer with feedback
  -- Use merge count as proxy for rule effectiveness
  let scorer' := stats.foldl (fun (sc : RuleScorer) (p : String × Nat) =>
    sc.updateStats p.1 (-(p.2 : Int)) p.2) scorer
  -- Step 4: Rebuild
  let g'' := rebuildF g' rebuildFuel
  (g'', scorer')

-- ══════════════════════════════════════════════════════════════════
-- Section 2: UCB1-guided saturation loop
-- ══════════════════════════════════════════════════════════════════

/-- UCB1-guided saturation: like saturateMixedF but selects top-K rules
    per iteration based on accumulated scoring. Returns final graph + scorer. -/
def saturateMixedF_guided (ematchFuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (topK : Nat := 5) : (EGraph Op × RuleScorer) :=
  let initialScorer := RuleScorer.empty (k := topK)
  go ematchFuel maxIter rebuildFuel g rules initialScorer
where
  go (ematchFuel maxIter rebuildFuel : Nat)
      (g : EGraph Op) (rules : List (RewriteRule Op))
      (scorer : RuleScorer) : (EGraph Op × RuleScorer) :=
    match maxIter with
    | 0 => (g, scorer)
    | n + 1 =>
      let (g', scorer') := guidedSatStep ematchFuel rebuildFuel g rules scorer
      if EGraph.numClasses g' == EGraph.numClasses g then (g', scorer')  -- fixpoint
      else go ematchFuel n rebuildFuel g' rules scorer'

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Growth-bounded saturation
-- ══════════════════════════════════════════════════════════════════

/-- Compute safe fuel for a phase given current graph size and rule count. -/
def phaseSafeFuel (currentNodes numRules maxNodes requestedFuel : Nat) : Nat :=
  let budget : SaturationBudget :=
    { maxNodes := maxNodes, maxSteps := requestedFuel, maxRules := numRules }
  min requestedFuel (safeFuel budget currentNodes)

/-- Growth-bounded saturation: adjusts fuel based on predicted graph growth.
    If the predicted growth exceeds maxNodes, reduces fuel to stay within budget. -/
def saturateMixedF_bounded (ematchFuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (maxNodes : Nat) : EGraph Op :=
  let currentNodes := g.classes.size
  let adjustedIter := phaseSafeFuel currentNodes rules.length maxNodes maxIter
  saturateMixedF ematchFuel adjustedIter rebuildFuel g rules

/-- Growth-bounded + UCB1-guided saturation. -/
def saturateMixedF_fullGuided (ematchFuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (maxNodes : Nat) (topK : Nat := 5) : (EGraph Op × RuleScorer) :=
  let currentNodes := g.classes.size
  let adjustedIter := phaseSafeFuel currentNodes rules.length maxNodes maxIter
  saturateMixedF_guided ematchFuel adjustedIter rebuildFuel g rules topK

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)

/-- Smoke: guided saturation on empty graph returns empty. -/
example : (saturateMixedF_guided 10 5 3 (EGraph.empty : EGraph MixedNodeOp) []).1.numClasses = 0
    := by native_decide

/-- Smoke: growth-bounded saturation on empty graph returns empty. -/
example : (saturateMixedF_bounded 10 5 3 (EGraph.empty : EGraph MixedNodeOp) [] 1000).numClasses = 0
    := by native_decide

/-- Smoke: phaseSafeFuel reduces fuel when growth exceeds budget. -/
example : phaseSafeFuel 10 50 100 20 < 20 := by native_decide

/-- Smoke: phaseSafeFuel keeps full fuel when growth is small. -/
example : phaseSafeFuel 1 2 10000 5 = 5 := by native_decide

end SmokeTests

end GuidedMixedSaturation
