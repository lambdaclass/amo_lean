import Std.Data.HashMap
import AmoLean.EGraph.Verified.Bitwise.CostModelDef

/-!
# AmoLean.EGraph.Verified.Bitwise.Discovery.ShadowGraph

Lightweight cost-delta tracking structure for guided rewrite application.
A ShadowGraph records the current minimum cost per e-class and allows
efficient queries about whether a proposed rewrite would reduce cost.

## Key results

- `ShadowGraph.updateCost`: update cost if improvement, returning whether it changed
- `ShadowGraph.wouldImprove`: pure query for cost improvement
- `filterProfitable`: keep only rule applications that reduce cost
- `filterProfitable_subset`: every accepted application was in the original list
- `filterProfitable_profitable`: every accepted application would improve cost
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

/-! ## ShadowGraph -/

/-- Default cost for unknown e-classes (acts as infinity). -/
def infinityCost : Nat := 1000000

/-- Lightweight cost-delta tracker: maps each e-class to its current minimum cost. -/
structure ShadowGraph where
  /-- EClassId → current minimum cost -/
  costs : Std.HashMap Nat Nat
  /-- Sum of all minimum costs (for global progress tracking) -/
  totalCost : Nat
  deriving Repr, Inhabited

/-- Empty shadow graph with no cost information. -/
def ShadowGraph.empty : ShadowGraph :=
  { costs := {}, totalCost := 0 }

/-- Look up the cost of an e-class, returning `infinityCost` if unknown. -/
def ShadowGraph.getCost (sg : ShadowGraph) (classId : Nat) : Nat :=
  sg.costs.getD classId infinityCost

/-- Check whether updating `classId` to `newCost` would be an improvement, without mutating. -/
def ShadowGraph.wouldImprove (sg : ShadowGraph) (classId : Nat) (newCost : Nat) : Bool :=
  newCost < sg.getCost classId

/-- Update cost for `classId` if `newCost` is strictly less than the current cost.
    Returns the (possibly updated) graph and a flag indicating whether an improvement occurred. -/
def ShadowGraph.updateCost (sg : ShadowGraph) (classId : Nat) (newCost : Nat) : ShadowGraph × Bool :=
  if newCost < sg.getCost classId then
    let oldCost := match sg.costs.get? classId with | some c => c | none => 0
    let newTotal := sg.totalCost - oldCost + newCost
    ({ costs := sg.costs.insert classId newCost, totalCost := newTotal }, true)
  else
    (sg, false)

/-! ## ShadowGraph theorems -/

/-- `wouldImprove` is consistent with `updateCost`: improvement iff the second component is true. -/
theorem ShadowGraph.wouldImprove_iff_updateCost (sg : ShadowGraph) (classId : Nat) (newCost : Nat) :
    sg.wouldImprove classId newCost = (sg.updateCost classId newCost).2 := by
  simp [wouldImprove, updateCost]
  split <;> simp_all

/-- After a successful update, the stored cost equals the new cost. -/
theorem ShadowGraph.getCost_after_update (sg : ShadowGraph) (classId : Nat) (newCost : Nat)
    (h : newCost < sg.getCost classId) :
    (sg.updateCost classId newCost).1.getCost classId = newCost := by
  unfold updateCost
  rw [if_pos h]
  simp [getCost]

/-- `wouldImprove` implies the new cost is strictly less than the current cost. -/
theorem ShadowGraph.wouldImprove_lt (sg : ShadowGraph) (classId : Nat) (newCost : Nat)
    (h : sg.wouldImprove classId newCost = true) :
    newCost < sg.getCost classId := by
  simp [wouldImprove] at h
  exact h

/-- If `wouldImprove` is false, then the new cost is not less than the current cost. -/
theorem ShadowGraph.not_wouldImprove (sg : ShadowGraph) (classId : Nat) (newCost : Nat)
    (h : sg.wouldImprove classId newCost = false) :
    sg.getCost classId ≤ newCost := by
  simp [wouldImprove] at h
  exact h

/-- `updateCost` with no improvement returns the original graph unchanged. -/
theorem ShadowGraph.updateCost_no_improve (sg : ShadowGraph) (classId : Nat) (newCost : Nat)
    (h : ¬ newCost < sg.getCost classId) :
    (sg.updateCost classId newCost) = (sg, false) := by
  unfold updateCost
  rw [if_neg h]

/-! ## Batch initialization -/

/-- Initialize a ShadowGraph from a list of (classId, cost) pairs. -/
def ShadowGraph.fromList (entries : List (Nat × Nat)) : ShadowGraph :=
  entries.foldl (fun sg (cid, cost) => (sg.updateCost cid cost).1) ShadowGraph.empty

/-! ## RuleApplication -/

/-- A proposed rewrite rule application targeting a specific e-class. -/
structure RuleApplication where
  /-- Name of the rewrite rule -/
  ruleName : String
  /-- Target e-class identifier -/
  classId : Nat
  /-- Estimated cost after applying the rule -/
  estimatedCost : Nat
  deriving Repr, Inhabited

/-! ## Profitable filtering -/

/-- Keep only rule applications that would reduce cost in the shadow graph. -/
def filterProfitable (sg : ShadowGraph) (apps : List RuleApplication) : List RuleApplication :=
  apps.filter (fun app => sg.wouldImprove app.classId app.estimatedCost)

/-- Every element in the filtered result appears in the original list. -/
theorem filterProfitable_subset (sg : ShadowGraph) (apps : List RuleApplication)
    (app : RuleApplication) (h : app ∈ filterProfitable sg apps) :
    app ∈ apps := by
  simp [filterProfitable] at h
  exact h.1

/-- Every element in the filtered result satisfies `wouldImprove`. -/
theorem filterProfitable_profitable (sg : ShadowGraph) (apps : List RuleApplication)
    (app : RuleApplication) (h : app ∈ filterProfitable sg apps) :
    sg.wouldImprove app.classId app.estimatedCost = true := by
  simp [filterProfitable] at h
  exact h.2

/-- The filtered list is no longer than the original. -/
theorem filterProfitable_length_le (sg : ShadowGraph) (apps : List RuleApplication) :
    (filterProfitable sg apps).length ≤ apps.length := by
  exact List.length_filter_le _ _

/-- Filtering an empty list yields an empty list. -/
theorem filterProfitable_nil (sg : ShadowGraph) :
    filterProfitable sg [] = [] := by
  rfl

/-! ## ShadowStats -/

/-- Statistics for shadow-graph-guided rewriting. -/
structure ShadowStats where
  /-- Total proposed rule applications -/
  totalProposed : Nat
  /-- Total applications accepted (would improve cost) -/
  totalAccepted : Nat
  /-- Total applications skipped (would not improve cost) -/
  totalSkipped : Nat
  deriving Repr, Inhabited

/-- Initial (empty) statistics. -/
def ShadowStats.empty : ShadowStats :=
  { totalProposed := 0, totalAccepted := 0, totalSkipped := 0 }

/-- Update statistics after processing a batch of proposals. -/
def updateStats (stats : ShadowStats) (proposed accepted : Nat) : ShadowStats :=
  { totalProposed := stats.totalProposed + proposed,
    totalAccepted := stats.totalAccepted + accepted,
    totalSkipped  := stats.totalSkipped + (proposed - accepted) }

/-- The sum of accepted and skipped equals proposed (when accepted ≤ proposed). -/
theorem updateStats_consistent (stats : ShadowStats) (proposed accepted : Nat)
    (h : accepted ≤ proposed)
    (h1 : stats.totalAccepted + stats.totalSkipped = stats.totalProposed) :
    (updateStats stats proposed accepted).totalAccepted +
    (updateStats stats proposed accepted).totalSkipped =
    (updateStats stats proposed accepted).totalProposed := by
  simp [updateStats]
  omega

/-- Starting from empty stats, consistency holds. -/
theorem updateStats_empty_consistent (proposed accepted : Nat) (h : accepted ≤ proposed) :
    (updateStats ShadowStats.empty proposed accepted).totalAccepted +
    (updateStats ShadowStats.empty proposed accepted).totalSkipped =
    (updateStats ShadowStats.empty proposed accepted).totalProposed := by
  simp [updateStats, ShadowStats.empty]
  omega

/-! ## Integration: filter + stats -/

/-- Run profitable filtering and compute stats in one pass. -/
def filterWithStats (sg : ShadowGraph) (apps : List RuleApplication)
    (stats : ShadowStats) : List RuleApplication × ShadowStats :=
  let profitable := filterProfitable sg apps
  let newStats := updateStats stats apps.length profitable.length
  (profitable, newStats)

/-- After `filterWithStats`, the returned list satisfies profitability. -/
theorem filterWithStats_profitable (sg : ShadowGraph) (apps : List RuleApplication)
    (stats : ShadowStats) (app : RuleApplication)
    (h : app ∈ (filterWithStats sg apps stats).1) :
    sg.wouldImprove app.classId app.estimatedCost = true := by
  exact filterProfitable_profitable sg apps app h

/-! ## Smoke tests -/

-- Create an empty shadow graph and verify default cost.
#eval
  let sg := ShadowGraph.empty
  let c := sg.getCost 42
  s!"Empty graph, getCost 42 = {c} (expected {infinityCost})"

-- Update a cost and verify it is stored.
#eval
  let sg := ShadowGraph.empty
  let (sg2, improved) := sg.updateCost 7 50
  s!"After updateCost 7 50: getCost 7 = {sg2.getCost 7}, improved = {improved}"

-- Verify wouldImprove is consistent.
#eval
  let sg := ShadowGraph.empty
  let (sg2, _) := sg.updateCost 3 100
  let yes := sg2.wouldImprove 3 50
  let no  := sg2.wouldImprove 3 200
  s!"wouldImprove 3 50 = {yes}, wouldImprove 3 200 = {no}"

-- Verify filterProfitable keeps only improvements.
#eval
  let sg := ShadowGraph.empty
  let (sg2, _) := sg.updateCost 1 100
  let (sg3, _) := sg2.updateCost 2 80
  let apps : List RuleApplication := [
    { ruleName := "rule_a", classId := 1, estimatedCost := 50 },   -- improvement
    { ruleName := "rule_b", classId := 2, estimatedCost := 90 },   -- no improvement
    { ruleName := "rule_c", classId := 1, estimatedCost := 120 },  -- no improvement
    { ruleName := "rule_d", classId := 3, estimatedCost := 30 }    -- improvement (vs infinity)
  ]
  let result := filterProfitable sg3 apps
  s!"filterProfitable: {apps.length} proposed -> {result.length} accepted"

-- Verify fromList initialization.
#eval
  let sg := ShadowGraph.fromList [(1, 100), (2, 50), (3, 200)]
  s!"fromList: getCost 1={sg.getCost 1}, getCost 2={sg.getCost 2}, getCost 99={sg.getCost 99}"

end AmoLean.EGraph.Verified.Bitwise.Discovery
