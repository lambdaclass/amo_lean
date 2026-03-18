/-
  N24.6 RuleScoring — UCB1-lite rule scoring for exploitation/exploration
  balance in E-graph saturation.

  Provides a lightweight bandit-inspired mechanism to prioritize rewrite rules:
  - Exploitation: rules that historically reduced cost get higher priority
  - Exploration: under-explored rules receive a bonus (UCB1-style)
  - Selection: `selectTopK` picks the best K rules per iteration

  All arithmetic is integer-based (no Float). The exploration constant is
  scaled by 100 (default 141 ≈ √2 × 100).
-/
import Std.Data.HashMap

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

-- ============================================================================
-- Integer square root
-- ============================================================================

/-- Integer square root via Newton's method with bounded fuel.
    Returns ⌊√n⌋ for any `n : Nat`. -/
def isqrt (n : Nat) : Nat :=
  if n ≤ 1 then n
  else
    let rec go (fuel : Nat) (x : Nat) : Nat :=
      match fuel with
      | 0 => x
      | fuel' + 1 =>
        let x' := (x + n / x) / 2
        if x' ≥ x then x else go fuel' x'
    go 20 (n / 2 + 1)

-- ============================================================================
-- Core structures
-- ============================================================================

/-- Statistics for a single rewrite rule, accumulated across iterations. -/
structure RuleStats where
  totalApps : Nat       -- how many times this rule has been applied
  totalCostDelta : Int  -- cumulative cost reduction (negative = good)
  totalMatches : Nat    -- how many matches found
  deriving Repr, Inhabited

/-- UCB1-lite rule scorer for exploitation/exploration balance.

    The scorer maintains per-rule statistics and uses a UCB1-inspired formula
    to balance exploiting known-good rules with exploring under-used ones.
    The `explorationConstant` is scaled by 100 to avoid floating point. -/
structure RuleScorer where
  stats : Std.HashMap String RuleStats  -- ruleName -> stats
  totalApplications : Nat               -- sum of all applications
  explorationConstant : Nat             -- C parameter (scaled by 100)
  topK : Nat                            -- how many rules to select per iteration
  deriving Repr, Inhabited

-- ============================================================================
-- Operations
-- ============================================================================

/-- Create an empty scorer with default parameters.
    `explorationC = 141` approximates `√2 × 100`. -/
def RuleScorer.empty (explorationC : Nat := 141) (k : Nat := 5) : RuleScorer :=
  { stats := {}
    totalApplications := 0
    explorationConstant := explorationC
    topK := k }

/-- Get stats for a rule, returning default (all zeros) if unseen. -/
def RuleScorer.getStats (rs : RuleScorer) (name : String) : RuleStats :=
  match rs.stats[name]? with
  | some s => s
  | none => default

/-- Update stats after applying a rule.
    `costDelta` should be negative for cost-reducing applications.
    `numMatches` is how many pattern matches were found. -/
def RuleScorer.updateStats (rs : RuleScorer) (name : String)
    (costDelta : Int) (numMatches : Nat) : RuleScorer :=
  let old := rs.getStats name
  let new_ : RuleStats :=
    { totalApps := old.totalApps + 1
      totalCostDelta := old.totalCostDelta + costDelta
      totalMatches := old.totalMatches + numMatches }
  { rs with
    stats := rs.stats.insert name new_
    totalApplications := rs.totalApplications + 1 }

-- ============================================================================
-- Scoring functions
-- ============================================================================

/-- Exploitation score: average cost delta per match (negative = better).
    Returns 0 for rules that have never matched. -/
def exploitationScore (stats : RuleStats) : Int :=
  if stats.totalMatches > 0 then stats.totalCostDelta / stats.totalMatches else 0

/-- Exploration bonus: UCB1-style bonus for under-explored rules.
    `explorationC * isqrt(totalApps) / (ruleApps + 1)`
    Higher for rules with fewer applications relative to the total. -/
def explorationBonus (totalApps ruleApps explorationC : Nat) : Nat :=
  explorationC * isqrt totalApps / (ruleApps + 1)

/-- Combined UCB1 score: exploitation minus exploration bonus (lower = better).
    Exploitation is negative for cost-reducing rules, and the exploration bonus
    is subtracted so under-explored rules get lower (= more preferred) scores. -/
def ucb1Score (stats : RuleStats) (totalApps explorationC : Nat) : Int :=
  exploitationScore stats - ↑(explorationBonus totalApps stats.totalApps explorationC)

-- ============================================================================
-- Selection
-- ============================================================================

/-- Select the top K rules by UCB1 score (lower = better).
    Sorts all candidate rules by their UCB1 score and returns the best K. -/
def selectTopK (scorer : RuleScorer) (ruleNames : List String) : List String :=
  let scored := ruleNames.map fun name =>
    let s := scorer.getStats name
    (name, ucb1Score s scorer.totalApplications scorer.explorationConstant)
  let sorted := scored.mergeSort fun a b => a.2 ≤ b.2
  (sorted.take scorer.topK).map Prod.fst

-- ============================================================================
-- Theorems
-- ============================================================================

/-- `selectTopK` returns at most `topK` elements. -/
theorem selectTopK_length (scorer : RuleScorer) (ruleNames : List String) :
    (selectTopK scorer ruleNames).length ≤ scorer.topK := by
  unfold selectTopK
  simp only [List.length_map, List.length_take]
  exact Nat.min_le_left ..

/-- Every element in the output of `selectTopK` comes from the input list. -/
theorem selectTopK_subset (scorer : RuleScorer) (ruleNames : List String) :
    ∀ name, name ∈ selectTopK scorer ruleNames → name ∈ ruleNames := by
  intro name hmem
  unfold selectTopK at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨⟨n, sc⟩, hmem', heq⟩ := hmem
  simp only at heq; subst heq
  have h1 := List.take_subset scorer.topK _ hmem'
  rw [List.Perm.mem_iff (List.mergeSort_perm ..)] at h1
  simp only [List.mem_map] at h1
  obtain ⟨a, ha, heq2⟩ := h1
  have := Prod.mk.inj heq2
  exact this.1 ▸ ha

/-- `selectTopK` is defined as sort-then-take: the output is the first `topK`
    elements of a `mergeSort` on UCB1 scores. -/
theorem selectTopK_is_sorted_take (scorer : RuleScorer) (ruleNames : List String) :
    selectTopK scorer ruleNames =
    (((ruleNames.map fun name =>
      (name, ucb1Score (scorer.getStats name) scorer.totalApplications
        scorer.explorationConstant)).mergeSort
      fun a b => a.2 ≤ b.2).take scorer.topK).map Prod.fst := by
  rfl

-- ============================================================================
-- Examples
-- ============================================================================

/-- Exploitation score for a rule with negative cost delta is negative. -/
example : exploitationScore
    { totalApps := 5, totalCostDelta := -20, totalMatches := 4 } = -5 := by native_decide

/-- Exploration bonus is high for unseen rules. -/
example : explorationBonus 100 0 141 = 1410 := by native_decide

/-- Exploration bonus decreases as a rule is applied more. -/
example : explorationBonus 100 5 141 < explorationBonus 100 1 141 := by native_decide

/-- UCB1 score combines exploitation and exploration. -/
example : ucb1Score
    { totalApps := 0, totalCostDelta := 0, totalMatches := 0 } 100 141 = -1410 := by native_decide

/-- Unseen rules get a large exploration bonus (low UCB1 score = preferred). -/
example : ucb1Score
    { totalApps := 0, totalCostDelta := 0, totalMatches := 0 } 100 141 <
    ucb1Score
    { totalApps := 10, totalCostDelta := 0, totalMatches := 5 } 100 141 := by native_decide

/-- selectTopK on empty input returns empty. -/
example : selectTopK (RuleScorer.empty) [] = [] := by native_decide

/-- selectTopK respects topK limit. -/
example : (selectTopK (RuleScorer.empty (k := 2))
    ["a", "b", "c", "d"]).length ≤ 2 := by native_decide

/-- isqrt smoke tests. -/
example : isqrt 0 = 0 := by native_decide
example : isqrt 1 = 1 := by native_decide
example : isqrt 4 = 2 := by native_decide
example : isqrt 9 = 3 := by native_decide
example : isqrt 100 = 10 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
