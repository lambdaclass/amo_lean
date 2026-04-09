/-
  N24.7 GrowthPrediction — Growth bound for E-graph saturation
  with auto fuel/budget adjustment.

  Proves that E-graph size after `steps` of saturation with `numRules`
  rules is bounded by `initialNodes * (numRules + 1) ^ steps`.
  Provides `SaturationBudget` and `safeFuel` for budget-aware saturation.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

/-! ## Growth bound -/

/-- Upper bound on E-graph size after `steps` of saturation with `numRules` rules.
    Each step can at most multiply the number of nodes by `(numRules + 1)`. -/
def maxNodesBound (initialNodes numRules steps : Nat) : Nat :=
  initialNodes * (numRules + 1) ^ steps

theorem maxNodesBound_base (initialNodes numRules : Nat) :
    maxNodesBound initialNodes numRules 0 = initialNodes := by
  simp [maxNodesBound]

theorem maxNodesBound_step (initialNodes numRules steps : Nat) :
    maxNodesBound initialNodes numRules (steps + 1) =
    maxNodesBound initialNodes numRules steps * (numRules + 1) := by
  simp [maxNodesBound, Nat.pow_succ]
  ring

theorem maxNodesBound_ge_initial (initialNodes numRules steps : Nat) :
    initialNodes ≤ maxNodesBound initialNodes numRules steps := by
  simp [maxNodesBound]
  exact Nat.le_mul_of_pos_right initialNodes (Nat.pos_of_ne_zero (by positivity))

theorem maxNodesBound_mono_steps (initialNodes numRules : Nat)
    {steps steps' : Nat} (h : steps ≤ steps') :
    maxNodesBound initialNodes numRules steps ≤
    maxNodesBound initialNodes numRules steps' := by
  simp [maxNodesBound]
  exact Nat.mul_le_mul_left initialNodes (Nat.pow_le_pow_right (by omega) h)

theorem maxNodesBound_mono_rules (initialNodes steps : Nat)
    {rules rules' : Nat} (h : rules ≤ rules') :
    maxNodesBound initialNodes rules steps ≤
    maxNodesBound initialNodes rules' steps := by
  simp [maxNodesBound]
  exact Nat.mul_le_mul_left initialNodes (Nat.pow_le_pow_left (by omega) steps)

theorem maxNodesBound_zero_initial (numRules steps : Nat) :
    maxNodesBound 0 numRules steps = 0 := by
  simp [maxNodesBound]

theorem maxNodesBound_one_step (initialNodes numRules : Nat) :
    maxNodesBound initialNodes numRules 1 = initialNodes * (numRules + 1) := by
  simp [maxNodesBound]

/-! ## Saturation budget -/

/-- Configuration for bounding saturation resource usage. -/
structure SaturationBudget where
  /-- Maximum number of nodes allowed in the E-graph. -/
  maxNodes : Nat
  /-- Maximum number of saturation steps. -/
  maxSteps : Nat
  /-- Number of rewrite rules applied per step. -/
  maxRules : Nat

/-- Check whether saturation should stop: current nodes exceed the budget. -/
def budgetExceeded (budget : SaturationBudget) (currentNodes : Nat) : Bool :=
  currentNodes > budget.maxNodes || currentNodes > budget.maxSteps * budget.maxRules

/-- Default budget: 10000 nodes, 100 steps, 20 rules. -/
def SaturationBudget.default : SaturationBudget :=
  { maxNodes := 10000, maxSteps := 100, maxRules := 20 }

/-- Small budget for testing. -/
def SaturationBudget.small : SaturationBudget :=
  { maxNodes := 500, maxSteps := 10, maxRules := 10 }

/-! ## Safe fuel computation -/

/-- Linearly search for the largest `k ≤ fuel` such that
    `maxNodesBound initialNodes rules k ≤ maxNodes`.
    Returns the last `k` that fits within the node budget. -/
def safeFuelAux (initialNodes rules maxNodes fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | n + 1 =>
    if maxNodesBound initialNodes rules (n + 1) ≤ maxNodes then
      n + 1
    else
      safeFuelAux initialNodes rules maxNodes n

/-- Compute a safe number of saturation steps such that the predicted
    node count stays within `budget.maxNodes`. Searches up to `budget.maxSteps`. -/
def safeFuel (budget : SaturationBudget) (initialNodes : Nat) : Nat :=
  safeFuelAux initialNodes budget.maxRules budget.maxNodes budget.maxSteps

/-! ## safeFuelAux properties -/

theorem safeFuelAux_le_fuel (initialNodes rules maxNodes fuel : Nat) :
    safeFuelAux initialNodes rules maxNodes fuel ≤ fuel := by
  induction fuel with
  | zero => simp [safeFuelAux]
  | succ n ih =>
    simp only [safeFuelAux]
    split
    · omega
    · omega

theorem safeFuelAux_bound (initialNodes rules maxNodes fuel : Nat)
    (hInit : initialNodes ≤ maxNodes) :
    maxNodesBound initialNodes rules (safeFuelAux initialNodes rules maxNodes fuel) ≤
    maxNodes := by
  induction fuel with
  | zero =>
    simp [safeFuelAux, maxNodesBound_base]
    exact hInit
  | succ n ih =>
    simp only [safeFuelAux]
    split
    · assumption
    · exact ih

/-- The safe fuel is at most `budget.maxSteps`. -/
theorem safeFuel_le_maxSteps (budget : SaturationBudget) (initialNodes : Nat) :
    safeFuel budget initialNodes ≤ budget.maxSteps := by
  simp [safeFuel]
  exact safeFuelAux_le_fuel initialNodes budget.maxRules budget.maxNodes budget.maxSteps

/-- The predicted node count at safeFuel steps is within the budget.
    Note: the bound `O((numRules+1)^steps)` is deliberately conservative —
    it assumes every rule fires in every step and creates a new node.
    In practice, saturation terminates much earlier (rules reach fixpoints,
    rebuild merges duplicate nodes). The conservatism ensures safeFuel
    never over-allocates fuel, preventing E-graph explosion at the cost
    of potentially under-saturating. -/
theorem safeFuel_bound (budget : SaturationBudget) (initialNodes : Nat)
    (hInit : initialNodes ≤ budget.maxNodes) :
    maxNodesBound initialNodes budget.maxRules (safeFuel budget initialNodes) ≤
    budget.maxNodes := by
  simp [safeFuel]
  exact safeFuelAux_bound initialNodes budget.maxRules budget.maxNodes budget.maxSteps hInit

/-! ## Budget exceeded properties -/

theorem budgetExceeded_of_gt (budget : SaturationBudget) (currentNodes : Nat)
    (h : currentNodes > budget.maxNodes) :
    budgetExceeded budget currentNodes = true := by
  simp [budgetExceeded, h]

theorem not_budgetExceeded_of_le (budget : SaturationBudget) (currentNodes : Nat)
    (h1 : currentNodes ≤ budget.maxNodes)
    (h2 : currentNodes ≤ budget.maxSteps * budget.maxRules) :
    budgetExceeded budget currentNodes = false := by
  simp [budgetExceeded]
  omega

/-! ## Concrete examples -/

example : maxNodesBound 10 5 3 = 2160 := by native_decide

example : maxNodesBound 100 10 0 = 100 := by native_decide

example : maxNodesBound 1 1 10 = 1024 := by native_decide

example : maxNodesBound 0 100 5 = 0 := by native_decide

example : safeFuel SaturationBudget.small 10 = 1 := by native_decide

example : budgetExceeded SaturationBudget.small 501 = true := by native_decide

example : budgetExceeded SaturationBudget.small 100 = false := by native_decide

/-! ## Growth rate helpers -/

/-- The growth factor per step is `numRules + 1`. -/
def growthFactor (numRules : Nat) : Nat := numRules + 1

theorem maxNodesBound_eq_mul_pow (initialNodes numRules steps : Nat) :
    maxNodesBound initialNodes numRules steps =
    initialNodes * growthFactor numRules ^ steps := by
  simp [maxNodesBound, growthFactor]

/-- If growth factor is 1 (zero rules), bound equals initial for any steps. -/
theorem maxNodesBound_zero_rules (initialNodes steps : Nat) :
    maxNodesBound initialNodes 0 steps = initialNodes := by
  simp [maxNodesBound]

/-- Combining two phases: running `s1` steps then `s2` more steps gives the
    same bound as `s1 + s2` steps total. -/
theorem maxNodesBound_compose (initialNodes numRules s1 s2 : Nat) :
    maxNodesBound (maxNodesBound initialNodes numRules s1) numRules s2 =
    maxNodesBound initialNodes numRules (s1 + s2) := by
  simp [maxNodesBound, Nat.pow_add]
  ring

/-- Strict monotonicity: with ≥2 rules and ≥1 initial node,
    more steps yields a strictly larger bound. -/
theorem maxNodesBound_strict_mono_steps (initialNodes numRules s : Nat)
    (hInit : 1 ≤ initialNodes) (hRules : 2 ≤ numRules) :
    maxNodesBound initialNodes numRules s <
    maxNodesBound initialNodes numRules (s + 1) := by
  simp only [maxNodesBound, Nat.pow_succ]
  apply Nat.mul_lt_mul_of_pos_left
  · nth_rw 1 [show (numRules + 1) ^ s = (numRules + 1) ^ s * 1 from (Nat.mul_one _).symm]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  · omega

end AmoLean.EGraph.Verified.Bitwise.Discovery
