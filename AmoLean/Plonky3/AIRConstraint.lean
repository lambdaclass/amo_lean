/-
  AIR Constraint Format — N20.1 (FUNDACIONAL)
  Algebraic Intermediate Representation for STARK constraint systems.
  Self-contained: no project imports, only Mathlib algebra basics.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs

namespace AmoLean.Plonky3.AIRConstraint

/-- A polynomial expression over a field F.
    Represents multivariate polynomials used in AIR constraint systems.
    Variables are indexed by Nat (column index in the execution trace). -/
inductive ConstraintExpr (F : Type) where
  | var : Nat → ConstraintExpr F
  | const : F → ConstraintExpr F
  | add : ConstraintExpr F → ConstraintExpr F → ConstraintExpr F
  | mul : ConstraintExpr F → ConstraintExpr F → ConstraintExpr F
  | neg : ConstraintExpr F → ConstraintExpr F
  | sub : ConstraintExpr F → ConstraintExpr F → ConstraintExpr F
  deriving Repr, BEq, DecidableEq

/-- A witness assigns field values to variables. -/
abbrev Witness (F : Type) := Nat → F

/-- Evaluate a constraint expression at a witness. -/
def evalExpr [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (e : ConstraintExpr F) (w : Witness F) : F :=
  match e with
  | .var i => w i
  | .const c => c
  | .add e1 e2 => evalExpr e1 w + evalExpr e2 w
  | .mul e1 e2 => evalExpr e1 w * evalExpr e2 w
  | .neg e1 => -(evalExpr e1 w)
  | .sub e1 e2 => evalExpr e1 w - evalExpr e2 w

/-- A constraint: an expression that must equal zero. -/
structure Constraint (F : Type) where
  expr : ConstraintExpr F
  name : String := ""

/-- A constraint system: a set of constraints over n variables. -/
structure ConstraintSystem (F : Type) where
  constraints : List (Constraint F)
  numVars : Nat

/-- A constraint is satisfied when it evaluates to zero. -/
def satisfies [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (w : Witness F) : Prop :=
  evalExpr c.expr w = 0

/-- All constraints in the system are satisfied. -/
def systemSatisfied [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (cs : ConstraintSystem F) (w : Witness F) : Prop :=
  ∀ c ∈ cs.constraints, satisfies c w

-- ── Basic properties ────────────────────────────────────────────────

theorem satisfies_empty [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (w : Witness F) :
    systemSatisfied (⟨[], 0⟩ : ConstraintSystem F) w := by
  simp [systemSatisfied]

theorem satisfies_singleton [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (w : Witness F)
    (h : satisfies c w) :
    systemSatisfied ⟨[c], 1⟩ w := by
  simp [systemSatisfied]
  exact h

theorem satisfies_cons [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (cs : List (Constraint F)) (n : Nat) (w : Witness F)
    (hc : satisfies c w)
    (hcs : systemSatisfied ⟨cs, n⟩ w) :
    systemSatisfied ⟨c :: cs, n + 1⟩ w := by
  intro c' hc'
  simp [List.mem_cons] at hc'
  cases hc' with
  | inl heq => rw [heq]; exact hc
  | inr hmem => exact hcs c' hmem

-- ── evalExpr structural lemmas ──────────────────────────────────────

@[simp]
theorem evalExpr_var [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (i : Nat) (w : Witness F) :
    evalExpr (.var i) w = w i := rfl

@[simp]
theorem evalExpr_const [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : F) (w : Witness F) :
    evalExpr (.const c) w = c := rfl

@[simp]
theorem evalExpr_add [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (e1 e2 : ConstraintExpr F) (w : Witness F) :
    evalExpr (.add e1 e2) w = evalExpr e1 w + evalExpr e2 w := rfl

@[simp]
theorem evalExpr_mul [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (e1 e2 : ConstraintExpr F) (w : Witness F) :
    evalExpr (.mul e1 e2) w = evalExpr e1 w * evalExpr e2 w := rfl

@[simp]
theorem evalExpr_neg [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (e : ConstraintExpr F) (w : Witness F) :
    evalExpr (.neg e) w = -(evalExpr e w) := rfl

@[simp]
theorem evalExpr_sub [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (e1 e2 : ConstraintExpr F) (w : Witness F) :
    evalExpr (.sub e1 e2) w = evalExpr e1 w - evalExpr e2 w := rfl

-- ── Helper constructors ─────────────────────────────────────────────

/-- Constraint that lhs = rhs (encoded as lhs - rhs = 0). -/
def mkEq (lhs rhs : ConstraintExpr F) : Constraint F :=
  { expr := .sub lhs rhs }

/-- Constraint x₀ * x₁ = x₂ (multiplication gate). -/
def mulGate : Constraint F := mkEq (.mul (.var 0) (.var 1)) (.var 2)

/-- Constraint x₀ + x₁ = x₂ (addition gate). -/
def addGate : Constraint F := mkEq (.add (.var 0) (.var 1)) (.var 2)

/-- Constraint x_i = c (constant assignment). -/
def constGate (i : Nat) (c : F) : Constraint F := mkEq (.var i) (.const c)

-- ── Smoke tests over Int ────────────────────────────────────────────

#eval evalExpr (ConstraintExpr.add (.var 0) (.const 5))
  (fun | 0 => (3 : Int) | _ => 0)
-- Expected: 8

#eval evalExpr (ConstraintExpr.mul (.var 0) (.var 1))
  (fun | 0 => (3 : Int) | 1 => 7 | _ => 0)
-- Expected: 21

#eval evalExpr (ConstraintExpr.neg (.const (4 : Int))) (fun _ => 0)
-- Expected: -4

-- ── Non-vacuity examples ────────────────────────────────────────────

/-- Non-vacuity: mulGate is satisfiable (3 * 7 = 21). -/
example : satisfies (mulGate : Constraint Int)
    (fun | 0 => 3 | 1 => 7 | 2 => 21 | _ => 0) := by
  unfold satisfies mulGate mkEq evalExpr
  rfl

/-- Non-vacuity: addGate is satisfiable (3 + 7 = 10). -/
example : satisfies (addGate : Constraint Int)
    (fun | 0 => 3 | 1 => 7 | 2 => 10 | _ => 0) := by
  unfold satisfies addGate mkEq evalExpr
  rfl

/-- Non-vacuity: constGate is satisfiable (x₀ = 42). -/
example : satisfies (constGate 0 (42 : Int) : Constraint Int)
    (fun | 0 => 42 | _ => 0) := by
  unfold satisfies constGate mkEq evalExpr
  rfl

/-- Non-vacuity: a 2-constraint system is jointly satisfiable.
    Witness: x₀=2, x₁=3, x₂=6 satisfies 2*3=6 and x₂=6. -/
example : systemSatisfied
    (⟨[mulGate, constGate 2 (6 : Int)], 3⟩ : ConstraintSystem Int)
    (fun | 0 => 2 | 1 => 3 | 2 => 6 | _ => 0) := by
  intro c hc
  simp [List.mem_cons] at hc
  rcases hc with rfl | rfl
  · unfold satisfies mulGate mkEq evalExpr; rfl
  · unfold satisfies constGate mkEq evalExpr; rfl

/-- Non-vacuity (negative): wrong witness does NOT satisfy mulGate. -/
example : ¬ satisfies (mulGate : Constraint Int)
    (fun | 0 => 3 | 1 => 7 | 2 => 20 | _ => 0) := by
  unfold satisfies mulGate mkEq evalExpr
  decide

end AmoLean.Plonky3.AIRConstraint
