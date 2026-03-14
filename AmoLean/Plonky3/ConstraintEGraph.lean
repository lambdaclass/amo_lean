/-
  AMO-Lean v2.8.0 — Constraint-to-EGraph Bridge
  N20.3 (PARALELO): Map AIR constraints to the E-Graph engine format.

  Architecture:
  - ConstraintExpr F (AIRConstraint.lean) represents multivariate polynomials
  - CircuitExpr (VerifiedExtraction/CircuitAdaptor.lean) is the E-Graph expression type
  - This file bridges them via a structural homomorphism

  Key definitions:
  - constraintToCircuit: ConstraintExpr F → CircuitExpr
  - evalConstraintToCircuit: evaluation is preserved through the mapping
  - optimized_constraint_sound: E-Graph optimization preserves constraint satisfaction

  Approach: ConstraintExpr has {var, const, add, mul, neg, sub}. CircuitExpr has
  {constE, witnessE, pubInputE, addE, mulE, negE, smulE}. The mapping sends:
  - var i → witnessE i (variables are witness values)
  - const c → constE (encode c) (constants mapped via an encoding)
  - add → addE, mul → mulE, neg → negE
  - sub e1 e2 → addE (map e1) (negE (map e2))  (sub = add + neg)

  For the field-to-Nat encoding of constants, we parameterize over an injective
  encoding function. This keeps the file generic.
-/

import AmoLean.Plonky3.AIRConstraint
import AmoLean.EGraph.VerifiedExtraction.CircuitAdaptor

set_option autoImplicit false

namespace AmoLean.Plonky3.ConstraintEGraph

open AmoLean.Plonky3.AIRConstraint
open AmoLean.EGraph.VerifiedExtraction.CircuitAdaptor
open AmoLean.EGraph.Verified

/-! ## Constraint-to-Circuit Translation -/

/-- Encode a ConstraintExpr as a CircuitExpr.
    Variables map to `witnessE` (execution trace columns = witnesses).
    Constants map via an encoding function `encodeConst : F → Nat`.
    Sub is desugared to add + neg (matching the CircuitExpr algebra). -/
def constraintToCircuit {F : Type} (encodeConst : F → Nat) :
    ConstraintExpr F → CircuitExpr
  | .var i => .witnessE i
  | .const c => .constE (encodeConst c)
  | .add e1 e2 => .addE (constraintToCircuit encodeConst e1)
                        (constraintToCircuit encodeConst e2)
  | .mul e1 e2 => .mulE (constraintToCircuit encodeConst e1)
                        (constraintToCircuit encodeConst e2)
  | .neg e => .negE (constraintToCircuit encodeConst e)
  | .sub e1 e2 => .addE (constraintToCircuit encodeConst e1)
                        (.negE (constraintToCircuit encodeConst e2))

/-! ## Evaluation Preservation

  We show that evaluating a ConstraintExpr on a witness `w` yields the same
  result as evaluating its CircuitExpr translation on a matching CircuitEnv.
  The matching condition requires:
  - env.witnessVal i = w i       (variables)
  - env.constVal (encodeConst c) = c   (constants via encoding)
-/

/-- A CircuitEnv matches a witness and encoding if witness values and encoded
    constants are faithfully represented. -/
structure EnvMatchesWitness (F : Type) [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (env : CircuitEnv F) (w : Witness F) (encodeConst : F → Nat) : Prop where
  witness_match : ∀ i : Nat, env.witnessVal i = w i
  const_match : ∀ c : F, env.constVal (encodeConst c) = c

/-- Evaluation preservation: translating a ConstraintExpr to CircuitExpr
    and evaluating it on a matching CircuitEnv yields the same field value
    as evaluating the ConstraintExpr directly on the witness.

    The sub case uses the ring identity: a - b = a + (-b). -/
theorem evalConstraintToCircuit
    {F : Type} [Ring F]
    (e : ConstraintExpr F) (w : Witness F)
    (env : CircuitEnv F) (encodeConst : F → Nat)
    (hmatch : EnvMatchesWitness F env w encodeConst) :
    CircuitExpr.eval (constraintToCircuit encodeConst e) env = evalExpr e w := by
  induction e with
  | var i =>
    unfold constraintToCircuit
    simp [CircuitExpr.eval, evalExpr, hmatch.witness_match]
  | const c =>
    unfold constraintToCircuit
    simp [CircuitExpr.eval, evalExpr, hmatch.const_match]
  | add e1 e2 ih1 ih2 =>
    unfold constraintToCircuit
    simp only [CircuitExpr.eval, evalExpr]
    rw [ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
    unfold constraintToCircuit
    simp only [CircuitExpr.eval, evalExpr]
    rw [ih1, ih2]
  | neg e ih =>
    unfold constraintToCircuit
    simp only [CircuitExpr.eval, evalExpr]
    rw [ih]
  | sub e1 e2 ih1 ih2 =>
    unfold constraintToCircuit
    simp only [CircuitExpr.eval, evalExpr]
    rw [ih1, ih2, sub_eq_add_neg]

/-! ## Constraint Optimizability

  A constraint is "optimizable" if it can be translated and the translation
  faithfully represents its semantics. The key result is that if two
  CircuitExprs evaluate identically (as certified by the E-Graph engine),
  then substituting one for the other preserves constraint satisfaction.
-/

/-- Two ConstraintExprs are semantically equivalent if they evaluate identically
    on all witnesses. -/
def constraintEquiv {F : Type} [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (e1 e2 : ConstraintExpr F) : Prop :=
  ∀ w : Witness F, evalExpr e1 w = evalExpr e2 w

/-- If the CircuitExpr translations of two ConstraintExprs evaluate identically
    on all matching environments, then the original ConstraintExprs are
    semantically equivalent. -/
theorem circuit_equiv_implies_constraint_equiv
    {F : Type} [Ring F]
    (e1 e2 : ConstraintExpr F)
    (encodeConst : F → Nat)
    (h_circuit : ∀ env : CircuitEnv F,
      CircuitExpr.eval (constraintToCircuit encodeConst e1) env =
      CircuitExpr.eval (constraintToCircuit encodeConst e2) env)
    (h_surj : ∀ w : Witness F, ∃ env : CircuitEnv F,
      EnvMatchesWitness F env w encodeConst) :
    constraintEquiv e1 e2 := by
  intro w
  obtain ⟨env, hmatch⟩ := h_surj w
  rw [← evalConstraintToCircuit e1 w env encodeConst hmatch,
      ← evalConstraintToCircuit e2 w env encodeConst hmatch]
  exact h_circuit env

/-- The core optimization soundness theorem:
    If two constraint expressions have CircuitExpr translations that are
    semantically equivalent (as certified by the E-Graph), then substituting
    one for the other preserves constraint satisfaction. -/
theorem optimized_constraint_sound
    {F : Type} [Ring F]
    (original optimized : ConstraintExpr F)
    (h_equiv : constraintEquiv original optimized)
    (w : Witness F) :
    evalExpr original w = 0 ↔ evalExpr optimized w = 0 := by
  constructor
  · intro h; rw [← h_equiv w]; exact h
  · intro h; rw [h_equiv w]; exact h

/-- Corollary: optimization preserves system satisfaction when applied to
    one constraint in the system. -/
theorem optimized_system_sound
    {F : Type} [Ring F]
    (cs : List (Constraint F)) (n : Nat)
    (idx : Nat) (hidx : idx < cs.length)
    (optimized : ConstraintExpr F)
    (h_equiv : constraintEquiv (cs[idx].expr) optimized)
    (w : Witness F)
    (h_sat : systemSatisfied ⟨cs, n⟩ w) :
    evalExpr optimized w = 0 := by
  have h_orig := h_sat (cs[idx]) (List.getElem_mem hidx)
  rw [satisfies] at h_orig
  exact (optimized_constraint_sound (cs[idx]).expr optimized h_equiv w).mp h_orig

/-! ## Non-vacuity Examples -/

/-- Non-vacuity: constraintEquiv is not vacuously true —
    semantically different expressions are NOT equivalent. -/
example : ¬ @constraintEquiv Int _ _ _ _ _
    (.var 0) (.var 1) := by
  intro h
  have := h (fun | 0 => 1 | _ => 0)
  simp [evalExpr] at this

/-- Non-vacuity: optimized_constraint_sound works on a concrete example.
    x₀ * x₁ - x₂ = 0 ↔ x₀ * x₁ + (-x₂) = 0 (sub desugaring). -/
example : @constraintEquiv Int _ _ _ _ _
    (.sub (.mul (.var 0) (.var 1)) (.var 2))
    (.add (.mul (.var 0) (.var 1)) (.neg (.var 2))) := by
  intro w
  simp [evalExpr]; omega

/-- Non-vacuity: evalConstraintToCircuit is non-vacuously satisfiable. -/
example : let enc : Int → Nat := fun n => n.toNat
    let w : Witness Int := fun i => (i : Int)
    let env : CircuitEnv Int := ⟨fun n => (n : Int), fun n => (n : Int), fun _ => 0⟩
    CircuitExpr.eval
      (constraintToCircuit enc (.add (.var 0) (.const 5) : ConstraintExpr Int)) env =
    evalExpr (.add (.var 0) (.const 5) : ConstraintExpr Int) w := by
  simp [constraintToCircuit, CircuitExpr.eval, evalExpr]

/-- Non-vacuity: optimized_constraint_sound produces a real iff, not trivially true. -/
example : let e1 : ConstraintExpr Int := .sub (.var 0) (.const 42)
    let e2 : ConstraintExpr Int := .add (.var 0) (.neg (.const 42))
    let w : Witness Int := fun | 0 => 42 | _ => 0
    (evalExpr e1 w = 0 ↔ evalExpr e2 w = 0) := by
  simp [evalExpr]

end AmoLean.Plonky3.ConstraintEGraph
