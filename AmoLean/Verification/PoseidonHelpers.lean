/-
  AMO-Lean: Poseidon2 Verification Helpers
  B92 — Phase B sorry elimination support

  This module provides:
  1. Helper functions that factor out nested pattern matching from evalMatExpr
  2. A flat-pattern alternative evaluator (evalMatExpr')
  3. Bridge theorem: evalMatExpr = evalMatExpr'

  The core issue: evalMatExpr has nested pattern matching on ElemOp
  within the .elemwise and .partialElemwise cases. While this does NOT
  prevent proving the Phase B congruence lemmas (those are all rfl or
  simp with string lemmas), the flat-pattern version enables equation
  lemma generation for ALL constructors, which is useful for future
  Phase C/D proofs.

  References:
  - L-471: Equation compiler lesson (flat patterns vs nested)
  - Poseidon_Semantics.lean: evalMatExpr definition, Phase B proofs
-/

import AmoLean.Verification.Poseidon_Semantics

namespace AmoLean.Verification.Poseidon

open AmoLean.Matrix (MatExpr ElemOp)
open AmoLean.Protocols.Poseidon.Spec

/-! ## Part 1: ElemOp / MDS Helper Functions

    These extract the nested pattern matching from evalMatExpr into
    standalone functions with flat patterns. This enables equation
    lemma generation for downstream proofs.
-/

/-- Evaluate an element-wise operation on a state vector.
    Factors out the ElemOp match from evalMatExpr's .elemwise case. -/
def evalElemOp (prime : Nat) (op : ElemOp) (state : PoseidonState) : PoseidonState :=
  match op with
  | .pow α => state.map (sbox prime α)
  | .custom _ => state

/-- Evaluate a partial element-wise operation on a state vector.
    Factors out the ElemOp match from evalMatExpr's .partialElemwise case. -/
def evalPartialElemOp (prime : Nat) (idx : Nat) (op : ElemOp)
    (state : PoseidonState) : PoseidonState :=
  match op with
  | .pow α =>
    if idx < state.size then
      state.set! idx (sbox prime α state[idx]!)
    else
      state
  | .custom _ => state

/-- Evaluate MDS dispatch based on name string.
    Factors out the hasSubstring branch from evalMatExpr's .mdsApply case. -/
def evalMdsOp (prime : Nat) (mdsName : String) (state : PoseidonState) : PoseidonState :=
  if hasSubstring mdsName "INTERNAL" then
    mdsInternal3 prime state
  else
    mdsExternal prime state

/-! ## Part 2: Flat-Pattern evalMatExpr'

    An alternative evaluator with flat patterns that delegates nested
    matching to the helper functions above. This enables equation lemma
    generation for ALL constructors.
-/

/-- Alternative evaluator with flat patterns.
    Delegates ElemOp matching to evalElemOp/evalPartialElemOp
    and MDS dispatch to evalMdsOp. -/
def evalMatExpr' (ctx : EvalCtx) : MatExpr α m n → PoseidonState → PoseidonState
  | .identity _, state => state
  | .zero _ _, _ => zeroState ctx.stateSize
  | .elemwise op inner, state =>
    evalElemOp ctx.prime op (evalMatExpr' ctx inner state)
  | .partialElemwise idx op inner, state =>
    evalPartialElemOp ctx.prime idx op (evalMatExpr' ctx inner state)
  | .mdsApply mdsName _ inner, state =>
    evalMdsOp ctx.prime mdsName (evalMatExpr' ctx inner state)
  | .addRoundConst round _ inner, state =>
    addRoundConstants ctx.prime (ctx.getRoundConst round) (evalMatExpr' ctx inner state)
  | .compose left right, state =>
    evalMatExpr' ctx left (evalMatExpr' ctx right state)
  | .add a b, state =>
    let aResult := evalMatExpr' ctx a state
    let bResult := evalMatExpr' ctx b state
    aResult.zipWith (modAdd ctx.prime) bResult
  | _, state => state

/-! ## Part 3: Bridge Theorem

    Proves that evalMatExpr and evalMatExpr' agree on all inputs.
    This allows using evalMatExpr' equation lemmas to reason about evalMatExpr.
-/

/-- evalMatExpr and evalMatExpr' are extensionally equal. -/
theorem evalMatExpr_eq_evalMatExpr' (ctx : EvalCtx) (e : MatExpr α m n)
    (state : PoseidonState) :
    evalMatExpr ctx e state = evalMatExpr' ctx e state := by
  induction e generalizing state with
  | identity => rfl
  | zero => rfl
  | elemwise op inner ih =>
    simp only [evalMatExpr, evalMatExpr', evalElemOp]
    cases op with
    | pow α => simp [ih]
    | custom s => simp [ih]
  | partialElemwise idx op inner ih =>
    simp only [evalMatExpr, evalMatExpr', evalPartialElemOp]
    cases op with
    | pow α => simp [ih]
    | custom s => simp [ih]
  | mdsApply mdsName stateSize inner ih =>
    simp only [evalMatExpr, evalMatExpr', evalMdsOp, ih]
  | addRoundConst round stateSize inner ih =>
    simp only [evalMatExpr, evalMatExpr', ih]
  | compose left right ihl ihr =>
    simp only [evalMatExpr, evalMatExpr']
    rw [ihr, ihl]
  | add a b iha ihb =>
    simp only [evalMatExpr, evalMatExpr']
    rw [iha, ihb]
  | _ => rfl

end AmoLean.Verification.Poseidon
