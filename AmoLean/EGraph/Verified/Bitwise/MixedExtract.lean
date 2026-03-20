/-
  AmoLean.EGraph.Verified.Bitwise.MixedExtract — Extractable adaptor for MixedNodeOp

  Provides:
  - MixedExpr: expression tree mirroring MixedNodeOp's 13 constructors
  - Extractable MixedNodeOp MixedExpr instance
  - EvalExpr MixedExpr MixedEnv Nat instance
  - mixed_extractable_sound : ExtractableSound MixedNodeOp MixedExpr MixedEnv Nat

  Follows CircuitAdaptor.lean pattern line-by-line.
  Design: 13 constructors (7 algebraic + 6 bitwise). Each proof case is explicit.
-/
import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge
import AmoLean.EGraph.VerifiedExtraction.Greedy

namespace AmoLean.EGraph.Verified.Bitwise.MixedExtract

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.VerifiedExtraction.Greedy (Extractable EvalExpr ExtractableSound)
open AmoLean.EGraph.Verified (CircuitEnv EClassId)
open AmoLean.EGraph.Verified.Bitwise

/-! ## Helper lemmas for list destructuring -/

private theorem list_length_two {α : Type} {l : List α} (h : l.length = 2) :
    ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

private theorem list_length_one {α : Type} {l : List α} (h : l.length = 1) :
    ∃ x, l = [x] := by
  match l, h with
  | [x], _ => exact ⟨x, rfl⟩

/-! ## MixedExpr: Expression Type for Mixed Extraction -/

/-- Extracted expression tree for mixed (algebraic + bitwise) operations.
    Each constructor mirrors a MixedNodeOp variant. -/
inductive MixedExpr where
  | constE      (n : Nat)
  | witnessE    (n : Nat)
  | pubInputE   (n : Nat)
  | addE        (a b : MixedExpr)
  | mulE        (a b : MixedExpr)
  | negE        (a : MixedExpr)
  | smulE       (n : Nat) (a : MixedExpr)
  | shiftLeftE  (a : MixedExpr) (n : Nat)
  | shiftRightE (a : MixedExpr) (n : Nat)
  | bitAndE     (a b : MixedExpr)
  | bitXorE     (a b : MixedExpr)
  | bitOrE      (a b : MixedExpr)
  | constMaskE  (n : Nat)
  | subE        (a b : MixedExpr)
  | reduceE     (a : MixedExpr) (p : Nat)
  | kronPackE   (a b : MixedExpr) (w : Nat)
  | kronUnpackLoE (a : MixedExpr) (w : Nat)
  | kronUnpackHiE (a : MixedExpr) (w : Nat)
  | montyReduceE  (a : MixedExpr) (p : Nat) (mu : Nat)
  | barrettReduceE (a : MixedExpr) (p : Nat) (m : Nat)
  | harveyReduceE (a : MixedExpr) (p : Nat)

/-! ## Extractable Instance -/

/-- Reconstruct a MixedExpr from a MixedNodeOp and its children's extracted expressions. -/
@[simp] private def mixedReconstruct (op : MixedNodeOp) (children : List MixedExpr) :
    Option MixedExpr :=
  match op, children with
  | .constGate n, []       => some (.constE n)
  | .witness n, []         => some (.witnessE n)
  | .pubInput n, []        => some (.pubInputE n)
  | .addGate _ _, [a, b]   => some (.addE a b)
  | .mulGate _ _, [a, b]   => some (.mulE a b)
  | .negGate _, [a]        => some (.negE a)
  | .smulGate n _, [a]     => some (.smulE n a)
  | .shiftLeft _ n, [a]    => some (.shiftLeftE a n)
  | .shiftRight _ n, [a]   => some (.shiftRightE a n)
  | .bitAnd _ _, [a, b]    => some (.bitAndE a b)
  | .bitXor _ _, [a, b]    => some (.bitXorE a b)
  | .bitOr _ _, [a, b]     => some (.bitOrE a b)
  | .constMask n, []       => some (.constMaskE n)
  | .subGate _ _, [a, b]   => some (.subE a b)
  | .reduceGate _ p, [a]   => some (.reduceE a p)
  | .kronPack _ _ w, [a, b] => some (.kronPackE a b w)
  | .kronUnpackLo _ w, [a] => some (.kronUnpackLoE a w)
  | .kronUnpackHi _ w, [a] => some (.kronUnpackHiE a w)
  | .montyReduce _ p mu, [a] => some (.montyReduceE a p mu)
  | .barrettReduce _ p m, [a] => some (.barrettReduceE a p m)
  | .harveyReduce _ p, [a] => some (.harveyReduceE a p)
  | _, _                   => none

instance : Extractable MixedNodeOp MixedExpr where
  reconstruct := mixedReconstruct

/-! ## EvalExpr Instance -/

/-- Evaluate a MixedExpr tree in the Nat domain. -/
@[simp] def MixedExpr.eval (e : MixedExpr) (env : MixedEnv) : Nat :=
  match e with
  | .constE n       => env.constVal n
  | .witnessE n     => env.witnessVal n
  | .pubInputE n    => env.pubInputVal n
  | .addE a b       => a.eval env + b.eval env
  | .mulE a b       => a.eval env * b.eval env
  | .negE _         => 0
  | .smulE n a      => env.constVal n * a.eval env
  | .shiftLeftE a n => Nat.shiftLeft (a.eval env) n
  | .shiftRightE a n => Nat.shiftRight (a.eval env) n
  | .bitAndE a b    => Nat.land (a.eval env) (b.eval env)
  | .bitXorE a b    => Nat.xor (a.eval env) (b.eval env)
  | .bitOrE a b     => Nat.lor (a.eval env) (b.eval env)
  | .constMaskE n   => 2 ^ n - 1
  | .subE a b       => a.eval env - b.eval env
  | .reduceE a p    => a.eval env % p
  | .kronPackE a b w => a.eval env + b.eval env * 2 ^ w
  | .kronUnpackLoE a w => a.eval env % 2 ^ w
  | .kronUnpackHiE a w => a.eval env / 2 ^ w
  | .montyReduceE a p _mu => a.eval env % p
  | .barrettReduceE a p _m => a.eval env % p
  | .harveyReduceE a p => a.eval env % p

instance : EvalExpr MixedExpr MixedEnv Nat where
  evalExpr e env := e.eval env

/-! ## ExtractableSound Proof -/

/-- MixedNodeOp adaptor satisfies ExtractableSound. -/
theorem mixed_extractable_sound :
    ExtractableSound MixedNodeOp MixedExpr MixedEnv Nat := by
  intro op childExprs expr env v hrec hlen hchildren
  cases op with
  | constGate n =>
    simp [NodeOps.children, mixedChildren] at hlen
    subst hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    rfl
  | witness n =>
    simp [NodeOps.children, mixedChildren] at hlen
    subst hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    rfl
  | pubInput n =>
    simp [NodeOps.children, mixedChildren] at hlen
    subst hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    rfl
  | addGate a b =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0, h1]
  | mulGate a b =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0, h1]
  | negGate a =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    rfl
  | smulGate n a =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | shiftLeft a n =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | shiftRight a n =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | bitAnd a b =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0, h1]
  | bitXor a b =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0, h1]
  | bitOr a b =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0, h1]
  | constMask n =>
    simp [NodeOps.children, mixedChildren] at hlen
    subst hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    rfl
  | subGate a b =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0, h1]
  | reduceGate a p =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | kronPack a b w =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0, h1]
  | kronUnpackLo a w =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | kronUnpackHi a w =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | montyReduce a p mu =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | barrettReduce a p m =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]
  | harveyReduce a p =>
    simp [NodeOps.children, mixedChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, mixedReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, MixedExpr.eval, NodeSemantics.evalOp, evalMixedOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, mixedChildren])
    rw [h0]

end AmoLean.EGraph.Verified.Bitwise.MixedExtract
