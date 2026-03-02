/-
  AmoLean.EGraph.VerifiedExtraction.CircuitAdaptor — NodeOps + NodeSemantics for CircuitNodeOp

  Provides the bridge between AMO-Lean's CircuitNodeOp and the generic
  VerifiedExtraction framework. Defines:
  - NodeOps CircuitNodeOp instance (children, mapChildren, replaceChildren, localCost + 4 laws)
  - NodeSemantics CircuitNodeOp (CircuitEnv Val) Val instance (evalOp + evalOp_ext)

  Follows ArithOp adaptor pattern from VerifiedExtraction/Integration.lean.

  Design: CircuitExpr mirrors CircuitNodeOp's 7 constructors. Adding a new
  gate type requires updating: CircuitNodeOp, circuitChildren, circuitMapChildren,
  circuitReplaceChildren, CircuitExpr, circuitReconstruct, CircuitExpr.eval,
  and the 7-case proofs. This duplication is inherent to the adaptor pattern
  and ensures each proof case is explicit and auditable.
-/
import AmoLean.EGraph.VerifiedExtraction.Core
import AmoLean.EGraph.VerifiedExtraction.Greedy
import AmoLean.EGraph.Verified.Core
import AmoLean.EGraph.Verified.SemanticSpec

namespace AmoLean.EGraph.VerifiedExtraction.CircuitAdaptor

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.VerifiedExtraction.Greedy (Extractable EvalExpr ExtractableSound)
open AmoLean.EGraph.Verified (CircuitNodeOp CircuitEnv)

/-! ## Helper functions for NodeOps -/

@[simp] private def circuitChildren : CircuitNodeOp → List EClassId
  | .constGate _   => []
  | .witness _     => []
  | .pubInput _    => []
  | .addGate a b   => [a, b]
  | .mulGate a b   => [a, b]
  | .negGate a     => [a]
  | .smulGate _ a  => [a]

@[simp] private def circuitMapChildren (f : EClassId → EClassId) : CircuitNodeOp → CircuitNodeOp
  | .constGate c   => .constGate c
  | .witness i     => .witness i
  | .pubInput i    => .pubInput i
  | .addGate a b   => .addGate (f a) (f b)
  | .mulGate a b   => .mulGate (f a) (f b)
  | .negGate a     => .negGate (f a)
  | .smulGate c a  => .smulGate c (f a)

@[simp] private def circuitReplaceChildren (op : CircuitNodeOp) (ids : List EClassId) :
    CircuitNodeOp :=
  match op, ids with
  | .addGate _ _, a :: b :: _ => .addGate a b
  | .mulGate _ _, a :: b :: _ => .mulGate a b
  | .negGate _, a :: _       => .negGate a
  | .smulGate c _, a :: _    => .smulGate c a
  | op, _                    => op

/-- Cost model: only mulGate has cost 1; all other ops are free.
    Matches AMO-Lean's existing ENode.localCost in Verified/Core.lean. -/
private def circuitLocalCost : CircuitNodeOp → Nat
  | .mulGate _ _ => 1
  | _            => 0

/-! ## List length helpers -/

private theorem list_length_two {l : List α} (h : l.length = 2) :
    ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

private theorem list_length_one {l : List α} (h : l.length = 1) :
    ∃ x, l = [x] := by
  match l, h with
  | [x], _ => exact ⟨x, rfl⟩

/-! ## NodeOps Instance -/

instance : NodeOps CircuitNodeOp where
  children := circuitChildren
  mapChildren := circuitMapChildren
  replaceChildren := circuitReplaceChildren
  localCost := circuitLocalCost
  mapChildren_children f op := by cases op <;> simp
  mapChildren_id op := by cases op <;> simp
  replaceChildren_children op ids hlen := by
    cases op with
    | constGate _ => simp at hlen; subst hlen; rfl
    | witness _ => simp at hlen; subst hlen; rfl
    | pubInput _ => simp at hlen; subst hlen; rfl
    | addGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | mulGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | negGate a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | smulGate c a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
  replaceChildren_sameShape op ids hlen := by
    cases op with
    | constGate _ => simp at hlen; subst hlen; rfl
    | witness _ => simp at hlen; subst hlen; rfl
    | pubInput _ => simp at hlen; subst hlen; rfl
    | addGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | mulGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | negGate a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | smulGate c a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl

/-! ## NodeSemantics Instance -/

@[simp] private def circuitEvalOp {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (op : CircuitNodeOp) (env : CircuitEnv Val) (v : EClassId → Val) : Val :=
  match op with
  | .constGate n  => env.constVal n
  | .witness n    => env.witnessVal n
  | .pubInput n   => env.pubInputVal n
  | .addGate a b  => v a + v b
  | .mulGate a b  => v a * v b
  | .negGate a    => -(v a)
  | .smulGate n a => env.constVal n * v a

instance {Val : Type} [Add Val] [Mul Val] [Neg Val] :
    NodeSemantics CircuitNodeOp (CircuitEnv Val) Val where
  evalOp := circuitEvalOp
  evalOp_ext op env v v' h := by
    cases op with
    | constGate _ => rfl
    | witness _ => rfl
    | pubInput _ => rfl
    | addGate a b =>
      simp only [circuitEvalOp]
      congr 1
      · exact h a (by simp [NodeOps.children, circuitChildren])
      · exact h b (by simp [NodeOps.children, circuitChildren])
    | mulGate a b =>
      simp only [circuitEvalOp]
      congr 1
      · exact h a (by simp [NodeOps.children, circuitChildren])
      · exact h b (by simp [NodeOps.children, circuitChildren])
    | negGate a =>
      simp only [circuitEvalOp]
      congr 1
      exact h a (by simp [NodeOps.children, circuitChildren])
    | smulGate n a =>
      simp only [circuitEvalOp]
      congr 1
      exact h a (by simp [NodeOps.children, circuitChildren])

/-! ## CircuitExpr: Expression Type for Circuit Extraction -/

/-- Extracted circuit expression tree.
    Each constructor mirrors a CircuitNodeOp variant. -/
inductive CircuitExpr where
  | constE  (n : Nat)
  | witnessE (n : Nat)
  | pubInputE (n : Nat)
  | addE (a b : CircuitExpr)
  | mulE (a b : CircuitExpr)
  | negE (a : CircuitExpr)
  | smulE (n : Nat) (a : CircuitExpr)

/-! ## Extractable Instance -/

@[simp] private def circuitReconstruct (op : CircuitNodeOp) (children : List CircuitExpr) :
    Option CircuitExpr :=
  match op, children with
  | .constGate n, []      => some (.constE n)
  | .witness n, []        => some (.witnessE n)
  | .pubInput n, []       => some (.pubInputE n)
  | .addGate _ _, [a, b]  => some (.addE a b)
  | .mulGate _ _, [a, b]  => some (.mulE a b)
  | .negGate _, [a]       => some (.negE a)
  | .smulGate n _, [a]    => some (.smulE n a)
  | _, _                  => none

instance : Extractable CircuitNodeOp CircuitExpr where
  reconstruct := circuitReconstruct

/-! ## EvalExpr Instance -/

/-- Evaluate a CircuitExpr under a CircuitEnv. -/
@[simp] def CircuitExpr.eval {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (e : CircuitExpr) (env : CircuitEnv Val) : Val :=
  match e with
  | .constE n     => env.constVal n
  | .witnessE n   => env.witnessVal n
  | .pubInputE n  => env.pubInputVal n
  | .addE a b     => a.eval env + b.eval env
  | .mulE a b     => a.eval env * b.eval env
  | .negE a       => -(a.eval env)
  | .smulE n a    => env.constVal n * a.eval env

instance {Val : Type} [Add Val] [Mul Val] [Neg Val] :
    EvalExpr CircuitExpr (CircuitEnv Val) Val where
  evalExpr e env := e.eval env

/-! ## ExtractableSound Proof -/

/-- CircuitNodeOp adaptor satisfies ExtractableSound. -/
theorem circuit_extractable_sound {Val : Type} [Add Val] [Mul Val] [Neg Val] :
    ExtractableSound CircuitNodeOp CircuitExpr (CircuitEnv Val) Val := by
  intro op childExprs expr env v hrec hlen hchildren
  cases op with
  | constGate n =>
    simp [NodeOps.children, circuitChildren] at hlen
    subst hlen
    simp [Extractable.reconstruct, circuitReconstruct] at hrec
    subst hrec
    rfl
  | witness n =>
    simp [NodeOps.children, circuitChildren] at hlen
    subst hlen
    simp [Extractable.reconstruct, circuitReconstruct] at hrec
    subst hrec
    rfl
  | pubInput n =>
    simp [NodeOps.children, circuitChildren] at hlen
    subst hlen
    simp [Extractable.reconstruct, circuitReconstruct] at hrec
    subst hrec
    rfl
  | addGate a b =>
    simp [NodeOps.children, circuitChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, circuitReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, CircuitExpr.eval, NodeSemantics.evalOp, circuitEvalOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, circuitChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, circuitChildren])
    rw [h0, h1]
  | mulGate a b =>
    simp [NodeOps.children, circuitChildren] at hlen
    obtain ⟨x, y, rfl⟩ := list_length_two hlen
    simp [Extractable.reconstruct, circuitReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, CircuitExpr.eval, NodeSemantics.evalOp, circuitEvalOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, circuitChildren])
    have h1 : y.eval env = v b :=
      hchildren 1 (by omega) (by simp [NodeOps.children, circuitChildren])
    rw [h0, h1]
  | negGate a =>
    simp [NodeOps.children, circuitChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, circuitReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, CircuitExpr.eval, NodeSemantics.evalOp, circuitEvalOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, circuitChildren])
    rw [h0]
  | smulGate n a =>
    simp [NodeOps.children, circuitChildren] at hlen
    obtain ⟨x, rfl⟩ := list_length_one hlen
    simp [Extractable.reconstruct, circuitReconstruct] at hrec
    subst hrec
    simp only [EvalExpr.evalExpr, CircuitExpr.eval, NodeSemantics.evalOp, circuitEvalOp]
    have h0 : x.eval env = v a :=
      hchildren 0 (by omega) (by simp [NodeOps.children, circuitChildren])
    rw [h0]

end AmoLean.EGraph.VerifiedExtraction.CircuitAdaptor
