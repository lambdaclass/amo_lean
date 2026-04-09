/-
  AmoLean.EGraph.Verified.Bitwise.MixedEMatch — Generic E-Matching for MixedNodeOp

  Adapted from OptiSat LambdaSat/EMatch.lean + LambdaSat/SaturationSpec.lean (lines 1-370).
  Provides:
  - Pattern Op: generic pattern type with patVar and node constructors
  - Substitution: HashMap-based variable bindings
  - sameShape: skeleton comparison via mapChildren
  - ematchF: fuel-based e-matching (total)
  - instantiateF: fuel-based pattern instantiation (total)
  - RewriteRule Op: rewrite rule with optional side condition

  All definitions are generic over Op with [NodeOps Op] [BEq Op] [Hashable Op].
  Uses top-level namespace to avoid clash with AmoLean.EGraph.Verified.EGraph (concrete).
-/
import AmoLean.EGraph.Verified.Bitwise.MixedNodeOp

-- Top-level namespace avoids clash between AmoLean.EGraph.Verified.EGraph (concrete)
-- and AmoLean.EGraph.VerifiedExtraction.EGraph (generic). Same pattern as MixedPipeline.
namespace MixedEMatch

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)

/-- Hashable instance for MixedNodeOp (needed by EGraph's HashMap-based structure).
    Defined here so MixedEMatch can be imported without depending on MixedPipeline. -/
instance : Hashable MixedNodeOp where
  hash op := match op with
    | .constGate n    => mixHash 0 (hash n)
    | .witness n      => mixHash 1 (hash n)
    | .pubInput n     => mixHash 2 (hash n)
    | .addGate a b    => mixHash 3 (mixHash (hash a) (hash b))
    | .mulGate a b    => mixHash 4 (mixHash (hash a) (hash b))
    | .negGate a      => mixHash 5 (hash a)
    | .smulGate n a   => mixHash 6 (mixHash (hash n) (hash a))
    | .shiftLeft a n  => mixHash 7 (mixHash (hash a) (hash n))
    | .shiftRight a n => mixHash 8 (mixHash (hash a) (hash n))
    | .bitAnd a b     => mixHash 9 (mixHash (hash a) (hash b))
    | .bitXor a b     => mixHash 10 (mixHash (hash a) (hash b))
    | .bitOr a b      => mixHash 11 (mixHash (hash a) (hash b))
    | .constMask n    => mixHash 12 (hash n)
    | .subGate a b    => mixHash 13 (mixHash (hash a) (hash b))
    | .reduceGate a p   => mixHash 14 (mixHash (hash a) (hash p))
    | .kronPack a b w   => mixHash 15 (mixHash (mixHash (hash a) (hash b)) (hash w))
    | .kronUnpackLo a w => mixHash 16 (mixHash (hash a) (hash w))
    | .kronUnpackHi a w => mixHash 17 (mixHash (hash a) (hash w))
    | .montyReduce a p mu => mixHash 21 (mixHash (mixHash (hash a) (hash p)) (hash mu))
    | .barrettReduce a p m => mixHash 22 (mixHash (mixHash (hash a) (hash p)) (hash m))
    | .harveyReduce a p => mixHash 23 (mixHash (hash a) (hash p))

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Pattern and Substitution
-- ══════════════════════════════════════════════════════════════════

abbrev PatVarId := Nat

/-- Generic pattern for e-matching, parameterized by operation type.
    - `patVar pv`: matches any e-class, binds to variable `pv`
    - `node skelOp subpats`: matches e-nodes whose op has the same skeleton as `skelOp`,
      recursively matching children against `subpats` -/
inductive Pattern (Op : Type) where
  | patVar : PatVarId → Pattern Op
  | node : Op → List (Pattern Op) → Pattern Op
  deriving Inhabited

abbrev Substitution := Std.HashMap PatVarId EClassId

namespace Substitution

def empty : Substitution := Std.HashMap.ofList []

def extend (subst : Substitution) (pv : PatVarId) (id : EClassId) : Option Substitution :=
  match subst.get? pv with
  | none => some (subst.insert pv id)
  | some existingId => if existingId == id then some subst else none

def lookup (subst : Substitution) (pv : PatVarId) : Option EClassId :=
  subst.get? pv

end Substitution

abbrev MatchResult := List Substitution

-- ══════════════════════════════════════════════════════════════════
-- Section 2: sameShape — skeleton comparison
-- ══════════════════════════════════════════════════════════════════

/-- Check if two ops have the same skeleton (ignoring children IDs).
    Maps all children to 0 and compares via BEq. -/
def sameShape {Op : Type} [NodeOps Op] [BEq Op] (p o : Op) : Bool :=
  NodeOps.mapChildren (fun _ => 0) p == NodeOps.mapChildren (fun _ => 0) o

-- ══════════════════════════════════════════════════════════════════
-- Section 3: ematchF — Fuel-based e-matching (total)
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

/-- Total e-matching with fuel. Uses `root` (non-compressing) to avoid
    threading e-graph state. Returns all substitutions making the pattern
    match nodes in the given class.

    Adapted from OptiSat SaturationSpec.lean:290-317. -/
def ematchF (fuel : Nat) (g : EGraph Op) (pattern : Pattern Op)
    (classId : EClassId) (subst : Substitution := .empty) : MatchResult :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let canonId := UnionFind.root g.unionFind classId
    match pattern with
    | .patVar pv =>
      match subst.extend pv canonId with
      | some s => [s]
      | none => []
    | .node skelOp subpats =>
      match g.classes.get? canonId with
      | none => []
      | some eclass =>
        let rec matchChildren (pats : List (Pattern Op))
            (nodeChildren : List EClassId) (subst : Substitution)
            (acc : MatchResult) : MatchResult :=
          match pats, nodeChildren with
          | [], [] => acc ++ [subst]
          | p :: ps, c :: cs =>
            let results := ematchF fuel g p c subst
            results.foldl (fun a s => matchChildren ps cs s a) acc
          | _, _ => acc
        eclass.nodes.foldl (init := []) fun acc node =>
          if sameShape skelOp node.op then
            matchChildren subpats (NodeOps.children node.op) subst acc
          else acc

-- Equation lemma
@[simp] theorem ematchF_zero (g : EGraph Op) (pat : Pattern Op)
    (cid : EClassId) (subst : Substitution) :
    ematchF 0 g pat cid subst = [] := by
  cases pat <;> rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 4: instantiateF — Fuel-based pattern instantiation (total)
-- ══════════════════════════════════════════════════════════════════

/-- Total pattern instantiation with fuel. Given a pattern and substitution,
    add the corresponding nodes to the e-graph.

    Adapted from OptiSat SaturationSpec.lean:42-65. -/
def instantiateF (fuel : Nat) (g : EGraph Op) (pattern : Pattern Op)
    (subst : Substitution) : Option (EClassId × EGraph Op) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match pattern with
    | .patVar pv =>
      match subst.lookup pv with
      | some id => some (id, g)
      | none => none
    | .node skelOp subpats =>
      let rec go (g : EGraph Op) (pats : List (Pattern Op))
          (ids : List EClassId) : Option (List EClassId × EGraph Op) :=
        match pats with
        | [] => some (ids.reverse, g)
        | p :: ps =>
          match instantiateF fuel g p subst with
          | none => none
          | some (id, g') => go g' ps (id :: ids)
      match go g subpats [] with
      | none => none
      | some (childIds, g') =>
        some (g'.add ⟨NodeOps.replaceChildren skelOp childIds⟩)

-- Equation lemmas
@[simp] theorem instantiateF_zero (g : EGraph Op) (pat : Pattern Op)
    (subst : Substitution) : instantiateF 0 g pat subst = none := by
  cases pat <;> rfl

@[simp] theorem instantiateF_succ_patVar (n : Nat) (g : EGraph Op) (pv : PatVarId)
    (subst : Substitution) :
    instantiateF (n + 1) g (.patVar pv) subst =
    (match subst.lookup pv with | some id => some (id, g) | none => none) := rfl

@[simp] theorem instantiateF_succ_node (n : Nat) (g : EGraph Op) (skelOp : Op)
    (subpats : List (Pattern Op)) (subst : Substitution) :
    instantiateF (n + 1) g (.node skelOp subpats) subst =
    (match instantiateF.go subst n g subpats [] with
      | none => none
      | some (childIds, g') => some (g'.add ⟨NodeOps.replaceChildren skelOp childIds⟩)) := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 5: RewriteRule — Rewrite rule with optional side condition
-- ══════════════════════════════════════════════════════════════════

/-- A rewrite rule for equality saturation.
    Optionally includes a side condition that must pass before the rule fires. -/
structure RewriteRule (Op : Type) [BEq Op] [Hashable Op] where
  name : String
  lhs : Pattern Op
  rhs : Pattern Op
  sideCondCheck : Option (EGraph Op → Substitution → Bool) := none

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests — non-vacuity
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- Smoke test: Pattern for `bitAnd(x, x)` (and_self).
    Uses distinct child IDs (0, 1) so Pattern.eval works correctly. -/
private def patAndSelf : Pattern MixedNodeOp :=
  .node (.bitAnd 0 1) [.patVar 0, .patVar 0]

/-- Smoke test: Pattern for `x` (result of and_self). -/
private def patX : Pattern MixedNodeOp :=
  .patVar 0

/-- Smoke test: a simple RewriteRule. -/
private def ruleAndSelf : RewriteRule MixedNodeOp where
  name := "and_self"
  lhs := patAndSelf
  rhs := patX

/-- Smoke test: rule has the expected name. -/
example : ruleAndSelf.name = "and_self" := rfl

/-- Smoke test: Substitution.extend on empty returns the binding. -/
example : (Substitution.extend (Substitution.empty) 0 42).isSome = true := by native_decide

/-- Smoke test: Substitution.extend with conflict returns none. -/
example : (Substitution.extend (Substitution.empty.insert 0 42) 0 99).isNone = true := by
  native_decide

/-- Smoke test: sameShape for identical skeletons. -/
example : sameShape (MixedNodeOp.bitAnd 0 1) (MixedNodeOp.bitAnd 5 7) = true := by native_decide

/-- Smoke test: sameShape for different op kinds. -/
example : sameShape (MixedNodeOp.bitAnd 0 1) (MixedNodeOp.bitOr 0 1) = false := by native_decide

/-- Smoke test: instantiateF with patVar and unbound var returns none. -/
example : (instantiateF 10 (EGraph.empty : EGraph MixedNodeOp) (.patVar 0) .empty).isNone = true := by
  simp [instantiateF, Substitution.lookup, Substitution.empty]

end SmokeTests

end MixedEMatch
