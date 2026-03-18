/-
  AmoLean.EGraph.Verified.Bitwise.MixedPipeline — Pipeline soundness + TV for MixedNodeOp

  Composes the bitwise verification infrastructure (B73) into:
  1. mixed_extractF_correct: instantiation of generic extractF_correct for MixedNodeOp
  2. bitwise_verified_equivalent: E-graph equivalence implies semantic equivalence
  3. Field fold verification: concrete fold theorems for Mersenne31, BabyBear, Goldilocks
  4. Translation validation: mixedEquivalent predicate with equivalence relation properties

  Dependencies:
  - MixedExtract.lean: MixedExpr, Extractable, EvalExpr, mixed_extractable_sound
  - FieldFoldRules.lean: mersenne_fold_correct, pseudo_mersenne_fold_correct, convenience theorems
  - Greedy.lean: extractF_correct, extractAuto_correct (generic)
  - VerifiedExtraction/Core.lean: ConsistentValuation, BestNodeInv, EGraph, UnionFind.WellFormed

  Note: We use the VerifiedExtraction namespace types (EGraph, ConsistentValuation, etc.)
  which are generic over NodeSemantics, not the Verified.SemanticSpec versions.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedExtract
import AmoLean.EGraph.Verified.Bitwise.FieldFoldRules
import AmoLean.EGraph.VerifiedExtraction.Greedy

set_option autoImplicit false

-- Use a top-level namespace to avoid priority clashes between
-- AmoLean.EGraph.Verified.* and AmoLean.EGraph.VerifiedExtraction.*
namespace MixedPipeline

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.VerifiedExtraction.Greedy
  (Extractable EvalExpr ExtractableSound extractF extractAuto extractF_correct extractAuto_correct)
open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr mixed_extractable_sound)

/-- Hashable instance for MixedNodeOp, needed by EGraph's HashMap-based structure. -/
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

/-- Alias for the generic EGraph type specialized to MixedNodeOp. -/
abbrev MixedEGraph := EGraph MixedNodeOp

/-! ## Part 1: Instantiation of generic extraction for MixedNodeOp -/

/-- Extraction correctness for MixedNodeOp: if we extract an expression from a
    well-formed E-graph with consistent valuation, the extracted MixedExpr evaluates
    to the correct value.

    This is a direct instantiation of the generic `extractF_correct` from Greedy.lean,
    with Op := MixedNodeOp, Expr := MixedExpr, Env := MixedEnv, Val := Nat. -/
theorem mixed_extractF_correct
    (g : MixedEGraph) (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (fuel : Nat) (classId : EClassId) (expr : MixedExpr)
    (hext : extractF g classId fuel = some expr) :
    expr.eval env = v (UnionFind.root g.unionFind classId) :=
  extractF_correct g env v hcv hwf hbni mixed_extractable_sound fuel classId expr hext

/-- Corollary: extractAuto (fuel = numClasses + 1) is also correct for MixedNodeOp. -/
theorem mixed_extractAuto_correct
    (g : MixedEGraph) (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (rootId : EClassId) (expr : MixedExpr)
    (hext : extractAuto g rootId = some expr) :
    expr.eval env = v (UnionFind.root g.unionFind rootId) :=
  extractAuto_correct g env v hcv hwf hbni mixed_extractable_sound rootId expr hext

/-! ## Part 2: E-graph equivalence implies semantic equivalence -/

/-- **Bitwise verified equivalent**: if two e-class IDs share the same root in the
    union-find (i.e., the E-graph has proved them equivalent via rewriting),
    then they evaluate to the same Nat value under any consistent valuation.

    This is the compositional result: bitwise rules + algebraic rules + saturation
    produce correct equivalences. -/
theorem bitwise_verified_equivalent
    (g : MixedEGraph) (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (implClass specClass : EClassId)
    (hequiv : UnionFind.root g.unionFind implClass =
              UnionFind.root g.unionFind specClass) :
    v implClass = v specClass :=
  hcv.equiv_same_val implClass specClass hequiv

/-- Extraction + equivalence: if two classes are equivalent and we can extract from both,
    the extracted expressions evaluate to the same value. -/
theorem extract_equivalent_eval
    (g : MixedEGraph) (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (implClass specClass : EClassId)
    (hequiv : UnionFind.root g.unionFind implClass =
              UnionFind.root g.unionFind specClass)
    (fuel : Nat) (implExpr specExpr : MixedExpr)
    (hextImpl : extractF g implClass fuel = some implExpr)
    (hextSpec : extractF g specClass fuel = some specExpr) :
    implExpr.eval env = specExpr.eval env := by
  have h1 := mixed_extractF_correct g env v hcv hwf hbni fuel implClass implExpr hextImpl
  have h2 := mixed_extractF_correct g env v hcv hwf hbni fuel specClass specExpr hextSpec
  rw [h1, h2, hequiv]

/-! ## Part 3: Field fold verification — concrete theorems -/

/-- **Mersenne31 fold verification**: the bitwise fold `(x >>> 31) + (x &&& (2^31 - 1))`
    computes the same residue modulo `2^31 - 1` as the identity.

    This is the core optimization identity for Plonky3's Mersenne31 field. -/
theorem fold_verified_mod_mersenne31 (x : Nat) :
    let fold := (x >>> 31) + (x &&& (2 ^ 31 - 1))
    fold % (2 ^ 31 - 1) = x % (2 ^ 31 - 1) :=
  mersenne_fold_correct x 31 (by omega)

/-- **BabyBear fold verification**: the bitwise fold
    `(x >>> 31) * (2^27 - 1) + (x &&& (2^31 - 1))`
    computes the same residue modulo `2^31 - 2^27 + 1` as the identity.

    This is the pseudo-Mersenne folding identity for Plonky3's BabyBear field. -/
theorem fold_verified_mod_babybear (x : Nat) :
    let fold := (x >>> 31) * (2 ^ 27 - 1) + (x &&& (2 ^ 31 - 1))
    fold % (2 ^ 31 - 2 ^ 27 + 1) = x % (2 ^ 31 - 2 ^ 27 + 1) := by
  show ((x >>> 31) * (2 ^ 27 - 1) + (x &&& (2 ^ 31 - 1))) % (2 ^ 31 - 2 ^ 27 + 1) =
    x % (2 ^ 31 - 2 ^ 27 + 1)
  have : (2 : Nat) ^ 31 - 2 ^ 27 + 1 = 2 ^ 31 - (2 ^ 27 - 1) := by omega
  rw [this]
  exact pseudo_mersenne_fold_correct x 31 (2 ^ 27 - 1) (by decide) (by decide)

/-- **Goldilocks fold verification**: the bitwise fold
    `(x >>> 64) * (2^32 - 1) + (x &&& (2^64 - 1))`
    computes the same residue modulo `2^64 - 2^32 + 1` as the identity.

    This is the pseudo-Mersenne folding identity for Plonky3's Goldilocks field. -/
theorem fold_verified_mod_goldilocks (x : Nat) :
    let fold := (x >>> 64) * (2 ^ 32 - 1) + (x &&& (2 ^ 64 - 1))
    fold % (2 ^ 64 - 2 ^ 32 + 1) = x % (2 ^ 64 - 2 ^ 32 + 1) := by
  show ((x >>> 64) * (2 ^ 32 - 1) + (x &&& (2 ^ 64 - 1))) % (2 ^ 64 - 2 ^ 32 + 1) =
    x % (2 ^ 64 - 2 ^ 32 + 1)
  have : (2 : Nat) ^ 64 - 2 ^ 32 + 1 = 2 ^ 64 - (2 ^ 32 - 1) := by omega
  rw [this]
  exact pseudo_mersenne_fold_correct x 64 (2 ^ 32 - 1) (by decide) (by decide)

/-! ## Part 4: Translation validation — mixedEquivalent predicate -/

/-- Two MixedExpr trees are equivalent under an environment if they evaluate
    to the same Nat value. This is the translation validation predicate for
    bitwise + algebraic mixed expressions. -/
def mixedEquivalent (e1 e2 : MixedExpr) (env : MixedEnv) : Prop :=
  e1.eval env = e2.eval env

/-- mixedEquivalent is reflexive. -/
theorem mixedEquivalent_refl (e : MixedExpr) (env : MixedEnv) :
    mixedEquivalent e e env :=
  rfl

/-- mixedEquivalent is symmetric. -/
theorem mixedEquivalent_symm {e1 e2 : MixedExpr} {env : MixedEnv}
    (h : mixedEquivalent e1 e2 env) :
    mixedEquivalent e2 e1 env :=
  h.symm

/-- mixedEquivalent is transitive. -/
theorem mixedEquivalent_trans {e1 e2 e3 : MixedExpr} {env : MixedEnv}
    (h12 : mixedEquivalent e1 e2 env)
    (h23 : mixedEquivalent e2 e3 env) :
    mixedEquivalent e1 e3 env :=
  h12.trans h23

/-- If two extracted expressions come from the same e-class, they are mixedEquivalent. -/
theorem extract_same_class_equivalent
    (g : MixedEGraph) (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (classId : EClassId) (fuel1 fuel2 : Nat)
    (e1 e2 : MixedExpr)
    (hext1 : extractF g classId fuel1 = some e1)
    (hext2 : extractF g classId fuel2 = some e2) :
    mixedEquivalent e1 e2 env := by
  unfold mixedEquivalent
  have h1 := mixed_extractF_correct g env v hcv hwf hbni fuel1 classId e1 hext1
  have h2 := mixed_extractF_correct g env v hcv hwf hbni fuel2 classId e2 hext2
  rw [h1, h2]

/-- **Pipeline composition**: E-graph equivalence lifts to mixedEquivalent on extracted expressions.
    This is the end-to-end result: if the E-graph (via saturation with bitwise + algebraic rules)
    proves two classes equivalent, then any extracted expressions from those classes are
    semantically equivalent. -/
theorem pipeline_mixed_equivalent
    (g : MixedEGraph) (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (implClass specClass : EClassId)
    (hequiv : UnionFind.root g.unionFind implClass =
              UnionFind.root g.unionFind specClass)
    (fuel : Nat) (implExpr specExpr : MixedExpr)
    (hextImpl : extractF g implClass fuel = some implExpr)
    (hextSpec : extractF g specClass fuel = some specExpr) :
    mixedEquivalent implExpr specExpr env := by
  unfold mixedEquivalent
  exact extract_equivalent_eval g env v hcv hwf hbni implClass specClass
    hequiv fuel implExpr specExpr hextImpl hextSpec

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity: fold_verified_mod_mersenne31 is not vacuously true.
    x = 2^32 + 7 exercises the fold (high bits are nonzero). -/
example : let fold := ((2 ^ 32 + 7) >>> 31) + ((2 ^ 32 + 7) &&& (2 ^ 31 - 1))
    fold % (2 ^ 31 - 1) = (2 ^ 32 + 7) % (2 ^ 31 - 1) :=
  fold_verified_mod_mersenne31 (2 ^ 32 + 7)

/-- Non-vacuity: fold_verified_mod_babybear with a concrete value. -/
example : let fold := ((2 ^ 32 + 7) >>> 31) * (2 ^ 27 - 1) + ((2 ^ 32 + 7) &&& (2 ^ 31 - 1))
    fold % (2 ^ 31 - 2 ^ 27 + 1) = (2 ^ 32 + 7) % (2 ^ 31 - 2 ^ 27 + 1) :=
  fold_verified_mod_babybear (2 ^ 32 + 7)

/-- Non-vacuity: mixedEquivalent is symmetric for a concrete case. -/
example : mixedEquivalent (.constE 0) (.constE 0)
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 } :=
  mixedEquivalent_refl (.constE 0) _

end MixedPipeline
