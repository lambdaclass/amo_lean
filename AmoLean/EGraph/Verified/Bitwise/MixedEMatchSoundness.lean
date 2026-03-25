/-
  AmoLean.EGraph.Verified.Bitwise.MixedEMatchSoundness — Core verification for E-Matching

  B63: Connects the operational e-matching (MixedEMatch) to the semantic framework
  (MixedSemanticSpec) via:
  - SameShapeSemantics: ops with the same skeleton evaluate identically (13-case proof)
  - PatternSoundRule: rewrite rules with semantic soundness certificates
  - applyRuleAtF_preserves_cv: rule application preserves ConsistentValuation
  - applyRulesF_preserves_cv: list of rules preserves ConsistentValuation

  Key insight (L-381): since MixedNodeOp has 13 constructors and sameShape maps all
  children to 0 then compares, two ops with sameShape=true must have the same constructor
  (possibly different children). Then evalMixedOp only depends on children via the
  valuation, so the positional child value hypothesis suffices.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple
import AmoLean.EGraph.Verified.Bitwise.MixedEMatchSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AmoLean.EGraph.Verified.Bitwise.MixedEMatchSoundness

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)
open AmoLean.EGraph.VerifiedExtraction (EClassId NodeOps NodeSemantics)

-- Import abbreviations
abbrev MGraph := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.MGraph
abbrev MNode  := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.MNode
abbrev CId    := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.CId
abbrev VPMI   := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.VPMI
abbrev CV     := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.CV
abbrev PreservesCV := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.PreservesCV

open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec (ndCh ndMapCh ndChildren sameShape)

open MixedEMatch (Pattern PatVarId Substitution RewriteRule
  ematchF instantiateF)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: SameShapeSemantics — the 13-case proof
-- ══════════════════════════════════════════════════════════════════

/-- Two MixedNodeOps with the same shape evaluate identically when corresponding
    children have matching values. "Same shape" means mapChildren(0, op1) = mapChildren(0, op2),
    which forces the same constructor (possibly different child IDs).

    For leaf constructors (constGate, witness, pubInput, constMask), evalMixedOp
    does not depend on children at all.
    For node constructors (addGate, mulGate, negGate, smulGate, shiftLeft,
    shiftRight, bitAnd, bitXor, bitOr), evalMixedOp depends only on child values
    via the valuation function, and the child-matching hypothesis ensures agreement. -/
def SameShapeSemantics : Prop :=
  ∀ (op₁ op₂ : MixedNodeOp) (env : MixedEnv) (v₁ v₂ : CId → Nat),
    sameShape op₁ op₂ = true →
    (∀ i (h₁ : i < (ndCh op₁).length) (h₂ : i < (ndCh op₂).length),
      v₁ ((ndCh op₁)[i]) = v₂ ((ndCh op₂)[i])) →
    evalMixedOp op₁ env v₁ = evalMixedOp op₂ env v₂

/-- Helper: sameShape = true implies mapChildren(0, op1) = mapChildren(0, op2). -/
private theorem sameShape_eq (op₁ op₂ : MixedNodeOp) (h : sameShape op₁ op₂ = true) :
    ndMapCh (fun _ => (0 : CId)) op₁ = ndMapCh (fun _ => (0 : CId)) op₂ := by
  unfold sameShape at h; exact eq_of_beq h

/-- Main theorem: SameShapeSemantics holds for MixedNodeOp.
    Proof by cases on op1. For each constructor, sameShape = true forces op2
    to have the same constructor (via injectivity of mapChildren on the tag).
    Then evalMixedOp agreement follows from the child value hypothesis. -/
theorem sameShapeSemantics_holds : SameShapeSemantics := by
  intro op₁ op₂ env v₁ v₂ hss hchildren
  -- Get the structural equality from sameShape
  have heq := sameShape_eq op₁ op₂ hss
  -- Macro for the simp set used to unfold mapChildren
  -- Case split on op1; in each case, heq forces op2 to match
  cases op₁ with
  -- Leaf cases: no children, evalMixedOp is independent of valuation
  | constGate n₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp_all (config := { failIfUnchanged := false })
  | witness n₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp_all (config := { failIfUnchanged := false })
  | pubInput n₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp_all (config := { failIfUnchanged := false })
  | constMask n₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp_all (config := { failIfUnchanged := false })
  -- negGate: evaluates to 0 regardless of child
  | negGate a₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp_all (config := { failIfUnchanged := false })
  -- Binary ops: two children, evalMixedOp depends on both via valuation
  | addGate a₁ b₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ b₂
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    have h1 := hchildren 1 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | mulGate a₁ b₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ b₂
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    have h1 := hchildren 1 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | bitAnd a₁ b₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ b₂
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    have h1 := hchildren 1 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | bitXor a₁ b₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ b₂
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    have h1 := hchildren 1 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | bitOr a₁ b₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ b₂
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    have h1 := hchildren 1 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  -- Unary ops with Nat payload: sameShape forces same payload, one child
  | smulGate c₁ a₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i c₂ a₂
    subst heq
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero] at h0
    rw [h0]
  | shiftLeft a₁ n₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ n₂
    subst heq
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero] at h0
    rw [h0]
  | shiftRight a₁ n₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ n₂
    subst heq
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero] at h0
    rw [h0]
  -- subGate: binary op, two children (follows addGate pattern)
  | subGate a₁ b₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ b₂
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    have h1 := hchildren 1 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  -- reduceGate: unary op with Nat payload (follows smulGate pattern)
  | reduceGate a₁ p₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ p₂
    subst heq
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero] at h0
    rw [h0]
  -- kronPack: binary op with Nat payload (follows addGate pattern)
  | kronPack a₁ b₁ w₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ b₂ w₂
    obtain ⟨rfl⟩ := heq
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    have h1 := hchildren 1 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  -- kronUnpackLo: unary op with Nat payload (follows shiftRight pattern)
  | kronUnpackLo a₁ w₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ w₂
    subst heq
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero] at h0
    rw [h0]
  -- kronUnpackHi: unary op with Nat payload (follows shiftRight pattern)
  | kronUnpackHi a₁ w₁ =>
    simp only [ndMapCh, NodeOps.mapChildren, AmoLean.EGraph.Verified.Bitwise.mixedMapChildren] at heq
    cases op₂ <;> simp at heq
    rename_i a₂ w₂
    subst heq
    simp only [evalMixedOp]
    have h0 := hchildren 0 (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
      (by simp [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren])
    simp only [ndCh, NodeOps.children, AmoLean.EGraph.Verified.Bitwise.mixedChildren,
      List.getElem_cons_zero] at h0
    rw [h0]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: WellFormedPat + PatternSoundRule
-- ══════════════════════════════════════════════════════════════════

/-- Well-formed pattern: all skeleton ops have distinct children,
    and subpattern lists match the children count. -/
def WellFormedPat : MixedEMatch.Pattern MixedNodeOp → Prop
  | .patVar _ => True
  | .node skelOp subpats =>
    (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).Nodup ∧
    subpats.length = (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).length ∧
    ∀ p ∈ subpats, WellFormedPat p

/-- A pattern-based rewrite rule with a soundness proof.
    The rule is sound if for all environments and pattern variable assignments,
    evaluating the LHS and RHS patterns produces the same value.
    Uses Pattern.eval from MixedEMatchSpec. -/
structure PatternSoundRule where
  rule : RewriteRule MixedNodeOp
  soundness : ∀ (env : Nat → Nat) (σ : PatVarId → Nat),
    MixedEMatchSpec.Pattern.eval rule.lhs env σ =
    MixedEMatchSpec.Pattern.eval rule.rhs env σ
  wfp_lhs : WellFormedPat rule.lhs
  wfp_rhs : WellFormedPat rule.rhs

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Focused soundness properties (L-391 decomposition)
-- ══════════════════════════════════════════════════════════════════

/-- Substitute pattern variables with class values via UF roots.
    Maps patVar pv → v(root(σ(pv))) where σ : Substitution.
    cf. OptiSat EMatchSpec.lean substVal. -/
def substVal (v : CId → Nat) (uf : AmoLean.EGraph.VerifiedExtraction.UnionFind)
    (σ : MixedEMatch.Substitution) (pv : MixedEMatch.PatVarId) : Nat :=
  match σ.get? pv with
  | some id => v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root uf id)
  | none => 0

/-- substVal agrees when substitutions agree on a key. -/
private theorem substVal_get (v : CId → Nat) (uf : AmoLean.EGraph.VerifiedExtraction.UnionFind)
    (σ : MixedEMatch.Substitution) (pv : MixedEMatch.PatVarId) (id : CId)
    (h : σ.get? pv = some id) :
    substVal v uf σ pv = v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root uf id) := by
  unfold substVal; rw [h]

/-- extend always maps the target key to the target value on success. -/
private theorem extend_maps_key (subst : MixedEMatch.Substitution)
    (pv : MixedEMatch.PatVarId) (id : AmoLean.EGraph.VerifiedExtraction.EClassId)
    (s : MixedEMatch.Substitution)
    (hext : MixedEMatch.Substitution.extend subst pv id = some s) :
    s.get? pv = some id := by
  unfold MixedEMatch.Substitution.extend at hext
  split at hext
  · -- get? pv = none → insert
    obtain rfl := Option.some.inj hext
    simp [Std.HashMap.get?_eq_getElem?]
  · -- get? pv = some existingId
    rename_i existingId h_some
    split at hext
    · rename_i heq_id
      obtain rfl := Option.some.inj hext
      have : (existingId == id) = true := heq_id
      rw [beq_iff_eq] at this; subst this; exact h_some
    · simp at hext


/-- Lookup in a zipped list with nodup keys: keys[i] maps to vals[i]. -/
private theorem zip_lookup_nodup {α : Type} [BEq α] [LawfulBEq α]
    (keys : List α) (vals : List Nat)
    (hnodup : keys.Nodup) (hlen : keys.length = vals.length)
    (i : Nat) (hi : i < keys.length) :
    (keys.zip vals).lookup (keys[i]) = some (vals[i]'(hlen ▸ hi)) := by
  induction keys generalizing vals i with
  | nil => simp at hi
  | cons k ks ih =>
    match vals with
    | [] => simp at hlen
    | v :: vs =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      cases i with
      | zero => simp
      | succ j =>
        simp only [List.getElem_cons_succ]
        have hnodup_ks := (List.nodup_cons.mp hnodup).2
        have hnotmem := (List.nodup_cons.mp hnodup).1
        have hlen' : ks.length = vs.length := by simp at hlen; exact hlen
        have hj : j < ks.length := by simp at hi; exact hi
        have hne : ks[j] ≠ k := fun h =>
          hnotmem (h ▸ List.getElem_mem hj)
        have hbeq : (ks[j] == k) = false := by
          rw [beq_eq_false_iff_ne]; exact hne
        simp only [hbeq]
        exact ih vs hnodup_ks hlen' j hj

/-- matchChildren is monotone: elements of acc are preserved. -/
private theorem matchChildren_mono {Op : Type} [AmoLean.EGraph.VerifiedExtraction.NodeOps Op]
    [BEq Op] [Hashable Op]
    (g : AmoLean.EGraph.VerifiedExtraction.EGraph Op) (fuel : Nat)
    (pats : List (MixedEMatch.Pattern Op))
    (nodeChildren : List AmoLean.EGraph.VerifiedExtraction.EClassId)
    (subst : MixedEMatch.Substitution) (acc : MixedEMatch.MatchResult)
    (σ : MixedEMatch.Substitution) (hmem : σ ∈ acc) :
    σ ∈ MixedEMatch.ematchF.matchChildren g fuel pats nodeChildren subst acc := by
  induction pats generalizing nodeChildren subst acc with
  | nil =>
    cases nodeChildren with
    | nil => simp [MixedEMatch.ematchF.matchChildren]; exact Or.inl hmem
    | cons _ _ => simp [MixedEMatch.ematchF.matchChildren]; exact hmem
  | cons p ps ih_pats =>
    cases nodeChildren with
    | nil => simp [MixedEMatch.ematchF.matchChildren]; exact hmem
    | cons c cs =>
      simp [MixedEMatch.ematchF.matchChildren]
      suffices ∀ (acc' : MixedEMatch.MatchResult) (results : List MixedEMatch.Substitution),
          σ ∈ acc' →
          σ ∈ List.foldl (fun a s =>
            MixedEMatch.ematchF.matchChildren g fuel ps cs s a) acc' results by
        exact this acc _ hmem
      intro acc' results hacc
      induction results generalizing acc' with
      | nil => exact hacc
      | cons r rs ih_rs => exact ih_rs _ (ih_pats cs r acc' hacc)

/-- Generic foldl soundness: if σ ∈ foldl f [] nodes and f is monotone,
    then σ came from some node. Uses the "soundness predicate" approach:
    carry a predicate P through the foldl. -/
private theorem foldl_sound_predicate
    {β : Type} (f : List MixedEMatch.Substitution → β → List MixedEMatch.Substitution)
    (P : MixedEMatch.Substitution → Prop)
    (nodes : List β)
    (hsound : ∀ acc (b : β), b ∈ nodes → ∀ σ, σ ∈ f acc b → σ ∉ acc → P σ)
    (init : List MixedEMatch.Substitution) (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ List.foldl f init nodes) (hnotinit : σ ∉ init) :
    P σ := by
  -- Generic: σ ∈ foldl f init ns → σ ∈ init ∨ P σ
  suffices ∀ (ns : List β) (init : List MixedEMatch.Substitution),
      (∀ b, b ∈ ns → b ∈ nodes) →
      σ ∈ List.foldl f init ns → σ ∈ init ∨ P σ by
    exact (this nodes init (fun b hb => hb) hmem).resolve_left hnotinit
  intro ns init₀ hsub hmem₀
  induction ns generalizing init₀ with
  | nil => exact Or.inl hmem₀
  | cons nd nds ih =>
    exact (ih (f init₀ nd) (fun b hb => hsub b (List.mem_cons_of_mem _ hb)) hmem₀).elim
      (fun h => by
        by_cases h_init : σ ∈ init₀
        · exact Or.inl h_init
        · exact Or.inr (hsound init₀ nd (hsub nd (List.Mem.head _)) σ h h_init))
      Or.inr

/-- matchChildren extends: σ from matchChildren extends the initial substitution. -/
private theorem matchChildren_extends_aux (g : MGraph) (n : Nat)
    (ih : ∀ (pat : MixedEMatch.Pattern MixedNodeOp) (classId : CId) (subst₀ σ : MixedEMatch.Substitution),
      σ ∈ MixedEMatch.ematchF n g pat classId subst₀ →
      ∀ pv id, subst₀.get? pv = some id → σ.get? pv = some id)
    (pats : List (MixedEMatch.Pattern MixedNodeOp))
    (nodeChildren : List CId)
    (subst₀ : MixedEMatch.Substitution)
    (acc : MixedEMatch.MatchResult) (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF.matchChildren g n pats nodeChildren subst₀ acc)
    (hnotacc : σ ∉ acc)
    (pv : MixedEMatch.PatVarId) (id : CId)
    (hget : subst₀.get? pv = some id) :
    σ.get? pv = some id := by
  induction pats generalizing nodeChildren subst₀ acc σ pv id with
  | nil =>
    cases nodeChildren with
    | nil =>
      simp [MixedEMatch.ematchF.matchChildren, List.mem_append] at hmem
      exact hmem.resolve_left hnotacc ▸ hget
    | cons _ _ =>
      exact absurd (by simpa [MixedEMatch.ematchF.matchChildren] using hmem) hnotacc
  | cons p ps ih_pats =>
    cases nodeChildren with
    | nil => exact absurd (by simpa [MixedEMatch.ematchF.matchChildren] using hmem) hnotacc
    | cons c cs =>
      simp only [MixedEMatch.ematchF.matchChildren] at hmem
      exact foldl_sound_predicate
        (fun a s => MixedEMatch.ematchF.matchChildren g n ps cs s a)
        (fun σ' => σ'.get? pv = some id)
        (MixedEMatch.ematchF n g p c subst₀)
        (fun acc' s hs_mem σ' hmem_mc hnotacc' =>
          ih_pats cs s acc' σ' hmem_mc hnotacc' pv id (ih p c subst₀ s hs_mem pv id hget))
        acc σ hmem hnotacc

/-- ematchF extends: all bindings in input subst₀ are preserved in output σ. -/
private theorem ematchF_extends
    (fuel : Nat) (g : MGraph) (pat : MixedEMatch.Pattern MixedNodeOp)
    (classId : CId) (subst₀ σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g pat classId subst₀) :
    ∀ pv id, subst₀.get? pv = some id → σ.get? pv = some id := by
  induction fuel generalizing pat classId subst₀ σ with
  | zero => simp at hmem
  | succ n ih =>
    cases pat with
    | patVar pv =>
      simp only [MixedEMatch.ematchF] at hmem
      split at hmem
      · rename_i s hext
        rw [List.mem_singleton] at hmem; subst hmem
        intro pv' id' hget
        unfold MixedEMatch.Substitution.extend at hext
        split at hext
        · obtain rfl := Option.some.inj hext
          by_cases heq : pv' = pv
          · subst heq; simp_all
          · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
              beq_iff_eq, Ne.symm heq, ite_false] at hget ⊢
            exact hget
        · rename_i existingId _
          split at hext
          · obtain rfl := Option.some.inj hext; exact hget
          · simp at hext
      · simp at hmem
    | node skelOp subpats =>
      simp only [MixedEMatch.ematchF] at hmem
      split at hmem
      · simp at hmem
      · rename_i eclass _
        -- σ ∈ Array.foldl ... [] eclass.nodes
        -- matchChildren threads subst₀ through, only extending
        -- The foldl passes subst₀ to matchChildren, which passes it to ematchF
        -- Node case: use foldl_sound_predicate + matchChildren_extends
        -- First convert Array.foldl to List.foldl
        rw [← Array.foldl_toList] at hmem
        intro pv id hget
        exact foldl_sound_predicate
          (fun (acc : MixedEMatch.MatchResult) (nd : AmoLean.EGraph.VerifiedExtraction.ENode MixedNodeOp) =>
            if MixedEMatch.sameShape skelOp nd.op = true then
              MixedEMatch.ematchF.matchChildren g n subpats
                (AmoLean.EGraph.VerifiedExtraction.NodeOps.children nd.op) subst₀ acc
            else acc)
          (fun σ' => σ'.get? pv = some id)
          eclass.nodes.toList
          (fun acc nd _ σ' hmem_f hnotacc => by
            simp only [] at hmem_f
            split at hmem_f
            · exact matchChildren_extends_aux g n ih subpats _ subst₀ acc σ' hmem_f hnotacc pv id hget
            · exact absurd hmem_f hnotacc)
          [] σ hmem (by simp)

/-- sameShape implies children have the same length. -/
private theorem sameShape_children_length (op₁ op₂ : MixedNodeOp)
    (hss : MixedEMatch.sameShape op₁ op₂ = true) :
    (AmoLean.EGraph.VerifiedExtraction.NodeOps.children op₁).length =
    (AmoLean.EGraph.VerifiedExtraction.NodeOps.children op₂).length := by
  have heq := sameShape_eq op₁ op₂ hss
  have := congrArg (fun op => (AmoLean.EGraph.VerifiedExtraction.NodeOps.children op).length) heq
  simp [AmoLean.EGraph.VerifiedExtraction.NodeOps.mapChildren_children] at this
  exact this

/-- matchChildren combined soundness: proves per-child eval, extension, and per-child stability
    for any σ produced by matchChildren. Uses the combined IH from ematchF_combined.

    The proof is by induction on pats (mirroring matchChildren_extends_aux):
    - Base ([], []): σ = subst₀, per-child is vacuous
    - Step (p :: ps, c :: cs): σ came from matchChildren ps cs s acc where s ∈ ematchF n g p c subst₀.
      By IH on p: eval p constVal (substVal v uf s) = v(root c), s extends subst₀, and eval p is stable.
      By recursive IH on ps: per-child eval for tail, s-extension, stability for tail.
      Compose: σ extends s extends subst₀. Per-child eval for head uses stability of head. -/
private theorem matchChildren_combined_sound (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (n : Nat)
    (ih : ∀ (pat : MixedEMatch.Pattern MixedNodeOp),
      WellFormedPat pat →
      ∀ (classId : CId) (subst₀ σ : MixedEMatch.Substitution),
        σ ∈ MixedEMatch.ematchF n g pat classId subst₀ →
          MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) =
            v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) ∧
          (∀ pv id, subst₀.get? pv = some id → σ.get? pv = some id) ∧
          (∀ σ', (∀ pv id, σ.get? pv = some id → σ'.get? pv = some id) →
            MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ') =
            MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ)))
    (pats : List (MixedEMatch.Pattern MixedNodeOp))
    (hwfps : ∀ p ∈ pats, WellFormedPat p)
    (nodeChildren : List CId)
    (subst₀ : MixedEMatch.Substitution)
    (acc : MixedEMatch.MatchResult) (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF.matchChildren g n pats nodeChildren subst₀ acc)
    (hnotacc : σ ∉ acc) :
    -- (A) per-child eval
    (∀ i (hi_p : i < pats.length) (hi_c : i < nodeChildren.length),
      MixedEMatchSpec.Pattern.eval (pats[i]) (fun n => env.constVal n) (substVal v g.unionFind σ) =
        v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind (nodeChildren[i]))) ∧
    -- (B) extension
    (∀ pv id, subst₀.get? pv = some id → σ.get? pv = some id) ∧
    -- (C) per-child eval stability
    (∀ σ', (∀ pv id, σ.get? pv = some id → σ'.get? pv = some id) →
      ∀ i (hi : i < pats.length),
        MixedEMatchSpec.Pattern.eval (pats[i]) (fun n => env.constVal n) (substVal v g.unionFind σ') =
        MixedEMatchSpec.Pattern.eval (pats[i]) (fun n => env.constVal n) (substVal v g.unionFind σ)) := by
  induction pats generalizing nodeChildren subst₀ acc σ with
  | nil =>
    cases nodeChildren with
    | nil =>
      simp [MixedEMatch.ematchF.matchChildren, List.mem_append] at hmem
      obtain rfl := hmem.resolve_left hnotacc
      exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i),
             fun pv id h => h,
             fun _ _ i hi => absurd hi (Nat.not_lt_zero i)⟩
    | cons _ _ =>
      exact absurd (by simpa [MixedEMatch.ematchF.matchChildren] using hmem) hnotacc
  | cons p ps ih_pats =>
    cases nodeChildren with
    | nil => exact absurd (by simpa [MixedEMatch.ematchF.matchChildren] using hmem) hnotacc
    | cons c cs =>
      simp only [MixedEMatch.ematchF.matchChildren] at hmem
      -- σ ∈ foldl (fun a s => matchChildren g n ps cs s a) acc (ematchF n g p c subst₀)
      -- Extract: ∃ s ∈ ematchF n g p c subst₀, σ ∈ matchChildren g n ps cs s ... ∧ σ ∉ ...
      -- Use foldl_sound_predicate
      have := foldl_sound_predicate
        (fun a s => MixedEMatch.ematchF.matchChildren g n ps cs s a)
        (fun σ' =>
          (∀ i (hi_p : i < (p :: ps).length) (hi_c : i < (c :: cs).length),
            MixedEMatchSpec.Pattern.eval ((p :: ps)[i]) (fun n => env.constVal n) (substVal v g.unionFind σ') =
              v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind ((c :: cs)[i]))) ∧
          (∀ pv id, subst₀.get? pv = some id → σ'.get? pv = some id) ∧
          (∀ σ'', (∀ pv id, σ'.get? pv = some id → σ''.get? pv = some id) →
            ∀ i (hi : i < (p :: ps).length),
              MixedEMatchSpec.Pattern.eval ((p :: ps)[i]) (fun n => env.constVal n) (substVal v g.unionFind σ'') =
              MixedEMatchSpec.Pattern.eval ((p :: ps)[i]) (fun n => env.constVal n) (substVal v g.unionFind σ')))
        (MixedEMatch.ematchF n g p c subst₀)
        (fun acc' s hs_mem σ' hmem_mc hnotacc' => by
          -- s ∈ ematchF n g p c subst₀ → IH gives us properties for p
          have hwfp_p := hwfps p (List.Mem.head ps)
          have ⟨heval_s, hext_s, hstab_s⟩ := ih p hwfp_p c subst₀ s hs_mem
          -- Recursive IH on (ps, cs) with s as initial subst
          have hwfps' : ∀ q ∈ ps, WellFormedPat q :=
            fun q hq => hwfps q (List.mem_cons_of_mem p hq)
          have ⟨heval_tail, hext_tail, hstab_tail⟩ :=
            ih_pats hwfps' cs s acc' σ' hmem_mc hnotacc'
          refine ⟨?_, ?_, ?_⟩
          · -- Per-child eval for all indices
            intro i hi_p hi_c
            cases i with
            | zero =>
              simp only [List.getElem_cons_zero]
              rw [hstab_s σ' hext_tail]
              exact heval_s
            | succ j =>
              simp only [List.getElem_cons_succ]
              exact heval_tail j (by simp [List.length_cons] at hi_p; omega)
                (by simp [List.length_cons] at hi_c; omega)
          · -- Extension: subst₀ → s → σ'
            intro pv id hget
            exact hext_tail pv id (hext_s pv id hget)
          · -- Stability for all indices
            intro σ'' hext'' i hi
            cases i with
            | zero =>
              simp only [List.getElem_cons_zero]
              rw [hstab_s σ'' (fun pv id hget => hext'' pv id (hext_tail pv id hget))]
              exact (hstab_s σ' hext_tail).symm
            | succ j =>
              simp only [List.getElem_cons_succ]
              exact hstab_tail σ'' hext''
                j (by simp [List.length_cons] at hi; omega))
        acc σ hmem hnotacc
      exact this

/-- Combined ematchF soundness + extension + eval stability.
    All three properties are proved simultaneously to handle the mutual dependence. -/
private theorem ematchF_combined (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal)
    (fuel : Nat) (pat : MixedEMatch.Pattern MixedNodeOp)
    (hwfp : WellFormedPat pat)
    (classId : CId)
    (subst₀ σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g pat classId subst₀) :
    -- (1) soundness
    MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) ∧
    -- (2) extension
    (∀ pv id, subst₀.get? pv = some id → σ.get? pv = some id) ∧
    -- (3) eval stability: for any σ' that extends σ, Pattern.eval agrees
    (∀ σ', (∀ pv id, σ.get? pv = some id → σ'.get? pv = some id) →
      MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ') =
      MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ)) := by
  induction fuel generalizing pat classId subst₀ σ hwfp with
  | zero => simp at hmem
  | succ n ih =>
    cases pat with
    | patVar pv =>
      simp only [MixedEMatch.ematchF] at hmem
      split at hmem
      · rename_i s hext_eq
        rw [List.mem_singleton] at hmem; subst hmem
        have hget := extend_maps_key subst₀ pv _ σ hext_eq
        refine ⟨?_, ?_, ?_⟩
        · -- (1) soundness
          simp only [MixedEMatchSpec.Pattern.eval]
          rw [substVal_get v g.unionFind σ pv _ hget]
          exact AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv hwf _
        · -- (2) extension
          intro pv' id' hget'
          unfold MixedEMatch.Substitution.extend at hext_eq
          split at hext_eq
          · obtain rfl := Option.some.inj hext_eq
            by_cases heq : pv' = pv
            · subst heq; simp_all
            · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
                beq_iff_eq, Ne.symm heq, ite_false] at hget' ⊢; exact hget'
          · split at hext_eq
            · obtain rfl := Option.some.inj hext_eq; exact hget'
            · simp at hext_eq
        · -- (3) eval stability
          intro σ' hext'
          simp only [MixedEMatchSpec.Pattern.eval, substVal]
          rw [hext' pv _ hget, hget]
      · simp at hmem
    | node skelOp subpats =>
      simp only [MixedEMatch.ematchF] at hmem
      split at hmem
      · simp at hmem
      · rename_i eclass hcls
        -- Node case: σ from Array.foldl over eclass.nodes via matchChildren
        -- Extract WellFormedPat
        unfold WellFormedPat at hwfp
        obtain ⟨hnodup, hlen_sp, hwfps⟩ := hwfp
        -- Convert Array.foldl to List.foldl
        rw [← Array.foldl_toList] at hmem
        -- Use foldl_sound_predicate to find the node and establish all three properties
        have := foldl_sound_predicate
          (fun (acc : MixedEMatch.MatchResult) (nd : AmoLean.EGraph.VerifiedExtraction.ENode MixedNodeOp) =>
            if MixedEMatch.sameShape skelOp nd.op = true then
              MixedEMatch.ematchF.matchChildren g n subpats
                (AmoLean.EGraph.VerifiedExtraction.NodeOps.children nd.op) subst₀ acc
            else acc)
          (fun σ =>
            MixedEMatchSpec.Pattern.eval (.node skelOp subpats) (fun n => env.constVal n)
              (substVal v g.unionFind σ) =
              v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) ∧
            (∀ pv id, subst₀.get? pv = some id → σ.get? pv = some id) ∧
            (∀ σ', (∀ pv id, σ.get? pv = some id → σ'.get? pv = some id) →
              MixedEMatchSpec.Pattern.eval (.node skelOp subpats) (fun n => env.constVal n)
                (substVal v g.unionFind σ') =
              MixedEMatchSpec.Pattern.eval (.node skelOp subpats) (fun n => env.constVal n)
                (substVal v g.unionFind σ)))
          eclass.nodes.toList
          (fun acc nd hnd_mem σ' hmem_f hnotacc => by
            simp only [] at hmem_f
            split at hmem_f
            · -- The matchChildren case: use matchChildren_combined_sound
              rename_i hss_nd
              have hcv2 := hcv.2 (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId)
                eclass hcls nd hnd_mem
              have ⟨heval_ch, hext_ch, hstab_ch⟩ :=
                matchChildren_combined_sound g env v hcv hwf n ih subpats hwfps
                  (AmoLean.EGraph.VerifiedExtraction.NodeOps.children nd.op) subst₀ acc σ' hmem_f hnotacc
              refine ⟨?_, hext_ch, ?_⟩
              · -- (1) eval (.node skelOp subpats) constVal (substVal v uf σ') = v(root classId)
                -- Use sameShapeSemantics + per-child eval
                simp only [MixedEMatchSpec.Pattern.eval]
                -- Need: evalMixedOp skelOp syntheticEnv w = v(root classId)
                -- where w maps children[i] to childVals[i]
                -- By sameShapeSemantics: evalMixedOp skelOp env w = evalMixedOp nd.op env v
                --   when corresponding children match
                -- By CV: evalMixedOp nd.op env v = v(root classId)
                have henv_eq : (⟨fun n => env.constVal n, fun n => env.constVal n,
                    fun n => env.constVal n⟩ : MixedEnv) = env := by
                  cases env with | mk c w p =>
                  simp only at henv_w henv_p ⊢
                  subst henv_w; subst henv_p; rfl
                have hsse := sameShapeSemantics_holds skelOp nd.op
                  ⟨fun n => env.constVal n, fun n => env.constVal n, fun n => env.constVal n⟩
                  (fun id => match (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).zip
                      (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
                        (substVal v g.unionFind σ'))) |>.lookup id with
                    | some val => val | none => 0)
                  v hss_nd
                have hlen_ch := sameShape_children_length skelOp nd.op hss_nd
                have hchildren_match : ∀ (i : Nat)
                    (h₁ : i < (ndCh skelOp).length) (h₂ : i < (ndCh nd.op).length),
                    (fun id => match (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).zip
                        (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
                          (substVal v g.unionFind σ'))) |>.lookup id with
                      | some val => val | none => 0) ((ndCh skelOp)[i]) = v ((ndCh nd.op)[i]) := by
                  intro i h₁ h₂
                  have hlen_zip : (ndCh skelOp).length =
                      (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
                        (substVal v g.unionFind σ'))).length := by simp [hlen_sp]
                  have hlook := zip_lookup_nodup (ndCh skelOp)
                    (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
                      (substVal v g.unionFind σ'))) hnodup hlen_zip i h₁
                  simp only [ndCh] at hlook ⊢
                  rw [hlook]; simp only [List.getElem_map]
                  rw [heval_ch i (hlen_sp ▸ h₁) h₂]
                  exact AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv hwf _
                rw [henv_eq] at hsse ⊢
                rw [AmoLean.EGraph.VerifiedExtraction.NodeEval] at hcv2
                change evalMixedOp nd.op env v = v _ at hcv2
                exact (hsse hchildren_match).trans hcv2
              · -- (3) eval stability: eval (.node skelOp subpats) is stable under extensions of σ'
                intro σ'' hext''
                simp only [MixedEMatchSpec.Pattern.eval]
                -- The only σ-dependent part is subpats.map (fun p => eval p ...).
                -- Per-child stability gives pointwise equality → map equality → full equality
                have hmap_eq : subpats.map (fun p => MixedEMatchSpec.Pattern.eval p
                    (fun n => env.constVal n) (substVal v g.unionFind σ'')) =
                  subpats.map (fun p => MixedEMatchSpec.Pattern.eval p
                    (fun n => env.constVal n) (substVal v g.unionFind σ')) := by
                  apply List.ext_getElem (by simp)
                  intro i h₁ h₂
                  simp only [List.getElem_map]
                  exact hstab_ch σ'' hext'' i (by simpa using h₁)
                rw [hmap_eq]
            · exact absurd hmem_f hnotacc)
          [] σ hmem (by simp)
        exact this


/-- The entire node case of ematchF_sound_gen, factored out.
    Given σ from the Array.foldl over eclass.nodes, connects Pattern.eval to v(canonId). -/
private theorem node_case_sound (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal)
    (n : Nat)
    (ih : ∀ (pat : MixedEMatch.Pattern MixedNodeOp) (classId : CId)
      (hwfp : WellFormedPat pat)
      (subst₀ σ : MixedEMatch.Substitution),
      σ ∈ MixedEMatch.ematchF n g pat classId subst₀ →
        MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) =
          v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId))
    (skelOp : MixedNodeOp) (subpats : List (MixedEMatch.Pattern MixedNodeOp))
    (hwfp : WellFormedPat (MixedEMatch.Pattern.node skelOp subpats))
    (canonId : CId) (eclass : AmoLean.EGraph.VerifiedExtraction.EClass MixedNodeOp)
    (hcls : g.classes.get? canonId = some eclass)
    (subst₀ : MixedEMatch.Substitution) (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ Array.foldl
      (fun acc node =>
        if MixedEMatch.sameShape skelOp node.op = true then
          MixedEMatch.ematchF.matchChildren g n subpats
            (AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op) subst₀ acc
        else acc) [] eclass.nodes) :
    (let childVals := subpats.map (fun p =>
        MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n) (substVal v g.unionFind σ))
     let children := AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp
     let w : AmoLean.EGraph.VerifiedExtraction.EClassId → Nat := fun id =>
       match (children.zip childVals).lookup id with
       | some val => val
       | none => 0
     evalMixedOp skelOp ⟨fun n => env.constVal n, fun n => env.constVal n, fun n => env.constVal n⟩ w) =
      v canonId := by
  -- Extract WellFormedPat components
  unfold WellFormedPat at hwfp
  obtain ⟨hnodup, hlen_sp, hwfps⟩ := hwfp
  -- Step 1: Extract a matching node from the Array.foldl
  -- We need a lemma about Array.foldl membership
  suffices ∃ (node : AmoLean.EGraph.VerifiedExtraction.ENode MixedNodeOp),
      node ∈ eclass.nodes.toList ∧
      MixedEMatch.sameShape skelOp node.op = true ∧
      (∀ (i : Nat) (hi_p : i < subpats.length)
        (hi_c : i < (AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op).length),
        MixedEMatchSpec.Pattern.eval (subpats[i]) (fun n => env.constVal n) (substVal v g.unionFind σ) =
          v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind
            ((AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op)[i]))) by
    obtain ⟨node, hnode_mem, hss, hchildren_eq⟩ := this
    -- By CV: evalMixedOp node.op env v = v canonId
    have hcv2 := hcv.2 canonId eclass hcls node hnode_mem
    -- Use sameShapeSemantics to connect
    have hsse := sameShapeSemantics_holds skelOp node.op
      ⟨fun n => env.constVal n, fun n => env.constVal n, fun n => env.constVal n⟩
      (fun id => match (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).zip
          (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
            (substVal v g.unionFind σ))) |>.lookup id with
        | some val => val | none => 0)
      v hss
    -- Step A: prove env uniformity — syntheticEnv = env
    have henv_eq : (⟨fun n => env.constVal n, fun n => env.constVal n,
        fun n => env.constVal n⟩ : MixedEnv) = env := by
      cases env with | mk c w p =>
      simp only at henv_w henv_p ⊢
      subst henv_w; subst henv_p; rfl
    -- Step B: connect NodeEval to evalMixedOp with syntheticEnv
    -- hcv2 : NodeEval node env v = v canonId
    -- NodeEval node env v = evalMixedOp node.op env v
    rw [AmoLean.EGraph.VerifiedExtraction.NodeEval] at hcv2
    -- Step C: prove antecedent of hsse
    have hchildren_match : ∀ (i : Nat) (h₁ : i < (ndCh skelOp).length) (h₂ : i < (ndCh node.op).length),
        (fun id => match (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).zip
            (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
              (substVal v g.unionFind σ))) |>.lookup id with
          | some val => val | none => 0) ((ndCh skelOp)[i]) = v ((ndCh node.op)[i]) := by
      intro i h₁ h₂
      -- Use zip_lookup_nodup to resolve the List.lookup
      have hlen_zip : (ndCh skelOp).length =
          (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
            (substVal v g.unionFind σ))).length := by simp [hlen_sp]
      have hlook := zip_lookup_nodup (ndCh skelOp)
        (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
          (substVal v g.unionFind σ))) hnodup hlen_zip i h₁
      simp only [ndCh] at hlook ⊢
      rw [hlook]
      -- Now: childVals[i] = v((ndCh node.op)[i])
      simp only [List.getElem_map]
      -- childVals[i] = Pattern.eval subpats[i] ...
      -- By hchildren_eq: = v(root(children node.op[i]))
      rw [hchildren_eq i (hlen_sp ▸ h₁) h₂]
      -- v(root(children node.op[i])) = v(children node.op[i])
      exact AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv hwf _
    -- Step D: apply hsse
    have h_skel_eq := hsse hchildren_match
    -- h_skel_eq : evalMixedOp skelOp syntheticEnv w = evalMixedOp node.op syntheticEnv v
    rw [henv_eq] at h_skel_eq
    -- now h_skel_eq : evalMixedOp skelOp env w = evalMixedOp node.op env v
    -- hcv2 : NodeSemantics.evalOp node.op env v = v canonId
    -- NodeSemantics.evalOp = evalMixedOp for MixedNodeOp
    change evalMixedOp node.op env v = v canonId at hcv2
    -- Goal: evalMixedOp skelOp syntheticEnv w = v canonId
    -- Rewrite synthetic env to env in goal
    simp only []
    rw [henv_eq]
    exact h_skel_eq.trans hcv2
  -- Prove the suffices: extract node + sameShape + per-child eval from foldl
  rw [← Array.foldl_toList] at hmem
  -- The ih here gives eval-only soundness (no WellFormedPat needed in the callback
  -- since node_case_sound's ih already has it)
  -- But we DO have hwfps for all subpatterns.
  -- We need a combined matchChildren IH. Use matchChildren_combined_sound.
  -- First, upgrade ih to the combined form for use in matchChildren_combined_sound.
  -- ih gives eval only. matchChildren_combined_sound needs the full 3-tuple ih.
  -- We can build the full ih from ematchF_combined + ematchF_sound_gen context.
  -- Actually, for this lemma, ih is the simpler (eval-only) form.
  -- matchChildren_combined_sound needs the full ih from ematchF_combined.
  -- Let's use a direct approach: foldl_sound_predicate with per-child eval.
  exact foldl_sound_predicate
    (fun (acc : MixedEMatch.MatchResult) (nd : AmoLean.EGraph.VerifiedExtraction.ENode MixedNodeOp) =>
      if MixedEMatch.sameShape skelOp nd.op = true then
        MixedEMatch.ematchF.matchChildren g n subpats
          (AmoLean.EGraph.VerifiedExtraction.NodeOps.children nd.op) subst₀ acc
      else acc)
    (fun σ' => ∃ node, node ∈ eclass.nodes.toList ∧
      MixedEMatch.sameShape skelOp node.op = true ∧
      ∀ (i : Nat) (hi_p : i < subpats.length)
        (hi_c : i < (AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op).length),
        MixedEMatchSpec.Pattern.eval (subpats[i]) (fun n => env.constVal n) (substVal v g.unionFind σ') =
          v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind
            ((AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op)[i])))
    eclass.nodes.toList
    (fun acc nd hnd_mem σ' hmem_f hnotacc => by
      simp only [] at hmem_f
      split at hmem_f
      · -- matchChildren produced σ'
        rename_i hss_nd
        -- Use matchChildren with the per-child eval IH
        -- We need: for each i, eval subpats[i] ... σ' = v(root children[i])
        -- This requires the full combined IH. Build it from ih + ematchF_extends.
        -- Actually, ih only gives eval soundness. We need eval stability too.
        -- Alternative: prove per-child directly using matchChildren_extends_aux + ih.
        -- The key: matchChildren processes (subpats[i], children[i]) pairs left to right.
        -- For each i, ematchF n g subpats[i] children[i] produces an intermediate σ_i.
        -- ih gives: eval subpats[i] ... σ_i = v(root children[i])
        -- σ' extends σ_i, so by eval stability, eval subpats[i] ... σ' = eval subpats[i] ... σ_i
        -- But eval stability comes from ematchF_combined, which we can't directly invoke here
        -- since ih is the simpler version.
        -- SOLUTION: use ematchF_combined directly as the full ih for matchChildren_combined_sound
        -- We can construct the full ih from scratch using ematchF_combined.
        have ih_full : ∀ (pat : MixedEMatch.Pattern MixedNodeOp),
            WellFormedPat pat →
            ∀ (classId : CId) (subst₀' σ' : MixedEMatch.Substitution),
              σ' ∈ MixedEMatch.ematchF n g pat classId subst₀' →
                MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ') =
                  v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) ∧
                (∀ pv id, subst₀'.get? pv = some id → σ'.get? pv = some id) ∧
                (∀ σ'', (∀ pv id, σ'.get? pv = some id → σ''.get? pv = some id) →
                  MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ'') =
                  MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ')) := by
          intro pat hwfpat cid sub₀ sub₁ hm
          exact ematchF_combined g env v hcv hwf henv_w henv_p n pat hwfpat cid sub₀ sub₁ hm
        have ⟨heval_ch, _, _⟩ :=
          matchChildren_combined_sound g env v hcv hwf n ih_full subpats hwfps
            (AmoLean.EGraph.VerifiedExtraction.NodeOps.children nd.op) subst₀ acc σ' hmem_f hnotacc
        exact ⟨nd, hnd_mem, hss_nd, heval_ch⟩
      · exact absurd hmem_f hnotacc)
    [] σ hmem (by simp)

/-- Generalized ematchF soundness with arbitrary input substitution.
    Derived from ematchF_combined. -/
private theorem ematchF_sound_gen (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal)
    (fuel : Nat) (pat : MixedEMatch.Pattern MixedNodeOp) (classId : CId)
    (hwfp : WellFormedPat pat)
    (subst₀ : MixedEMatch.Substitution) (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g pat classId subst₀) :
    MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) :=
  (ematchF_combined g env v hcv hwf henv_w henv_p fuel pat hwfp classId subst₀ σ hmem).1

/-- ematchF soundness: for any substitution σ from ematchF, the LHS pattern evaluates
    to the matched class's value. Deep inductive proof on fuel + Pattern.
    cf. OptiSat EMatchSpec.lean:453-462. -/
theorem ematchF_sound (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal)
    (fuel : Nat) (pat : MixedEMatch.Pattern MixedNodeOp) (classId : CId)
    (hwfp : WellFormedPat pat)
    (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g pat classId) :
    MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) :=
  ematchF_sound_gen g env v hcv hwf henv_w henv_p fuel pat classId hwfp
    MixedEMatch.Substitution.empty σ hmem

open AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple (ShapeHashconsInv)

/-- Children of replaceChildren are bounded when all ids and all original children are bounded.
    Needed for CHILDREN-BND in instantiateF_sound.
    Uses Decidable.decide + rfl to reduce the nested match on (op, ids). -/
private theorem replaceChildren_children_bounded (op : MixedNodeOp) (ids : List CId) (bound : Nat)
    (hids : ∀ c ∈ ids, c < bound)
    (hch : ∀ c ∈ AmoLean.EGraph.VerifiedExtraction.NodeOps.children op, c < bound) :
    ∀ c ∈ AmoLean.EGraph.VerifiedExtraction.NodeOps.children
      (AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren op ids), c < bound := by
  change ∀ c ∈ mixedChildren (mixedReplaceChildren op ids), c < bound
  change ∀ c ∈ mixedChildren op, c < bound at hch
  intro c hc
  -- Strategy: case split on op, then on ids, using `dsimp` for kernel-level reduction
  -- (The nested match on (op, ids) in mixedReplaceChildren needs both known to reduce)
  cases op <;> (first
    -- Leaf ops: mixedReplaceChildren returns op regardless of ids; children = []
    | (dsimp only [mixedReplaceChildren, mixedChildren] at hc; exact absurd hc (by simp))
    -- Non-leaf: need ids structure. Split on ids.
    | (cases ids with
       | nil =>
         -- Fallback | op, _ => op: use hch
         dsimp only [mixedReplaceChildren, mixedChildren] at hc; exact hch c hc
       | cons hd tl =>
         -- For binary ops, still need tl = hd2 :: _
         first
         | (-- Binary with tl = [] or tl = hd2 :: _
            cases tl with
            | nil =>
              first
              | (-- Binary fallback: ids too short, returns op
                 dsimp only [mixedReplaceChildren, mixedChildren] at hc; exact hch c hc)
              | (-- Unary: (.negGate hd) etc. Children = [hd]
                 dsimp only [mixedReplaceChildren, mixedChildren] at hc
                 simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
                 subst hc; exact hids _ (by simp [List.mem_cons]))
            | cons hd2 tl2 =>
              first
              | (-- Binary: (.addGate hd hd2) etc. Children = [hd, hd2]
                 dsimp only [mixedReplaceChildren, mixedChildren] at hc
                 simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
                 rcases hc with rfl | rfl
                 · exact hids _ (by simp [List.mem_cons])
                 · exact hids _ (by simp [List.mem_cons]))
              | (-- Unary: (.negGate hd) etc with extra ids. Children = [hd]
                 dsimp only [mixedReplaceChildren, mixedChildren] at hc
                 simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
                 subst hc; exact hids _ (by simp [List.mem_cons])))))

/-- Auxiliary: instantiateF.go preserves CV and tracks child ID bounds.
    Induction on pats using ih_fuel (which works for instantiateF at reduced fuel n). -/
private theorem go_preserves_cv (n : Nat) (σ : MixedEMatch.Substitution) (env : MixedEnv)
    (ih_fuel : ∀ (g : MGraph) (pat : MixedEMatch.Pattern MixedNodeOp) (v : CId → Nat),
      CV g env v → VPMI g → ShapeHashconsInv g →
      (∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size) →
      WellFormedPat pat →
      ∀ id g', MixedEMatch.instantiateF n g pat σ = some (id, g') →
      ∃ v', CV g' env v' ∧ VPMI g' ∧ ShapeHashconsInv g' ∧
        g.unionFind.parent.size ≤ g'.unionFind.parent.size ∧
        (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
        id < g'.unionFind.parent.size)
    (pats : List (MixedEMatch.Pattern MixedNodeOp))
    (g₀ : MGraph) (v₀ : CId → Nat) (ids₀ : List CId)
    (hcv₀ : CV g₀ env v₀) (hpmi₀ : VPMI g₀) (hshi₀ : ShapeHashconsInv g₀)
    (hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g₀.unionFind.parent.size)
    (hwfp_pats : ∀ p ∈ pats, WellFormedPat p)
    (hbnd_ids₀ : ∀ c ∈ ids₀, c < g₀.unionFind.parent.size)
    (childIds : List CId) (g_final : MGraph)
    (hgo : MixedEMatch.instantiateF.go σ n g₀ pats ids₀ = some (childIds, g_final)) :
    ∃ v', CV g_final env v' ∧ VPMI g_final ∧ ShapeHashconsInv g_final ∧
      g₀.unionFind.parent.size ≤ g_final.unionFind.parent.size ∧
      (∀ i, i < g₀.unionFind.parent.size → v' i = v₀ i) ∧
      (∀ c ∈ childIds, c < g_final.unionFind.parent.size) := by
  induction pats generalizing g₀ v₀ ids₀ with
  | nil =>
    simp [MixedEMatch.instantiateF.go] at hgo
    obtain ⟨rfl, rfl⟩ := hgo
    exact ⟨v₀, hcv₀, hpmi₀, hshi₀, Nat.le_refl _, fun _ _ => rfl,
      fun c hc => hbnd_ids₀ c (List.mem_reverse.mp hc)⟩
  | cons p ps ih_go =>
    simp only [MixedEMatch.instantiateF.go] at hgo
    split at hgo
    · simp at hgo
    · rename_i cid g1 h_eq
      have hwfp_p : WellFormedPat p := hwfp_pats p (List.mem_cons.mpr (Or.inl rfl))
      have hwfp_ps : ∀ q ∈ ps, WellFormedPat q :=
        fun q hq => hwfp_pats q (List.mem_cons.mpr (Or.inr hq))
      obtain ⟨v₁, hcv₁, hpmi₁, hshi₁, hsize₁, hagree₁, hcid_bnd⟩ :=
        ih_fuel g₀ p v₀ hcv₀ hpmi₀ hshi₀ hbnd_σ hwfp_p cid g1 h_eq
      obtain ⟨v', hcv', hpmi', hshi', hsize', hagree', hbnd_ids⟩ :=
        ih_go g1 v₁ (cid :: ids₀) hcv₁ hpmi₁ hshi₁
          (fun pv id h => Nat.lt_of_lt_of_le (hbnd_σ pv id h) hsize₁)
          hwfp_ps
          (fun c hc => by
            rw [List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact hcid_bnd
            · exact Nat.lt_of_lt_of_le (hbnd_ids₀ c hc) hsize₁)
          hgo
      exact ⟨v', hcv', hpmi', hshi',
        Nat.le_trans hsize₁ hsize',
        fun i hi => (hagree' i (Nat.lt_of_lt_of_le hi hsize₁)).trans (hagree₁ i hi),
        hbnd_ids⟩


private theorem go_length (n : Nat) (σ : MixedEMatch.Substitution)
    (pats : List (MixedEMatch.Pattern MixedNodeOp))
    (g₀ : MGraph) (ids₀ childIds : List CId) (g_final : MGraph)
    (hgo : MixedEMatch.instantiateF.go σ n g₀ pats ids₀ = some (childIds, g_final)) :
    childIds.length = pats.length + ids₀.length := by
  induction pats generalizing g₀ ids₀ with
  | nil =>
    simp [MixedEMatch.instantiateF.go] at hgo
    obtain ⟨hlen, _⟩ := hgo
    rw [← hlen]; simp [List.length_reverse]
  | cons p ps ih =>
    simp only [MixedEMatch.instantiateF.go] at hgo
    split at hgo
    · simp at hgo
    · rename_i cid g1 _
      have := ih g1 (cid :: ids₀) hgo
      simp only [List.length_cons] at this ⊢
      omega

/-- go structural: childIds = ids₀.reverse ++ newIds with newIds.length = pats.length. -/
private theorem go_prefix (n : Nat) (σ : MixedEMatch.Substitution)
    (pats : List (MixedEMatch.Pattern MixedNodeOp))
    (g₀ : MGraph) (ids₀ childIds : List CId) (g_final : MGraph)
    (hgo : MixedEMatch.instantiateF.go σ n g₀ pats ids₀ = some (childIds, g_final)) :
    ∃ newIds, childIds = ids₀.reverse ++ newIds ∧ newIds.length = pats.length := by
  induction pats generalizing g₀ ids₀ with
  | nil =>
    simp [MixedEMatch.instantiateF.go] at hgo
    obtain ⟨rfl, rfl⟩ := hgo
    exact ⟨[], by simp, rfl⟩
  | cons p ps ih =>
    simp only [MixedEMatch.instantiateF.go] at hgo
    split at hgo
    · simp at hgo
    · rename_i cid g1 _
      obtain ⟨newIds, heq, hlen⟩ := ih g1 (cid :: ids₀) hgo
      rw [List.reverse_cons] at heq
      exact ⟨cid :: newIds, by rw [heq]; simp [List.append_assoc], by simp [hlen]⟩

/-- go_child_values: strengthened go with per-child value tracking.
    For each child j produced by go (at index ids₀.length + j in childIds),
    the final valuation maps it to Pattern.eval of the corresponding subpattern. -/
private theorem go_child_values (n : Nat) (σ : MixedEMatch.Substitution) (env : MixedEnv)
    (ih_fuel : ∀ (g : MGraph) (pat : MixedEMatch.Pattern MixedNodeOp) (v : CId → Nat),
      CV g env v → VPMI g → ShapeHashconsInv g →
      (∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size) →
      WellFormedPat pat →
      ∀ id g', MixedEMatch.instantiateF n g pat σ = some (id, g') →
      ∃ v', CV g' env v' ∧ VPMI g' ∧ ShapeHashconsInv g' ∧
        g.unionFind.parent.size ≤ g'.unionFind.parent.size ∧
        (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
        id < g'.unionFind.parent.size ∧
        v' (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g'.unionFind id) =
          MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ))
    (g_ref : MGraph) (v_ref : CId → Nat)
    (hcv_ref : CV g_ref env v_ref) (hpmi_ref : VPMI g_ref)
    (hbnd_σ_ref : ∀ pv id, σ.get? pv = some id → id < g_ref.unionFind.parent.size)
    (pats : List (MixedEMatch.Pattern MixedNodeOp))
    (g₀ : MGraph) (v₀ : CId → Nat) (ids₀ : List CId)
    (hcv₀ : CV g₀ env v₀) (hpmi₀ : VPMI g₀) (hshi₀ : ShapeHashconsInv g₀)
    (hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g₀.unionFind.parent.size)
    (hwfp_pats : ∀ p ∈ pats, WellFormedPat p)
    (hbnd_ids₀ : ∀ c ∈ ids₀, c < g₀.unionFind.parent.size)
    (hsize_ref : g_ref.unionFind.parent.size ≤ g₀.unionFind.parent.size)
    (hagree_ref : ∀ i, i < g_ref.unionFind.parent.size → v₀ i = v_ref i)
    (childIds : List CId) (g_final : MGraph)
    (hgo : MixedEMatch.instantiateF.go σ n g₀ pats ids₀ = some (childIds, g_final)) :
    ∃ v', CV g_final env v' ∧ VPMI g_final ∧ ShapeHashconsInv g_final ∧
      g₀.unionFind.parent.size ≤ g_final.unionFind.parent.size ∧
      (∀ i, i < g₀.unionFind.parent.size → v' i = v₀ i) ∧
      (∀ c ∈ childIds, c < g_final.unionFind.parent.size) ∧
      (∀ j (hj : j < pats.length),
        v' (childIds[ids₀.length + j]'(by
          have := go_length n σ pats g₀ ids₀ childIds g_final hgo; omega)) =
        MixedEMatchSpec.Pattern.eval (pats[j]) (fun n => env.constVal n)
          (substVal v_ref g_ref.unionFind σ)) := by
  induction pats generalizing g₀ v₀ ids₀ with
  | nil =>
    simp [MixedEMatch.instantiateF.go] at hgo
    obtain ⟨rfl, rfl⟩ := hgo
    exact ⟨v₀, hcv₀, hpmi₀, hshi₀, Nat.le_refl _, fun _ _ => rfl,
      fun c hc => hbnd_ids₀ c (List.mem_reverse.mp hc),
      fun j hj => absurd hj (by simp)⟩
  | cons p ps ih_go =>
    simp only [MixedEMatch.instantiateF.go] at hgo
    split at hgo
    · simp at hgo
    · rename_i cid g1 h_eq
      have hwfp_p : WellFormedPat p := hwfp_pats p (List.mem_cons.mpr (Or.inl rfl))
      have hwfp_ps : ∀ q ∈ ps, WellFormedPat q :=
        fun q hq => hwfp_pats q (List.mem_cons.mpr (Or.inr hq))
      obtain ⟨v₁, hcv₁, hpmi₁, hshi₁, hsize₁, hagree₁, hcid_bnd, hval₁⟩ :=
        ih_fuel g₀ p v₀ hcv₀ hpmi₀ hshi₀ hbnd_σ hwfp_p cid g1 h_eq
      have hbnd_σ₁ : ∀ pv id, σ.get? pv = some id → id < g1.unionFind.parent.size :=
        fun pv id h => Nat.lt_of_lt_of_le (hbnd_σ pv id h) hsize₁
      obtain ⟨v', hcv', hpmi', hshi', hsize', hagree', hbnd_ids, hvals⟩ :=
        ih_go g1 v₁ (cid :: ids₀) hcv₁ hpmi₁ hshi₁
          hbnd_σ₁ hwfp_ps
          (fun c hc => by
            rw [List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact hcid_bnd
            · exact Nat.lt_of_lt_of_le (hbnd_ids₀ c hc) hsize₁)
          (Nat.le_trans hsize_ref hsize₁)
          (fun i hi => (hagree₁ i (Nat.lt_of_lt_of_le hi hsize_ref)).trans (hagree_ref i hi))
          hgo
      refine ⟨v', hcv', hpmi', hshi',
        Nat.le_trans hsize₁ hsize',
        fun i hi => (hagree' i (Nat.lt_of_lt_of_le hi hsize₁)).trans (hagree₁ i hi),
        hbnd_ids, ?_⟩
      intro j hj
      cases j with
      | zero =>
        -- Goal: v' childIds[ids₀.length + 0] = Pattern.eval (p :: ps)[0] ...
        simp only [Nat.add_zero, List.getElem_cons_zero]
        -- childIds = ids₀.reverse ++ (cid :: newIds) by go_prefix
        have ⟨newIds, heq_struct, _⟩ := go_prefix n σ ps g1 (cid :: ids₀) childIds g_final hgo
        rw [List.reverse_cons] at heq_struct
        have heq_cons : childIds = ids₀.reverse ++ (cid :: newIds) := by
          rw [heq_struct]; simp [List.append_assoc]
        -- v' childIds[ids₀.length] = v' cid (since childIds[ids₀.length] = cid)
        have hlen_childIds := go_length n σ (p :: ps) g₀ ids₀ childIds g_final
          (by simp only [MixedEMatch.instantiateF.go, h_eq]; exact hgo)
        have hi_bnd : ids₀.length < childIds.length := by
          simp only [List.length_cons] at hlen_childIds; omega
        -- v'(childIds[ids₀.length]) = v'(cid) via subst + structural
        subst heq_cons
        -- Now childIds is gone, goal is about ids₀.reverse ++ (cid :: newIds)
        simp only [List.getElem_append_right (show ids₀.reverse.length ≤ ids₀.length by simp),
          List.length_reverse, Nat.sub_self, List.getElem_cons_zero]
        -- Goal: v' cid = Pattern.eval p ...
        -- Chain: v'(cid) → v₁(cid) → eval p → substVal agree
        rw [hagree' cid hcid_bnd,
            ← AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv₁ hpmi₁.uf_wf cid,
            hval₁]
        congr 1; funext pv; unfold substVal; split
        · rename_i id hget
          rw [AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv₀ hpmi₀.uf_wf id,
              hagree_ref id (hbnd_σ_ref pv id hget),
              ← AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv_ref hpmi_ref.uf_wf id]
        · rfl
      | succ j' =>
        simp only [List.length_cons] at hj
        have hj' : j' < ps.length := by omega
        have := hvals j' hj'
        -- Bridge: ids₀.length + (j' + 1) = (ids₀.length + 1) + j' = (cid :: ids₀).length + j'
        simp only [List.getElem_cons_succ, List.length_cons] at this ⊢
        -- Use congr to match indices
        have hidx : ids₀.length + (j' + 1) = ids₀.length + 1 + j' := by omega
        simp only [hidx]
        exact this

/-- InstantiateEvalSound: instantiateF preserves CV and the new node's value
    matches the pattern evaluation. Proved by induction on fuel + go_preserves_cv.
    cf. OptiSat EMatchSpec.lean:509-527. -/
theorem instantiateF_sound (fuel : Nat) (g : MGraph) (pat : MixedEMatch.Pattern MixedNodeOp)
    (σ : MixedEMatch.Substitution) (v : CId → Nat) (env : MixedEnv)
    (hcv : CV g env v) (hpmi : VPMI g)
    (hshi : AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.ShapeHashconsInv g)
    (hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size)
    (hwfp : WellFormedPat pat)
    (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal)
    (id : CId) (g' : MGraph)
    (hinst : MixedEMatch.instantiateF fuel g pat σ = some (id, g')) :
    ∃ v', CV g' env v' ∧ VPMI g' ∧
      AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.ShapeHashconsInv g' ∧
      g.unionFind.parent.size ≤ g'.unionFind.parent.size ∧
      (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
      id < g'.unionFind.parent.size ∧
      v' (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g'.unionFind id) =
        MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) := by
  -- Induction on fuel
  induction fuel generalizing g v id g' pat with
  | zero => simp [MixedEMatch.instantiateF] at hinst
  | succ n ih =>
    -- Case split on pattern
    cases pat with
    | patVar pv =>
      -- patVar: unfold shows match on σ.lookup pv
      simp only [MixedEMatch.instantiateF, MixedEMatch.Substitution.lookup] at hinst
      -- Split on lookup result
      split at hinst
      · -- lookup = some → (id, g') = (existId, g)
        rename_i existId hlookup
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinst)
        exact ⟨v, hcv, hpmi, hshi, Nat.le_refl _, fun _ _ => rfl,
          hbnd_σ pv existId hlookup, by
          simp_all [MixedEMatchSpec.Pattern.eval, substVal, MixedEMatch.Substitution.lookup]⟩
      · -- lookup = none → contradiction
        exact absurd hinst (by simp)
    | node skelOp subpats =>
      -- patNode: unfold to match on go result
      simp only [MixedEMatch.instantiateF] at hinst
      -- Split on go result
      split at hinst
      · exact absurd hinst (by simp)  -- go = none
      · -- go = some (childIds, g'')
        rename_i childIds g'' h_go_eq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinst)
        -- Extract WellFormedPat components
        unfold WellFormedPat at hwfp
        obtain ⟨hnodup, hlen_eq, hwfp_sub⟩ := hwfp
        -- Step 1: go_child_values gives CV+VPMI+SHI + per-child values
        have go_result := go_child_values n σ env ih
            g v hcv hpmi hbnd_σ
            subpats g v [] hcv hpmi hshi hbnd_σ hwfp_sub
            (fun _ h => by simp at h)
            (Nat.le_refl _) (fun _ _ => rfl)
            childIds g'' h_go_eq
        obtain ⟨v'', hcv'', hpmi'', hshi'', hsize'', hagree'', hchildIds_bnd, hchild_vals⟩ :=
          go_result
        -- Step 2: add_node_consistent for g''.add(replaceChildren skelOp childIds)
        have hgo_len := go_length n σ subpats g [] childIds g'' h_go_eq
        have hlen_ids : childIds.length =
            (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).length := by
          simp only [List.length_nil, Nat.add_zero] at hgo_len
          exact hgo_len.trans hlen_eq
        have hch_eq := AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren_children
            skelOp childIds hlen_ids
        have hnode_bnd : ∀ c ∈ ndChildren
            ⟨AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds⟩,
            c < g''.unionFind.parent.size := by
          intro c hc
          change c ∈ AmoLean.EGraph.VerifiedExtraction.NodeOps.children
            (AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds) at hc
          rw [hch_eq] at hc
          exact hchildIds_bnd c hc
        obtain ⟨v', hcv', hpmi', hval', hid_bnd', hsize', hagree'⟩ :=
          AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.add_node_consistent
            g'' ⟨AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds⟩
            env v'' hcv'' hpmi'' hshi'' hnode_bnd
        -- Step 3: VALUE proof
        -- v'(root g'.uf id) = v'(id) = NodeEvalM node env v'
        -- Need to connect NodeEvalM to Pattern.eval via sameShapeSemantics
        have hroot_eq := AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv' hpmi'.uf_wf
            (g''.add ⟨AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds⟩).1
        -- hval' : v' id = NodeEvalM ⟨replaceChildren skelOp childIds⟩ env v'
        -- = evalMixedOp (replaceChildren skelOp childIds) env v'
        -- By sameShapeSemantics: evalMixedOp (replaceChildren skelOp childIds) env v'
        --   = evalMixedOp skelOp env' w (where w maps children to child vals)
        -- Then by per-child values: = Pattern.eval (.node skelOp subpats) constVal (substVal v g.uf σ)
        -- Per-child value agreement: v'(childIds[j]) = v''(childIds[j]) = hchild_vals j
        have hchild_agree : ∀ j (hj : j < subpats.length),
            v' (childIds[j]'(by simp only [List.length_nil, Nat.add_zero] at hgo_len; omega)) =
            MixedEMatchSpec.Pattern.eval (subpats[j]) (fun n => env.constVal n)
              (substVal v g.unionFind σ) := by
          intro j hj
          have hj_bnd : j < childIds.length := by
            simp only [List.length_nil, Nat.add_zero] at hgo_len; omega
          have := hchild_vals j hj
          simp only [List.length_nil, Nat.zero_add] at this
          rw [hagree' (childIds[j]) (hchildIds_bnd _ (List.getElem_mem hj_bnd))]
          exact this
        exact ⟨v', hcv', hpmi',
          AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.add_preserves_shi
            g'' ⟨AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds⟩
            hshi'' hpmi'',
          Nat.le_trans hsize'' hsize',
          fun i hi => (hagree' i (Nat.lt_of_lt_of_le hi hsize'')).trans (hagree'' i hi),
          hid_bnd',
          hroot_eq.trans (hval'.trans (by
            unfold AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.NodeEvalM
            rw [AmoLean.EGraph.VerifiedExtraction.NodeEval]
            simp only [MixedEMatchSpec.Pattern.eval]
            have hss : sameShape skelOp
                (AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds) = true := by
              unfold sameShape
              rw [beq_iff_eq]
              exact (AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren_sameShape
                skelOp childIds hlen_ids).symm
            -- env uniformity: ⟨constVal, constVal, constVal⟩ = env
            have henv_eq : (⟨fun n => env.constVal n, fun n => env.constVal n,
                fun n => env.constVal n⟩ : MixedEnv) = env := by
              cases env with | mk c w p =>
              simp only at henv_w henv_p ⊢; subst henv_w; subst henv_p; rfl
            symm; rw [henv_eq]
            let childVals := subpats.map (fun p =>
              MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n) (substVal v g.unionFind σ))
            exact sameShapeSemantics_holds skelOp
              (AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds)
              env (fun id => match (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).zip
                childVals |>.lookup id with | some val => val | none => 0) v' hss (fun i h₁ h₂ => by
                -- h₁ : i < (ndCh skelOp).length
                -- h₂ : i < (ndCh (replaceChildren skelOp childIds)).length
                -- Goal: w(children(skelOp)[i]) = v'(children(replaceChildren skelOp childIds)[i])
                -- RHS = v'(childIds[i]) (by hch_eq)
                -- LHS = Pattern.eval(subpats[i], ...) (by zip_lookup)
                -- Both equal by hchild_agree
                have hi_ch : i < (AmoLean.EGraph.VerifiedExtraction.NodeOps.children
                    (AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds)).length := h₂
                rw [hch_eq] at hi_ch
                -- v'(ndCh(replaceChildren skelOp childIds)[i]) = v'(childIds[i])
                have : (ndCh (AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp
                    childIds))[i]'h₂ = childIds[i]'hi_ch := by
                  show (AmoLean.EGraph.VerifiedExtraction.NodeOps.children _)[i] = _
                  simp [hch_eq]
                rw [this]
                simp only [ndCh] at h₁ ⊢
                show (match ((AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).zip
                      childVals).lookup
                    ((AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp)[i]) with
                  | some val => val | none => 0) = v' childIds[i]
                have hlen_zip : (AmoLean.EGraph.VerifiedExtraction.NodeOps.children skelOp).length =
                    childVals.length := by
                  show _ = (subpats.map _).length; simp [hlen_eq]
                rw [zip_lookup_nodup _ _ hnodup hlen_zip i h₁]
                show (subpats.map (fun p => MixedEMatchSpec.Pattern.eval p (fun n => env.constVal n)
                  (substVal v g.unionFind σ)))[i]'(by rw [List.length_map]; exact hlen_eq ▸ h₁) = v' childIds[i]
                rw [List.getElem_map]
                exact (hchild_agree i (hlen_eq ▸ h₁)).symm)))⟩

/-- Simpler version: instantiateF just preserves CV+VPMI (no value property).
    Used in applyRuleAtF where we only need CV preservation for the non-merge cases. -/
private theorem instantiateF_preserves (fuel : Nat) (g : MGraph)
    (pat : MixedEMatch.Pattern MixedNodeOp) (σ : MixedEMatch.Substitution)
    (v : CId → Nat) (env : MixedEnv)
    (hcv : CV g env v) (hpmi : VPMI g)
    (hshi : AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.ShapeHashconsInv g)
    (hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size)
    (hwfp : WellFormedPat pat)
    (henv_w : env.witnessVal = env.constVal) (henv_p : env.pubInputVal = env.constVal)
    (id : CId) (g' : MGraph)
    (hinst : MixedEMatch.instantiateF fuel g pat σ = some (id, g')) :
    ∃ v', CV g' env v' ∧ VPMI g' := by
  obtain ⟨v', hcv', hpmi', _, _, _, _, _⟩ := instantiateF_sound fuel g pat σ v env hcv hpmi hshi hbnd_σ hwfp henv_w henv_p id g' hinst
  exact ⟨v', hcv', hpmi'⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 3b: ematchF substitution boundedness
-- ══════════════════════════════════════════════════════════════════

/-- IDs stored via Substitution.extend are bounded when the stored ID is bounded. -/
private theorem extend_bounded (subst : MixedEMatch.Substitution) (pv : MixedEMatch.PatVarId)
    (id : CId) (s : MixedEMatch.Substitution) (bound : Nat)
    (hext : MixedEMatch.Substitution.extend subst pv id = some s)
    (hid : id < bound)
    (hbnd : ∀ pv' id', subst.get? pv' = some id' → id' < bound) :
    ∀ pv' id', s.get? pv' = some id' → id' < bound := by
  intro pv' id' hget
  unfold MixedEMatch.Substitution.extend at hext
  split at hext
  · -- subst.get? pv = none → s = subst.insert pv id
    obtain rfl := Option.some.inj hext
    by_cases h : pv' = pv
    · subst h
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, ↓reduceIte] at hget
      exact Option.some.inj hget ▸ hid
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq] at hget
      split at hget
      · rename_i heq; exfalso; exact h heq.symm
      · exact hbnd pv' id' (by rw [Std.HashMap.get?_eq_getElem?]; exact hget)
  · rename_i existId _ _
    split at hext
    · obtain rfl := Option.some.inj hext; exact hbnd pv' id' hget
    · simp at hext

/-- matchChildren preserves substitution boundedness. -/
private theorem matchChildren_bounded (g : MGraph)
    (n : Nat)
    (ih : ∀ (pat : MixedEMatch.Pattern MixedNodeOp) (classId : CId) (subst σ : MixedEMatch.Substitution),
      σ ∈ MixedEMatch.ematchF n g pat classId subst →
      (∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size) →
      classId < g.unionFind.parent.size →
      ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size)
    (pats : List (MixedEMatch.Pattern MixedNodeOp))
    (nodeChildren : List CId)
    (subst : MixedEMatch.Substitution) (acc : MixedEMatch.MatchResult)
    (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF.matchChildren g n pats nodeChildren subst acc)
    (hnotacc : σ ∉ acc)
    (hbnd_subst : ∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size)
    (hbnd_ch : ∀ c ∈ nodeChildren, c < g.unionFind.parent.size) :
    ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size := by
  induction pats generalizing nodeChildren subst acc σ with
  | nil =>
    cases nodeChildren with
    | nil =>
      simp [MixedEMatch.ematchF.matchChildren, List.mem_append] at hmem
      exact hmem.resolve_left hnotacc ▸ hbnd_subst
    | cons _ _ =>
      exact absurd (by simpa [MixedEMatch.ematchF.matchChildren] using hmem) hnotacc
  | cons p ps ih_pats =>
    cases nodeChildren with
    | nil => exact absurd (by simpa [MixedEMatch.ematchF.matchChildren] using hmem) hnotacc
    | cons c cs =>
      simp only [MixedEMatch.ematchF.matchChildren] at hmem
      exact foldl_sound_predicate
        (fun a s => MixedEMatch.ematchF.matchChildren g n ps cs s a)
        (fun σ' => ∀ pv id, σ'.get? pv = some id → id < g.unionFind.parent.size)
        (MixedEMatch.ematchF n g p c subst)
        (fun acc' s hs_mem σ' hmem_mc hnotacc' =>
          ih_pats cs s acc' σ' hmem_mc hnotacc'
            (ih p c subst s hs_mem hbnd_subst (hbnd_ch c (List.mem_cons.mpr (Or.inl rfl))))
            (fun c' hc' => hbnd_ch c' (List.mem_cons.mpr (Or.inr hc'))))
        acc σ hmem hnotacc

/-- All IDs in substitutions produced by ematchF are bounded by g.uf.parent.size.
    Proved by induction on fuel + pattern structure. -/
private theorem ematchF_subst_bounded (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g)
    (fuel : Nat) (pat : MixedEMatch.Pattern MixedNodeOp)
    (hwfp : WellFormedPat pat)
    (classId : CId) (hclass : classId < g.unionFind.parent.size)
    (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g pat classId)
    (pv : MixedEMatch.PatVarId) (id : CId)
    (hget : σ.get? pv = some id) :
    id < g.unionFind.parent.size := by
  -- Lift to general subst₀ form
  suffices h_gen : ∀ (fuel : Nat) (pat : MixedEMatch.Pattern MixedNodeOp) (classId : CId)
      (subst σ : MixedEMatch.Substitution),
      σ ∈ MixedEMatch.ematchF fuel g pat classId subst →
      (∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size) →
      classId < g.unionFind.parent.size →
      ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size from
    h_gen fuel pat classId MixedEMatch.Substitution.empty σ hmem
      (fun pv' id' h => by
        unfold MixedEMatch.Substitution.empty at h
        rw [Std.HashMap.get?_eq_getElem?] at h
        simp at h)
      hclass pv id hget
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; simp at h
  | succ n ih =>
    intro pat classId subst σ hmem hbnd_subst hclass_bnd
    cases pat with
    | patVar pv =>
      simp only [MixedEMatch.ematchF] at hmem
      split at hmem
      · -- extend succeeded: σ = [s] where extend subst pv (root classId) = some s
        rename_i _ _ hext
        rw [List.mem_singleton] at hmem; subst hmem
        have hroot_bnd := hpmi.uf_wf.root_bounded classId hclass_bnd
        exact extend_bounded subst pv _ _ g.unionFind.parent.size hext hroot_bnd hbnd_subst
      · simp at hmem
    | node skelOp subpats =>
      simp only [MixedEMatch.ematchF] at hmem
      split at hmem
      · simp at hmem
      · rename_i eclass hcls
        have hcls_bnd : ∀ (nd : AmoLean.EGraph.VerifiedExtraction.ENode MixedNodeOp),
            nd ∈ eclass.nodes.toList →
            ∀ c ∈ AmoLean.EGraph.VerifiedExtraction.NodeOps.children nd.op,
            c < g.unionFind.parent.size :=
          fun nd hnd c hc => hpmi.children_bounded
            (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId)
            eclass hcls nd hnd c hc
        -- hmem : σ ∈ Array.foldl ... [] eclass.nodes
        -- Need to convert to List.foldl over eclass.nodes.toList
        rw [← Array.foldl_toList] at hmem
        exact foldl_sound_predicate
          (fun acc (node : AmoLean.EGraph.VerifiedExtraction.ENode MixedNodeOp) =>
            if MixedEMatch.sameShape skelOp node.op = true then
              MixedEMatch.ematchF.matchChildren g n subpats
                (AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op) subst acc
            else acc)
          (fun σ' => ∀ pv id, σ'.get? pv = some id → id < g.unionFind.parent.size)
          eclass.nodes.toList
          (fun acc nd hnd_mem σ' hmem_step hnotacc => by
            simp only [MixedEMatch.sameShape] at hmem_step
            split at hmem_step
            · exact matchChildren_bounded g n ih subpats
                (AmoLean.EGraph.VerifiedExtraction.NodeOps.children nd.op)
                subst acc σ' hmem_step hnotacc hbnd_subst
                (hcls_bnd nd hnd_mem)
            · exact absurd hmem_step hnotacc)
          [] σ hmem (by simp)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Composition layer (applyRuleAtF_preserves_cv)
-- ══════════════════════════════════════════════════════════════════

/-- substVal agrees across graphs when valuations agree on σ's range.
    Key: consistent_root_eq' makes v(root uf id) = v(id), so different UFs give same result. -/
private theorem substVal_agrees_cv (g₁ g₂ : MGraph) (env : MixedEnv)
    (v₁ v₂ : CId → Nat) (σ : MixedEMatch.Substitution)
    (hcv₁ : CV g₁ env v₁) (hcv₂ : CV g₂ env v₂)
    (hwf₁ : g₁.unionFind.WellFormed) (hwf₂ : g₂.unionFind.WellFormed)
    (hbnd : ∀ pv id, σ.get? pv = some id → id < g₁.unionFind.parent.size)
    (hagree : ∀ i, i < g₁.unionFind.parent.size → v₂ i = v₁ i) :
    ∀ pv, substVal v₂ g₂.unionFind σ pv = substVal v₁ g₁.unionFind σ pv := by
  intro pv
  unfold substVal
  split
  · rename_i id hget
    have hid := hbnd pv id hget
    rw [AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv₂ hwf₂ id]
    rw [hagree id hid]
    rw [← AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv₁ hwf₁ id]
  · rfl

/-- Value chain: ematch + PatternSoundRule → RHS eval = v(classId).
    Bridges ematchF_sound + psrule.soundness to merge equality.
    cf. OptiSat EMatchSpec.lean:873-894. -/
private theorem ematch_value_chain (g₀ : MGraph) (env : MixedEnv) (v₀ : CId → Nat)
    (hcv₀ : CV g₀ env v₀) (hpmi₀ : VPMI g₀)
    (henv_w : env.witnessVal = env.constVal) (henv_p : env.pubInputVal = env.constVal)
    (psrule : PatternSoundRule) (fuel : Nat) (classId : CId)
    (hclass : classId < g₀.unionFind.parent.size)
    (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g₀ psrule.rule.lhs classId)
    (hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g₀.unionFind.parent.size)
    -- target graph (may differ from g₀ via adds/merges)
    (g : MGraph) (v : CId → Nat)
    (hcv : CV g env v) (hwf : g.unionFind.WellFormed)
    (hsize : g₀.unionFind.parent.size ≤ g.unionFind.parent.size)
    (hagrees : ∀ i, i < g₀.unionFind.parent.size → v i = v₀ i) :
    MixedEMatchSpec.Pattern.eval psrule.rule.rhs (fun n => env.constVal n) (substVal v₀ g₀.unionFind σ) =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) := by
  have hwf₀ := hpmi₀.uf_wf
  -- Step 1: rhs eval = lhs eval (by psrule.soundness)
  have h_sound := psrule.soundness (fun n => env.constVal n) (substVal v₀ g₀.unionFind σ)
  -- Step 2: lhs eval = v₀(root g₀.uf classId) (by ematchF_sound)
  have h_ematch := ematchF_sound g₀ env v₀ hcv₀ hwf₀ henv_w henv_p fuel
    psrule.rule.lhs classId psrule.wfp_lhs σ hmem
  -- Step 3: v₀(root g₀.uf classId) = v₀(classId) (by consistent_root_eq')
  have h_root₀ := AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv₀ hwf₀ classId
  -- Step 4: v₀(classId) = v(classId) (by hagrees)
  have h_agree := (hagrees classId hclass).symm
  -- Step 5: v(classId) = v(root g.uf classId) (by consistent_root_eq')
  have h_root := (AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv hwf classId).symm
  -- Chain
  rw [← h_sound, h_ematch, h_root₀, h_agree, h_root]

/-- Helper: foldl over ematch results preserves CV. Separate theorem to avoid
    match auxiliary mismatch with applyRuleAtF. -/
private theorem applyRuleAtF_foldl_cv (fuel : Nat) (psrule : PatternSoundRule)
      (classId : CId) (env : MixedEnv)
      (henv_w : env.witnessVal = env.constVal)
      (henv_p : env.pubInputVal = env.constVal)
      (g : MGraph) (v : CId → Nat)
      (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
      (hclass : classId < g.unionFind.parent.size)
      (results : List MixedEMatch.Substitution)
      (hbnd_all : ∀ σ ∈ results, ∀ pv id, σ.get? pv = some id →
        id < g.unionFind.parent.size)
      (hmem_all : ∀ σ ∈ results, σ ∈ MixedEMatch.ematchF fuel g psrule.rule.lhs classId)
      (g₀ : MGraph) (v₀ : CId → Nat)
      (hcv₀ : CV g₀ env v₀) (hpmi₀ : VPMI g₀) (hshi₀ : ShapeHashconsInv g₀)
      (hsize₀ : g.unionFind.parent.size ≤ g₀.unionFind.parent.size)
      (hagree₀ : ∀ i, i < g.unionFind.parent.size → v₀ i = v i) :
      ∃ v', CV (results.foldl (fun acc subst =>
        if (!match psrule.rule.sideCondCheck with
          | some check => check acc subst | none => true) = true then acc
        else match MixedEMatch.instantiateF fuel acc psrule.rule.rhs subst with
          | none => acc
          | some (rhsId, acc') =>
            if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
            then acc' else acc'.merge classId rhsId) g₀) env v' ∧
        VPMI (results.foldl (fun acc subst =>
        if (!match psrule.rule.sideCondCheck with
          | some check => check acc subst | none => true) = true then acc
        else match MixedEMatch.instantiateF fuel acc psrule.rule.rhs subst with
          | none => acc
          | some (rhsId, acc') =>
            if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
            then acc' else acc'.merge classId rhsId) g₀) ∧
        ShapeHashconsInv (results.foldl (fun acc subst =>
        if (!match psrule.rule.sideCondCheck with
          | some check => check acc subst | none => true) = true then acc
        else match MixedEMatch.instantiateF fuel acc psrule.rule.rhs subst with
          | none => acc
          | some (rhsId, acc') =>
            if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
            then acc' else acc'.merge classId rhsId) g₀) := by
    induction results generalizing g₀ v₀ with
    | nil => exact ⟨v₀, hcv₀, hpmi₀, hshi₀⟩
    | cons σ rest ih =>
      simp only [List.foldl]
      have hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g₀.unionFind.parent.size :=
        fun pv id h => Nat.lt_of_lt_of_le
          (hbnd_all σ (List.mem_cons.mpr (Or.inl rfl)) pv id h) hsize₀
      have hbnd_rest : ∀ σ' ∈ rest, ∀ pv id, σ'.get? pv = some id →
          id < g.unionFind.parent.size :=
        fun σ' hmem => hbnd_all σ' (List.mem_cons.mpr (Or.inr hmem))
      have hmem_rest : ∀ σ' ∈ rest, σ' ∈ MixedEMatch.ematchF fuel g psrule.rule.lhs classId :=
        fun σ' hmem => hmem_all σ' (List.mem_cons.mpr (Or.inr hmem))
      have hσ_mem : σ ∈ MixedEMatch.ematchF fuel g psrule.rule.lhs classId :=
        hmem_all σ (List.mem_cons.mpr (Or.inl rfl))
      split_ifs with h_cond
      · exact ih hbnd_rest hmem_rest g₀ v₀ hcv₀ hpmi₀ hshi₀ hsize₀ hagree₀
      · match h_inst : MixedEMatch.instantiateF fuel g₀ psrule.rule.rhs σ with
        | none =>
          simp only [h_inst]
          exact ih hbnd_rest hmem_rest g₀ v₀ hcv₀ hpmi₀ hshi₀ hsize₀ hagree₀
        | some (rhsId, acc') =>
          have ⟨v₁, hcv₁, hpmi₁, hshi₁, hsize₁, hagree₁, hrhsId_bnd, hval₁⟩ :=
            instantiateF_sound fuel g₀ psrule.rule.rhs σ v₀ env hcv₀ hpmi₀ hshi₀
              hbnd_σ psrule.wfp_rhs henv_w henv_p rhsId acc' h_inst
          simp only [h_inst]
          split_ifs with h_roots
          · -- INST-CV: roots equal → step = acc'
            exact ih hbnd_rest hmem_rest acc' v₁ hcv₁ hpmi₁ hshi₁
              (Nat.le_trans hsize₀ hsize₁)
              (fun i hi => (hagree₁ i (Nat.lt_of_lt_of_le hi hsize₀)).trans (hagree₀ i hi))
          · -- MERGE-CV: roots differ
            have hclass_acc : classId < acc'.unionFind.parent.size :=
              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hclass hsize₀) hsize₁
            have hbnd_σ_g : ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size :=
              hbnd_all σ (List.mem_cons.mpr (Or.inl rfl))
            have hagree_chain : ∀ i, i < g.unionFind.parent.size → v₁ i = v i :=
              fun i hi => (hagree₁ i (Nat.lt_of_lt_of_le hi hsize₀)).trans (hagree₀ i hi)
            have hval_eq : v₁ (AmoLean.EGraph.VerifiedExtraction.UnionFind.root acc'.unionFind classId) =
                v₁ (AmoLean.EGraph.VerifiedExtraction.UnionFind.root acc'.unionFind rhsId) := by
              rw [AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv₁ hpmi₁.uf_wf classId]
              rw [hval₁]
              have hvc := ematch_value_chain g env v hcv hpmi henv_w henv_p
                psrule fuel classId hclass σ hσ_mem hbnd_σ_g
                acc' v₁ hcv₁ hpmi₁.uf_wf (Nat.le_trans hsize₀ hsize₁) hagree_chain
              have hsva : ∀ pv, substVal v₀ g₀.unionFind σ pv = substVal v g.unionFind σ pv :=
                substVal_agrees_cv g g₀ env v v₀ σ hcv hcv₀ hpmi.uf_wf hpmi₀.uf_wf
                  hbnd_σ_g hagree₀
              conv_rhs => rw [show (substVal v₀ g₀.unionFind σ) = (substVal v g.unionFind σ) from
                funext hsva]
              rw [hvc, AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv₁ hpmi₁.uf_wf]
            have hcv_merge := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.merge_consistent
              acc' classId rhsId env v₁ hcv₁ hpmi₁ hclass_acc hrhsId_bnd hval_eq
            have hpmi_merge := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.merge_preserves_pmi
              acc' classId rhsId hpmi₁ hclass_acc hrhsId_bnd
            have hshi_merge := AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.merge_preserves_shi
              acc' classId rhsId hshi₁
            have hsize_merge : acc'.unionFind.parent.size ≤
                (acc'.merge classId rhsId).unionFind.parent.size :=
              Nat.le_of_eq (AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.merge_uf_size
                acc' classId rhsId).symm
            exact ih hbnd_rest hmem_rest (acc'.merge classId rhsId) v₁
              hcv_merge hpmi_merge hshi_merge
              (Nat.le_trans (Nat.le_trans hsize₀ hsize₁) hsize_merge)
              (fun i hi => (hagree₁ i (Nat.lt_of_lt_of_le hi hsize₀)).trans (hagree₀ i hi))

/-- Bridge lemma: applyRuleAtF equals an explicit foldl (resolves match auxiliary mismatch). -/
private theorem applyRuleAtF_eq_foldl (fuel : Nat) (classId : CId)
    (g : MGraph) (rule : MixedEMatch.RewriteRule MixedNodeOp) :
    MixedSaturation.applyRuleAtF fuel g rule classId =
    (MixedEMatch.ematchF fuel g rule.lhs classId).foldl (fun acc subst =>
      if (!match rule.sideCondCheck with
        | some check => check acc subst | none => true) = true then acc
      else match MixedEMatch.instantiateF fuel acc rule.rhs subst with
        | none => acc
        | some (rhsId, acc') =>
          if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
          then acc' else acc'.merge classId rhsId) g := by
  simp only [MixedSaturation.applyRuleAtF]
  congr 1; funext acc subst
  cases rule.sideCondCheck with
  | none =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases MixedEMatch.instantiateF fuel acc rule.rhs subst with
    | none => rfl
    | some p => cases p; rfl
  | some check =>
    simp only
    split <;> try rfl
    cases MixedEMatch.instantiateF fuel acc rule.rhs subst with
    | none => rfl
    | some p => cases p; rfl

/-- Applying a sound rewrite rule at a specific class preserves ConsistentValuation.
    Decomposed via L-391: ematchF_sound + InstantiateEvalSound + merge_consistent.
    cf. OptiSat EMatchSpec.lean:985-1085. -/
theorem applyRuleAtF_preserves_cv (fuel : Nat) (psrule : PatternSoundRule)
    (classId : CId) (env : MixedEnv)
    (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal) :
    ∀ (g : MGraph) (v : CId → Nat),
      CV g env v → VPMI g → ShapeHashconsInv g →
      classId < g.unionFind.parent.size →
      ∃ v', CV (MixedSaturation.applyRuleAtF fuel g psrule.rule classId) env v' ∧
        VPMI (MixedSaturation.applyRuleAtF fuel g psrule.rule classId) ∧
        ShapeHashconsInv (MixedSaturation.applyRuleAtF fuel g psrule.rule classId) := by
  intro g v hcv hpmi hshi hclass
  rw [applyRuleAtF_eq_foldl]
  exact applyRuleAtF_foldl_cv fuel psrule classId env henv_w henv_p g v hcv hpmi hshi hclass
    (MixedEMatch.ematchF fuel g psrule.rule.lhs classId)
    (fun σ hmem => ematchF_subst_bounded g env v hcv hpmi fuel psrule.rule.lhs
      psrule.wfp_lhs classId hclass σ hmem)
    (fun σ hmem => hmem)
    g v hcv hpmi hshi (Nat.le_refl _) (fun _ _ => rfl)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: applyRulesF_preserves_cv
-- ══════════════════════════════════════════════════════════════════

/-- instantiateF preserves UF size (graph only grows). -/
private theorem instantiateF_size_le (fuel : Nat) (g : MGraph)
    (pat : MixedEMatch.Pattern MixedNodeOp) (σ : MixedEMatch.Substitution) :
    ∀ id g', MixedEMatch.instantiateF fuel g pat σ = some (id, g') →
    g.unionFind.parent.size ≤ g'.unionFind.parent.size := by
  induction fuel generalizing g pat with
  | zero => intro _ _ h; simp [MixedEMatch.instantiateF] at h
  | succ n ih =>
    intro id g' h
    cases pat with
    | patVar pv =>
      simp only [MixedEMatch.instantiateF, MixedEMatch.Substitution.lookup] at h
      split at h
      · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact Nat.le_refl _
      · simp at h
    | node skelOp subpats =>
      simp only [MixedEMatch.instantiateF] at h
      split at h
      · simp at h
      · rename_i childIds g'' hgo
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact Nat.le_trans (go_size_le n σ subpats g [] childIds g'' hgo ih)
          (AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.add_size_le g''
            ⟨AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds⟩)
where
  go_size_le (n : Nat) (σ : MixedEMatch.Substitution)
      (pats : List (MixedEMatch.Pattern MixedNodeOp))
      (g₀ : MGraph) (ids₀ childIds : List CId) (g_final : MGraph)
      (hgo : MixedEMatch.instantiateF.go σ n g₀ pats ids₀ = some (childIds, g_final))
      (ih_fuel : ∀ (g : MGraph) (pat : MixedEMatch.Pattern MixedNodeOp)
        (id : CId) (g' : MGraph),
        MixedEMatch.instantiateF n g pat σ = some (id, g') →
        g.unionFind.parent.size ≤ g'.unionFind.parent.size) :
      g₀.unionFind.parent.size ≤ g_final.unionFind.parent.size := by
    induction pats generalizing g₀ ids₀ with
    | nil =>
      simp [MixedEMatch.instantiateF.go] at hgo
      obtain ⟨_, rfl⟩ := hgo; exact Nat.le_refl _
    | cons p ps ih_go =>
      simp only [MixedEMatch.instantiateF.go] at hgo
      split at hgo
      · simp at hgo
      · rename_i cid g1 h_eq
        exact Nat.le_trans (ih_fuel g₀ p cid g1 h_eq) (ih_go g1 (cid :: ids₀) hgo)

/-- applyRuleAtF preserves UF size (graph only grows). -/
private theorem applyRuleAtF_size_le (fuel : Nat) (rule : MixedEMatch.RewriteRule MixedNodeOp)
    (classId : CId) (g : MGraph) :
    g.unionFind.parent.size ≤ (MixedSaturation.applyRuleAtF fuel g rule classId).unionFind.parent.size := by
  unfold MixedSaturation.applyRuleAtF; simp only []
  generalize MixedEMatch.ematchF fuel g rule.lhs classId = results
  induction results generalizing g with
  | nil => exact Nat.le_refl _
  | cons σ rest ih =>
    simp only [List.foldl]
    apply Nat.le_trans _ (ih _)
    split_ifs with h_cond
    · exact Nat.le_refl _
    · match h_inst : MixedEMatch.instantiateF fuel g rule.rhs σ with
      | none => exact Nat.le_refl _
      | some (rhsId, acc') =>
        simp only [h_inst]
        split_ifs
        · exact instantiateF_size_le fuel g rule.rhs σ rhsId acc' h_inst
        · exact Nat.le_trans (instantiateF_size_le fuel g rule.rhs σ rhsId acc' h_inst)
            (Nat.le_of_eq (AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.merge_uf_size _ _ _).symm)

/-- Helper: applying a single rule across all classes preserves CV. -/
private theorem applyRuleF_preserves_cv (fuel : Nat) (psrule : PatternSoundRule)
    (env : MixedEnv) (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal) :
    PreservesCV env (fun g => MixedSaturation.applyRuleF fuel g psrule.rule) := by
  intro g v hcv hpmi hshi
  unfold MixedSaturation.applyRuleF
  suffices ∀ (classIds : List CId)
      (hbnd_cls : ∀ c ∈ classIds, c < g.unionFind.parent.size)
      (g₀ : MGraph) (v₀ : CId → Nat),
      CV g₀ env v₀ → VPMI g₀ → ShapeHashconsInv g₀ →
      g.unionFind.parent.size ≤ g₀.unionFind.parent.size →
      ∃ v', CV (classIds.foldl (fun acc cid =>
        MixedSaturation.applyRuleAtF fuel acc psrule.rule cid) g₀) env v' ∧
        VPMI (classIds.foldl (fun acc cid =>
          MixedSaturation.applyRuleAtF fuel acc psrule.rule cid) g₀) ∧
        ShapeHashconsInv (classIds.foldl (fun acc cid =>
          MixedSaturation.applyRuleAtF fuel acc psrule.rule cid) g₀) by
    refine this (g.classes.toList.map (·.1)) ?_ g v hcv hpmi hshi (Nat.le_refl _)
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨⟨k, v_cls⟩, hkv, rfl⟩ := hc
    -- hkv : (k, v_cls) ∈ g.classes.toList → g.classes.contains k
    have hcontains : g.classes.contains k = true := by
      rw [← Bool.not_eq_false]; intro hfalse
      rw [← Std.HashMap.find?_toList_eq_none_iff_contains_eq_false] at hfalse
      exact absurd ((List.find?_eq_none.mp hfalse) (k, v_cls) hkv) (by simp)
    exact hpmi.classes_entries_valid k hcontains
  intro classIds hbnd_cls
  induction classIds with
  | nil => intro g₀ v₀ hcv₀ hpmi₀ hshi₀ _; exact ⟨v₀, hcv₀, hpmi₀, hshi₀⟩
  | cons hd tl ih =>
    intro g₀ v₀ hcv₀ hpmi₀ hshi₀ hsize₀
    simp only [List.foldl]
    have hhd := Nat.lt_of_lt_of_le (hbnd_cls hd (List.mem_cons.mpr (Or.inl rfl))) hsize₀
    obtain ⟨v₁, hcv₁, hpmi₁, hshi₁⟩ :=
      applyRuleAtF_preserves_cv fuel psrule hd env henv_w henv_p g₀ v₀ hcv₀ hpmi₀ hshi₀ hhd
    exact ih (fun c hc => hbnd_cls c (List.mem_cons.mpr (Or.inr hc))) _ v₁ hcv₁ hpmi₁ hshi₁
      (Nat.le_trans hsize₀ (applyRuleAtF_size_le fuel psrule.rule hd g₀))

/-- map/foldl conversion: (rules.map f).foldl step = rules.foldl (step . f). -/
private theorem applyRulesF_foldl_eq (fuel : Nat) (rules : List PatternSoundRule)
    (g : MGraph) :
    MixedSaturation.applyRulesF fuel g (rules.map (·.rule)) =
    rules.foldl (fun acc r => MixedSaturation.applyRuleF fuel acc r.rule) g := by
  unfold MixedSaturation.applyRulesF
  induction rules generalizing g with
  | nil => rfl
  | cons hd tl ih => simp only [List.map, List.foldl]; exact ih _

/-- Applying a list of sound rewrite rules preserves ConsistentValuation.
    Composes applyRuleF_preserves_cv for each rule in the list. -/
theorem applyRulesF_preserves_cv (fuel : Nat) (rules : List PatternSoundRule)
    (env : MixedEnv) (henv_w : env.witnessVal = env.constVal)
    (henv_p : env.pubInputVal = env.constVal) :
    PreservesCV env (fun g => MixedSaturation.applyRulesF fuel g (rules.map (·.rule))) := by
  intro g v hcv hpmi hshi
  show ∃ v', CV (MixedSaturation.applyRulesF fuel g (rules.map (·.rule))) env v' ∧
    VPMI (MixedSaturation.applyRulesF fuel g (rules.map (·.rule))) ∧
    ShapeHashconsInv (MixedSaturation.applyRulesF fuel g (rules.map (·.rule)))
  rw [applyRulesF_foldl_eq]
  induction rules generalizing g v with
  | nil => exact ⟨v, hcv, hpmi, hshi⟩
  | cons hd tl ih =>
    simp only [List.foldl]
    obtain ⟨v₁, hcv₁, hpmi₁, hshi₁⟩ := applyRuleF_preserves_cv fuel hd env henv_w henv_p g v hcv hpmi hshi
    exact ih _ v₁ hcv₁ hpmi₁ hshi₁

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests — non-vacuity
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: SameShapeSemantics for concrete addGate. -/
example : evalMixedOp (.addGate 0 1)
    ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ (fun i => if i == 0 then 3 else 5) =
  evalMixedOp (.addGate 2 3)
    ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ (fun i => if i == 2 then 3 else 5) := by
  native_decide

/-- Non-vacuity: SameShapeSemantics for concrete bitAnd. -/
example : evalMixedOp (.bitAnd 0 1)
    ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ (fun i => if i == 0 then 15 else 7) =
  evalMixedOp (.bitAnd 10 20)
    ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ (fun i => if i == 10 then 15 else 7) := by
  native_decide

/-- Non-vacuity: sameShape holds for addGate variants. -/
example : sameShape (.addGate 0 1) (.addGate 5 6) = true := by native_decide

/-- Non-vacuity: sameShape rejects different constructors. -/
example : sameShape (.addGate 0 1) (.mulGate 0 1) = false := by native_decide

/-- Non-vacuity: PatternSoundRule structure is inhabited (trivial rule). -/
example : PatternSoundRule where
  rule := { name := "id", lhs := .patVar 0, rhs := .patVar 0 }
  soundness := fun _ _ => rfl
  wfp_lhs := by unfold WellFormedPat; trivial
  wfp_rhs := by unfold WellFormedPat; trivial

end AmoLean.EGraph.Verified.Bitwise.MixedEMatchSoundness
