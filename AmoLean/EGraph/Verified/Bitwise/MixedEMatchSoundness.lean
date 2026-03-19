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
-- Section 2: PatternSoundRule
-- ══════════════════════════════════════════════════════════════════

/-- A pattern-based rewrite rule with a soundness proof.
    The rule is sound if for all environments and pattern variable assignments,
    evaluating the LHS and RHS patterns produces the same value.
    Uses Pattern.eval from MixedEMatchSpec. -/
structure PatternSoundRule where
  rule : RewriteRule MixedNodeOp
  soundness : ∀ (env : Nat → Nat) (σ : PatVarId → Nat),
    MixedEMatchSpec.Pattern.eval rule.lhs env σ =
    MixedEMatchSpec.Pattern.eval rule.rhs env σ

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

/-- ematchF soundness: for any substitution σ from ematchF, the LHS pattern evaluates
    to the matched class's value. Deep inductive proof on fuel + Pattern.
    cf. OptiSat EMatchSpec.lean:453-462. -/
theorem ematchF_sound (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (fuel : Nat) (pat : MixedEMatch.Pattern MixedNodeOp) (classId : CId)
    (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g pat classId) :
    MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) := by
  sorry /- EMATCH-SOUND: induction on fuel + Pattern structure.
    patVar: σ extends with canonId → substVal returns v(root(canonId)) = v(root(classId)).
    patNode: iterate over class nodes, sameShape matching, recurse on children.
    ~200 LOC. cf. OptiSat EMatchSpec.lean:350-462. -/

/-- InstantiateEvalSound: instantiateF preserves CV and the new node's value
    matches the pattern evaluation. Proved by induction on Pattern + add_node_consistent.
    cf. OptiSat EMatchSpec.lean:509-527. -/
theorem instantiateF_sound (fuel : Nat) (g : MGraph) (pat : MixedEMatch.Pattern MixedNodeOp)
    (σ : MixedEMatch.Substitution) (v : CId → Nat) (env : MixedEnv)
    (hcv : CV g env v) (hpmi : VPMI g)
    (hshi : AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.ShapeHashconsInv g)
    (hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size)
    (id : CId) (g' : MGraph)
    (hinst : MixedEMatch.instantiateF fuel g pat σ = some (id, g')) :
    ∃ v', CV g' env v' ∧ VPMI g' ∧
      AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.ShapeHashconsInv g' ∧
      g.unionFind.parent.size ≤ g'.unionFind.parent.size ∧
      (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
      v' (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g'.unionFind id) =
        MixedEMatchSpec.Pattern.eval pat (fun n => env.constVal n) (substVal v g.unionFind σ) := by
  -- Induction on fuel
  induction fuel generalizing g v id g' with
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
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hinst)
        exact ⟨v, hcv, hpmi, hshi, Nat.le_refl _, fun _ _ => rfl, by
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
        -- Step 1: go preserves CV (need auxiliary lemma about go using ih)
        -- Step 2: add_node_consistent for the final g''.add
        -- For now, thread through: go gives g'' with CV, then add gives final result
        -- go_sound: auxiliary for go (induction on subpats)
        -- go calls instantiateF n (reduced fuel) → ih applies
        have go_cv : ∃ v'', CV g'' env v'' ∧ VPMI g'' ∧
            AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.ShapeHashconsInv g'' ∧
            g.unionFind.parent.size ≤ g''.unionFind.parent.size ∧
            (∀ i, i < g.unionFind.parent.size → v'' i = v i) := by
          sorry /- GO-CV: induction on subpats. Base ([]): go returns (ids.reverse, g) → CV unchanged.
            Step (p :: ps): instantiateF n g p σ = some (childId, g₁) → ih gives CV for g₁ →
            go g₁ ps ... → IH on ps gives CV for g''. Thread size + agreement. -/
        obtain ⟨v'', hcv'', hpmi'', hshi'', hsize'', hagree''⟩ := go_cv
        -- Step 2: add_node_consistent for g''.add(replaceChildren skelOp childIds)
        obtain ⟨v', hcv', hpmi', hval', _, hsize', hagree'⟩ :=
          AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.add_node_consistent
            g'' ⟨AmoLean.EGraph.VerifiedExtraction.NodeOps.replaceChildren skelOp childIds⟩
            env v'' hcv'' hpmi'' hshi'' (by sorry /- CHILDREN-BND: childIds bounded by g''.uf.size -/)
        exact ⟨v', hcv', hpmi',
          sorry /- SHI': ShapeHashconsInv preserved by add -/,
          Nat.le_trans hsize'' hsize',
          fun i hi => (hagree' i (Nat.lt_of_lt_of_le hi hsize'')).trans (hagree'' i hi),
          sorry /- VALUE: v'(root id) = Pattern.eval(.node skelOp subpats, ...) -/⟩

/-- Simpler version: instantiateF just preserves CV+VPMI (no value property).
    Used in applyRuleAtF where we only need CV preservation for the non-merge cases. -/
private theorem instantiateF_preserves (fuel : Nat) (g : MGraph)
    (pat : MixedEMatch.Pattern MixedNodeOp) (σ : MixedEMatch.Substitution)
    (v : CId → Nat) (env : MixedEnv)
    (hcv : CV g env v) (hpmi : VPMI g)
    (hshi : AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple.ShapeHashconsInv g)
    (hbnd_σ : ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size)
    (id : CId) (g' : MGraph)
    (hinst : MixedEMatch.instantiateF fuel g pat σ = some (id, g')) :
    ∃ v', CV g' env v' ∧ VPMI g' := by
  -- Derive from the full version
  obtain ⟨v', hcv', hpmi', _, _, _, _⟩ := instantiateF_sound fuel g pat σ v env hcv hpmi hshi hbnd_σ id g' hinst
  exact ⟨v', hcv', hpmi'⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Composition layer (applyRuleAtF_preserves_cv)
-- ══════════════════════════════════════════════════════════════════

/-- Value chain: ematch + PatternSoundRule → RHS eval = v(classId).
    Bridges ematchF_sound + psrule.soundness to merge equality.
    cf. OptiSat EMatchSpec.lean:873-894. -/
private theorem ematch_value_chain (g₀ g : MGraph) (env : MixedEnv) (v₀ v : CId → Nat)
    (hcv₀ : CV g₀ env v₀) (hcv : CV g env v)
    (hwf₀ : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g₀.unionFind)
    (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (hagrees : ∀ i, i < g₀.unionFind.parent.size → v i = v₀ i)
    (psrule : PatternSoundRule) (fuel : Nat) (classId : CId)
    (hclass : classId < g₀.unionFind.parent.size)
    (σ : MixedEMatch.Substitution)
    (hmem : σ ∈ MixedEMatch.ematchF fuel g₀ psrule.rule.lhs classId) :
    MixedEMatchSpec.Pattern.eval psrule.rule.rhs (fun n => env.constVal n) (substVal v g.unionFind σ) =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) := by
  sorry /- VALUE-CHAIN: calc chain.
    rhs eval = rhs eval (substVal v₀ g₀.uf σ)  [by substVal_agrees]
    = lhs eval (substVal v₀ g₀.uf σ)            [by psrule.soundness.symm]
    = v₀(root g₀.uf classId)                    [by ematchF_sound]
    = v₀(classId)                                [by consistent_root_eq']
    = v(classId)                                 [by hagrees.symm]
    = v(root g.uf classId)                       [by consistent_root_eq'.symm]
    ~15 LOC once substVal_agrees is proved. -/

/-- Applying a sound rewrite rule at a specific class preserves ConsistentValuation.
    Decomposed via L-391: ematchF_sound + InstantiateEvalSound + merge_consistent.
    cf. OptiSat EMatchSpec.lean:985-1085. -/
theorem applyRuleAtF_preserves_cv (fuel : Nat) (psrule : PatternSoundRule)
    (classId : CId) (env : MixedEnv) :
    PreservesCV env (fun g => MixedSaturation.applyRuleAtF fuel g psrule.rule classId) := by
  intro g v hcv hpmi
  unfold MixedSaturation.applyRuleAtF
  simp only []  -- zeta-reduce let-bindings (L-676)
  generalize MixedEMatch.ematchF fuel g psrule.rule.lhs classId = results
  -- Thread CV through foldl via ProofKit pattern (foldl_inv_extends)
  -- Invariant: ∃ v', CV g' env v' ∧ VPMI g'
  revert g v
  induction results with
  | nil => intro g v hcv hpmi; exact ⟨v, hcv, hpmi⟩
  | cons σ rest ih =>
    intro g₀ v₀ hcv₀ hpmi₀
    simp only [List.foldl]
    -- Case split: condMet → instantiateF → root equality
    -- Each branch: either unchanged (use v₀) or needs instantiateF/merge sorry
    -- split_ifs handles all if-then-else branches and reduces ite
    split_ifs with h_cond h_inst h_roots
    -- Branch 1: condMet false → graph unchanged
    · exact ih _ v₀ hcv₀ hpmi₀
    -- Branch 2: condMet true, instantiateF = none → graph unchanged
    · -- condMet true: match on instantiateF result
      -- L-574: use match in tactic mode to reduce the match expression
      match h_inst : MixedEMatch.instantiateF fuel g₀ psrule.rule.rhs σ with
      | none =>
        -- instantiateF = none → g₀ unchanged
        exact ih _ v₀ hcv₀ hpmi₀
      | some (rhsId, acc') =>
        -- instantiateF = some → acc' is the new graph
        split
        · -- roots equal → acc' has CV from instantiateF_sound, feed into ih
          sorry /- INST-CV: instantiateF_sound gives CV for acc', then ih for rest -/
        · sorry /- MERGE-CV: instantiateF_sound + value chain + merge_consistent + ih -/

-- ══════════════════════════════════════════════════════════════════
-- Section 4: applyRulesF_preserves_cv
-- ══════════════════════════════════════════════════════════════════

/-- Helper: applying a single rule across all classes preserves CV. -/
private theorem applyRuleF_preserves_cv (fuel : Nat) (psrule : PatternSoundRule)
    (env : MixedEnv) :
    PreservesCV env (fun g => MixedSaturation.applyRuleF fuel g psrule.rule) := by
  intro g v hcv hpmi
  -- applyRuleF = foldl of applyRuleAtF over all class IDs
  unfold MixedSaturation.applyRuleF
  -- We need to show: foldl (fun acc cid => applyRuleAtF fuel acc rule cid) g allClasses
  -- preserves CV. This follows by induction on the class list.
  suffices ∀ (classIds : List CId) (g₀ : MGraph) (v₀ : CId → Nat),
      CV g₀ env v₀ → VPMI g₀ →
      ∃ v', CV (classIds.foldl (fun acc cid =>
        MixedSaturation.applyRuleAtF fuel acc psrule.rule cid) g₀) env v' ∧
        VPMI (classIds.foldl (fun acc cid =>
          MixedSaturation.applyRuleAtF fuel acc psrule.rule cid) g₀) by
    obtain ⟨v', hcv', hpmi'⟩ := this _ g v hcv hpmi
    exact ⟨v', hcv', hpmi'⟩
  intro classIds
  induction classIds with
  | nil => intro g₀ v₀ hcv₀ hpmi₀; exact ⟨v₀, hcv₀, hpmi₀⟩
  | cons hd tl ih =>
    intro g₀ v₀ hcv₀ hpmi₀
    simp only [List.foldl]
    -- Each step preserves CV by applyRuleAtF_preserves_cv at the specific classId
    obtain ⟨v₁, hcv₁, hpmi₁⟩ := applyRuleAtF_preserves_cv fuel psrule hd env g₀ v₀ hcv₀ hpmi₀
    exact ih _ v₁ hcv₁ hpmi₁

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
    (env : MixedEnv) :
    PreservesCV env (fun g => MixedSaturation.applyRulesF fuel g (rules.map (·.rule))) := by
  intro g v hcv hpmi
  -- Convert to foldl over PatternSoundRules
  show ∃ v', CV (MixedSaturation.applyRulesF fuel g (rules.map (·.rule))) env v' ∧
    VPMI (MixedSaturation.applyRulesF fuel g (rules.map (·.rule)))
  rw [applyRulesF_foldl_eq]
  -- Induction on rules list
  induction rules generalizing g v with
  | nil => exact ⟨v, hcv, hpmi⟩
  | cons hd tl ih =>
    simp only [List.foldl]
    obtain ⟨v₁, hcv₁, hpmi₁⟩ := applyRuleF_preserves_cv fuel hd env g v hcv hpmi
    exact ih _ v₁ hcv₁ hpmi₁

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

end AmoLean.EGraph.Verified.Bitwise.MixedEMatchSoundness
