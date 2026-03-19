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
-- Section 3: applyRuleAtF_preserves_cv (sorry'd)
-- ══════════════════════════════════════════════════════════════════

/-- Applying a sound rewrite rule at a specific class preserves ConsistentValuation.
    This is the core soundness lemma for the e-matching pipeline.

    Sorry'd because the proof requires:
    - ematchF soundness: matched substitutions map pattern vars to class values
    - instantiateF soundness: the RHS evaluates to the same value as the LHS
    - merge_consistent: merging LHS and RHS classes preserves CV
    - foldl composition: iterating over all substitutions preserves the triple

    These are complex inductive proofs over the fuel parameter. -/
theorem applyRuleAtF_preserves_cv (fuel : Nat) (psrule : PatternSoundRule)
    (classId : CId) (env : MixedEnv) :
    PreservesCV env (fun g => MixedSaturation.applyRuleAtF fuel g psrule.rule classId) := by
  sorry

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
