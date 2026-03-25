/-
  AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec — Semantic soundness for MixedNodeOp EGraph

  B61 (CRITICO): Proves merge_consistent for VerifiedExtraction.EGraph MixedNodeOp.
  Key theorem: merging two classes with equal values preserves ConsistentValuation.

  Simplification vs OptiSat: no path compression, no processClass, no rebuild needed.
  The VerifiedExtraction EGraph only needs merge + add for the soundness chain.

  Deliverables:
  - merge_consistent: merge preserves ConsistentValuation when values are equal
  - PreservesCV predicate + foldl combinator
-/
import AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)

-- Re-export abbreviations from MixedCoreSpec
open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec
  (MGraph MNode MClass MUF CId UFWF ufRoot ndChildren
   merge_hashcons merge_uf_size)

-- Qualified names for VerifiedExtraction types to avoid Verified.* collisions
abbrev CV := @AmoLean.EGraph.VerifiedExtraction.ConsistentValuation
  MixedNodeOp MixedEnv Nat _ _ _ _
abbrev VPMI := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.PostMergeInvariant

-- ══════════════════════════════════════════════════════════════════
-- Section 1: merge_consistent — THE key theorem
-- ══════════════════════════════════════════════════════════════════

/-- merge preserves ConsistentValuation when the merged classes have equal values.
    The same valuation v works for the merged graph.

    Proof sketch (from OptiSat SemanticSpec.lean, simplified):
    - Part 1 (UF-consistency): after union(root1, root2), any two IDs with the same
      new root must have had old roots in {root1, root2} or the same old root.
      Since v(root1) = v(root2) by heq, v(i) = v(j).
    - Part 2 (Node-consistency): if classId = root1, the merged class has nodes from
      both old classes; otherwise the class is unchanged. -/
theorem merge_consistent (g : MGraph) (id1 id2 : CId)
    (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hswf : VPMI g)
    (h1 : id1 < g.unionFind.parent.size) (h2 : id2 < g.unionFind.parent.size)
    (heq : v (ufRoot g.unionFind id1) = v (ufRoot g.unionFind id2)) :
    CV (g.merge id1 id2) env v := by
  unfold AmoLean.EGraph.VerifiedExtraction.EGraph.merge
  dsimp only
  split
  · exact hcv
  · -- Different roots case
    rename_i hne_beq
    constructor
    · -- Part 1: UF-consistency via union_root_cases
      intro i j hij
      have hwf := hcv.equiv_same_val
      have hv_root := fun k => AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv
        (AmoLean.EGraph.Verified.Bitwise.MixedUnionFind.strongWF_implies_UFWF hswf.uf_swf) k
      rw [← hv_root i, ← hv_root j]
      -- Use union_root_cases for i and j
      have hurc := AmoLean.EGraph.Verified.Bitwise.MixedUnionFind.union_root_cases
      rcases hurc g.unionFind (ufRoot g.unionFind id1) (ufRoot g.unionFind id2) i
        hswf.uf_swf (hswf.uf_wf.root_bounded id1 h1) (hswf.uf_wf.root_bounded id2 h2)
        with hi | ⟨hi_new, hi_old⟩ <;>
      rcases hurc g.unionFind (ufRoot g.unionFind id1) (ufRoot g.unionFind id2) j
        hswf.uf_swf (hswf.uf_wf.root_bounded id1 h1) (hswf.uf_wf.root_bounded id2 h2)
        with hj | ⟨hj_new, hj_old⟩
      · -- Both unchanged
        rw [hi, hj] at hij; exact congrArg v hij
      · -- i unchanged, j redirected
        rw [hi, hj_new] at hij
        rw [hij, hswf.uf_wf.root_idempotent id1 h1, hj_old,
            hswf.uf_wf.root_idempotent id2 h2]; exact heq
      · -- i redirected, j unchanged
        rw [hi_new, hj] at hij
        rw [hi_old, hswf.uf_wf.root_idempotent id2 h2,
            ← hij, hswf.uf_wf.root_idempotent id1 h1]; exact heq.symm
      · -- Both redirected to r1
        rw [hi_old, hswf.uf_wf.root_idempotent id2 h2,
            hj_old, hswf.uf_wf.root_idempotent id2 h2]
    · -- Part 2: Node-consistency in merged classes
      intro classId eclass hcls node hmem
      have hne : ufRoot g.unionFind id1 ≠ ufRoot g.unionFind id2 := by
        intro h; exact hne_beq (beq_iff_eq.mpr h)
      by_cases hid : g.unionFind.root id1 = classId
      · -- classId = root1: eclass is the merged class
        subst hid
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          beq_self_eq_true, ite_true] at hcls
        have hcls_eq := Option.some.inj hcls
        rw [← hcls_eq] at hmem
        -- node comes from root1's old class or root2's old class
        have hmem_union := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.eclass_union_mem
          _ _ node hmem
        rcases hmem_union with hmem1 | hmem2
        · -- node from root1's old class
          rw [← Std.HashMap.get?_eq_getElem?] at hmem1
          cases hc1 : g.classes.get? (g.unionFind.root id1) with
          | none => rw [hc1, show (none : Option MClass).getD default = default from rfl] at hmem1
                    exact absurd hmem1 (by simp [show (default : MClass).nodes = #[] from rfl])
          | some c1 =>
            rw [hc1, show (some c1).getD default = c1 from rfl] at hmem1
            exact hcv.node_consistent _ c1 hc1 node hmem1
        · -- node from root2's old class: evaluates to v(root2) = v(root1) = v(classId)
          rw [← Std.HashMap.get?_eq_getElem?] at hmem2
          cases hc2 : g.classes.get? (g.unionFind.root id2) with
          | none => rw [hc2, show (none : Option MClass).getD default = default from rfl] at hmem2
                    exact absurd hmem2 (by simp [show (default : MClass).nodes = #[] from rfl])
          | some c2 =>
            rw [hc2, show (some c2).getD default = c2 from rfl] at hmem2
            rw [hcv.node_consistent _ c2 hc2 node hmem2]
            exact heq.symm
      · -- classId ≠ root1: class is unchanged from g
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          show (g.unionFind.root id1 == classId) = false from
            beq_eq_false_iff_ne.mpr hid] at hcls
        exact hcv.node_consistent classId eclass
          (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls) node hmem

-- ══════════════════════════════════════════════════════════════════
-- Section 2: PreservesCV predicate + combinators
-- ══════════════════════════════════════════════════════════════════

-- Re-export ShapeHashconsInv from MixedCoreSpec
abbrev ShapeHashconsInv := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.ShapeHashconsInv

/-- A step function preserves the consistency triple (CV + VPMI + SHI).
    This is the composability property for the saturation pipeline. -/
def PreservesCV (env : MixedEnv) (step : MGraph → MGraph) : Prop :=
  ∀ (g : MGraph) (v : CId → Nat),
    CV g env v → VPMI g → ShapeHashconsInv g →
    ∃ v', CV (step g) env v' ∧ VPMI (step g) ∧ ShapeHashconsInv (step g)

/-- Composition: if step1 and step2 preserve CV, so does step2 ∘ step1. -/
theorem comp_preserves_cv (env : MixedEnv) (step1 step2 : MGraph → MGraph)
    (h1 : PreservesCV env step1) (h2 : PreservesCV env step2) :
    PreservesCV env (step2 ∘ step1) := by
  intro g v hcv hpmi hshi
  obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h1 g v hcv hpmi hshi
  obtain ⟨v2, hcv2, hpmi2, hshi2⟩ := h2 (step1 g) v1 hcv1 hpmi1 hshi1
  exact ⟨v2, hcv2, hpmi2, hshi2⟩

/-- Identity preserves CV trivially. -/
theorem id_preserves_cv (env : MixedEnv) : PreservesCV env id := by
  intro g v hcv hpmi hshi; exact ⟨v, hcv, hpmi, hshi⟩

/-- foldl with PreservesCV steps preserves CV. -/
theorem foldl_preserves_cv (env : MixedEnv) (steps : List (MGraph → MGraph))
    (g : MGraph) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
    (hall : ∀ s ∈ steps, PreservesCV env s) :
    ∃ v', CV (steps.foldl (fun acc s => s acc) g) env v' := by
  induction steps generalizing g v with
  | nil => exact ⟨v, hcv⟩
  | cons hd tl ih =>
    simp only [List.foldl]
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := hall hd (List.Mem.head _) g v hcv hpmi hshi
    exact ih (hd g) v1 hcv1 hpmi1 hshi1 (fun s hs => hall s (List.mem_cons_of_mem _ hs))

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: PreservesCV is composable. -/
example : PreservesCV
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    id :=
  id_preserves_cv _

end AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec
