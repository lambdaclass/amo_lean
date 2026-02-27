/-
  AMO-Lean — Saturation Specification
  Fase 11 N11.3: Saturation soundness + fuel-based spec functions.

  Key components:
  - `processClass_shi_combined`: SHI + merge validity through processClass
  - `processAll_preserves_cv_shi`: threads (CV, PMI, SHI, merges) through processAll
  - `rebuildStepBody`/`rebuildF`: total (fuel-based) rebuild
  - `saturateF`: total (fuel-based) saturation loop
  - `saturateF_preserves_consistent`: main soundness theorem

  Adapted from OptiSat/SaturationSpec.lean for the AMO circuit domain.
-/
import AmoLean.EGraph.Verified.SoundRewriteRule

namespace AmoLean.EGraph.Verified

open UnionFind

set_option linter.unusedSectionVars false

variable {Val : Type} [Add Val] [Mul Val] [Neg Val]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: processClass_shi_combined
-- ══════════════════════════════════════════════════════════════════

/-- processClass preserves SemanticHashconsInv AND emits merge pairs with
    v-equal values. Joint proof via Array.foldl_induction.
    Adapted from OptiSat processClass_shi_combined. -/
theorem processClass_shi_combined (g : EGraph) (classId : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v)
    (hshi : SemanticHashconsInv g env v)
    (hpmi : PostMergeInvariant g) :
    SemanticHashconsInv (g.processClass classId).1 env v ∧
    (∀ pr ∈ (g.processClass classId).2, v pr.1 = v pr.2) := by
  unfold EGraph.processClass
  simp only [EGraph.find, find_fst_eq_root]
  have g1_roots : ∀ k, root (g.unionFind.find classId).2 k = root g.unionFind k :=
    fun k => find_preserves_roots g.unionFind classId k hpmi.uf_wf
  have g1_wf : WellFormed (g.unionFind.find classId).2 :=
    find_preserves_wf g.unionFind classId hpmi.uf_wf
  have g1_sz : (g.unionFind.find classId).2.parent.size = g.unionFind.parent.size :=
    find_snd_size g.unionFind classId
  unfold SemanticHashconsInv
  split
  · -- none: no class found
    constructor
    · intro nd id hget; rw [hshi nd id hget]; congr 1; exact (g1_roots id).symm
    · intro _ h; exact nomatch h
  · -- some eclass
    rename_i eclass heclass
    have hcls_canon : g.classes.get? (root g.unionFind classId) = some eclass := by
      rwa [Std.HashMap.get?_eq_getElem?]
    have canonId_bnd : root g.unionFind classId < g.unionFind.parent.size := by
      apply hpmi.classes_entries_valid
      rw [Std.HashMap.contains_eq_isSome_getElem?,
          show g.classes[root g.unionFind classId]? =
            g.classes.get? (root g.unionFind classId) from
            (Std.HashMap.get?_eq_getElem? ..).symm,
          hcls_canon]; rfl
    have h_base :
        ((∀ nd id, g.hashcons.get? nd = some id →
          NodeEval nd env v = v (root (g.unionFind.find classId).2 id)) ∧
         (∀ pr ∈ ([] : List (EClassId × EClassId)), v pr.1 = v pr.2)) ∧
        (∀ k, root (g.unionFind.find classId).2 k = root g.unionFind k) ∧
        WellFormed (g.unionFind.find classId).2 ∧
        (g.unionFind.find classId).2.parent.size = g.unionFind.parent.size ∧
        g.classes = g.classes :=
      ⟨⟨fun nd id hget => by rw [hshi nd id hget]; congr 1; exact (g1_roots id).symm,
        fun _ h => nomatch h⟩, g1_roots, g1_wf, g1_sz, rfl⟩
    exact (@Array.foldl_induction ENode (EGraph × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (r : EGraph × List (EClassId × EClassId)) =>
        ((∀ nd id, r.1.hashcons.get? nd = some id →
          NodeEval nd env v = v (root r.1.unionFind id)) ∧
         (∀ pr ∈ r.2, v pr.1 = v pr.2)) ∧
        (∀ k, root r.1.unionFind k = root g.unionFind k) ∧
        WellFormed r.1.unionFind ∧
        r.1.unionFind.parent.size = g.unionFind.parent.size ∧
        r.1.classes = g.classes)
      ({ g with unionFind := (g.unionFind.find classId).2 },
        ([] : List (EClassId × EClassId)))
      h_base
      (fun (x : EGraph × List (EClassId × EClassId)) (node : ENode) =>
        let canonNode := (x.1.canonicalize node).1
        let acc1 := (x.1.canonicalize node).2
        if canonNode == node then (acc1, x.2)
        else
          let hashcons1 := acc1.hashcons.erase node
          match hashcons1.get? canonNode with
          | some existingId =>
            ({ acc1 with hashcons := hashcons1.insert canonNode (root g.unionFind classId) },
              (root g.unionFind classId, existingId) :: x.2)
          | none =>
            ({ acc1 with hashcons := hashcons1.insert canonNode (root g.unionFind classId) },
              x.2))
      (fun ⟨i, hi⟩ b ih => by
        obtain ⟨acc, merges⟩ := b
        obtain ⟨⟨ih_shi, ih_sem⟩, ih_roots, ih_wf, ih_sz, ih_cls⟩ := ih
        dsimp only at ih_shi ih_sem ih_roots ih_wf ih_sz ih_cls ⊢
        -- Properties after canonicalize
        have a1_hcs := canonicalize_hashcons acc eclass.nodes[i]
        have a1_cls := canonicalize_classes acc eclass.nodes[i]
        have a1_roots : ∀ k, root (acc.canonicalize eclass.nodes[i]).2.unionFind k =
            root g.unionFind k :=
          fun k => by rw [canonicalize_preserves_roots acc _ ih_wf]; exact ih_roots k
        have a1_wf := canonicalize_uf_wf acc eclass.nodes[i] ih_wf
        have a1_sz : (acc.canonicalize eclass.nodes[i]).2.unionFind.parent.size =
            g.unionFind.parent.size := by rw [canonicalize_uf_size]; exact ih_sz
        -- SHI for acc1 (canonicalize doesn't change hashcons)
        have a1_shi : ∀ nd id,
            (acc.canonicalize eclass.nodes[i]).2.hashcons.get? nd = some id →
            NodeEval nd env v = v (root (acc.canonicalize eclass.nodes[i]).2.unionFind id) := by
          intro nd id hget; rw [a1_hcs] at hget
          rw [ih_shi nd id hget]; congr 1
          exact (ih_roots id).trans (a1_roots id).symm
        -- UF-consistency of v
        have acc_cv : ∀ a b, root acc.unionFind a = root acc.unionFind b → v a = v b :=
          fun a b h => hv.1 a b (by rw [← ih_roots a, ← ih_roots b]; exact h)
        -- Children bounded in acc
        have hmem_i : eclass.nodes[i] ∈ eclass.nodes.toList :=
          Array.mem_toList_iff.mpr (Array.getElem_mem hi)
        have hbnd_i : ∀ c ∈ (eclass.nodes[i]).children, c < acc.unionFind.parent.size := by
          intro c hc; rw [ih_sz]
          exact hpmi.children_bounded _ eclass hcls_canon _ hmem_i c hc
        -- nodeEval_canonicalize + CV combined
        have heval_canon : NodeEval (acc.canonicalize eclass.nodes[i]).1 env v =
            v (root g.unionFind classId) :=
          (nodeEval_canonicalize acc eclass.nodes[i] env v acc_cv ih_wf hbnd_i).trans
            (hv.2 (root g.unionFind classId) eclass hcls_canon _ hmem_i)
        split
        · -- Case 1: canonNode == node, no hashcons change
          exact ⟨⟨a1_shi, ih_sem⟩, a1_roots, a1_wf, a1_sz, a1_cls.trans ih_cls⟩
        · -- Case 2: canonNode ≠ node
          rename_i hne_beq
          -- SHI for erased hashcons
          have erase_shi : ∀ nd id,
              ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).get? nd =
                some id →
              NodeEval nd env v =
                v (root (acc.canonicalize eclass.nodes[i]).2.unionFind id) := by
            intro nd id hget
            by_cases hnn : eclass.nodes[i] = nd
            · subst hnn; rw [hashcons_get?_erase_self] at hget; exact nomatch hget
            · rw [hashcons_get?_erase_ne _ _ _ hnn, a1_hcs] at hget
              rw [ih_shi nd id hget]; congr 1
              exact (ih_roots id).trans (a1_roots id).symm
          -- SHI for inserted hashcons
          have insert_shi : ∀ nd id,
              (((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
                (acc.canonicalize eclass.nodes[i]).1 (root g.unionFind classId)).get? nd =
                some id →
              NodeEval nd env v =
                v (root (acc.canonicalize eclass.nodes[i]).2.unionFind id) := by
            intro nd id hget
            by_cases hcn : (acc.canonicalize eclass.nodes[i]).1 = nd
            · subst hcn; rw [hashcons_get?_insert_self] at hget
              rw [← Option.some.inj hget, heval_canon]
              congr 1
              rw [a1_roots]
              rcases Nat.lt_or_ge classId g.unionFind.parent.size with hlt | hge
              · exact (root_idempotent g.unionFind classId hpmi.uf_wf hlt).symm
              · exact absurd (root_oob g.unionFind classId (Nat.not_lt.mpr hge) ▸ canonId_bnd)
                  (Nat.not_lt.mpr hge)
            · rw [hashcons_get?_insert_ne _ _ _ _ hcn] at hget
              exact erase_shi nd id hget
          -- SHI for the new graph (with updated hashcons only)
          have new_shi : ∀ nd id,
              ({ (acc.canonicalize eclass.nodes[i]).2 with
                hashcons := ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
                  (acc.canonicalize eclass.nodes[i]).1 (root g.unionFind classId) } : EGraph).hashcons.get? nd =
                some id →
              NodeEval nd env v = v (root
                ({ (acc.canonicalize eclass.nodes[i]).2 with
                  hashcons := ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
                    (acc.canonicalize eclass.nodes[i]).1 (root g.unionFind classId) } : EGraph).unionFind id) := by
            intro nd id hget
            simp only [] at hget ⊢
            exact insert_shi nd id hget
          split
          · -- Subcase: existing entry found → emit merge
            rename_i existingId hexists
            refine ⟨⟨new_shi, ?_⟩, a1_roots, a1_wf, a1_sz,
              show ((acc.canonicalize eclass.nodes[i]).2 |>.classes) = g.classes
                from a1_cls.trans ih_cls⟩
            intro pr hpr
            simp only [List.mem_cons] at hpr
            rcases hpr with rfl | hpr
            · -- merge pair: (canonId, existingId)
              simp only []
              have h_ex := erase_shi _ _ hexists
              have : v (root g.unionFind classId) =
                  v (root (acc.canonicalize eclass.nodes[i]).2.unionFind existingId) :=
                heval_canon.symm.trans h_ex
              rw [a1_roots] at this
              have hv_root := consistent_root_eq' g env v hv hpmi.uf_wf existingId
              exact this.trans hv_root
            · exact ih_sem pr hpr
          · -- Subcase: no existing entry
            exact ⟨⟨new_shi, ih_sem⟩, a1_roots, a1_wf, a1_sz,
              show ((acc.canonicalize eclass.nodes[i]).2 |>.classes) = g.classes
                from a1_cls.trans ih_cls⟩
      )).1

-- ══════════════════════════════════════════════════════════════════
-- Section 2: processAll_preserves_cv_shi
-- ══════════════════════════════════════════════════════════════════

/-- Processing a list of classes preserves CV, PMI, SHI, and merge validity. -/
theorem processAll_preserves_cv_shi : ∀ (toProcess : List EClassId)
    (g : EGraph) (merges : List (EClassId × EClassId))
    (env : CircuitEnv Val) (v : EClassId → Val),
    ConsistentValuation g env v →
    PostMergeInvariant g →
    SemanticHashconsInv g env v →
    (∀ pr ∈ merges, v pr.1 = v pr.2) →
    let result := toProcess.foldl
      (fun (am : EGraph × List (EClassId × EClassId)) (cid : EClassId) =>
        ((am.1.processClass cid).1, (am.1.processClass cid).2 ++ am.2))
      (g, merges)
    ConsistentValuation result.1 env v ∧
    PostMergeInvariant result.1 ∧
    SemanticHashconsInv result.1 env v ∧
    (∀ pr ∈ result.2, v pr.1 = v pr.2) := by
  intro toProcess
  induction toProcess with
  | nil => intro g merges env v hcv hpmi hshi hm; exact ⟨hcv, hpmi, hshi, hm⟩
  | cons cid rest ih =>
    intro g merges env v hcv hpmi hshi hm
    simp only [List.foldl_cons]
    have hcv' := processClass_consistent g cid env v hcv hpmi.uf_wf
    have hpmi' := processClass_preserves_pmi g cid hpmi
    have ⟨hshi', hmerges'⟩ := processClass_shi_combined g cid env v hcv hshi hpmi
    have hm' : ∀ pr ∈ (g.processClass cid).2 ++ merges, v pr.1 = v pr.2 := by
      intro pr hpr
      rcases List.mem_append.mp hpr with h | h
      · exact hmerges' pr h
      · exact hm pr h
    exact ih (g.processClass cid).1 ((g.processClass cid).2 ++ merges)
      env v hcv' hpmi' hshi' hm'

-- ══════════════════════════════════════════════════════════════════
-- Section 3: rebuildStep preserves (CV, PMI, SHI)
-- ══════════════════════════════════════════════════════════════════

/-- Core rebuild fact: processAll then mergeAll preserves the triple.
    Adapted from OptiSat rebuildStep_preserves_triple_aux. -/
private theorem rebuildStep_preserves_triple_aux (g1 : EGraph)
    (toProcess : List EClassId) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g1 env v)
    (hpmi : PostMergeInvariant g1)
    (hshi : SemanticHashconsInv g1 env v) :
    let pa := toProcess.foldl
      (fun (am : EGraph × List (EClassId × EClassId)) (cid : EClassId) =>
        ((am.1.processClass cid).1, (am.1.processClass cid).2 ++ am.2))
      (g1, ([] : List (EClassId × EClassId)))
    ConsistentValuation (pa.2.foldl (fun acc (id1, id2) => acc.merge id1 id2) pa.1) env v ∧
    PostMergeInvariant (pa.2.foldl (fun acc (id1, id2) => acc.merge id1 id2) pa.1) ∧
    SemanticHashconsInv (pa.2.foldl (fun acc (id1, id2) => acc.merge id1 id2) pa.1) env v := by
  intro pa
  have ⟨hcv2, hpmi2, hshi2, hm2⟩ := processAll_preserves_cv_shi
    toProcess g1 [] env v hcv hpmi hshi (fun _ h => nomatch h)
  have ⟨_, hsize2, hbnd2⟩ := processAll_preserves_pmi toProcess g1 []
    hpmi (fun _ h => nomatch h)
  have hbnd_adj : ∀ p ∈ pa.2,
      p.1 < pa.1.unionFind.parent.size ∧ p.2 < pa.1.unionFind.parent.size := by
    intro p hp; rw [hsize2]; exact hbnd2 p hp
  exact ⟨mergeAll_consistent pa.2 pa.1 env v hcv2 hpmi2.uf_wf hm2 hbnd_adj,
    mergeAll_preserves_pmi pa.2 pa.1 hpmi2 hbnd_adj,
    mergeAll_preserves_shi pa.2 pa.1 env v hcv2 hpmi2.uf_wf hshi2 hm2 hbnd_adj⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Fuel-based total functions
-- ══════════════════════════════════════════════════════════════════

/-- Body of one rebuild iteration (total version). -/
def rebuildStepBody (g : EGraph) : EGraph :=
  let toProcess := g.worklist ++ g.dirtyArr.toList
  let g1 : EGraph := { g with worklist := [], dirtyArr := #[] }
  let (g2, pendingMerges) := toProcess.foldl (fun (acc, merges) classId =>
    let (acc', newMerges) := acc.processClass classId
    (acc', newMerges ++ merges)
  ) (g1, [])
  pendingMerges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g2

/-- Fuel-based total version of rebuild. -/
def rebuildF (g : EGraph) : Nat → EGraph
  | 0 => g
  | fuel + 1 =>
    if g.worklist.isEmpty && g.dirtyArr.isEmpty then g
    else rebuildF (rebuildStepBody g) fuel

/-- Total saturation loop. Each iteration: apply step, then rebuild. -/
def saturateF (step : EGraph → EGraph) (maxIter : Nat) (rebuildFuel : Nat)
    (g : EGraph) : EGraph :=
  match maxIter with
  | 0 => g
  | n + 1 =>
    let g' := step g
    let g'' := rebuildF g' rebuildFuel
    saturateF step n rebuildFuel g''

-- ══════════════════════════════════════════════════════════════════
-- Section 5: rebuildStepBody/rebuildF preserve (CV, PMI, SHI)
-- ══════════════════════════════════════════════════════════════════

/-- rebuildStepBody preserves the triple (CV, PMI, SHI) with the same v. -/
theorem rebuildStepBody_preserves_triple (g : EGraph)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) :
    ConsistentValuation (rebuildStepBody g) env v ∧
    PostMergeInvariant (rebuildStepBody g) ∧
    SemanticHashconsInv (rebuildStepBody g) env v :=
  rebuildStep_preserves_triple_aux
    { g with worklist := [], dirtyArr := #[] }
    (g.worklist ++ g.dirtyArr.toList) env v
    hcv (clear_worklist_pmi g hpmi) (clear_worklist_shi g env v hshi)

/-- rebuildF preserves the triple with the same v. -/
theorem rebuildF_preserves_triple (env : CircuitEnv Val) (fuel : Nat)
    (g : EGraph) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) :
    ConsistentValuation (rebuildF g fuel) env v ∧
    PostMergeInvariant (rebuildF g fuel) ∧
    SemanticHashconsInv (rebuildF g fuel) env v := by
  induction fuel generalizing g v with
  | zero => exact ⟨hcv, hpmi, hshi⟩
  | succ n ih =>
    simp only [rebuildF]
    split
    · exact ⟨hcv, hpmi, hshi⟩
    · have ⟨hcv', hpmi', hshi'⟩ :=
        rebuildStepBody_preserves_triple g env v hcv hpmi hshi
      exact ih (rebuildStepBody g) v hcv' hpmi' hshi'

-- ══════════════════════════════════════════════════════════════════
-- Section 6: PreservesCV + saturation soundness
-- ══════════════════════════════════════════════════════════════════

/-- Predicate: a step function preserves the triple (CV, PMI, SHI).
    Core composability property for the saturation pipeline. -/
def PreservesCV (env : CircuitEnv Val) (step : EGraph → EGraph) : Prop :=
  ∀ (g : EGraph) (v : EClassId → Val),
    ConsistentValuation g env v →
    PostMergeInvariant g →
    SemanticHashconsInv g env v →
    ∃ v', ConsistentValuation (step g) env v' ∧
          PostMergeInvariant (step g) ∧
          SemanticHashconsInv (step g) env v'

/-- Main soundness theorem: saturateF preserves ConsistentValuation
    when the step function preserves the triple. -/
theorem saturateF_preserves_consistent (step : EGraph → EGraph)
    (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step) :
    ∃ v', ConsistentValuation (saturateF step maxIter rebuildFuel g) env v' := by
  induction maxIter generalizing g v with
  | zero => exact ⟨v, hcv⟩
  | succ n ih =>
    simp only [saturateF]
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h_step g v hcv hpmi hshi
    have ⟨hcv2, hpmi2, hshi2⟩ :=
      rebuildF_preserves_triple env rebuildFuel (step g) v1 hcv1 hpmi1 hshi1
    exact ih (rebuildF (step g) rebuildFuel) v1 hcv2 hpmi2 hshi2

end AmoLean.EGraph.Verified
