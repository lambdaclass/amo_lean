/-
  AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec — Structural invariants for MixedNodeOp EGraph

  B60 (FUNDACIONAL): Adapts OptiSat's CoreSpec to amo-lean's simpler VerifiedExtraction.EGraph.
  Key simplification: no dirtyArr, non-compressing root (vs find with path compression).

  Deliverables:
  - LawfulBEq + LawfulHashable for MixedNodeOp
  - ChildrenBounded, PostMergeInvariant for VerifiedExtraction.EGraph
  - merge structural properties (hashcons, uf_size, children_bounded)
  - merge_preserves_pmi, mergeAll_preserves_pmi
  - HashMap bridge lemmas, EClass.union membership
  - sameShape for MixedNodeOp
-/
import AmoLean.EGraph.Verified.Bitwise.MixedNodeOp
import AmoLean.EGraph.Verified.Bitwise.MixedUnionFind

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Hashable + Lawful instances for MixedNodeOp
-- (Must come BEFORE type abbreviations that require Hashable)
-- ══════════════════════════════════════════════════════════════════

/-- Hashable instance for MixedNodeOp (deterministic, tag + payload). -/
instance mixedHashable : Hashable MixedNodeOp where
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
    | .conditionalSub a p => mixHash 25 (mixHash (hash a) (hash p))

/-- BEq for MixedNodeOp comes from DecidableEq and is lawful. -/
instance mixedLawfulBEq : LawfulBEq MixedNodeOp where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Hash respects equality. -/
instance mixedLawfulHashable : LawfulHashable MixedNodeOp where
  hash_eq {a b} h := by have : a = b := eq_of_beq h; subst this; rfl

-- ══════════════════════════════════════════════════════════════════
-- Abbreviations to avoid namespace conflicts with Verified.*
-- ══════════════════════════════════════════════════════════════════

abbrev MGraph := AmoLean.EGraph.VerifiedExtraction.EGraph MixedNodeOp
abbrev MNode  := AmoLean.EGraph.VerifiedExtraction.ENode MixedNodeOp
abbrev MClass := AmoLean.EGraph.VerifiedExtraction.EClass MixedNodeOp
abbrev MUF    := AmoLean.EGraph.VerifiedExtraction.UnionFind
abbrev CId    := AmoLean.EGraph.VerifiedExtraction.EClassId
abbrev UFWF   := AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed

-- Full-path accessors (avoids conflicts with Verified.* namespace)
abbrev ufRoot  := AmoLean.EGraph.VerifiedExtraction.UnionFind.root
abbrev ndChildren (n : MNode) := AmoLean.EGraph.VerifiedExtraction.ENode.children n
abbrev ndMapCh := @AmoLean.EGraph.VerifiedExtraction.NodeOps.mapChildren MixedNodeOp _
abbrev ndCh    := @AmoLean.EGraph.VerifiedExtraction.NodeOps.children MixedNodeOp _
abbrev ndMCC   := @AmoLean.EGraph.VerifiedExtraction.NodeOps.mapChildren_children MixedNodeOp _

-- ══════════════════════════════════════════════════════════════════
-- Section 2: UnionFind lemmas
-- ══════════════════════════════════════════════════════════════════

/-- union preserves parent array size. -/
theorem uf_union_size (uf : MUF) (id1 id2 : CId) :
    (uf.union id1 id2).parent.size = uf.parent.size := by
  unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.union
  simp only
  split
  · rfl
  · split
    · simp [Array.size_setIfInBounds]
    · rfl

-- ══════════════════════════════════════════════════════════════════
-- (UF rootD lemmas deferred to dedicated module)
-- ══════════════════════════════════════════════════════════════════
/-- All node children in all classes are valid (bounded by UF size). -/
def ChildrenBounded (g : MGraph) : Prop :=
  ∀ (classId : CId) (cls : MClass),
    g.classes.get? classId = some cls →
    ∀ (node : MNode), node ∈ cls.nodes.toList →
      ∀ (child : CId), child ∈ ndChildren node →
        child < g.unionFind.parent.size

/-- All hashcons entry children are valid. -/
def HashconsChildrenBounded (g : MGraph) : Prop :=
  ∀ (nd : MNode) (id : CId),
    g.hashcons.get? nd = some id →
    ∀ (child : CId), child ∈ ndChildren nd →
      child < g.unionFind.parent.size

abbrev StrongWF := AmoLean.EGraph.Verified.Bitwise.MixedUnionFind.StrongWF

/-- Invariant preserved across merge/saturation.
    Uses StrongWF (ParentsBounded ∧ IsAcyclic) instead of the weak UFWF. -/
structure PostMergeInvariant (g : MGraph) : Prop where
  uf_swf : StrongWF g.unionFind
  children_bounded : ChildrenBounded g
  hashcons_entries_valid : ∀ (node : MNode) (id : CId),
    g.hashcons.get? node = some id → id < g.unionFind.parent.size
  classes_entries_valid : ∀ (id : CId),
    g.classes.contains id = true → id < g.unionFind.parent.size

/-- StrongWF implies the old weak UFWF. -/
def PostMergeInvariant.uf_wf {g : MGraph} (hpmi : PostMergeInvariant g) : UFWF g.unionFind :=
  AmoLean.EGraph.Verified.Bitwise.MixedUnionFind.strongWF_implies_UFWF hpmi.uf_swf

-- ══════════════════════════════════════════════════════════════════
-- Section 4: HashMap bridge lemmas
-- ══════════════════════════════════════════════════════════════════

theorem hashcons_get?_insert_self (hm : Std.HashMap MNode CId)
    (node : MNode) (id : CId) :
    (hm.insert node id).get? node = some id := by
  simp [Std.HashMap.get?_eq_getElem?]

theorem hashcons_get?_insert_ne (hm : Std.HashMap MNode CId)
    (n1 n2 : MNode) (id : CId) (hne : n1 ≠ n2) :
    (hm.insert n1 id).get? n2 = hm.get? n2 := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_eq_false_iff_ne.mpr hne]; rfl

theorem classes_get?_insert_self (hm : Std.HashMap CId MClass)
    (id : CId) (cls : MClass) :
    (hm.insert id cls).get? id = some cls := by
  simp [Std.HashMap.get?_eq_getElem?]

theorem classes_get?_insert_ne (hm : Std.HashMap CId MClass)
    (id1 id2 : CId) (cls : MClass) (hne : id1 ≠ id2) :
    (hm.insert id1 cls).get? id2 = hm.get? id2 := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_eq_false_iff_ne.mpr hne]; rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 5: EClass.union membership
-- ══════════════════════════════════════════════════════════════════

/-- A node in the union of two e-classes came from one of the originals. -/
theorem eclass_union_mem (ec1 ec2 : MClass) (node : MNode)
    (hmem : node ∈ (ec1.union ec2).nodes.toList) :
    node ∈ ec1.nodes.toList ∨ node ∈ ec2.nodes.toList := by
  unfold AmoLean.EGraph.VerifiedExtraction.EClass.union at hmem
  simp only [] at hmem
  -- hmem : node ∈ (Array.foldl (conditional push) ec1.nodes ec2.nodes).toList
  -- The foldl adds ec2 nodes one by one to ec1's array.
  -- Any element in the result must have come from ec1 or ec2.
  -- We prove this by showing every element of the final array is from ec1 or ec2.
  -- Use Array.foldl_induction with f explicit to track provenance.
  let f : Array MNode → MNode → Array MNode :=
    fun acc n => if acc.contains n then acc else acc.push n
  have hprov : ∀ x ∈ (Array.foldl f ec1.nodes ec2.nodes).toList,
      x ∈ ec1.nodes.toList ∨ x ∈ ec2.nodes.toList :=
    @Array.foldl_induction MNode (Array MNode) ec2.nodes
      (fun _ acc => ∀ x ∈ acc.toList, x ∈ ec1.nodes.toList ∨ x ∈ ec2.nodes.toList)
      ec1.nodes (fun x hx => Or.inl hx) f
      (fun i acc hm x hx => by
        show x ∈ ec1.nodes.toList ∨ x ∈ ec2.nodes.toList
        simp only [f] at hx
        split at hx
        · exact hm x hx
        · rw [Array.toList_push] at hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hm x hx
          · exact Or.inr (Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt)))
  exact hprov node hmem

-- ══════════════════════════════════════════════════════════════════
-- Section 6: merge structural properties
-- ══════════════════════════════════════════════════════════════════

/-- merge does not change the hashcons map. -/
theorem merge_hashcons (g : MGraph) (id1 id2 : CId) :
    (g.merge id1 id2).hashcons = g.hashcons := by
  unfold AmoLean.EGraph.VerifiedExtraction.EGraph.merge
  dsimp only
  split <;> rfl

/-- merge preserves UF size. -/
theorem merge_uf_size (g : MGraph) (id1 id2 : CId) :
    (g.merge id1 id2).unionFind.parent.size = g.unionFind.parent.size := by
  unfold AmoLean.EGraph.VerifiedExtraction.EGraph.merge
  dsimp only
  split
  · rfl
  · exact uf_union_size g.unionFind (ufRoot g.unionFind id1) (ufRoot g.unionFind id2)

/-- merge preserves ChildrenBounded. -/
theorem merge_preserves_children_bounded (g : MGraph) (id1 id2 : CId)
    (hcb : ChildrenBounded g) :
    ChildrenBounded (g.merge id1 id2) := by
  intro classId cls hcls node hmem child hchild
  rw [merge_uf_size]
  unfold AmoLean.EGraph.VerifiedExtraction.EGraph.merge at hcls
  simp only at hcls
  split at hcls
  · exact hcb classId cls hcls node hmem child hchild
  · -- Different roots case
    by_cases heq : ufRoot g.unionFind id1 = classId
    · subst heq
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, ite_true] at hcls
      have hcls_eq := Option.some.inj hcls
      rw [← hcls_eq] at hmem
      rcases eclass_union_mem _ _ node hmem with h1 | h2
      · -- node from root1's class
        rw [← Std.HashMap.get?_eq_getElem?] at h1
        cases hc1 : g.classes.get? (ufRoot g.unionFind id1) with
        | none =>
          rw [hc1, show (none : Option MClass).getD default = default from rfl] at h1
          exact absurd h1 (by simp [show (default : MClass).nodes = #[] from rfl])
        | some c1 =>
          rw [hc1, show (some c1).getD default = c1 from rfl] at h1
          exact hcb _ c1 hc1 node h1 child hchild
      · -- node from root2's class
        rw [← Std.HashMap.get?_eq_getElem?] at h2
        cases hc2 : g.classes.get? (ufRoot g.unionFind id2) with
        | none =>
          rw [hc2, show (none : Option MClass).getD default = default from rfl] at h2
          exact absurd h2 (by simp [show (default : MClass).nodes = #[] from rfl])
        | some c2 =>
          rw [hc2, show (some c2).getD default = c2 from rfl] at h2
          exact hcb _ c2 hc2 node h2 child hchild
    · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        show (ufRoot g.unionFind id1 == classId) = false from
          beq_eq_false_iff_ne.mpr heq] at hcls
      exact hcb classId cls (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls)
        node hmem child hchild

-- ══════════════════════════════════════════════════════════════════
-- Section 7: merge preserves PostMergeInvariant
-- ══════════════════════════════════════════════════════════════════

/-- merge preserves PostMergeInvariant when both IDs are bounded.
    Note: uf_wf preservation for union requires rootD induction — deferred to
    a dedicated UF lemma. For the soundness chain, merge_consistent (B61)
    only needs the ORIGINAL uf_wf, not the updated one. -/
theorem merge_preserves_pmi (g : MGraph) (id1 id2 : CId)
    (hpmi : PostMergeInvariant g)
    (h1 : id1 < g.unionFind.parent.size)
    (h2 : id2 < g.unionFind.parent.size) :
    PostMergeInvariant (g.merge id1 id2) where
  uf_swf := by
    unfold AmoLean.EGraph.VerifiedExtraction.EGraph.merge
    simp only
    split
    · exact hpmi.uf_swf
    · have hwf := AmoLean.EGraph.Verified.Bitwise.MixedUnionFind.strongWF_implies_UFWF hpmi.uf_swf
      exact AmoLean.EGraph.Verified.Bitwise.MixedUnionFind.union_preserves_strongWF
        g.unionFind _ _ hpmi.uf_swf (hwf.root_bounded id1 h1) (hwf.root_bounded id2 h2)
  children_bounded := merge_preserves_children_bounded g id1 id2 hpmi.children_bounded
  hashcons_entries_valid := by
    intro node id hget
    rw [merge_hashcons] at hget; rw [merge_uf_size]
    exact hpmi.hashcons_entries_valid node id hget
  classes_entries_valid := by
    intro id hcont; rw [merge_uf_size]
    unfold AmoLean.EGraph.VerifiedExtraction.EGraph.merge at hcont
    simp only at hcont
    split at hcont
    · exact hpmi.classes_entries_valid id hcont
    · rw [Std.HashMap.contains_insert] at hcont
      rcases Bool.or_eq_true_iff.mp hcont with heq | hc
      · rw [beq_iff_eq] at heq; subst heq
        exact hpmi.uf_wf.root_bounded id1 h1
      · exact hpmi.classes_entries_valid id hc

/-- mergeAll preserves PostMergeInvariant for a list of bounded pairs. -/
theorem mergeAll_preserves_pmi (merges : List (CId × CId))
    (g : MGraph) (hpmi : PostMergeInvariant g)
    (hbnd : ∀ p ∈ merges,
      p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) :
    PostMergeInvariant (merges.foldl
      (fun (acc : MGraph) (p : CId × CId) => acc.merge p.1 p.2) g) := by
  induction merges generalizing g with
  | nil => exact hpmi
  | cons hd tl ih =>
    simp only [List.foldl]
    have ⟨hd1, hd2⟩ := hbnd hd (List.Mem.head _)
    exact ih (g.merge hd.1 hd.2) (merge_preserves_pmi g hd.1 hd.2 hpmi hd1 hd2)
      (fun p hp => by
        constructor
        · rw [merge_uf_size]; exact (hbnd p (List.mem_cons_of_mem _ hp)).1
        · rw [merge_uf_size]; exact (hbnd p (List.mem_cons_of_mem _ hp)).2)

-- ══════════════════════════════════════════════════════════════════
-- Section 8: sameShape for MixedNodeOp
-- ══════════════════════════════════════════════════════════════════

/-- Check if two MixedNodeOps have the same shape (ignoring children). -/
def sameShape (p o : MixedNodeOp) : Bool :=
  ndMapCh (fun _ => (0 : CId)) p == ndMapCh (fun _ => (0 : CId)) o

/-- sameShape preserves children length. -/
theorem sameShape_children_length (op₁ op₂ : MixedNodeOp) (h : sameShape op₁ op₂ = true) :
    (ndCh op₁).length = (ndCh op₂).length := by
  -- sameShape means mapChildren(0, op₁) = mapChildren(0, op₂)
  have heq : ndMapCh (fun _ => (0 : CId)) op₁ = ndMapCh (fun _ => (0 : CId)) op₂ := by
    unfold sameShape at h; exact eq_of_beq h
  -- mapChildren_children: children(mapChildren f op) = map f (children op)
  have h1 := ndMCC (fun _ => (0 : CId)) op₁
  have h2 := ndMCC (fun _ => (0 : CId)) op₂
  -- Both sides equal via heq → map(0, ch₁) = map(0, ch₂) → length ch₁ = length ch₂
  have h3 := congrArg ndCh heq
  -- h3 : ndCh(ndMapCh 0 op₁) = ndCh(ndMapCh 0 op₂)
  -- But h3 uses ndCh ∘ ndMapCh which equals h1/h2 via unfold
  -- Use transitivity through the mapChildren_children law
  have : List.map (fun _ => (0 : CId)) (ndCh op₁) =
         List.map (fun _ => (0 : CId)) (ndCh op₂) := by
    calc List.map (fun _ => (0 : CId)) (ndCh op₁)
        = ndCh (ndMapCh (fun _ => 0) op₁) := h1.symm
      _ = ndCh (ndMapCh (fun _ => 0) op₂) := h3
      _ = List.map (fun _ => (0 : CId)) (ndCh op₂) := h2
  have := congrArg List.length this
  simp [List.length_map] at this
  exact this

-- ══════════════════════════════════════════════════════════════════
-- Section 8b: ShapeHashconsInv
-- ══════════════════════════════════════════════════════════════════

/-- Shape-Hashcons Integrity: every node in the hashcons map has a corresponding
    class that contains it. This is separate from PostMergeInvariant (which is
    structural — UF well-formedness + children bounds + entries valid). -/
def ShapeHashconsInv (g : MGraph) : Prop :=
  ∀ (nd : MNode) (id : CId), g.hashcons.get? nd = some id →
    ∃ cls, g.classes.get? id = some cls ∧ nd ∈ cls.nodes.toList

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: LawfulBEq works. -/
example : (MixedNodeOp.addGate 0 1 == MixedNodeOp.addGate 0 1) = true := by native_decide

/-- Smoke: sameShape detects matching operators. -/
example : sameShape (.addGate 0 1) (.addGate 2 3) = true := by native_decide

/-- Smoke: sameShape rejects different operators. -/
example : sameShape (.addGate 0 1) (.mulGate 0 1) = false := by native_decide

end AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec
