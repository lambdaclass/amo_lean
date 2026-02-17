/-
  AMO-Lean — Verified EGraph Core Specification (Hashcons Invariant)
  Ported from VR1CS-Lean (Fase 6 Subfase 3).
  Well-formedness predicates and proofs for EGraph.
-/
import AmoLean.EGraph.Verified.Core

namespace AmoLean.EGraph.Verified

open UnionFind

/-! ## Layer 1: Well-Formedness Predicates -/

def ENode.isCanonical (node : ENode) (uf : UnionFind) : Prop :=
  ∀ child, child ∈ node.children → IsRootAt uf.parent child

def HashconsConsistent (eg : EGraph) : Prop :=
  ∀ node id, eg.hashcons.get? node = some id →
    id < eg.unionFind.parent.size ∧
    node.isCanonical eg.unionFind ∧
    IsRootAt eg.unionFind.parent id

def HashconsComplete (eg : EGraph) : Prop :=
  ∀ id cls, eg.classes.get? id = some cls →
    ∀ node, node ∈ cls.nodes.toList →
      node.isCanonical eg.unionFind →
      ∃ rid, eg.hashcons.get? node = some rid ∧
        root eg.unionFind rid = root eg.unionFind id

def ClassesConsistent (eg : EGraph) : Prop :=
  (∀ id, eg.classes.contains id = true →
    id < eg.unionFind.parent.size ∧ IsRootAt eg.unionFind.parent id) ∧
  (∀ id, id < eg.unionFind.parent.size → IsRootAt eg.unionFind.parent id →
    eg.classes.contains id = true)

def HashconsClassesAligned (eg : EGraph) : Prop :=
  ∀ node id, eg.hashcons.get? node = some id →
    ∃ cls, eg.classes.get? id = some cls ∧ node ∈ cls.nodes.toList

def ChildrenBounded (eg : EGraph) : Prop :=
  ∀ id cls, eg.classes.get? id = some cls →
    ∀ node, node ∈ cls.nodes.toList →
      ∀ child, child ∈ node.children → child < eg.unionFind.parent.size

structure EGraphWF (eg : EGraph) : Prop where
  uf_wf : WellFormed eg.unionFind
  hashcons_consistent : HashconsConsistent eg
  hashcons_complete : HashconsComplete eg
  classes_consistent : ClassesConsistent eg
  hashcons_classes_aligned : HashconsClassesAligned eg
  children_bounded : ChildrenBounded eg

/-! ## Layer 2: Bridge Lemmas -/

theorem hashcons_get?_insert_self (hm : Std.HashMap ENode EClassId)
    (node : ENode) (id : EClassId) :
    (hm.insert node id).get? node = some id := by
  simp [Std.HashMap.get?_eq_getElem?]

theorem hashcons_get?_insert_ne (hm : Std.HashMap ENode EClassId)
    (n1 n2 : ENode) (id : EClassId) (hne : n1 ≠ n2) :
    (hm.insert n1 id).get? n2 = hm.get? n2 := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  simp [beq_eq_false_iff_ne.mpr hne]

theorem egraph_find_hashcons (g : EGraph) (id : EClassId) :
    (g.find id).2.hashcons = g.hashcons := rfl
theorem egraph_find_classes (g : EGraph) (id : EClassId) :
    (g.find id).2.classes = g.classes := rfl
theorem egraph_find_uf_size (g : EGraph) (id : EClassId) :
    (g.find id).2.unionFind.parent.size = g.unionFind.parent.size :=
  find_snd_size g.unionFind id
theorem egraph_find_uf_wf (g : EGraph) (id : EClassId) (hwf : WellFormed g.unionFind) :
    WellFormed (g.find id).2.unionFind :=
  find_preserves_wf g.unionFind id hwf
theorem egraph_find_preserves_roots (g : EGraph) (id j : EClassId)
    (hwf : WellFormed g.unionFind) :
    root (g.find id).2.unionFind j = root g.unionFind j :=
  find_preserves_roots g.unionFind id j hwf
theorem egraph_find_preserves_isRootAt (g : EGraph) (id i : EClassId)
    (hroot : IsRootAt g.unionFind.parent i) :
    IsRootAt (g.find id).2.unionFind.parent i :=
  compressPath_preserves_root_entry hroot

/-! ## Layer 3: Canonicalization -/

theorem isCanonical_of_no_children {node : ENode} {uf : UnionFind}
    (h : node.children = []) : node.isCanonical uf := by
  intro child hc; rw [h] at hc; simp at hc

theorem canonicalize_leaf (g : EGraph) (node : ENode)
    (h : node.children = []) : g.canonicalize node = (node, g) := by
  unfold EGraph.canonicalize
  have : node.children.isEmpty = true := by rw [h]; rfl
  simp [this]

private theorem go_hashcons (cs : List EClassId) (g : EGraph) (ps : List (EClassId × EClassId)) :
    (EGraph.canonicalize.go cs g ps).2.hashcons = g.hashcons := by
  induction cs generalizing g ps with
  | nil => rfl
  | cons c rest ih => unfold EGraph.canonicalize.go; rw [ih]; rfl

private theorem go_classes (cs : List EClassId) (g : EGraph) (ps : List (EClassId × EClassId)) :
    (EGraph.canonicalize.go cs g ps).2.classes = g.classes := by
  induction cs generalizing g ps with
  | nil => rfl
  | cons c rest ih => unfold EGraph.canonicalize.go; rw [ih]; rfl

private theorem go_uf_size (cs : List EClassId) (g : EGraph) (ps : List (EClassId × EClassId)) :
    (EGraph.canonicalize.go cs g ps).2.unionFind.parent.size = g.unionFind.parent.size := by
  induction cs generalizing g ps with
  | nil => rfl
  | cons c rest ih => unfold EGraph.canonicalize.go; rw [ih]; exact egraph_find_uf_size g c

private theorem go_uf_wf (cs : List EClassId) (g : EGraph) (ps : List (EClassId × EClassId))
    (hwf : WellFormed g.unionFind) :
    WellFormed (EGraph.canonicalize.go cs g ps).2.unionFind := by
  induction cs generalizing g ps with
  | nil => exact hwf
  | cons c rest ih => unfold EGraph.canonicalize.go; exact ih _ _ (egraph_find_uf_wf g c hwf)

private theorem go_preserves_roots (cs : List EClassId) (g : EGraph)
    (ps : List (EClassId × EClassId)) (hwf : WellFormed g.unionFind) (j : EClassId) :
    root (EGraph.canonicalize.go cs g ps).2.unionFind j = root g.unionFind j := by
  induction cs generalizing g ps with
  | nil => rfl
  | cons c rest ih =>
    unfold EGraph.canonicalize.go
    rw [ih _ _ (egraph_find_uf_wf g c hwf)]; exact egraph_find_preserves_roots g c j hwf

private theorem go_preserves_isRootAt (cs : List EClassId) (g : EGraph)
    (ps : List (EClassId × EClassId)) (i : EClassId) (hroot : IsRootAt g.unionFind.parent i) :
    IsRootAt (EGraph.canonicalize.go cs g ps).2.unionFind.parent i := by
  induction cs generalizing g ps with
  | nil => exact hroot
  | cons c rest ih => unfold EGraph.canonicalize.go; exact ih _ _ (egraph_find_preserves_isRootAt g c i hroot)

theorem canonicalize_hashcons (g : EGraph) (node : ENode) :
    (g.canonicalize node).2.hashcons = g.hashcons := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]
  · simp [h]; exact go_hashcons _ _ _

theorem canonicalize_classes (g : EGraph) (node : ENode) :
    (g.canonicalize node).2.classes = g.classes := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]
  · simp [h]; exact go_classes _ _ _

theorem canonicalize_uf_wf (g : EGraph) (node : ENode) (hwf : WellFormed g.unionFind) :
    WellFormed (g.canonicalize node).2.unionFind := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]; exact hwf
  · simp [h]; exact go_uf_wf _ _ _ hwf

theorem canonicalize_preserves_roots (g : EGraph) (node : ENode)
    (hwf : WellFormed g.unionFind) (j : EClassId) :
    root (g.canonicalize node).2.unionFind j = root g.unionFind j := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]
  · simp [h]; exact go_preserves_roots _ _ _ hwf j

theorem canonicalize_preserves_isRootAt (g : EGraph) (node : ENode)
    (i : EClassId) (hroot : IsRootAt g.unionFind.parent i) :
    IsRootAt (g.canonicalize node).2.unionFind.parent i := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]; exact hroot
  · simp [h]; exact go_preserves_isRootAt _ _ _ i hroot

theorem IsRootAt_of_push {parent : Array EClassId} {v i : EClassId}
    (hroot : IsRootAt (parent.push v) i) (hlt : i < parent.size) :
    IsRootAt parent i := by
  obtain ⟨_, hself⟩ := hroot
  refine ⟨hlt, ?_⟩
  rw [Array.getElem_push] at hself
  split at hself
  · exact hself
  · omega

/-- root in a UF extended by push equals root in the original UF (in-bounds). -/
theorem root_push_eq {uf : UnionFind} (hwf : WellFormed uf)
    {id : EClassId} (hid : id < uf.parent.size) :
    root ⟨uf.parent.push uf.parent.size⟩ id = root uf id := by
  simp only [root, Array.size_push]
  rw [rootD_push hwf.1 hid]
  exact rootD_fuel_extra hwf.1 hid (hwf.2 id hid)

/-- root in a UF extended by push equals root in the original UF (all IDs). -/
theorem root_push_all_eq {uf : UnionFind} (hwf : WellFormed uf) (k : EClassId) :
    root ⟨uf.parent.push uf.parent.size⟩ k = root uf k := by
  by_cases hk : k < uf.parent.size
  · exact root_push_eq hwf hk
  · -- k ≥ uf.parent.size: both sides = k
    have lhs_eq : root ⟨uf.parent.push uf.parent.size⟩ k = k := by
      unfold root; rw [Array.size_push]
      have hge : uf.parent.size ≤ k := Nat.le_of_not_lt hk
      by_cases hke : k = uf.parent.size
      · subst hke
        exact rootD_of_isRoot
          ⟨by simp [Array.size_push], Array.getElem_push_eq⟩ (Nat.zero_lt_succ _)
      · have hgt : uf.parent.size < k := Nat.lt_of_le_of_ne hge (Ne.symm hke)
        exact rootD_succ_oob (by simp [Array.size_push]; omega)
    have rhs_eq : root uf k = k := by
      unfold root
      match hsz : uf.parent.size with
      | 0 => rfl
      | _ + 1 => exact rootD_succ_oob (by omega)
    rw [lhs_eq, rhs_eq]

/-! ## Layer 3e: IsRootAt backward through find (path compression) -/

/-- If rootD parent i size = i then IsRootAt parent i (by acyclicity). -/
theorem IsRootAt_of_rootD_self {parent : Array EClassId} {i : EClassId}
    (hacyc : ∀ j, j < parent.size → IsRootAt parent (rootD parent j parent.size))
    (hlt : i < parent.size) (heq : rootD parent i parent.size = i) :
    IsRootAt parent i :=
  heq ▸ hacyc i hlt

/-- If i is a root after path compression (find) and i < original size,
    then i was a root in the original array. -/
theorem IsRootAt_backward_find (g : EGraph) (id i : EClassId)
    (hwf : WellFormed g.unionFind)
    (hroot : IsRootAt (g.find id).2.unionFind.parent i)
    (hlt : i < g.unionFind.parent.size) :
    IsRootAt g.unionFind.parent i := by
  -- Step 1: root (find id).2.uf i = i (because i is a root there)
  have h1 : root (g.find id).2.unionFind i = i := by
    unfold root
    exact rootD_of_isRoot hroot (by exact Nat.lt_of_le_of_lt (Nat.zero_le i) hroot.1)
  -- Step 2: root g.uf i = i by transitivity through find_preserves_roots
  have h2 : root g.unionFind i = i :=
    (egraph_find_preserves_roots g id i hwf).symm.trans h1
  -- Step 3: conclude IsRootAt from root g.uf i = i and acyclicity
  exact IsRootAt_of_rootD_self hwf.2 hlt (by unfold root at h2; exact h2)

/-! ## Layer 4: Base Case -/

theorem egraph_empty_wf : EGraphWF EGraph.empty where
  uf_wf := UnionFind.empty_wf
  hashcons_consistent := fun _ _ hget => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at hget
  hashcons_complete := fun _ _ hget => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at hget
  classes_consistent := ⟨
    fun _ hc => by simp [EGraph.empty, Std.HashMap.ofList_nil] at hc,
    fun _ hlt _ => absurd hlt (Nat.not_lt_zero _)⟩
  hashcons_classes_aligned := fun _ _ hget => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at hget
  children_bounded := fun _ _ hget => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at hget

/-! ## Layer 5: add preserves WF (leaf nodes) -/

theorem mem_singleton_nodes (node n : ENode) :
    n ∈ (EClass.singleton node).nodes.toList ↔ n = node := by
  simp [EClass.singleton]

/-- Characterize add for leaf nodes: existing case. -/
theorem add_leaf_existing (g : EGraph) (node : ENode) (existingId : EClassId)
    (hleaf : node.children = []) (hm : g.hashcons.get? node = some existingId) :
    g.add node = g.find existingId := by
  show EGraph.add g node = g.find existingId
  unfold EGraph.add; rw [canonicalize_leaf g node hleaf]
  simp only [Std.HashMap.get?_eq_getElem?] at hm; simp [hm]

/-- Characterize add for leaf nodes: new case. -/
theorem add_leaf_new (g : EGraph) (node : ENode)
    (hleaf : node.children = []) (hm : g.hashcons.get? node = none) :
    g.add node = (g.unionFind.parent.size,
      { g with
        unionFind := ⟨g.unionFind.parent.push g.unionFind.parent.size⟩
        hashcons := g.hashcons.insert node g.unionFind.parent.size
        classes := g.classes.insert g.unionFind.parent.size (EClass.singleton node) }) := by
  show EGraph.add g node = _
  unfold EGraph.add; rw [canonicalize_leaf g node hleaf]
  simp only [Std.HashMap.get?_eq_getElem?] at hm; simp [hm, UnionFind.add]

/-- add of a leaf node preserves EGraphWF — existing node branch. -/
private theorem add_leaf_existing_wf (g : EGraph) (node : ENode) (existingId : EClassId)
    (hwf : EGraphWF g) (hleaf : node.children = [])
    (hm : g.hashcons.get? node = some existingId) :
    EGraphWF (g.add node).2 := by
  rw [add_leaf_existing g node existingId hleaf hm]
  -- (g.find existingId).2 has same hashcons/classes as g, different UF
  exact {
    uf_wf := egraph_find_uf_wf g existingId hwf.uf_wf
    hashcons_consistent := fun n id hget => by
      rw [egraph_find_hashcons] at hget
      obtain ⟨hlt, hcan, hir⟩ := hwf.hashcons_consistent n id hget
      exact ⟨by rw [egraph_find_uf_size]; exact hlt,
             fun child hc => egraph_find_preserves_isRootAt g existingId child (hcan child hc),
             egraph_find_preserves_isRootAt g existingId id hir⟩
    hashcons_complete := fun id cls hget n hn hcan => by
      rw [egraph_find_classes] at hget
      -- Need n.isCanonical g.unionFind from n.isCanonical (g.find existingId).2.unionFind
      have hcan_g : n.isCanonical g.unionFind := fun child hc => by
        have hir := hcan child hc
        have hlt : child < g.unionFind.parent.size := by
          rw [← egraph_find_uf_size g existingId]; exact hir.1
        exact IsRootAt_backward_find g existingId child hwf.uf_wf hir hlt
      obtain ⟨rid, hrid, hroots⟩ := hwf.hashcons_complete id cls hget n hn hcan_g
      exact ⟨rid, by rw [egraph_find_hashcons]; exact hrid,
             by rw [egraph_find_preserves_roots g existingId _ hwf.uf_wf,
                     egraph_find_preserves_roots g existingId _ hwf.uf_wf]; exact hroots⟩
    classes_consistent := ⟨
      fun id hc => by
        rw [egraph_find_classes] at hc
        obtain ⟨hlt, hroot⟩ := hwf.classes_consistent.1 id hc
        exact ⟨by rw [egraph_find_uf_size]; exact hlt,
               egraph_find_preserves_isRootAt g existingId id hroot⟩,
      fun id hlt hroot => by
        rw [egraph_find_classes]
        have hlt_g : id < g.unionFind.parent.size := by
          rw [← egraph_find_uf_size g existingId]; exact hlt
        have hroot_g := IsRootAt_backward_find g existingId id hwf.uf_wf hroot hlt_g
        exact hwf.classes_consistent.2 id hlt_g hroot_g⟩
    hashcons_classes_aligned := fun n id hget => by
      rw [egraph_find_hashcons] at hget; rw [egraph_find_classes]
      exact hwf.hashcons_classes_aligned n id hget
    children_bounded := fun id cls hget n hn child hc => by
      rw [egraph_find_classes] at hget; rw [egraph_find_uf_size]
      exact hwf.children_bounded id cls hget n hn child hc
  }

/-- add of a leaf node preserves EGraphWF — new node branch. -/
private theorem add_leaf_new_wf (g : EGraph) (node : ENode) (hwf : EGraphWF g)
    (hleaf : node.children = []) (hm : g.hashcons.get? node = none) :
    EGraphWF (g.add node).2 := by
  rw [add_leaf_new g node hleaf hm]; simp only []
  -- Result: { uf = push, hashcons = insert, classes = insert }
  exact {
    uf_wf := UnionFind.add_wf g.unionFind hwf.uf_wf
    hashcons_consistent := fun n id hget => by
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
      by_cases hneq : node == n
      · have hnn := beq_iff_eq.mp hneq; subst hnn; simp at hget; subst hget
        refine ⟨?_, fun child hc => by rw [hleaf] at hc; simp at hc,
               ⟨?_, Array.getElem_push_eq⟩⟩
        all_goals show _ < (g.unionFind.parent.push g.unionFind.parent.size).size
        all_goals rw [Array.size_push]; exact Nat.lt_add_one _
      · simp [hneq] at hget
        obtain ⟨hlt, hcan, hir⟩ := hwf.hashcons_consistent n id hget
        refine ⟨?_, fun child hc => IsRootAt_push (hcan child hc), IsRootAt_push hir⟩
        show id < (g.unionFind.parent.push g.unionFind.parent.size).size
        rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt
    hashcons_complete := fun id cls hget n hn hcan => by
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
      by_cases hneq : (g.unionFind.parent.size == id)
      · have hid_eq : g.unionFind.parent.size = id := beq_iff_eq.mp hneq
        subst hid_eq; simp at hget; subst hget
        rw [mem_singleton_nodes] at hn; subst hn
        exact ⟨g.unionFind.parent.size,
          by simp only [Std.HashMap.get?_eq_getElem?]; exact Std.HashMap.getElem?_insert_self, rfl⟩
      · simp [hneq] at hget
        have hget' : g.classes.get? id = some cls := by
          rw [Std.HashMap.get?_eq_getElem?]; exact hget
        have hid_lt := (hwf.classes_consistent.1 id (by
          rw [Std.HashMap.contains_eq_isSome_getElem?]; simp [hget])).1
        have hcan_g : n.isCanonical g.unionFind := fun child hc =>
          IsRootAt_of_push (hcan child hc) (hwf.children_bounded id cls hget' n hn child hc)
        obtain ⟨rid, hrid, hroots⟩ := hwf.hashcons_complete id cls hget' n hn hcan_g
        have hne_key : node ≠ n := fun h => by
          rw [h, Std.HashMap.get?_eq_getElem?] at hm; simp [hm] at hrid
        exact ⟨rid,
          by simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
                         beq_eq_false_iff_ne.mpr hne_key]; exact hrid,
          by rw [root_push_eq hwf.uf_wf (hwf.hashcons_consistent _ rid hrid).1,
                 root_push_eq hwf.uf_wf hid_lt]; exact hroots⟩
    classes_consistent := ⟨
      fun id hc => by
        simp only [Std.HashMap.contains_insert] at hc
        by_cases hneq : (g.unionFind.parent.size == id)
        · have := beq_iff_eq.mp hneq; subst this
          exact ⟨by simp [Array.size_push],
                 ⟨by simp [Array.size_push], Array.getElem_push_eq⟩⟩
        · simp [hneq] at hc
          obtain ⟨hlt, hroot⟩ := hwf.classes_consistent.1 id hc
          refine ⟨?_, IsRootAt_push hroot⟩
          show id < (g.unionFind.parent.push g.unionFind.parent.size).size
          rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt,
      fun id hlt hroot => by
        simp only [Std.HashMap.contains_insert] at *
        by_cases hid : id = g.unionFind.parent.size
        · subst hid; simp
        · have hlt_orig : id < g.unionFind.parent.size := by
            have hsz : (g.unionFind.parent.push g.unionFind.parent.size).size =
                        g.unionFind.parent.size + 1 := by rw [Array.size_push]
            rw [hsz] at hlt
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with h | h
            · exact h
            · exact absurd h hid
          have : (g.unionFind.parent.size == id) = false :=
            beq_eq_false_iff_ne.mpr (Ne.symm hid)
          simp [this]
          exact hwf.classes_consistent.2 id hlt_orig (IsRootAt_of_push hroot hlt_orig)⟩
    hashcons_classes_aligned := fun n id hget => by
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
      by_cases hneq : node == n
      · have hnn : node = n := beq_iff_eq.mp hneq; subst hnn
        simp at hget; subst hget
        exact ⟨EClass.singleton node,
          by simp [Std.HashMap.get?_eq_getElem?],
          (mem_singleton_nodes node node).mpr rfl⟩
      · simp [hneq] at hget
        obtain ⟨cls, hcls, hmem⟩ := hwf.hashcons_classes_aligned n id hget
        have hlt := (hwf.hashcons_consistent n id hget).1
        have hne : (g.unionFind.parent.size == id) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro heq; rw [heq] at hlt; exact Nat.lt_irrefl _ hlt
        refine ⟨cls, ?_, hmem⟩
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hne]
        exact hcls
    children_bounded := fun id cls hget n hn child hc => by
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
      by_cases hneq : (g.unionFind.parent.size == id)
      · simp [hneq] at hget; subst hget
        rw [mem_singleton_nodes] at hn; subst hn; rw [hleaf] at hc; simp at hc
      · simp [hneq] at hget
        have hget' : g.classes.get? id = some cls := by
          rw [Std.HashMap.get?_eq_getElem?]; exact hget
        show child < (g.unionFind.parent.push g.unionFind.parent.size).size
        rw [Array.size_push]; exact Nat.lt_succ_of_lt (hwf.children_bounded id cls hget' n hn child hc)
  }

/-- add of a leaf node preserves EGraphWF. -/
theorem add_leaf_preserves_wf (g : EGraph) (node : ENode) (hwf : EGraphWF g)
    (hleaf : node.children = []) :
    EGraphWF (g.add node).2 := by
  match hm : g.hashcons.get? node with
  | some existingId => exact add_leaf_existing_wf g node existingId hwf hleaf hm
  | none => exact add_leaf_new_wf g node hwf hleaf hm

/-! ## Layer 6: Deduplication -/

theorem add_existing_returns_id (g : EGraph) (node : ENode) (id : EClassId)
    (hleaf : node.children = []) (hget : g.hashcons.get? node = some id) :
    (g.add node).1 = (g.find id).1 := by
  rw [add_leaf_existing g node id hleaf hget]

theorem add_new_returns_fresh (g : EGraph) (node : ENode)
    (hleaf : node.children = []) (hget : g.hashcons.get? node = none) :
    (g.add node).1 = g.unionFind.parent.size := by
  rw [add_leaf_new g node hleaf hget]

theorem egraph_find_fst (g : EGraph) (id : EClassId) :
    (g.find id).1 = root g.unionFind id := find_fst_eq_root g.unionFind id

private theorem find_root_eq (g : EGraph) (id : EClassId)
    (hwf : WellFormed g.unionFind) (hid : id < g.unionFind.parent.size) :
    root (g.find id).2.unionFind (g.find id).1 = root g.unionFind id := by
  rw [egraph_find_fst, egraph_find_preserves_roots g id _ hwf]
  exact root_idempotent g.unionFind id hwf hid

theorem add_idempotent (g : EGraph) (node : ENode) (hwf : EGraphWF g)
    (hleaf : node.children = []) :
    let r1 := g.add node
    root r1.2.unionFind r1.1 =
      root (r1.2.add node).2.unionFind (r1.2.add node).1 := by
  simp only
  match hm : g.hashcons.get? node with
  | some existingId =>
    rw [add_leaf_existing g node existingId hleaf hm,
        add_leaf_existing (g.find existingId).2 node existingId hleaf
          (by rw [egraph_find_hashcons]; exact hm)]
    have hid := (hwf.hashcons_consistent node existingId hm).1
    have hwf1 := egraph_find_uf_wf g existingId hwf.uf_wf
    have hid1 : existingId < (g.find existingId).2.unionFind.parent.size := by
      rw [egraph_find_uf_size]; exact hid
    rw [find_root_eq _ existingId hwf1 hid1, find_root_eq g existingId hwf.uf_wf hid]
    exact (egraph_find_preserves_roots g existingId existingId hwf.uf_wf).symm
  | none =>
    rw [add_leaf_new g node hleaf hm]
    simp only []
    have hins : (g.hashcons.insert node g.unionFind.parent.size).get? node =
        some g.unionFind.parent.size :=
      hashcons_get?_insert_self _ _ _
    rw [add_leaf_existing _ node g.unionFind.parent.size hleaf hins]
    have hwf' : EGraphWF (g.add node).2 := add_leaf_preserves_wf g node hwf hleaf
    rw [add_leaf_new g node hleaf hm] at hwf'
    simp only [] at hwf'
    have hN : g.unionFind.parent.size <
        (g.unionFind.parent.push g.unionFind.parent.size).size := by
      simp [Array.size_push]
    rw [find_root_eq _ g.unionFind.parent.size hwf'.uf_wf hN]

/-! ## Layer 7: Composition -/

theorem adds_leaf_preserve_wf (g : EGraph) (nodes : List ENode) (hwf : EGraphWF g)
    (hleaf : ∀ nd, nd ∈ nodes → nd.children = []) :
    EGraphWF (nodes.foldl (fun acc n => (acc.add n).2) g) := by
  induction nodes generalizing g with
  | nil => exact hwf
  | cons n rest ih =>
    simp only [List.foldl]
    exact ih _ (add_leaf_preserves_wf g n hwf (hleaf n (.head rest)))
      (fun nd hnd => hleaf nd (.tail n hnd))

/-! ## Layer 8: Merge Lemmas (Fase 6 Subfase 4) -/

/-- Merge does not touch hashcons. -/
theorem merge_hashcons (g : EGraph) (id1 id2 : EClassId) :
    (g.merge id1 id2).hashcons = g.hashcons := by
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  split -- root1 == root2
  · rfl
  · rfl

/-- Merge preserves UF parent array size. -/
theorem merge_uf_size (g : EGraph) (id1 id2 : EClassId) :
    (g.merge id1 id2).unionFind.parent.size = g.unionFind.parent.size := by
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  split -- root1 == root2
  · rw [find_snd_size, find_snd_size]
  · simp only []
    rw [union_size, find_snd_size, find_snd_size]

/-- Nodes in the foldl-based union are from either input. -/
private theorem foldl_push_subset (xs : Array ENode) (init : Array ENode) :
    ∀ n, n ∈ (xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) init).toList →
    n ∈ init.toList ∨ n ∈ xs.toList := by
  intro n hmem
  exact (@Array.foldl_induction ENode (Array ENode) xs
    (fun (_ : Nat) (acc : Array ENode) => n ∈ acc.toList → n ∈ init.toList ∨ n ∈ xs.toList)
    init (fun h => .inl h)
    (fun (acc : Array ENode) (x : ENode) => if acc.contains x then acc else acc.push x)
    (fun ⟨i, hi⟩ (b : Array ENode) ih => by
      intro hmem
      dsimp only at hmem
      split at hmem
      · exact ih hmem
      · rw [Array.toList_push] at hmem
        rcases List.mem_append.mp hmem with h | h
        · exact ih h
        · exact .inr (List.mem_singleton.mp h ▸
            Array.mem_toList_iff.mpr (Array.getElem_mem hi)))) hmem

/-- If n is a node in (ec1.union ec2), then n was in ec1 or ec2. -/
theorem eclass_union_mem (ec1 ec2 : EClass) (n : ENode)
    (h : n ∈ (ec1.union ec2).nodes.toList) :
    n ∈ ec1.nodes.toList ∨ n ∈ ec2.nodes.toList := by
  simp only [EClass.union] at h
  exact foldl_push_subset ec2.nodes ec1.nodes n h

/-- Merge preserves ChildrenBounded. -/
theorem merge_preserves_children_bounded (g : EGraph) (id1 id2 : EClassId)
    (hwf : EGraphWF g) :
    ChildrenBounded (g.merge id1 id2) := by
  unfold ChildrenBounded EGraph.merge EGraph.find
  simp only [find_fst_eq_root]
  split
  · -- Equal roots: classes unchanged (find only modifies UF)
    intro id cls hget node hn child hc
    show child < _; rw [find_snd_size, find_snd_size]
    exact hwf.children_bounded id cls hget node hn child hc
  · -- Different roots: classes = g.classes.insert root1 mergedClass
    intro id cls hget node hn child hc
    simp only [] at hget ⊢
    rw [union_size, find_snd_size, find_snd_size]
    -- hget : (g.classes.insert root1 mergedClass).get? id = some cls
    -- Case split: id = root1 or id ≠ root1
    by_cases hid : root g.unionFind id1 = id
    · -- id = root1: cls = mergedClass
      subst hid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, ite_true] at hget
      -- hget : some mergedClass = some cls → mergedClass = cls
      have hcls := Option.some.inj hget
      rw [← hcls] at hn
      -- node ∈ mergedClass.nodes.toList → came from class1 or class2
      rcases eclass_union_mem _ _ node hn with h1 | h2
      · -- node from class1
        cases hcls1 : g.classes[root g.unionFind id1]? with
        | none =>
          simp only [hcls1, Option.getD,
            show (default : EClass).nodes = #[] from rfl] at h1
          exact nomatch h1
        | some c1 =>
          simp only [hcls1, Option.getD_some] at h1
          exact hwf.children_bounded _ c1
            (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls1) node h1 child hc
      · -- node from class2
        cases hcls2 : g.classes[(g.unionFind.find id1).snd.root id2]? with
        | none =>
          simp only [hcls2, Option.getD,
            show (default : EClass).nodes = #[] from rfl] at h2
          exact nomatch h2
        | some c2 =>
          simp only [hcls2, Option.getD_some] at h2
          exact hwf.children_bounded _ c2
            (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls2) node h2 child hc
    · -- id ≠ root1: cls from g.classes
      have hget' : g.classes.get? id = some cls := by
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          beq_eq_false_iff_ne.mpr hid] at hget
        rw [Std.HashMap.get?_eq_getElem?]; exact hget
      exact hwf.children_bounded id cls hget' node hn child hc

/-- Merge preserves UF WellFormed when id1 is in bounds. -/
theorem merge_preserves_uf_wf (g : EGraph) (id1 id2 : EClassId)
    (hwf : EGraphWF g) (h1 : id1 < g.unionFind.parent.size) :
    WellFormed (g.merge id1 id2).unionFind := by
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  split
  · exact find_preserves_wf _ id2 (find_preserves_wf g.unionFind id1 hwf.uf_wf)
  · simp only []
    exact union_preserves_wf _ _ _
      (find_preserves_wf _ id2 (find_preserves_wf g.unionFind id1 hwf.uf_wf))
      (by rw [find_snd_size, find_snd_size]; exact rootD_bounded hwf.uf_wf.1 h1)

/-- After merge(g, id1, id2), root(id1) = root(id2) in the merged e-graph. -/
theorem merge_creates_equiv (g : EGraph) (id1 id2 : EClassId)
    (hwf : EGraphWF g) (h1 : id1 < g.unionFind.parent.size)
    (h2 : id2 < g.unionFind.parent.size) :
    root (g.merge id1 id2).unionFind (root g.unionFind id1) =
    root (g.merge id1 id2).unionFind (root g.unionFind id2) := by
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  split
  · -- Equal roots: result is g2 without union
    next heq =>
    have hwf1 := find_preserves_wf g.unionFind id1 hwf.uf_wf
    have h_fpr1 : ∀ j, root (g.unionFind.find id1).2 j = root g.unionFind j :=
      fun j => find_preserves_roots g.unionFind id1 j hwf.uf_wf
    have h_fpr2 : ∀ j, root ((g.unionFind.find id1).2.find id2).2 j =
        root (g.unionFind.find id1).2 j :=
      fun j => find_preserves_roots (g.unionFind.find id1).2 id2 j hwf1
    simp only [h_fpr2, h_fpr1]
    rw [root_idempotent g.unionFind id1 hwf.uf_wf h1,
        root_idempotent g.unionFind id2 hwf.uf_wf h2]
    have := beq_iff_eq.mp heq
    rwa [h_fpr1] at this
  · -- Different roots: apply union_creates_equiv
    next hneq =>
    simp only []
    have hwf1 := find_preserves_wf g.unionFind id1 hwf.uf_wf
    have hwf2 := find_preserves_wf _ id2 hwf1
    have h_fpr1 : ∀ j, root (g.unionFind.find id1).2 j = root g.unionFind j :=
      fun j => find_preserves_roots g.unionFind id1 j hwf.uf_wf
    have h_fpr2 : ∀ j, root ((g.unionFind.find id1).2.find id2).2 j =
        root (g.unionFind.find id1).2 j :=
      fun j => find_preserves_roots (g.unionFind.find id1).2 id2 j hwf1
    -- Rewrite second union arg to use root g.uf id2
    rw [h_fpr1 id2]
    have hbnd1 : root g.unionFind id1 <
        ((g.unionFind.find id1).2.find id2).2.parent.size := by
      rw [find_snd_size, find_snd_size]; exact rootD_bounded hwf.uf_wf.1 h1
    have hbnd2 : root g.unionFind id2 <
        ((g.unionFind.find id1).2.find id2).2.parent.size := by
      rw [find_snd_size, find_snd_size]; exact rootD_bounded hwf.uf_wf.1 h2
    have key := union_creates_equiv _ _ _ hwf2 hbnd1 hbnd2
    simp only [h_fpr2, h_fpr1] at key
    rw [root_idempotent g.unionFind id1 hwf.uf_wf h1,
        root_idempotent g.unionFind id2 hwf.uf_wf h2] at key
    exact key

/-- Merge preserves existing equivalences. -/
theorem merge_preserves_equiv (g : EGraph) (id1 id2 a b : EClassId)
    (hwf : EGraphWF g) (heq_ab : root g.unionFind a = root g.unionFind b) :
    root (g.merge id1 id2).unionFind a = root (g.merge id1 id2).unionFind b := by
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  split
  · -- Equal roots: result is g2 without union
    have hwf1 := find_preserves_wf g.unionFind id1 hwf.uf_wf
    have h_fpr1 : ∀ j, root (g.unionFind.find id1).2 j = root g.unionFind j :=
      fun j => find_preserves_roots g.unionFind id1 j hwf.uf_wf
    have h_fpr2 : ∀ j, root ((g.unionFind.find id1).2.find id2).2 j =
        root (g.unionFind.find id1).2 j :=
      fun j => find_preserves_roots (g.unionFind.find id1).2 id2 j hwf1
    simp only [h_fpr2, h_fpr1]; exact heq_ab
  · -- Different roots: apply union_preserves_equiv
    simp only []
    have hwf1 := find_preserves_wf g.unionFind id1 hwf.uf_wf
    have hwf2 := find_preserves_wf _ id2 hwf1
    have h_fpr1 : ∀ j, root (g.unionFind.find id1).2 j = root g.unionFind j :=
      fun j => find_preserves_roots g.unionFind id1 j hwf.uf_wf
    have h_fpr2 : ∀ j, root ((g.unionFind.find id1).2.find id2).2 j =
        root (g.unionFind.find id1).2 j :=
      fun j => find_preserves_roots (g.unionFind.find id1).2 id2 j hwf1
    have heq_g2 : root ((g.unionFind.find id1).2.find id2).2 a =
        root ((g.unionFind.find id1).2.find id2).2 b := by
      simp only [h_fpr2, h_fpr1]; exact heq_ab
    exact union_preserves_equiv _ _ _ _ _ hwf2 heq_g2

/-- Weaker invariant that merge preserves (hashcons/classes are NOT consistent
    with the new UF, but key sub-properties hold). Rebuild restores full WF. -/
structure PostMergeInvariant (eg : EGraph) : Prop where
  uf_wf : WellFormed eg.unionFind
  children_bounded : ChildrenBounded eg
  hashcons_entries_valid : ∀ node id, eg.hashcons.get? node = some id →
    id < eg.unionFind.parent.size
  classes_entries_valid : ∀ id, eg.classes.contains id = true →
    id < eg.unionFind.parent.size

/-- Merge preserves the PostMergeInvariant. -/
theorem merge_post_invariant (g : EGraph) (id1 id2 : EClassId)
    (hwf : EGraphWF g) (h1 : id1 < g.unionFind.parent.size) :
    PostMergeInvariant (g.merge id1 id2) where
  uf_wf := merge_preserves_uf_wf g id1 id2 hwf h1
  children_bounded := merge_preserves_children_bounded g id1 id2 hwf
  hashcons_entries_valid := by
    intro node id hget
    rw [merge_hashcons] at hget; rw [merge_uf_size]
    exact (hwf.hashcons_consistent node id hget).1
  classes_entries_valid := by
    intro id hcont; rw [merge_uf_size]
    unfold EGraph.merge EGraph.find at hcont; simp only [find_fst_eq_root] at hcont
    split at hcont
    · exact (hwf.classes_consistent.1 id hcont).1
    · simp only [] at hcont
      rw [Std.HashMap.contains_insert] at hcont
      rcases Bool.or_eq_true_iff.mp hcont with heq | hc
      · exact beq_iff_eq.mp heq ▸ rootD_bounded hwf.uf_wf.1 h1
      · exact (hwf.classes_consistent.1 id hc).1

/-! ## Layer 9: Rebuild Foundations (Fase 6 Subfase 5) -/

/-! ### Paso 0: canonicalize_uf_size + HashMap erase bridges -/

theorem canonicalize_uf_size (g : EGraph) (node : ENode) :
    (g.canonicalize node).2.unionFind.parent.size = g.unionFind.parent.size := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]
  · simp [h]; exact go_uf_size _ _ _

theorem hashcons_get?_erase_self (hm : Std.HashMap ENode EClassId) (k : ENode) :
    (hm.erase k).get? k = none := by
  simp [Std.HashMap.get?_eq_getElem?]

theorem hashcons_get?_erase_ne (hm : Std.HashMap ENode EClassId)
    (k a : ENode) (hne : k ≠ a) :
    (hm.erase k).get? a = hm.get? a := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase,
             beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]

theorem hashcons_get?_erase_insert_self (hm : Std.HashMap ENode EClassId)
    (k : ENode) (id : EClassId) :
    ((hm.erase k).insert k id).get? k = some id := by
  simp [Std.HashMap.get?_eq_getElem?]

theorem hashcons_get?_erase_insert_ne (hm : Std.HashMap ENode EClassId)
    (erased inserted query : ENode) (id : EClassId)
    (hne : inserted ≠ query) :
    ((hm.erase erased).insert inserted id).get? query =
    (hm.erase erased).get? query := by
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_eq_false_iff_ne.mpr hne]

/-! ### Paso 1: processClass structural lemmas -/

theorem processClass_classes (g : EGraph) (classId : EClassId) :
    (g.processClass classId).1.classes = g.classes := by
  unfold EGraph.processClass
  -- After find: g1.classes = g.classes
  -- After match none: g1.classes = g.classes ✓
  -- After match some: foldl preserves classes (each step only modifies hashcons)
  show (match (g.find classId).2.classes.get? (g.find classId).1 with
    | none => ((g.find classId).2, [])
    | some eclass => _).1.classes = g.classes
  rw [egraph_find_classes]
  split
  · exact egraph_find_classes g classId
  · rename_i eclass heclass
    -- The foldl body only modifies hashcons via {acc1 with hashcons := ...}
    -- and canonicalize preserves classes. Prove by foldl_induction.
    exact @Array.foldl_induction ENode (EGraph × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (p : EGraph × List (EClassId × EClassId)) => p.1.classes = g.classes)
      ((g.find classId).2, [])
      (egraph_find_classes g classId)
      _
      (fun ⟨i, hi⟩ ⟨acc, merges⟩ ih => by
        dsimp only
        -- Step: let (canonNode, acc1) := acc.canonicalize node; ...
        -- acc1.classes = acc.classes = g.classes (by canonicalize_classes + ih)
        have hcls : (acc.canonicalize eclass.nodes[i]).2.classes = g.classes := by
          rw [canonicalize_classes]; exact ih
        split -- if canonNode == node
        · exact hcls
        · split -- match hashcons1.get? canonNode
          · exact hcls  -- { acc1 with hashcons := ... }.classes = acc1.classes
          · exact hcls)

theorem processClass_uf_size (g : EGraph) (classId : EClassId) :
    (g.processClass classId).1.unionFind.parent.size = g.unionFind.parent.size := by
  unfold EGraph.processClass
  show (match (g.find classId).2.classes.get? (g.find classId).1 with
    | none => ((g.find classId).2, [])
    | some eclass => _).1.unionFind.parent.size = g.unionFind.parent.size
  rw [egraph_find_classes]
  split
  · exact egraph_find_uf_size g classId
  · rename_i eclass heclass
    exact @Array.foldl_induction ENode (EGraph × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (p : EGraph × List (EClassId × EClassId)) =>
        p.1.unionFind.parent.size = g.unionFind.parent.size)
      ((g.find classId).2, [])
      (egraph_find_uf_size g classId)
      _
      (fun ⟨i, hi⟩ ⟨acc, merges⟩ ih => by
        dsimp only
        have husz : (acc.canonicalize eclass.nodes[i]).2.unionFind.parent.size =
            g.unionFind.parent.size := by
          rw [canonicalize_uf_size]; exact ih
        split
        · exact husz
        · split
          · exact husz
          · exact husz)

theorem processClass_preserves_roots (g : EGraph) (classId : EClassId)
    (hwf : WellFormed g.unionFind) (j : EClassId) :
    root (g.processClass classId).1.unionFind j = root g.unionFind j := by
  unfold EGraph.processClass
  show (match (g.find classId).2.classes.get? (g.find classId).1 with
    | none => ((g.find classId).2, [])
    | some eclass => _).1.unionFind.root j = g.unionFind.root j
  rw [egraph_find_classes]
  split
  · exact egraph_find_preserves_roots g classId j hwf
  · rename_i eclass _
    exact (@Array.foldl_induction ENode (EGraph × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (p : EGraph × List (EClassId × EClassId)) =>
        (∀ k, root p.1.unionFind k = root g.unionFind k) ∧
        WellFormed p.1.unionFind)
      ((g.find classId).2, [])
      ⟨fun k => egraph_find_preserves_roots g classId k hwf,
       egraph_find_uf_wf g classId hwf⟩
      _
      (fun ⟨i, hi⟩ ⟨acc, merges⟩ ⟨ih_root, ih_wf⟩ => by
        dsimp only
        have canon_root : ∀ k, root (acc.canonicalize eclass.nodes[i]).2.unionFind k =
            root g.unionFind k := by
          intro k; rw [canonicalize_preserves_roots acc _ ih_wf k]; exact ih_root k
        have canon_wf : WellFormed (acc.canonicalize eclass.nodes[i]).2.unionFind :=
          canonicalize_uf_wf acc _ ih_wf
        split
        · exact ⟨canon_root, canon_wf⟩
        · split
          · exact ⟨canon_root, canon_wf⟩
          · exact ⟨canon_root, canon_wf⟩)).1 j

/-! ### Paso 2-3: processClass preserves PostMergeInvariant -/

/-- Helper: classId is in bounds if processClass finds a class for it. -/
private theorem canonId_bounded (g : EGraph) (classId : EClassId)
    (hpmi : PostMergeInvariant g)
    (heclass : ∃ ec, g.classes.get? (g.find classId).1 = some ec) :
    (g.find classId).1 < g.unionFind.parent.size := by
  obtain ⟨ec, hec⟩ := heclass
  apply hpmi.classes_entries_valid
  rw [Std.HashMap.contains_eq_isSome_getElem?,
      show g.classes[(g.find classId).1]? = g.classes.get? (g.find classId).1 from
        (Std.HashMap.get?_eq_getElem? ..).symm, hec]
  rfl

/-- Combined invariant: processClass preserves PMI components and emits bounded merges. -/
private theorem processClass_invariant (g : EGraph) (classId : EClassId)
    (hpmi : PostMergeInvariant g) :
    WellFormed (g.processClass classId).1.unionFind ∧
    (∀ node id, (g.processClass classId).1.hashcons.get? node = some id →
      id < g.unionFind.parent.size) ∧
    (∀ p ∈ (g.processClass classId).2, p.1 < g.unionFind.parent.size ∧
      p.2 < g.unionFind.parent.size) := by
  -- g1 properties
  have g1_wf := egraph_find_uf_wf g classId hpmi.uf_wf
  have g1_hv : ∀ n id, (g.find classId).2.hashcons.get? n = some id →
      id < g.unionFind.parent.size := by
    intro n i h; rw [egraph_find_hashcons] at h; exact hpmi.hashcons_entries_valid n i h
  -- Use same show pattern as processClass_classes
  unfold EGraph.processClass
  show let r := (match (g.find classId).2.classes.get? (g.find classId).1 with
    | none => ((g.find classId).2, [])
    | some eclass => _)
    WellFormed r.1.unionFind ∧
    (∀ node id, r.1.hashcons.get? node = some id → id < g.unionFind.parent.size) ∧
    (∀ (p : EClassId × EClassId), p ∈ r.2 → p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size)
  rw [egraph_find_classes]
  split
  · exact ⟨g1_wf, g1_hv, fun _ h => nomatch h⟩
  · rename_i eclass heclass
    have canonId_bnd : (g.find classId).1 < g.unionFind.parent.size :=
      canonId_bounded g classId hpmi ⟨eclass, heclass⟩
    -- Extract all 3 properties from foldl_induction
    exact @Array.foldl_induction ENode (EGraph × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (p : EGraph × List (EClassId × EClassId)) =>
        WellFormed p.1.unionFind ∧
        (∀ node id, p.1.hashcons.get? node = some id →
          id < g.unionFind.parent.size) ∧
        (∀ (p' : EClassId × EClassId), p' ∈ p.2 → p'.1 < g.unionFind.parent.size ∧
          p'.2 < g.unionFind.parent.size))
      ((g.find classId).2, [])
      ⟨g1_wf, g1_hv, fun _ h => nomatch h⟩
      _
      (fun ⟨i, hi⟩ b ih => by
        obtain ⟨acc, merges⟩ := b
        obtain ⟨ih_wf, ih_hv, ih_mg⟩ := ih
        dsimp only at ih_wf ih_hv ih_mg ⊢
        -- acc1 properties (through canonicalize)
        have acc1_wf : WellFormed (acc.canonicalize eclass.nodes[i]).2.unionFind :=
          canonicalize_uf_wf acc _ ih_wf
        have acc1_hcs : (acc.canonicalize eclass.nodes[i]).2.hashcons = acc.hashcons :=
          canonicalize_hashcons acc _
        have acc1_hv : ∀ n id,
            (acc.canonicalize eclass.nodes[i]).2.hashcons.get? n = some id →
            id < g.unionFind.parent.size := by
          intro n id h; rw [acc1_hcs] at h; exact ih_hv n id h
        -- Split on the if (canonNode == node) in the goal
        split
        · -- canonNode == node: result is (acc1, merges)
          exact ⟨acc1_wf, acc1_hv, ih_mg⟩
        · -- canonNode ≠ node: erase + insert
          -- erase validity
          have erase_hv : ∀ n id,
              ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).get? n =
                some id → id < g.unionFind.parent.size := by
            intro n id hget
            by_cases hnn : eclass.nodes[i] = n
            · subst hnn; rw [hashcons_get?_erase_self] at hget; exact nomatch hget
            · rw [hashcons_get?_erase_ne _ _ _ hnn] at hget; exact acc1_hv n id hget
          -- Helper for hashcons entries valid after erase+insert of canonId
          have insert_hv : ∀ n id,
              (((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
                (acc.canonicalize eclass.nodes[i]).1 (g.find classId).1).get? n = some id →
              id < g.unionFind.parent.size := by
            intro n id hget
            by_cases hcn : (acc.canonicalize eclass.nodes[i]).1 = n
            · subst hcn; rw [hashcons_get?_insert_self] at hget
              exact Option.some.inj hget ▸ canonId_bnd
            · rw [hashcons_get?_insert_ne _ _ _ _ hcn] at hget
              exact erase_hv n id hget
          -- Case split on match (hashcons1.get? canonNode)
          split
          · -- some existingId
            rename_i existingId hexists
            refine ⟨acc1_wf, insert_hv, ?_⟩
            intro ⟨a, b⟩ hp
            simp only [List.mem_cons] at hp
            rcases hp with heq | hp
            · have h1 := (Prod.mk.inj heq).1; have h2 := (Prod.mk.inj heq).2
              exact ⟨h1 ▸ canonId_bnd, h2 ▸ erase_hv _ _ hexists⟩
            · exact ih_mg ⟨a, b⟩ hp
          · -- none
            exact ⟨acc1_wf, insert_hv, ih_mg⟩)

/-- processClass preserves PostMergeInvariant. -/
theorem processClass_preserves_pmi (g : EGraph) (classId : EClassId)
    (hpmi : PostMergeInvariant g) :
    PostMergeInvariant (g.processClass classId).1 := by
  obtain ⟨hwf, hhv, _⟩ := processClass_invariant g classId hpmi
  exact {
    uf_wf := hwf
    children_bounded := fun id cls hget node hn child hc => by
      rw [processClass_classes] at hget
      rw [processClass_uf_size]
      exact hpmi.children_bounded id cls hget node hn child hc
    hashcons_entries_valid := fun node id hget => by
      rw [processClass_uf_size]
      exact hhv node id hget
    classes_entries_valid := fun id hcont => by
      rw [processClass_classes] at hcont
      rw [processClass_uf_size]
      exact hpmi.classes_entries_valid id hcont
  }

/-- All merge pairs emitted by processClass are bounded. -/
theorem processClass_merges_bounded (g : EGraph) (classId : EClassId)
    (hpmi : PostMergeInvariant g) :
    ∀ (p : EClassId × EClassId), p ∈ (g.processClass classId).2 →
      p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size := by
  exact (processClass_invariant g classId hpmi).2.2

/-! ### Paso 4: merge_preserves_pmi (PMI → PMI) -/

/-- Factored: merge preserves UF WellFormed, requiring only WellFormed (not EGraphWF). -/
theorem merge_preserves_uf_wf' (g : EGraph) (id1 id2 : EClassId)
    (hufwf : WellFormed g.unionFind) (h1 : id1 < g.unionFind.parent.size) :
    WellFormed (g.merge id1 id2).unionFind := by
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  split
  · exact find_preserves_wf _ id2 (find_preserves_wf g.unionFind id1 hufwf)
  · simp only []
    exact union_preserves_wf _ _ _
      (find_preserves_wf _ id2 (find_preserves_wf g.unionFind id1 hufwf))
      (by rw [find_snd_size, find_snd_size]; exact rootD_bounded hufwf.1 h1)

/-- Factored: merge preserves ChildrenBounded, requiring only ChildrenBounded (not EGraphWF). -/
theorem merge_preserves_children_bounded' (g : EGraph) (id1 id2 : EClassId)
    (hcb : ChildrenBounded g) :
    ChildrenBounded (g.merge id1 id2) := by
  unfold ChildrenBounded EGraph.merge EGraph.find
  simp only [find_fst_eq_root]
  split
  · intro id cls hget node hn child hc
    show child < _; rw [find_snd_size, find_snd_size]
    exact hcb id cls hget node hn child hc
  · intro id cls hget node hn child hc
    simp only [] at hget ⊢
    rw [union_size, find_snd_size, find_snd_size]
    by_cases hid : root g.unionFind id1 = id
    · subst hid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, ite_true] at hget
      have hcls := Option.some.inj hget
      rw [← hcls] at hn
      rcases eclass_union_mem _ _ node hn with h1 | h2
      · cases hcls1 : g.classes[root g.unionFind id1]? with
        | none =>
          simp only [hcls1, Option.getD,
            show (default : EClass).nodes = #[] from rfl] at h1
          exact nomatch h1
        | some c1 =>
          simp only [hcls1, Option.getD_some] at h1
          exact hcb _ c1
            (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls1) node h1 child hc
      · cases hcls2 : g.classes[(g.unionFind.find id1).snd.root id2]? with
        | none =>
          simp only [hcls2, Option.getD,
            show (default : EClass).nodes = #[] from rfl] at h2
          exact nomatch h2
        | some c2 =>
          simp only [hcls2, Option.getD_some] at h2
          exact hcb _ c2
            (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls2) node h2 child hc
    · have hget' : g.classes.get? id = some cls := by
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          beq_eq_false_iff_ne.mpr hid] at hget
        rw [Std.HashMap.get?_eq_getElem?]; exact hget
      exact hcb id cls hget' node hn child hc

/-- Merge preserves PostMergeInvariant (PMI → PMI). -/
theorem merge_preserves_pmi (g : EGraph) (id1 id2 : EClassId)
    (hpmi : PostMergeInvariant g) (h1 : id1 < g.unionFind.parent.size) :
    PostMergeInvariant (g.merge id1 id2) where
  uf_wf := merge_preserves_uf_wf' g id1 id2 hpmi.uf_wf h1
  children_bounded := merge_preserves_children_bounded' g id1 id2 hpmi.children_bounded
  hashcons_entries_valid := by
    intro node id hget
    rw [merge_hashcons] at hget; rw [merge_uf_size]
    exact hpmi.hashcons_entries_valid node id hget
  classes_entries_valid := by
    intro id hcont; rw [merge_uf_size]
    unfold EGraph.merge EGraph.find at hcont; simp only [find_fst_eq_root] at hcont
    split at hcont
    · exact hpmi.classes_entries_valid id hcont
    · simp only [] at hcont
      rw [Std.HashMap.contains_insert] at hcont
      rcases Bool.or_eq_true_iff.mp hcont with heq | hc
      · exact beq_iff_eq.mp heq ▸ rootD_bounded hpmi.uf_wf.1 h1
      · exact hpmi.classes_entries_valid id hc

/-! ### Paso 5: rebuildStep_preserves_pmi -/

/-- Applying a list of bounded merges preserves PostMergeInvariant. -/
theorem mergeAll_preserves_pmi : ∀ (merges : List (EClassId × EClassId))
    (g : EGraph),
    PostMergeInvariant g →
    (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) →
    PostMergeInvariant (merges.foldl (fun acc p => acc.merge p.1 p.2) g) := by
  intro merges
  induction merges with
  | nil => intro g hpmi _; exact hpmi
  | cons hd tl ih =>
    intro g hpmi hbnd
    simp only [List.foldl_cons]
    have hhd := hbnd hd (.head _)
    have h_pmi' := merge_preserves_pmi g hd.1 hd.2 hpmi hhd.1
    have h_size' := merge_uf_size g hd.1 hd.2
    exact ih _ h_pmi' (fun p hp => by
      rw [h_size']; exact hbnd p (.tail _ hp))

/-- Processing a list of classes preserves PMI, UF size, and bounds emitted merges. -/
theorem processAll_preserves_pmi : ∀ (toProcess : List EClassId)
    (g : EGraph) (merges : List (EClassId × EClassId)),
    PostMergeInvariant g →
    (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) →
    let result := toProcess.foldl
      (fun (am : EGraph × List (EClassId × EClassId)) (cid : EClassId) =>
        ((am.1.processClass cid).1, (am.1.processClass cid).2 ++ am.2))
      (g, merges)
    PostMergeInvariant result.1 ∧
    result.1.unionFind.parent.size = g.unionFind.parent.size ∧
    (∀ p ∈ result.2, p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) := by
  intro toProcess
  induction toProcess with
  | nil => intro g merges hpmi hbnd; exact ⟨hpmi, rfl, hbnd⟩
  | cons hd tl ih =>
    intro g merges hpmi hbnd
    simp only [List.foldl_cons]
    have h_pmi' := processClass_preserves_pmi g hd hpmi
    have h_size' := processClass_uf_size g hd
    have h_mg := processClass_merges_bounded g hd hpmi
    have hbnd' : ∀ p ∈ (g.processClass hd).2 ++ merges,
        p.1 < (g.processClass hd).1.unionFind.parent.size ∧
        p.2 < (g.processClass hd).1.unionFind.parent.size := by
      intro p hp; rw [h_size']
      rcases List.mem_append.mp hp with h | h
      · exact h_mg p h
      · exact hbnd p h
    have := ih _ _ h_pmi' hbnd'
    obtain ⟨hpmi'', hsize'', hbnd''⟩ := this
    exact ⟨hpmi'', by rw [hsize'', h_size'],
      fun p hp => by rw [← h_size']; exact hbnd'' p hp⟩

/-- Clearing worklist/dirtyArr preserves PostMergeInvariant. -/
theorem clear_worklist_pmi (g : EGraph) (hpmi : PostMergeInvariant g) :
    PostMergeInvariant { g with worklist := ([] : List EClassId), dirtyArr := #[] } where
  uf_wf := hpmi.uf_wf
  children_bounded := hpmi.children_bounded
  hashcons_entries_valid := hpmi.hashcons_entries_valid
  classes_entries_valid := hpmi.classes_entries_valid

/-- One rebuild step (processAll then mergeAll) preserves PostMergeInvariant. -/
theorem rebuildStep_preserves_pmi (g : EGraph) (toProcess : List EClassId)
    (hpmi : PostMergeInvariant g) :
    let g1 : EGraph := { g with worklist := ([] : List EClassId), dirtyArr := #[] }
    let result := toProcess.foldl
      (fun (am : EGraph × List (EClassId × EClassId)) (cid : EClassId) =>
        ((am.1.processClass cid).1, (am.1.processClass cid).2 ++ am.2))
      (g1, [])
    PostMergeInvariant (result.2.foldl (fun acc p => acc.merge p.1 p.2) result.1) := by
  have hpmi1 := clear_worklist_pmi g hpmi
  have hpa := processAll_preserves_pmi toProcess
    { g with worklist := ([] : List EClassId), dirtyArr := #[] } []
    hpmi1 (fun _ h => nomatch h)
  obtain ⟨hpmi2, hsize2, hbnd2⟩ := hpa
  exact mergeAll_preserves_pmi _ _ hpmi2 (fun p hp => by rw [hsize2]; exact hbnd2 p hp)

/-! ## Layer 9: addExpr Infrastructure — general add for non-leaf nodes -/

/-- Minimal invariant sufficient for addExpr consistency proofs.
    Weaker than EGraphWF — omits hashcons_consistent, hashcons_complete, classes_consistent. -/
structure AddExprInv (eg : EGraph) : Prop where
  uf_wf : WellFormed eg.unionFind
  children_bounded : ChildrenBounded eg
  hashcons_classes_aligned : HashconsClassesAligned eg
  hashcons_entries_valid : ∀ node id, eg.hashcons.get? node = some id →
    id < eg.unionFind.parent.size

theorem EGraphWF.toAddExprInv (hwf : EGraphWF g) : AddExprInv g where
  uf_wf := hwf.uf_wf
  children_bounded := hwf.children_bounded
  hashcons_classes_aligned := hwf.hashcons_classes_aligned
  hashcons_entries_valid := fun n id hget => (hwf.hashcons_consistent n id hget).1

/-- go helper produces pairs whose .2 components are bounded. -/
private theorem go_output_bounded (cs : List EClassId) (g : EGraph)
    (ps : List (EClassId × EClassId)) (bound : Nat)
    (hwf : WellFormed g.unionFind)
    (hsz : g.unionFind.parent.size = bound)
    (hps : ∀ p ∈ ps, p.2 < bound)
    (hcs : ∀ c ∈ cs, c < bound) :
    ∀ p ∈ (EGraph.canonicalize.go cs g ps).1, p.2 < bound := by
  induction cs generalizing g ps with
  | nil => unfold EGraph.canonicalize.go; exact hps
  | cons c rest ih =>
    unfold EGraph.canonicalize.go
    have hwf' := egraph_find_uf_wf g c hwf
    have hsz' : (g.find c).2.unionFind.parent.size = bound := by
      rw [egraph_find_uf_size]; exact hsz
    have hc_lt : c < bound := hcs c (List.Mem.head rest)
    have hps' : ∀ p ∈ ((c, (g.find c).1) :: ps), p.2 < bound := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp; rw [egraph_find_fst, ← hsz]
        exact rootD_bounded hwf.1 (hsz ▸ hc_lt)
      · exact hps p hp
    have hcs' : ∀ c' ∈ rest, c' < bound :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    exact ih (g.find c).2 ((c, (g.find c).1) :: ps) hwf' hsz' hps' hcs'

/-- Helper: if pairs come from go_output_bounded and f is the lookup function,
    then f maps bounded IDs to bounded IDs. -/
private theorem lookup_bounded
    (pairs : List (EClassId × EClassId)) (bound : Nat)
    (hpairs : ∀ p ∈ pairs, p.2 < bound) (id : EClassId) (hid : id < bound) :
    (match pairs.find? (fun (old, _) => old == id) with
     | some (_, new_) => new_
     | none => id) < bound := by
  split
  · rename_i _ new_ heq
    exact hpairs _ (List.mem_of_find?_eq_some heq)
  · exact hid

/-- Children of (g.canonicalize node).1 are bounded by g.unionFind.parent.size
    whenever the original children are. -/
theorem canonicalize_output_bounded (g : EGraph) (node : ENode)
    (hwf : WellFormed g.unionFind)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    ∀ child, child ∈ (g.canonicalize node).1.children →
      child < g.unionFind.parent.size := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]; exact hbnd
  · simp [h]
    intro child hmem
    have hpairs := go_output_bounded node.children g [] g.unionFind.parent.size
      hwf rfl (fun _ h => nomatch h) hbnd
    -- Case analysis on node.op to relate mapChildren children to original children
    match node, hbnd, hmem with
    | ⟨.constGate _⟩, _, _ => simp [ENode.children] at h
    | ⟨.witness _⟩, _, _ => simp [ENode.children] at h
    | ⟨.pubInput _⟩, _, _ => simp [ENode.children] at h
    | ⟨.addGate a b⟩, hbnd, hmem =>
      simp [ENode.mapChildren, ENode.children] at hmem
      rcases hmem with rfl | rfl
      · exact lookup_bounded _ _ hpairs a (hbnd a (List.Mem.head _))
      · exact lookup_bounded _ _ hpairs b (hbnd b (List.mem_cons_of_mem _ (List.Mem.head _)))
    | ⟨.mulGate a b⟩, hbnd, hmem =>
      simp [ENode.mapChildren, ENode.children] at hmem
      rcases hmem with rfl | rfl
      · exact lookup_bounded _ _ hpairs a (hbnd a (List.Mem.head _))
      · exact lookup_bounded _ _ hpairs b (hbnd b (List.mem_cons_of_mem _ (List.Mem.head _)))
    | ⟨.negGate a⟩, hbnd, hmem =>
      simp [ENode.mapChildren, ENode.children] at hmem
      subst hmem; exact lookup_bounded _ _ hpairs a (hbnd a (List.Mem.head _))
    | ⟨.smulGate _ a⟩, hbnd, hmem =>
      simp [ENode.mapChildren, ENode.children] at hmem
      subst hmem; exact lookup_bounded _ _ hpairs a (hbnd a (List.Mem.head _))

/-- add preserves WellFormed on the UF. -/
theorem add_preserves_uf_wf (g : EGraph) (node : ENode) (hwf : WellFormed g.unionFind) :
    WellFormed (g.add node).2.unionFind := by
  simp only [EGraph.add]
  have hcuf := canonicalize_uf_wf g node hwf
  split
  · exact egraph_find_uf_wf _ _ hcuf
  · exact UnionFind.add_wf _ hcuf

/-- add preserves ChildrenBounded. -/
theorem add_preserves_children_bounded (g : EGraph) (node : ENode)
    (hwf : WellFormed g.unionFind)
    (hcb : ChildrenBounded g)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    ChildrenBounded (g.add node).2 := by
  unfold ChildrenBounded
  simp only [EGraph.add]
  split
  · -- Hit case: classes unchanged, uf size unchanged
    intro id cls hget n hn child hc
    rw [egraph_find_classes] at hget; rw [egraph_find_uf_size]
    rw [canonicalize_classes] at hget; rw [canonicalize_uf_size]
    exact hcb id cls hget n hn child hc
  · -- Miss case: classes insert + uf push
    intro id cls hget n hn child hc
    show child < (Array.push _ _).size
    rw [Array.size_push, canonicalize_uf_size]
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
    split at hget
    · rename_i heq; simp at hget; subst hget
      simp [UnionFind.add] at heq; subst heq
      rw [mem_singleton_nodes] at hn; subst hn
      exact Nat.lt_succ_of_lt (canonicalize_output_bounded g node hwf hbnd child hc)
    · rw [canonicalize_classes] at hget
      have hget' : g.classes.get? id = some cls := by
        rw [Std.HashMap.get?_eq_getElem?]; exact hget
      exact Nat.lt_succ_of_lt (hcb id cls hget' n hn child hc)

/-- add preserves HashconsClassesAligned. -/
theorem add_preserves_hashcons_classes_aligned (g : EGraph) (node : ENode)
    (hca : HashconsClassesAligned g)
    (hev : ∀ n id, g.hashcons.get? n = some id → id < g.unionFind.parent.size) :
    HashconsClassesAligned (g.add node).2 := by
  unfold HashconsClassesAligned
  simp only [EGraph.add]
  split
  · -- Hit case: hashcons/classes unchanged through find
    intro n id hget
    rw [egraph_find_hashcons] at hget; rw [egraph_find_classes]
    rw [canonicalize_hashcons] at hget; rw [canonicalize_classes]
    exact hca n id hget
  · -- Miss case: hashcons insert + classes insert
    intro n id hget
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
    split at hget
    · -- n = canonNode → id = newId
      rename_i heq; have hnn := beq_iff_eq.mp heq; subst hnn
      simp at hget; subst hget
      refine ⟨EClass.singleton (g.canonicalize node).1, ?_, (mem_singleton_nodes _ _).mpr rfl⟩
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      simp [UnionFind.add]
    · -- n ≠ canonNode → lookup in old hashcons
      rename_i hne
      rw [canonicalize_hashcons] at hget
      have hget' : g.hashcons.get? n = some id := by
        rw [Std.HashMap.get?_eq_getElem?]; exact hget
      obtain ⟨cls, hcls, hmem⟩ := hca n id hget'
      have hid_lt := hev n id hget'
      refine ⟨cls, ?_, hmem⟩
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      split
      · rename_i heq_id; simp [UnionFind.add] at heq_id
        rw [canonicalize_uf_size] at heq_id
        exact absurd heq_id (Nat.ne_of_gt hid_lt)
      · rw [canonicalize_classes]; exact hcls

/-- add preserves hashcons_entries_valid. -/
theorem add_preserves_hashcons_entries_valid (g : EGraph) (node : ENode)
    (hwf : WellFormed g.unionFind)
    (hev : ∀ n id, g.hashcons.get? n = some id → id < g.unionFind.parent.size) :
    ∀ n id, (g.add node).2.hashcons.get? n = some id →
      id < (g.add node).2.unionFind.parent.size := by
  simp only [EGraph.add]
  split
  · -- Hit case
    intro n id hget
    rw [egraph_find_hashcons] at hget; rw [egraph_find_uf_size]
    rw [canonicalize_hashcons] at hget; rw [canonicalize_uf_size]
    exact hev n id hget
  · -- Miss case
    intro n id hget
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
    show id < (Array.push _ _).size
    rw [Array.size_push, canonicalize_uf_size]
    split at hget
    · rename_i heq; simp at hget; subst hget
      simp [UnionFind.add]; rw [canonicalize_uf_size]
      exact Nat.lt_succ_of_le (Nat.le_refl _)
    · rw [canonicalize_hashcons] at hget
      have hget' : g.hashcons.get? n = some id := by
        rw [Std.HashMap.get?_eq_getElem?]; exact hget
      exact Nat.lt_succ_of_lt (hev n id hget')

/-- add preserves AddExprInv when children are bounded. -/
theorem add_preserves_add_expr_inv (g : EGraph) (node : ENode) (inv : AddExprInv g)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    AddExprInv (g.add node).2 where
  uf_wf := add_preserves_uf_wf g node inv.uf_wf
  children_bounded := add_preserves_children_bounded g node inv.uf_wf inv.children_bounded hbnd
  hashcons_classes_aligned := add_preserves_hashcons_classes_aligned g node
    inv.hashcons_classes_aligned inv.hashcons_entries_valid
  hashcons_entries_valid := add_preserves_hashcons_entries_valid g node
    inv.uf_wf inv.hashcons_entries_valid

/-- The ID returned by add is bounded by the result's UF size. -/
theorem add_id_bounded (g : EGraph) (node : ENode) (inv : AddExprInv g) :
    (g.add node).1 < (g.add node).2.unionFind.parent.size := by
  simp only [EGraph.add]
  split
  · -- Hit: returned ID = root of existingId
    rename_i existingId hm
    rw [egraph_find_uf_size, egraph_find_fst]
    rw [canonicalize_hashcons] at hm
    have hev := inv.hashcons_entries_valid _ _ hm
    have hcwf := canonicalize_uf_wf g node inv.uf_wf
    rw [← canonicalize_uf_size g node] at hev
    simp only [root]; exact rootD_bounded hcwf.1 hev
  · -- Miss: returned ID = g1.uf.size, new uf.size = g1.uf.size + 1
    show _ < (Array.push _ _).size
    rw [Array.size_push]; exact Nat.lt_succ_of_le (Nat.le_refl _)

/-- The UF size doesn't decrease after add. -/
theorem add_uf_size_ge (g : EGraph) (node : ENode) :
    g.unionFind.parent.size ≤ (g.add node).2.unionFind.parent.size := by
  simp only [EGraph.add]
  split
  · rw [egraph_find_uf_size, canonicalize_uf_size]; exact Nat.le_refl _
  · show _ ≤ (Array.push _ _).size
    rw [Array.size_push, canonicalize_uf_size]; exact Nat.le_succ _

end AmoLean.EGraph.Verified
