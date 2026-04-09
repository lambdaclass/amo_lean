/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.ReduceSpecAxiom

  B107 (N26.1 FUNDACIONAL): Specification axiom for modular reduction discovery.
  Inserts reduce(x) ≡ x % p into a MixedEGraph, preserving ConsistentValuation.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec
import AmoLean.EGraph.Verified.Bitwise.MixedExtract

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)
open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec
  (MGraph MNode MClass MUF CId ufRoot ndChildren ndMapCh ShapeHashconsInv)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (CV VPMI PreservesCV)
open AmoLean.EGraph.Verified.Bitwise.MixedUnionFind
  (StrongWF push_preserves_strongWF root_push_all_eq strongWF_implies_UFWF)

-- ════════════════════════════════════════════════════════════════
-- Section 1: ReduceSpec
-- ════════════════════════════════════════════════════════════════

structure ReduceSpec where
  p : Nat
  w : Nat
  p_pos : p > 0
  p_lt_bound : p < 2 ^ w
  deriving Repr

structure ReduceSpecResult where
  inputId : CId
  reduceId : CId
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- Section 2: insertReduceSpec
-- ════════════════════════════════════════════════════════════════

def insertReduceSpec (spec : ReduceSpec) (g : MGraph) : MGraph :=
  let (inputId, g1) := g.add ⟨MixedNodeOp.witness 0⟩
  (g1.add ⟨MixedNodeOp.reduceGate inputId spec.p⟩).2

def insertReduceSpecWithIds (spec : ReduceSpec) (g : MGraph) :
    ReduceSpecResult × MGraph :=
  let (inputId, g1) := g.add ⟨MixedNodeOp.witness 0⟩
  let (reduceId, g2) := g1.add ⟨MixedNodeOp.reduceGate inputId spec.p⟩
  (⟨inputId, reduceId⟩, g2)

-- ════════════════════════════════════════════════════════════════
-- Section 3: Helpers
-- ════════════════════════════════════════════════════════════════

/-- Canonical node: children mapped to roots, or node itself if leaf. -/
private def canonOf (g : MGraph) (node : MNode) : MNode :=
  if (ndChildren node).isEmpty then node
  else ⟨ndMapCh (ufRoot g.unionFind) node.op⟩

/-- Singleton class wrapper. -/
private abbrev mkSingleton (n : MNode) : MClass :=
  AmoLean.EGraph.VerifiedExtraction.EClass.singleton n

/-- evalOp for MixedNodeOp. -/
private abbrev mEvalOp (op : MixedNodeOp) (env : MixedEnv) (v : CId → Nat) : Nat :=
  @AmoLean.EGraph.VerifiedExtraction.NodeSemantics.evalOp MixedNodeOp MixedEnv Nat _ _ op env v

/-- evalOp extensionality for MixedNodeOp. -/
private theorem mEvalOp_ext (op : MixedNodeOp) (env : MixedEnv) (v v' : CId → Nat)
    (h : ∀ c, c ∈ AmoLean.EGraph.VerifiedExtraction.NodeOps.children op → v c = v' c) :
    mEvalOp op env v = mEvalOp op env v' :=
  @AmoLean.EGraph.VerifiedExtraction.NodeSemantics.evalOp_ext MixedNodeOp MixedEnv Nat _ _ op env v v' h

private theorem add_snd_cases (g : MGraph) (node : MNode) :
    ((g.hashcons.get? (canonOf g node) = none →
      (g.add node).2 = { g with
        unionFind := ⟨g.unionFind.parent.push g.unionFind.parent.size⟩
        hashcons := g.hashcons.insert (canonOf g node) g.unionFind.parent.size
        classes := g.classes.insert g.unionFind.parent.size (mkSingleton (canonOf g node)) }) ∧
     (∀ id, g.hashcons.get? (canonOf g node) = some id → (g.add node).2 = g)) := by
  constructor
  · intro h
    show (AmoLean.EGraph.VerifiedExtraction.EGraph.add g node).2 = _
    simp only [AmoLean.EGraph.VerifiedExtraction.EGraph.add,
      AmoLean.EGraph.VerifiedExtraction.ENode.children,
      AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren,
      AmoLean.EGraph.VerifiedExtraction.UnionFind.add,
      canonOf, ndChildren, ndMapCh, mkSingleton] at h ⊢
    split <;> simp_all
  · intro id h
    show (AmoLean.EGraph.VerifiedExtraction.EGraph.add g node).2 = g
    simp only [AmoLean.EGraph.VerifiedExtraction.EGraph.add,
      AmoLean.EGraph.VerifiedExtraction.ENode.children,
      AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren,
      AmoLean.EGraph.VerifiedExtraction.UnionFind.add,
      canonOf, ndChildren, ndMapCh] at h ⊢
    split <;> simp_all

private theorem add_fst_bounded (g : MGraph) (node : MNode)
    (hpmi : VPMI g) (_h_ch : ∀ c ∈ ndChildren node, c < g.unionFind.parent.size) :
    (g.add node).1 < (g.add node).2.unionFind.parent.size := by
  show (AmoLean.EGraph.VerifiedExtraction.EGraph.add g node).1 <
    (AmoLean.EGraph.VerifiedExtraction.EGraph.add g node).2.unionFind.parent.size
  simp only [AmoLean.EGraph.VerifiedExtraction.EGraph.add,
    AmoLean.EGraph.VerifiedExtraction.ENode.children,
    AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren,
    AmoLean.EGraph.VerifiedExtraction.UnionFind.add]
  split
  · exact (strongWF_implies_UFWF hpmi.uf_swf).root_bounded _
      (hpmi.hashcons_entries_valid _ _ (by assumption))
  · simp [Array.size_push]

private theorem root_ne_fresh {uf : MUF} (hwf : StrongWF uf) {j : CId}
    (hne : j ≠ uf.parent.size) : ufRoot uf j ≠ uf.parent.size := by
  by_cases hjb : j < uf.parent.size
  · exact Nat.ne_of_lt ((strongWF_implies_UFWF hwf).root_bounded j hjb)
  · rw [show ufRoot uf j = j from
      AmoLean.EGraph.VerifiedExtraction.UnionFind.root_oob uf j hjb]; exact hne

private theorem root_of_fresh (uf : MUF) :
    ufRoot uf uf.parent.size = uf.parent.size :=
  AmoLean.EGraph.VerifiedExtraction.UnionFind.root_oob uf uf.parent.size (Nat.lt_irrefl _)

/-- Membership in a singleton EClass: the only node in `(singleton n).nodes.toList` is `n`. -/
private theorem mem_singleton_nodes (n nd : MNode)
    (h : nd ∈ (mkSingleton n).nodes.toList) : nd = n := by
  simp only [mkSingleton, AmoLean.EGraph.VerifiedExtraction.EClass.singleton] at h
  simp at h; exact h

/-- Extract cls = mkSingleton canon from matching get? results. -/
private theorem cls_eq_of_get?_eq {cls : MClass} {canon : MNode}
    {hm : Std.HashMap CId MClass} {k : CId}
    (h1 : hm.get? k = some cls) (h2 : hm.get? k = some (mkSingleton canon)) :
    cls = mkSingleton canon := by
  rw [h1] at h2; exact Option.some.inj h2

-- ════════════════════════════════════════════════════════════════
-- Section 4: add_preserves_triple
-- ════════════════════════════════════════════════════════════════

/-- Helper: get? on HashMap after insert for the same key. -/
private theorem hm_get?_insert_self {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (hm : Std.HashMap α β) (k : α) (val : β) :
    (hm.insert k val).get? k = some val := by
  simp [Std.HashMap.get?_eq_getElem?]

/-- Helper: get? on HashMap after insert for a different key. -/
private theorem hm_get?_insert_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (hm : Std.HashMap α β) (k1 k2 : α) (val : β) (hne : k1 ≠ k2) :
    (hm.insert k1 val).get? k2 = hm.get? k2 := by
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hne]

/-- In the leaf case of canonOf, children membership is absurd (isEmpty = true). -/
private theorem canon_leaf_absurd {node : MNode} {c : CId}
    (h_leaf : (ndChildren node).isEmpty = true)
    (hc : c ∈ AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op) : False := by
  have h_nil : AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op = [] := by
    exact List.isEmpty_iff.mp h_leaf
  rw [h_nil] at hc; exact List.not_mem_nil hc

/-- Children of canon: either from the original node (leaf case) or mapped children. -/
private theorem canon_children_bounded {g : MGraph} {node : MNode} {child : CId}
    (hpmi : VPMI g) (h_ch : ∀ c ∈ ndChildren node, c < g.unionFind.parent.size)
    (h_child : child ∈ ndChildren (canonOf g node)) :
    child < g.unionFind.parent.size := by
  simp only [canonOf, ndChildren, ndMapCh,
    AmoLean.EGraph.VerifiedExtraction.ENode.children] at h_child
  split at h_child
  · -- leaf case: isEmpty = true, children membership is absurd
    rename_i h_leaf
    exact absurd h_child (by
      have h_nil : AmoLean.EGraph.VerifiedExtraction.NodeOps.children node.op = [] := by
        exact List.isEmpty_iff.mp h_leaf
      rw [h_nil]; exact List.not_mem_nil)
  · -- mapChildren case
    rw [AmoLean.EGraph.VerifiedExtraction.NodeOps.mapChildren_children] at h_child
    obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp h_child
    exact (strongWF_implies_UFWF hpmi.uf_swf).root_bounded c'
      (h_ch c' (show c' ∈ ndChildren node from hc'_mem))

theorem add_preserves_triple (env : MixedEnv) (node : MNode)
    (g : MGraph) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
    (h_ch : ∀ c ∈ ndChildren node, c < g.unionFind.parent.size) :
    ∃ v', CV (g.add node).2 env v' ∧ VPMI (g.add node).2 ∧
          ShapeHashconsInv (g.add node).2 := by
  obtain ⟨h_none, h_some⟩ := add_snd_cases g node
  by_cases h_found : ∃ id, g.hashcons.get? (canonOf g node) = some id
  · obtain ⟨id, hid⟩ := h_found
    rw [h_some id hid]; exact ⟨v, hcv, hpmi, hshi⟩
  · push_neg at h_found
    have h_lk : g.hashcons.get? (canonOf g node) = none := by
      cases h : g.hashcons.get? (canonOf g node) with
      | some id => exact absurd h (h_found id) | none => rfl
    rw [h_none h_lk]
    set newId := g.unionFind.parent.size
    set canon := canonOf g node
    set g' : MGraph := { g with
      unionFind := ⟨g.unionFind.parent.push newId⟩
      hashcons := g.hashcons.insert canon newId
      classes := g.classes.insert newId (mkSingleton canon) }
    -- Key structural fact about g'
    have g'_uf_size : g'.unionFind.parent.size = newId + 1 := by
      show (g.unionFind.parent.push newId).size = newId + 1
      rw [Array.size_push]
    -- Derived facts for HashMap operations on g'
    have hc_ins : (g.hashcons.insert canon newId).get? canon = some newId :=
      hm_get?_insert_self g.hashcons canon newId
    have hcls_ins : (g.classes.insert newId (mkSingleton canon)).get? newId =
        some (mkSingleton canon) :=
      hm_get?_insert_self g.classes newId (mkSingleton canon)
    set v' : CId → Nat := fun i => if i = newId then mEvalOp canon.op env v else v i
    refine ⟨v', ?_, ?_, ?_⟩
    · -- ═══ CV ═══
      constructor
      · -- equiv_same_val
        intro i j h_eq
        have hr := AmoLean.EGraph.Verified.Bitwise.MixedUnionFind.root_push_all_eq hpmi.uf_swf
        -- Rewrite h_eq from g'.unionFind.root to g.unionFind.root
        change AmoLean.EGraph.VerifiedExtraction.UnionFind.root
          ⟨g.unionFind.parent.push g.unionFind.parent.size⟩ i =
          AmoLean.EGraph.VerifiedExtraction.UnionFind.root
          ⟨g.unionFind.parent.push g.unionFind.parent.size⟩ j at h_eq
        rw [hr i, hr j] at h_eq
        show v' i = v' j; simp only [v']
        by_cases hi : i = newId <;> by_cases hj : j = newId
        · simp [hi, hj]
        · exfalso; subst hi
          have h_rf : ufRoot g.unionFind g.unionFind.parent.size = g.unionFind.parent.size :=
            root_of_fresh g.unionFind
          rw [show g.unionFind.root = ufRoot g.unionFind from rfl] at h_eq
          rw [h_rf] at h_eq
          exact root_ne_fresh hpmi.uf_swf hj h_eq.symm
        · exfalso; subst hj
          have h_rf : ufRoot g.unionFind g.unionFind.parent.size = g.unionFind.parent.size :=
            root_of_fresh g.unionFind
          rw [show g.unionFind.root = ufRoot g.unionFind from rfl] at h_eq
          rw [h_rf] at h_eq
          exact root_ne_fresh hpmi.uf_swf hi h_eq
        · simp [hi, hj]; exact hcv.equiv_same_val i j h_eq
      · -- node_consistent
        intro classId eclass h_cls nd h_nd
        show mEvalOp nd.op env v' = v' classId
        simp only [g'] at h_cls
        by_cases h_cid : classId = newId
        · subst h_cid
          have h_cls_eq : eclass = mkSingleton canon :=
            cls_eq_of_get?_eq h_cls hcls_ins
          rw [h_cls_eq] at h_nd
          have h_nd_eq : nd = canon := mem_singleton_nodes canon nd h_nd
          subst h_nd_eq; simp only [v', if_pos rfl]
          exact mEvalOp_ext canon.op env v' v fun c hc => by
            have : c < newId :=
              canon_children_bounded hpmi h_ch (show c ∈ ndChildren canon from hc)
            simp [v', Nat.ne_of_lt this]
        · have h_cls' : g.classes.get? classId = some eclass := by
            have := hm_get?_insert_ne g.classes newId classId (mkSingleton canon) (Ne.symm h_cid)
            rw [this] at h_cls; exact h_cls
          have h_eval : mEvalOp nd.op env v' = mEvalOp nd.op env v :=
            mEvalOp_ext nd.op env v' v fun c hc => by
              have : c < newId := hpmi.children_bounded classId eclass h_cls'
                nd h_nd c (show c ∈ ndChildren nd from hc)
              simp [v', Nat.ne_of_lt this]
          rw [h_eval, show v' classId = v classId from if_neg h_cid]
          exact hcv.node_consistent classId eclass h_cls' nd h_nd
    · -- ═══ VPMI ═══
      exact {
        uf_swf := push_preserves_strongWF hpmi.uf_swf
        children_bounded := fun classId cls h_cls nd' h_nd' child h_child => by
          simp only [g'] at h_cls
          by_cases h_cid : classId = newId
          · subst h_cid
            have h_cls_eq : cls = mkSingleton canon :=
              cls_eq_of_get?_eq h_cls hcls_ins
            rw [h_cls_eq] at h_nd'
            have h_nd_eq : nd' = canon := mem_singleton_nodes canon nd' h_nd'
            subst h_nd_eq
            rw [g'_uf_size]
            exact Nat.lt_succ_of_lt (canon_children_bounded hpmi h_ch h_child)
          · have h_cls' : g.classes.get? classId = some cls := by
              have := hm_get?_insert_ne g.classes newId classId (mkSingleton canon) (Ne.symm h_cid)
              rw [this] at h_cls; exact h_cls
            rw [g'_uf_size]; exact Nat.lt_succ_of_lt <|
              hpmi.children_bounded classId cls h_cls' nd' h_nd' child h_child
        hashcons_entries_valid := fun nd' id' h_hc => by
          simp only [g'] at h_hc
          by_cases h_nd_eq : nd' = canon
          · subst h_nd_eq
            rw [hc_ins] at h_hc; injection h_hc with h_hc; subst h_hc
            rw [g'_uf_size]; exact Nat.lt_add_one newId
          · have := hm_get?_insert_ne g.hashcons canon nd' newId (Ne.symm h_nd_eq)
            rw [this] at h_hc
            rw [g'_uf_size]; exact Nat.lt_succ_of_lt (hpmi.hashcons_entries_valid nd' id' h_hc)
        classes_entries_valid := fun id' h_contains => by
          simp only [g'] at h_contains
          by_cases h_id_eq : id' = newId
          · subst h_id_eq; rw [g'_uf_size]; exact Nat.lt_add_one newId
          · have h_old : g.classes.contains id' = true := by
              rw [Std.HashMap.contains_insert] at h_contains
              simp only [show (newId == id') = false from
                beq_eq_false_iff_ne.mpr (Ne.symm h_id_eq), Bool.false_or] at h_contains
              exact h_contains
            rw [g'_uf_size]; exact Nat.lt_succ_of_lt (hpmi.classes_entries_valid id' h_old) }
    · -- ═══ ShapeHashconsInv ═══
      intro nd' id' h_hc; simp only [g'] at h_hc
      by_cases h_nd_eq : nd' = canon
      · subst h_nd_eq
        rw [hc_ins] at h_hc; injection h_hc with h_hc; subst h_hc
        refine ⟨mkSingleton canon, ?_, ?_⟩
        · show g'.classes.get? newId = some (mkSingleton canon)
          exact hm_get?_insert_self g.classes newId (mkSingleton canon)
        · simp [mkSingleton, AmoLean.EGraph.VerifiedExtraction.EClass.singleton]
      · have h_hc' : g.hashcons.get? nd' = some id' := by
          have := hm_get?_insert_ne g.hashcons canon nd' newId (Ne.symm h_nd_eq)
          rw [this] at h_hc; exact h_hc
        obtain ⟨cls, h_cls, h_mem⟩ := hshi nd' id' h_hc'
        have h_id_ne : id' ≠ newId := by
          intro heq; subst heq
          exact absurd (hpmi.hashcons_entries_valid nd' newId h_hc') (Nat.lt_irrefl _)
        have h_cls' : g'.classes.get? id' = some cls := by
          show (g.classes.insert newId (mkSingleton canon)).get? id' = some cls
          rw [hm_get?_insert_ne g.classes newId id' (mkSingleton canon) (Ne.symm h_id_ne)]
          exact h_cls
        exact ⟨cls, h_cls', h_mem⟩

-- ════════════════════════════════════════════════════════════════
-- Section 5: insertReduceSpec_preserves_cv
-- ════════════════════════════════════════════════════════════════

theorem insertReduceSpec_preserves_cv (spec : ReduceSpec) (env : MixedEnv) :
    PreservesCV env (insertReduceSpec spec) := by
  intro g v hcv hpmi hshi
  show ∃ v', CV (insertReduceSpec spec g) env v' ∧
    VPMI (insertReduceSpec spec g) ∧ ShapeHashconsInv (insertReduceSpec spec g)
  simp only [insertReduceSpec]
  have h_ch_w : ∀ c ∈ ndChildren (⟨MixedNodeOp.witness 0⟩ : MNode),
      c < g.unionFind.parent.size := by
    intro c hc
    simp [ndChildren, AmoLean.EGraph.VerifiedExtraction.ENode.children,
      AmoLean.EGraph.VerifiedExtraction.NodeOps.children, mixedChildren] at hc
  obtain ⟨v1, hcv1, hpmi1, hshi1⟩ :=
    add_preserves_triple env ⟨.witness 0⟩ g v hcv hpmi hshi h_ch_w
  set p1 := g.add ⟨MixedNodeOp.witness 0⟩
  have h_bnd : p1.1 < p1.2.unionFind.parent.size :=
    add_fst_bounded g ⟨.witness 0⟩ hpmi h_ch_w
  have h_ch_r : ∀ c ∈ ndChildren (⟨MixedNodeOp.reduceGate p1.1 spec.p⟩ : MNode),
      c < p1.2.unionFind.parent.size := by
    intro c hc
    simp [ndChildren, AmoLean.EGraph.VerifiedExtraction.ENode.children,
      AmoLean.EGraph.VerifiedExtraction.NodeOps.children, mixedChildren] at hc
    subst hc; exact h_bnd
  exact add_preserves_triple env ⟨.reduceGate p1.1 spec.p⟩ p1.2 v1 hcv1 hpmi1 hshi1 h_ch_r

-- ════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ════════════════════════════════════════════════════════════════

def babybearSpec : ReduceSpec where
  p := 2013265921
  w := 32
  p_pos := by omega
  p_lt_bound := by omega

def mersenne31Spec : ReduceSpec where
  p := 2147483647
  w := 32
  p_pos := by omega
  p_lt_bound := by omega

example : (insertReduceSpec babybearSpec
    (AmoLean.EGraph.VerifiedExtraction.EGraph.empty (Op := MixedNodeOp))
    ).unionFind.parent.size ≥ 1 := by native_decide

example : (insertReduceSpecWithIds babybearSpec
    (AmoLean.EGraph.VerifiedExtraction.EGraph.empty (Op := MixedNodeOp))
    ).1.reduceId ≠
    (insertReduceSpecWithIds babybearSpec
    (AmoLean.EGraph.VerifiedExtraction.EGraph.empty (Op := MixedNodeOp))
    ).1.inputId := by native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
