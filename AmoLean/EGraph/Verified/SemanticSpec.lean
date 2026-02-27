/-
  AMO-Lean — Semantic Specification for Verified E-Graph
  N11.1: CryptoSemanticSpec — evalOp, evalOp_ext, evalOp_mapChildren,
  ConsistentValuation definition, empty_consistent, consistent_root_eq.
  Adapted from OptiSat/LambdaSat SemanticSpec (typeclass pattern → concrete types).
-/
import AmoLean.EGraph.Verified.CoreSpec

namespace AmoLean.EGraph.Verified

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 0: CircuitEnv + evalOp
-- ══════════════════════════════════════════════════════════════════

/-- Environment for circuit evaluation: maps indices to field values
    for each category of input. -/
structure CircuitEnv (Val : Type) where
  constVal    : Nat → Val
  witnessVal  : Nat → Val
  pubInputVal : Nat → Val

variable {Val : Type} [Add Val] [Mul Val] [Neg Val]

/-- Evaluate a circuit operation given an environment and a class-value mapping.
    Leaf ops (constGate, witness, pubInput) read from the environment.
    Arithmetic ops combine children values using ring operations. -/
def evalOp (op : CircuitNodeOp) (env : CircuitEnv Val) (v : EClassId → Val) : Val :=
  match op with
  | .constGate n  => env.constVal n
  | .witness n    => env.witnessVal n
  | .pubInput n   => env.pubInputVal n
  | .addGate a b  => v a + v b
  | .mulGate a b  => v a * v b
  | .negGate a    => -(v a)
  | .smulGate n a => env.constVal n * v a

/-- Evaluate an e-node: delegates to evalOp on the wrapped operation. -/
def NodeEval (node : ENode) (env : CircuitEnv Val) (v : EClassId → Val) : Val :=
  evalOp node.op env v

-- ══════════════════════════════════════════════════════════════════
-- Section 1: evalOp_ext (depends only on children)
-- ══════════════════════════════════════════════════════════════════

/-- `evalOp` depends on `v` only through the children of the node.
    If two valuations agree on all children, they produce the same result. -/
theorem evalOp_ext (node : ENode) (env : CircuitEnv Val) (v v' : EClassId → Val)
    (h : ∀ c ∈ node.children, v c = v' c) :
    NodeEval node env v = NodeEval node env v' := by
  unfold NodeEval evalOp
  match hnode : node with
  | ⟨.constGate _⟩  => rfl
  | ⟨.witness _⟩     => rfl
  | ⟨.pubInput _⟩    => rfl
  | ⟨.addGate a b⟩   =>
    have ha : v a = v' a := h a (by simp [ENode.children, List.mem_cons])
    have hb : v b = v' b := h b (by simp [ENode.children, List.mem_cons])
    simp [ha, hb]
  | ⟨.mulGate a b⟩   =>
    have ha : v a = v' a := h a (by simp [ENode.children, List.mem_cons])
    have hb : v b = v' b := h b (by simp [ENode.children, List.mem_cons])
    simp [ha, hb]
  | ⟨.negGate a⟩     =>
    have ha : v a = v' a := h a (by simp [ENode.children, List.mem_cons])
    simp [ha]
  | ⟨.smulGate n a⟩  =>
    have ha : v a = v' a := h a (by simp [ENode.children, List.mem_cons])
    simp [ha]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: evalOp_mapChildren (commutes with remapping)
-- ══════════════════════════════════════════════════════════════════

/-- `mapChildren f` commutes with evaluation: evaluating a remapped node
    is the same as evaluating the original node with `v ∘ f`. -/
theorem evalOp_mapChildren (f : EClassId → EClassId) (node : ENode)
    (env : CircuitEnv Val) (v : EClassId → Val) :
    NodeEval (node.mapChildren f) env v = NodeEval node env (fun c => v (f c)) := by
  unfold NodeEval evalOp ENode.mapChildren
  match node with
  | ⟨.constGate _⟩  => rfl
  | ⟨.witness _⟩     => rfl
  | ⟨.pubInput _⟩    => rfl
  | ⟨.addGate _ _⟩   => rfl
  | ⟨.mulGate _ _⟩   => rfl
  | ⟨.negGate _⟩     => rfl
  | ⟨.smulGate _ _⟩  => rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 3: ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- A valuation `v : EClassId → Val` is consistent with an e-graph `g`
    under environment `env` if:
    (1) UF-equivalent class IDs have the same value, and
    (2) every node in a class evaluates to that class's value. -/
def ConsistentValuation (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val) : Prop :=
  (∀ i j, root g.unionFind i = root g.unionFind j → v i = v j) ∧
  (∀ classId eclass, g.classes.get? classId = some eclass →
    ∀ node, node ∈ eclass.nodes.toList →
      NodeEval node env v = v classId)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Basic ConsistentValuation theorems
-- ══════════════════════════════════════════════════════════════════

/-- The empty e-graph trivially has a consistent valuation. -/
theorem empty_consistent [Inhabited Val] (env : CircuitEnv Val) :
    ConsistentValuation EGraph.empty env (fun _ => default) := by
  constructor
  · intro _ _ _; rfl
  · intro classId eclass h
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at h

/-- Consistent valuations respect root: v(root i) = v i. -/
theorem consistent_root_eq (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hid : i < g.unionFind.parent.size) :
    v (root g.unionFind i) = v i :=
  hv.1 (root g.unionFind i) i (root_idempotent g.unionFind i hwf hid)

/-- v(root id) = v id, handling both in-bounds and out-of-bounds. -/
theorem consistent_root_eq' (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (id : EClassId) :
    v (root g.unionFind id) = v id := by
  by_cases hid : id < g.unionFind.parent.size
  · exact consistent_root_eq g env v hv hwf hid
  · rw [root_oob g.unionFind id hid]

/-- Nodes in the same e-class evaluate to the same value. -/
theorem class_nodes_same_value (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v)
    (hcls : g.classes.get? classId = some eclass)
    (hn1 : n1 ∈ eclass.nodes.toList) (hn2 : n2 ∈ eclass.nodes.toList) :
    NodeEval n1 env v = NodeEval n2 env v :=
  (hv.2 classId eclass hcls n1 hn1).trans (hv.2 classId eclass hcls n2 hn2).symm

/-- UF-equivalent class IDs have the same value (direct accessor). -/
theorem equiv_same_value (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v)
    (heq : root g.unionFind i = root g.unionFind j) :
    v i = v j :=
  hv.1 i j heq

-- ══════════════════════════════════════════════════════════════════
-- Section 5: nodeEval_canonical (evaluation after canonicalization)
-- ══════════════════════════════════════════════════════════════════

/-- After canonicalizing a node's children to their UF roots, the evaluation
    with the original valuation is unchanged. -/
theorem nodeEval_canonical (g : EGraph) (node : ENode) (env : CircuitEnv Val)
    (v : EClassId → Val) (hv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    NodeEval (node.mapChildren (fun c => root g.unionFind c)) env v =
    NodeEval node env v := by
  rw [evalOp_mapChildren]
  apply evalOp_ext
  intro c hc
  exact consistent_root_eq g env v hv hwf (hbnd c hc)

-- ══════════════════════════════════════════════════════════════════
-- Section 5b: nodeEval_canonicalize (evaluation after EGraph.canonicalize)
-- ══════════════════════════════════════════════════════════════════

/-- The internal `go` function of canonicalize produces pairs (old, new) where
    v(new) = v(old), provided v respects root-equivalence. -/
private theorem go_preserves_v_eq
    (cs : List EClassId) (g : EGraph)
    (ps : List (EClassId × EClassId))
    (v : EClassId → Val)
    (hwf : WellFormed g.unionFind)
    (huf : ∀ i j, root g.unionFind i = root g.unionFind j → v i = v j)
    (hps : ∀ p ∈ ps, v p.2 = v p.1) :
    ∀ p ∈ (EGraph.canonicalize.go cs g ps).1, v p.2 = v p.1 := by
  induction cs generalizing g ps with
  | nil => unfold EGraph.canonicalize.go; exact hps
  | cons c rest ih =>
    unfold EGraph.canonicalize.go
    exact ih (g.find c).2 ((c, (g.find c).1) :: ps)
      (egraph_find_uf_wf g c hwf)
      (fun i j hrij => huf i j (by
        rwa [← egraph_find_preserves_roots g c i hwf,
             ← egraph_find_preserves_roots g c j hwf]))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only []
          rw [egraph_find_fst]
          by_cases hc : c < g.unionFind.parent.size
          · exact huf _ _ (root_idempotent g.unionFind c hwf hc)
          · rw [root_oob g.unionFind c hc]
        · exact hps p hp)

/-- The lookup function used by canonicalize preserves v-equality:
    v(f(id)) = v(id) when all pairs have v-equal components. -/
private theorem lookup_preserves_v
    (v : EClassId → Val)
    (pairs : List (EClassId × EClassId))
    (hpairs : ∀ p ∈ pairs, v p.2 = v p.1) (c : EClassId) :
    v (match pairs.find? (fun (old, _) => old == c) with
       | some (_, new_) => new_
       | none => c) = v c := by
  split
  · rename_i _ new_ heq
    have hmem := List.mem_of_find?_eq_some heq
    have hveq := hpairs _ hmem
    have hfind := List.find?_some heq
    simp only [BEq.beq, decide_eq_true_eq] at hfind
    exact hveq.trans (congrArg v hfind)
  · rfl

/-- EGraph.canonicalize preserves node evaluation: the canonicalized node
    evaluates identically to the original under any root-respecting valuation.
    Uses (g.canonicalize node).1 directly (not mapChildren). -/
theorem nodeEval_canonicalize (g : EGraph) (node : ENode) (env : CircuitEnv Val)
    (v : EClassId → Val)
    (huf : ∀ i j, root g.unionFind i = root g.unionFind j → v i = v j)
    (hwf : WellFormed g.unionFind)
    (_hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    NodeEval (g.canonicalize node).1 env v = NodeEval node env v := by
  unfold EGraph.canonicalize
  by_cases h : node.children.isEmpty = true
  · simp [h]
  · simp [h]
    rw [evalOp_mapChildren]
    apply evalOp_ext
    intro c hc
    exact lookup_preserves_v v _ (go_preserves_v_eq node.children g [] v hwf huf
      (fun _ hp => nomatch hp)) c

-- ══════════════════════════════════════════════════════════════════
-- Section 6: SemanticHashconsInv (canonical hashcons semantic invariant)
-- ══════════════════════════════════════════════════════════════════

/-- Semantic Hashcons Invariant: for every entry in the hashcons map,
    the node evaluates to the value of its mapped class ID. -/
def SemanticHashconsInv (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val) : Prop :=
  ∀ (node : ENode) (classId : EClassId),
    g.hashcons.get? node = some classId →
    NodeEval node env v = v (root g.unionFind classId)

/-- ConsistentValuation + HashconsClassesAligned + HashconsConsistent implies SHI. -/
theorem cv_hca_implies_shi (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hhca : HashconsClassesAligned g)
    (hhc : HashconsConsistent g) :
    SemanticHashconsInv g env v := by
  intro node classId hget
  obtain ⟨cls, hcls, hmem⟩ := hhca node classId hget
  rw [hv.2 classId cls hcls node hmem]
  exact (consistent_root_eq g env v hv hwf (hhc node classId hget).1).symm

/-- ConsistentValuation + EGraphWF implies SemanticHashconsInv. -/
theorem ewf_cv_implies_shi (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v)
    (hwf : EGraphWF g) :
    SemanticHashconsInv g env v := by
  intro node classId hget
  obtain ⟨cls, hcls, hmem⟩ := hwf.hashcons_classes_aligned node classId hget
  rw [hv.2 classId cls hcls node hmem]
  exact (consistent_root_eq g env v hv hwf.uf_wf
    ((hwf.hashcons_consistent node classId hget).1)).symm

/-- The empty e-graph trivially has SHI. -/
theorem empty_shi [Inhabited Val] (env : CircuitEnv Val) :
    SemanticHashconsInv EGraph.empty env (fun _ => default) := by
  intro node classId hget
  simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at hget

-- ══════════════════════════════════════════════════════════════════
-- Section 7: find preserves ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- find (path compression) preserves ConsistentValuation. -/
theorem find_consistent (g : EGraph) (id : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind) :
    ConsistentValuation (g.find id).2 env v := by
  have hfr : ∀ j, root (g.find id).2.unionFind j = root g.unionFind j :=
    fun j => egraph_find_preserves_roots g id j hwf
  constructor
  · intro i j hrij
    exact hv.1 i j (by rw [← hfr i, ← hfr j]; exact hrij)
  · intro classId eclass hcls node hmem
    simp [EGraph.find] at hcls
    exact hv.2 classId eclass hcls node hmem

-- ══════════════════════════════════════════════════════════════════
-- Section 8: merge preserves ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- merge preserves ConsistentValuation when the merged classes have equal
    values. The same valuation v works for the merged graph. -/
theorem merge_consistent (g : EGraph) (id1 id2 : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (h1 : id1 < g.unionFind.parent.size) (h2 : id2 < g.unionFind.parent.size)
    (heq : v (root g.unionFind id1) = v (root g.unionFind id2)) :
    ConsistentValuation (g.merge id1 id2) env v := by
  -- Pure UF-level lemmas
  have hfpr1 : ∀ k, root (g.unionFind.find id1).2 k = root g.unionFind k :=
    fun k => find_preserves_roots g.unionFind id1 k hwf
  have hwf1 : WellFormed (g.unionFind.find id1).2 :=
    find_preserves_wf g.unionFind id1 hwf
  have hfpr2 : ∀ k, root ((g.unionFind.find id1).2.find id2).2 k = root g.unionFind k :=
    fun k => (find_preserves_roots _ id2 k hwf1).trans (hfpr1 k)
  have hwf2 : WellFormed ((g.unionFind.find id1).2.find id2).2 :=
    find_preserves_wf _ id2 hwf1
  have hsz2 : ((g.unionFind.find id1).2.find id2).2.parent.size = g.unionFind.parent.size := by
    rw [find_snd_size, find_snd_size]
  -- Unfold merge
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  rw [show root (g.unionFind.find id1).2 id2 = root g.unionFind id2 from hfpr1 id2]
  -- Split on root equality
  split
  · -- Same root: merge returns g2
    constructor
    · intro i j hij; rw [hfpr2, hfpr2] at hij; exact hv.1 i j hij
    · intro cid cls hcls nd hmem; exact hv.2 cid cls hcls nd hmem
  · -- Different roots
    rename_i hne_beq
    have hne : root g.unionFind id1 ≠ root g.unionFind id2 := by
      intro h; exact hne_beq (beq_iff_eq.mpr h)
    -- Bounds for union_root_cases
    have hr1_bnd : root g.unionFind id1 < ((g.unionFind.find id1).2.find id2).2.parent.size :=
      hsz2 ▸ rootD_bounded hwf.1 h1
    have hr2_bnd : root g.unionFind id2 < ((g.unionFind.find id1).2.find id2).2.parent.size :=
      hsz2 ▸ rootD_bounded hwf.1 h2
    -- root_idempotent
    have hr1_idem : root g.unionFind (root g.unionFind id1) = root g.unionFind id1 :=
      root_idempotent g.unionFind id1 hwf h1
    have hr2_idem : root g.unionFind (root g.unionFind id2) = root g.unionFind id2 :=
      root_idempotent g.unionFind id2 hwf h2
    constructor
    · -- Part 1: UF-consistency
      intro i j hij
      have hvi := (consistent_root_eq' g env v hv hwf i).symm
      have hvj := (consistent_root_eq' g env v hv hwf j).symm
      rw [hvi, hvj]
      rcases union_root_cases _ _ _ i hwf2 hr1_bnd hr2_bnd with hi | ⟨hi_new, hi_old⟩ <;>
        rcases union_root_cases _ _ _ j hwf2 hr1_bnd hr2_bnd with hj | ⟨hj_new, hj_old⟩
      · rw [hi, hj] at hij; simp only [hfpr2] at hij; exact congrArg v hij
      · rw [hi, hj_new] at hij; simp only [hfpr2] at hij hj_old
        rw [hij, hr1_idem, hj_old, hr2_idem]; exact heq
      · rw [hi_new, hj] at hij; simp only [hfpr2] at hij hi_old
        rw [hi_old, hr2_idem, ← hij, hr1_idem]; exact heq.symm
      · simp only [hfpr2] at hi_old hj_old; rw [hi_old, hr2_idem, hj_old, hr2_idem]
    · -- Part 2: Node-consistency
      intro classId eclass hcls node hmem
      simp only [] at hcls
      by_cases hid : root g.unionFind id1 = classId
      · -- classId = root1: eclass = mergedClass
        subst hid
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          beq_self_eq_true, ite_true] at hcls
        have hcls_eq := Option.some.inj hcls
        rw [← hcls_eq] at hmem
        rcases eclass_union_mem _ _ node hmem with h1m | h2m
        · -- node from class1
          cases hcls1 : g.classes[root g.unionFind id1]? with
          | none =>
            simp only [hcls1, Option.getD,
              show (default : EClass).nodes = #[] from rfl] at h1m
            exact nomatch h1m
          | some c1 =>
            simp only [hcls1, Option.getD_some] at h1m
            exact hv.2 (root g.unionFind id1) c1
              (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls1) node h1m
        · -- node from class2
          cases hcls2 : g.classes[root g.unionFind id2]? with
          | none =>
            simp only [hcls2, Option.getD,
              show (default : EClass).nodes = #[] from rfl] at h2m
            exact nomatch h2m
          | some c2 =>
            simp only [hcls2, Option.getD_some] at h2m
            rw [hv.2 (root g.unionFind id2) c2
              (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls2) node h2m]
            exact heq.symm
      · -- classId ≠ root1: eclass from g.classes unchanged
        have hcls_orig : g.classes.get? classId = some eclass := by
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_eq_false_iff_ne.mpr hid] at hcls
          rw [Std.HashMap.get?_eq_getElem?]; exact hcls
        exact hv.2 classId eclass hcls_orig node hmem

-- ══════════════════════════════════════════════════════════════════
-- Section 9: canonicalize + processClass preserve CV
-- ══════════════════════════════════════════════════════════════════

/-- canonicalize preserves ConsistentValuation (only does path compression). -/
theorem canonicalize_consistent (g : EGraph) (node : ENode)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind) :
    ConsistentValuation (g.canonicalize node).2 env v := by
  have hroots : ∀ j, root (g.canonicalize node).2.unionFind j = root g.unionFind j :=
    canonicalize_preserves_roots g node hwf
  constructor
  · intro i j hij
    exact hv.1 i j (by rw [← hroots i, ← hroots j]; exact hij)
  · intro classId eclass hcls nd hmem
    rw [canonicalize_classes] at hcls
    exact hv.2 classId eclass hcls nd hmem

/-- processClass preserves ConsistentValuation. -/
theorem processClass_consistent (g : EGraph) (classId : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind) :
    ConsistentValuation (g.processClass classId).1 env v := by
  constructor
  · intro i j hij
    have hroots := processClass_preserves_roots g classId hwf
    exact hv.1 i j (by rw [← hroots i, ← hroots j]; exact hij)
  · intro cid cls hcls nd hmem
    rw [processClass_classes] at hcls
    exact hv.2 cid cls hcls nd hmem

-- ══════════════════════════════════════════════════════════════════
-- Section 10: processClass produces semantically valid merges
-- ══════════════════════════════════════════════════════════════════

/-- HCA + ConsistentValuation means each hashcons entry evaluates correctly. -/
private theorem hashcons_entries_eval (g : EGraph) (env : CircuitEnv Val)
    (v : EClassId → Val) (hv : ConsistentValuation g env v)
    (hca : HashconsClassesAligned g) :
    ∀ nd id, g.hashcons.get? nd = some id → NodeEval nd env v = v id := by
  intro nd id hget
  obtain ⟨cls, hcls, hmem⟩ := hca nd id hget
  exact hv.2 id cls hcls nd hmem

/-- processClass emits merge pairs with semantically equal valuations.
    The proof uses Array.foldl_induction tracking (merge_validity, roots_eq,
    wf, hashcons_inv, acc.classes = g.classes) through the inner foldl.
    Adapted from OptiSat processClass_merges_semantically_valid. -/
theorem processClass_merges_valid (g : EGraph) (classId : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hca : HashconsClassesAligned g) (hcb : ChildrenBounded g) :
    ∀ (pr : EClassId × EClassId), pr ∈ (g.processClass classId).2 →
      v pr.1 = v pr.2 := by
  unfold EGraph.processClass
  simp only [EGraph.find, find_fst_eq_root]
  split
  · intro pr hp; exact nomatch hp
  · rename_i eclass heclass
    have hcls_canon : g.classes.get? (root g.unionFind classId) = some eclass := by
      rw [Std.HashMap.get?_eq_getElem?]; exact heclass
    -- Foldl invariant: (merges_valid, roots_eq, wf, hashcons_inv, size_eq, classes_eq)
    have h_base : (∀ pr ∈ ([] : List (EClassId × EClassId)), v pr.1 = v pr.2) ∧
        (∀ k, root (g.unionFind.find classId).2 k = root g.unionFind k) ∧
        WellFormed (g.unionFind.find classId).2 ∧
        (∀ nd id, g.hashcons.get? nd = some id →
          g.hashcons.get? nd = some id ∨ id = root g.unionFind classId) ∧
        (g.unionFind.find classId).2.parent.size = g.unionFind.parent.size ∧
        g.classes = g.classes := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ h; exact nomatch h
      · exact fun k => find_preserves_roots g.unionFind classId k hwf
      · exact find_preserves_wf g.unionFind classId hwf
      · intro nd id h; exact Or.inl h
      · exact find_snd_size g.unionFind classId
      · rfl
    exact (@Array.foldl_induction ENode (EGraph × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (r : EGraph × List (EClassId × EClassId)) =>
        (∀ pr ∈ r.2, v pr.1 = v pr.2) ∧
        (∀ k, root r.1.unionFind k = root g.unionFind k) ∧
        WellFormed r.1.unionFind ∧
        (∀ nd id, r.1.hashcons.get? nd = some id →
          g.hashcons.get? nd = some id ∨ id = root g.unionFind classId) ∧
        r.1.unionFind.parent.size = g.unionFind.parent.size ∧
        r.1.classes = g.classes)
      _
      h_base
      _
      (fun ⟨i, hi⟩ b ih => by
        obtain ⟨acc, merges⟩ := b
        obtain ⟨ih_sem, ih_roots, ih_wf, ih_hcs, ih_sz, ih_cls⟩ := ih
        dsimp only at ih_sem ih_roots ih_wf ih_hcs ih_sz ih_cls ⊢
        -- Canonicalize preserves all invariants
        have a1_hcs := canonicalize_hashcons acc eclass.nodes[i]
        have a1_roots : ∀ k, root (acc.canonicalize eclass.nodes[i]).2.unionFind k =
            root g.unionFind k :=
          fun k => by rw [canonicalize_preserves_roots acc _ ih_wf]; exact ih_roots k
        have a1_wf := canonicalize_uf_wf acc eclass.nodes[i] ih_wf
        have a1_sz : (acc.canonicalize eclass.nodes[i]).2.unionFind.parent.size =
            g.unionFind.parent.size := by
          rw [canonicalize_uf_size]; exact ih_sz
        have a1_cls : (acc.canonicalize eclass.nodes[i]).2.classes = g.classes := by
          rw [canonicalize_classes]; exact ih_cls
        have a1_hcs_inv : ∀ nd id,
            (acc.canonicalize eclass.nodes[i]).2.hashcons.get? nd = some id →
            g.hashcons.get? nd = some id ∨ id = root g.unionFind classId := by
          intro nd id h; rw [a1_hcs] at h; exact ih_hcs nd id h
        -- Insert invariant for modified hashcons
        have ins_inv : ∀ nd id,
            (((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
              (acc.canonicalize eclass.nodes[i]).1 (root g.unionFind classId)).get? nd = some id →
            g.hashcons.get? nd = some id ∨ id = root g.unionFind classId := by
          intro nd id hget
          by_cases hcn : (acc.canonicalize eclass.nodes[i]).1 = nd
          · subst hcn; rw [hashcons_get?_insert_self] at hget
            exact .inr (Option.some.inj hget.symm)
          · rw [hashcons_get?_insert_ne _ _ _ _ hcn] at hget
            by_cases hnn : eclass.nodes[i] = nd
            · subst hnn; rw [hashcons_get?_erase_self] at hget; exact nomatch hget
            · rw [hashcons_get?_erase_ne _ _ _ hnn, a1_hcs] at hget
              exact ih_hcs nd id hget
        split
        · -- canonNode == node: no hashcons change
          exact ⟨ih_sem, a1_roots, a1_wf, a1_hcs_inv, a1_sz, a1_cls⟩
        · -- canonNode ≠ node
          rename_i hne_beq
          split
          · -- existing entry found → emit merge (canonId, existingId)
            rename_i existingId hexists
            refine ⟨?_, a1_roots, a1_wf, ins_inv, a1_sz, a1_cls⟩
            intro pr hpr
            simp only [List.mem_cons] at hpr
            rcases hpr with rfl | hpr
            · -- The new merge pair
              simp only []
              have hne : (acc.canonicalize eclass.nodes[i]).1 ≠ eclass.nodes[i] :=
                fun h => hne_beq (beq_iff_eq.mpr h)
              have hex_acc : acc.hashcons.get? (acc.canonicalize eclass.nodes[i]).1 =
                  some existingId := by
                have h1 : ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).get?
                    (acc.canonicalize eclass.nodes[i]).1 = some existingId := hexists
                rw [hashcons_get?_erase_ne _ _ _ hne.symm, a1_hcs] at h1; exact h1
              rcases ih_hcs _ _ hex_acc with hg_orig | hid_eq
              · -- existingId came from g.hashcons
                obtain ⟨cls_ex, hcls_ex, hmem_ex⟩ := hca _ _ hg_orig
                have heval_ex := hv.2 existingId cls_ex hcls_ex _ hmem_ex
                have hmem_i : eclass.nodes[i] ∈ eclass.nodes.toList :=
                  Array.mem_toList_iff.mpr (Array.getElem_mem hi)
                have heval_can := hv.2 _ eclass hcls_canon _ hmem_i
                -- Use nodeEval_canonicalize to bridge: NodeEval(canon) = NodeEval(orig)
                have huf_acc : ∀ a b, root acc.unionFind a = root acc.unionFind b →
                    v a = v b :=
                  fun a b h => hv.1 a b (by rw [← ih_roots a, ← ih_roots b]; exact h)
                have hbnd_acc : ∀ c ∈ (eclass.nodes[i]).children,
                    c < acc.unionFind.parent.size := by
                  intro c hc; rw [ih_sz]; exact hcb _ eclass hcls_canon _ hmem_i c hc
                have heval_canonical :=
                  nodeEval_canonicalize acc eclass.nodes[i] env v huf_acc ih_wf hbnd_acc
                exact heval_can.symm.trans (heval_canonical.symm.trans heval_ex)
              · -- existingId = root(classId)
                rw [hid_eq]
            · exact ih_sem pr hpr
          · -- no existing entry: no merge emitted
            exact ⟨ih_sem, a1_roots, a1_wf, ins_inv, a1_sz, a1_cls⟩)).1

-- ══════════════════════════════════════════════════════════════════
-- Section 11: mergeAll preserves CV (with valid merge pairs)
-- ══════════════════════════════════════════════════════════════════

/-- Applying a list of merges preserves ConsistentValuation when all pairs
    have equal values. Precondition uses v(p.1) = v(p.2) (not root form)
    since v is invariant across merges. -/
theorem mergeAll_consistent : ∀ (merges : List (EClassId × EClassId))
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val),
    ConsistentValuation g env v →
    WellFormed g.unionFind →
    (∀ p ∈ merges, v p.1 = v p.2) →
    (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) →
    ConsistentValuation (merges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g) env v := by
  intro merges
  induction merges with
  | nil => intro _ _ _ hv _ _ _; exact hv
  | cons hd tl ih =>
    intro g env v hv hwf hval hbnd
    simp only [List.foldl_cons]
    have hhd_val := hval hd (.head _)
    have hhd_bnd := hbnd hd (.head _)
    have hv' := merge_consistent g hd.1 hd.2 env v hv hwf hhd_bnd.1 hhd_bnd.2
      (by rw [consistent_root_eq' g env v hv hwf hd.1,
              consistent_root_eq' g env v hv hwf hd.2]; exact hhd_val)
    have hwf' := merge_preserves_uf_wf' g hd.1 hd.2 hwf hhd_bnd.1
    have hsz := merge_uf_size g hd.1 hd.2
    exact ih (g.merge hd.1 hd.2) env v hv' hwf'
      (fun p hp => hval p (.tail _ hp))
      (fun p hp => by rw [hsz]; exact hbnd p (.tail _ hp))

-- ══════════════════════════════════════════════════════════════════
-- Section 12: SHI preservation through merge
-- ══════════════════════════════════════════════════════════════════

/-- Clearing worklist/dirtyArr preserves SHI. -/
theorem clear_worklist_shi (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hshi : SemanticHashconsInv g env v) :
    SemanticHashconsInv { g with worklist := ([] : List EClassId), dirtyArr := #[] } env v := by
  intro nd id hget; exact hshi nd id hget

/-- merge preserves SHI when the merged classes have equal values. -/
theorem merge_preserves_shi (g : EGraph) (id1 id2 : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hshi : SemanticHashconsInv g env v)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (h1 : id1 < g.unionFind.parent.size) (h2 : id2 < g.unionFind.parent.size)
    (heq : v (root g.unionFind id1) = v (root g.unionFind id2)) :
    SemanticHashconsInv (g.merge id1 id2) env v := by
  intro nd mid hget
  rw [merge_hashcons] at hget
  have hshi_orig := hshi nd mid hget
  have hcv_merged := merge_consistent g id1 id2 env v hcv hwf h1 h2 heq
  rw [hshi_orig]
  exact (consistent_root_eq' g env v hcv hwf mid).trans
    (consistent_root_eq' (g.merge id1 id2) env v hcv_merged
      (merge_preserves_uf_wf' g id1 id2 hwf h1) mid).symm

/-- mergeAll preserves SHI when CV and WF are threaded alongside. -/
theorem mergeAll_preserves_shi : ∀ (merges : List (EClassId × EClassId))
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val),
    ConsistentValuation g env v →
    WellFormed g.unionFind →
    SemanticHashconsInv g env v →
    (∀ p ∈ merges, v p.1 = v p.2) →
    (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) →
    SemanticHashconsInv (merges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g) env v := by
  intro merges
  induction merges with
  | nil => intro _ _ _ _ _ hshi _ _; exact hshi
  | cons hd tl ih =>
    intro g env v hcv hwf hshi hval hbnd
    simp only [List.foldl_cons]
    have hhd_val := hval hd (.head _)
    have hhd_bnd := hbnd hd (.head _)
    have heq : v (root g.unionFind hd.1) = v (root g.unionFind hd.2) := by
      rw [consistent_root_eq' g env v hcv hwf hd.1,
          consistent_root_eq' g env v hcv hwf hd.2]; exact hhd_val
    have hshi' := merge_preserves_shi g hd.1 hd.2 env v hshi hcv hwf hhd_bnd.1 hhd_bnd.2 heq
    have hcv' := merge_consistent g hd.1 hd.2 env v hcv hwf hhd_bnd.1 hhd_bnd.2 heq
    have hwf' := merge_preserves_uf_wf' g hd.1 hd.2 hwf hhd_bnd.1
    have hsz := merge_uf_size g hd.1 hd.2
    exact ih (g.merge hd.1 hd.2) env v hcv' hwf' hshi'
      (fun p hp => hval p (.tail _ hp))
      (fun p hp => by rw [hsz]; exact hbnd p (.tail _ hp))

end AmoLean.EGraph.Verified
