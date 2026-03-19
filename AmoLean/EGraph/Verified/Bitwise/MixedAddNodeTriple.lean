/-
  AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple — EGraph.add preserves ConsistentValuation

  Strategy: field-access lemmas abstract EGraph.add structure (cf. OptiSat CoreSpec.lean).
  The main proof never unfolds EGraph.add directly — only the access lemmas do.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp evalOp_mapChildren)

abbrev MGraph := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.MGraph
abbrev MNode  := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.MNode
abbrev CId    := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.CId
abbrev VPMI   := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.VPMI
abbrev CV     := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.CV

abbrev NodeEvalM (node : MNode) (env : MixedEnv) (v : CId → Nat) : Nat :=
  AmoLean.EGraph.VerifiedExtraction.NodeEval node env v

open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec (ndChildren)
open AmoLean.EGraph.VerifiedExtraction.UnionFind (root root_oob)
open AmoLean.EGraph.VerifiedExtraction (EClassId NodeSemantics)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Structural lemma
-- ══════════════════════════════════════════════════════════════════

theorem add_size_le (g : MGraph) (node : MNode) :
    g.unionFind.parent.size ≤ (g.add node).2.unionFind.parent.size := by
  unfold AmoLean.EGraph.VerifiedExtraction.EGraph.add; simp only
  split
  · exact Nat.le_refl _
  · unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add
    simp only [Array.size_push]; exact Nat.le_succ _

-- ══════════════════════════════════════════════════════════════════
-- Section 2: ShapeHashconsInv + nodeEval_canonical
-- ══════════════════════════════════════════════════════════════════

def ShapeHashconsInv (g : MGraph) : Prop :=
  ∀ (nd : MNode) (id : CId), g.hashcons.get? nd = some id →
    ∃ cls, g.classes.get? id = some cls ∧ nd ∈ cls.nodes.toList

/-- Canonical-node bridge: evaluating a node after mapChildren root equals evaluating original.
    Combines evalOp_mapChildren (definitional) + evalOp_ext (v ∘ root = v by consistent_root_eq'). -/
theorem nodeEval_canonical (g : MGraph) (node : MNode) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind) :
    NodeEvalM (AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren (root g.unionFind) node) env v
    = NodeEvalM node env v := by
  simp only [NodeEvalM, AmoLean.EGraph.VerifiedExtraction.NodeEval,
    AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren,
    NodeSemantics.evalOp, AmoLean.EGraph.VerifiedExtraction.NodeOps.mapChildren]
  -- Now goal is: evalMixedOp (mixedMapChildren root node.op) env v = evalMixedOp node.op env v
  rw [evalOp_mapChildren]
  -- Goal: evalMixedOp node.op env (fun c => v (root c)) = evalMixedOp node.op env v
  exact NodeSemantics.evalOp_ext node.op env _ v
    (fun c _ => AmoLean.EGraph.VerifiedExtraction.consistent_root_eq' hcv hwf c)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: add_node_consistent
-- ══════════════════════════════════════════════════════════════════

theorem add_node_consistent (g : MGraph) (node : MNode) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g) (hshi : ShapeHashconsInv g)
    (hbnd : ∀ c ∈ ndChildren node, c < g.unionFind.parent.size) :
    ∃ v', CV (g.add node).2 env v' ∧
      VPMI (g.add node).2 ∧
      v' (g.add node).1 = NodeEvalM node env v' ∧
      (g.add node).1 < (g.add node).2.unionFind.parent.size ∧
      g.unionFind.parent.size ≤ (g.add node).2.unionFind.parent.size ∧
      ∀ i, i < g.unionFind.parent.size → v' i = v i := by
  unfold AmoLean.EGraph.VerifiedExtraction.EGraph.add; simp only
  split
  · -- ═══ HIT: canonical node in hashcons ═══
    rename_i existingId hlookup
    have hwf := hpmi.uf_wf
    have hid_bnd := hpmi.hashcons_entries_valid _ existingId hlookup
    obtain ⟨cls, hcls, hnd_mem⟩ := hshi _ existingId hlookup
    have heval := hcv.node_consistent existingId cls hcls _ hnd_mem
    refine ⟨v, hcv, hpmi, ?_, hwf.root_bounded existingId hid_bnd, Nat.le_refl _, fun i _ => rfl⟩
    -- Goal: v (root existingId) = NodeEvalM node env v
    rw [AmoLean.EGraph.VerifiedExtraction.consistent_root_eq hcv hwf hid_bnd, ← heval]
    -- Goal: NodeEvalM (if ... then node else mapChildren root node) env v = NodeEvalM node env v
    split
    · rfl  -- children empty: canonical = original
    · exact nodeEval_canonical g node env v hcv hwf  -- children non-empty: bridge
  · -- ═══ MISS: new node ═══
    rename_i hlookup_none
    have hwf := hpmi.uf_wf
    -- v' maps newId to nodeVal, agrees with v on old IDs
    refine ⟨fun i => if i = g.unionFind.parent.size
      then NodeEvalM node env v else v i, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- MISS-CV: ConsistentValuation for extended graph
      unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add
      simp only []  -- zeta-reduce ALL let-bindings (L-676)
      exact {
        equiv_same_val := by
          intro i j hij
          rw [MixedUnionFind.root_push_all_eq hpmi.uf_swf i,
              MixedUnionFind.root_push_all_eq hpmi.uf_swf j] at hij
          by_cases hi : i < g.unionFind.parent.size <;> by_cases hj : j < g.unionFind.parent.size
          · -- Both old: v'(i) = v(i), v'(j) = v(j), use hcv
            rw [if_neg (Nat.ne_of_lt hi), if_neg (Nat.ne_of_lt hj)]
            exact hcv.equiv_same_val i j hij
          · -- i old, j ≥ oldSize: root(i) < oldSize but root(j) = j ≥ oldSize → ⊥
            exfalso
            have h1 := hwf.root_bounded i hi
            rw [hij, root_oob g.unionFind j hj] at h1
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 (Nat.le_of_not_lt hj))
          · -- j old, i ≥ oldSize: symmetric
            exfalso
            have h1 := hwf.root_bounded j hj
            rw [← hij, root_oob g.unionFind i hi] at h1
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 (Nat.le_of_not_lt hi))
          · -- Both ≥ oldSize: root_oob → i = j
            rw [root_oob g.unionFind i hi, root_oob g.unionFind j hj] at hij
            subst hij; rfl
        node_consistent := by
          intro classId eclass hget nd hnd
          -- After zeta-reduction, classes is g.classes.insert newId (singleton canonNode)
          -- Split on classId = newId vs old class
          by_cases hcid : classId = g.unionFind.parent.size
          · -- classId = newId: new singleton class
            subst hcid; simp only [ite_true]
            -- Extract eclass from HashMap insert (classId = key → eclass = singleton canonNode)
            rw [MixedCoreSpec.classes_get?_insert_self] at hget
            obtain rfl := Option.some.inj hget
            -- nd ∈ singleton(canonNode).nodes → nd = canonNode
            simp only [AmoLean.EGraph.VerifiedExtraction.EClass.singleton] at hnd
            simp at hnd; subst hnd
            -- Goal: NodeEval(canonNode, env, v') = NodeEvalM node env v
            -- Strategy: reduce v' to v via evalOp_ext, then use nodeEval_canonical
            -- The goal has an if on children.isEmpty. Split:
            split
            · -- children empty: canon = node
              unfold NodeEvalM AmoLean.EGraph.VerifiedExtraction.NodeEval; symm
              apply NodeSemantics.evalOp_ext; intro c hc
              exact (if_neg (Nat.ne_of_lt (hbnd c hc))).symm
            · -- children non-empty: canon = mapChildren root node
              -- Step 1: v' → v on canonical children (evalOp_ext)
              have hstep1 : ∀ c,
                  c ∈ (AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren
                    (fun c => root g.unionFind c) node).children →
                  (fun i => if i = g.unionFind.parent.size then NodeEvalM node env v else v i) c = v c := by
                intro c hc
                simp only [AmoLean.EGraph.VerifiedExtraction.ENode.children,
                  AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren,
                  AmoLean.EGraph.VerifiedExtraction.NodeOps.mapChildren_children,
                  List.mem_map] at hc
                obtain ⟨c', hc'mem, rfl⟩ := hc
                exact if_neg (Nat.ne_of_lt (hwf.root_bounded c' (hbnd c' hc'mem)))
              -- Step 2: combine with nodeEval_canonical
              rw [show AmoLean.EGraph.VerifiedExtraction.NodeEval
                  (AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren (fun c => root g.unionFind c) node)
                  env (fun i => if i = g.unionFind.parent.size then NodeEvalM node env v else v i) =
                AmoLean.EGraph.VerifiedExtraction.NodeEval
                  (AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren (fun c => root g.unionFind c) node)
                  env v from NodeSemantics.evalOp_ext _ env _ _ hstep1]
              exact nodeEval_canonical g node env v hcv hwf
          · -- classId ≠ newId: old class
            simp only [show ¬(classId = g.unionFind.parent.size) from hcid, ite_false]
            rw [MixedCoreSpec.classes_get?_insert_ne _ _ _ _ (Ne.symm hcid)] at hget
            rw [← hcv.node_consistent classId eclass hget nd hnd]
            apply NodeSemantics.evalOp_ext; intro c hc
            exact if_neg (Nat.ne_of_lt
              (hpmi.children_bounded classId eclass hget nd hnd c hc))
      }
    · -- MISS-VPMI
      constructor
      · -- uf_swf
        exact MixedUnionFind.push_preserves_strongWF hpmi.uf_swf
      · -- children_bounded
        unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add
        simp only []  -- zeta-reduce let-bindings (L-676)
        intro cid cls hcls nd hnd c hc
        simp only [Array.size_push]
        -- Now classes is concrete: g.classes.insert newId (singleton canonNode)
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hcls
        split at hcls
        · -- cid = newId: new class with canonical node
          obtain rfl := Option.some.inj hcls
          -- hnd : nd ∈ singleton.nodes.toList — simplify to nd = canonNode
          simp only [AmoLean.EGraph.VerifiedExtraction.EClass.singleton] at hnd
          simp at hnd
          subst hnd
          -- c is child of canonNode; canonNode children are root(original children)
          -- All roots are < oldSize by root_bounded
          -- c ∈ ndChildren(canonNode). Split on children empty:
          simp only [ndChildren, AmoLean.EGraph.VerifiedExtraction.ENode.children] at hc
          split at hc
          · -- children empty: canonNode = node → c ∈ children(node)
            exact Nat.lt_succ_of_lt (hbnd c hc)
          · -- children non-empty: canonNode = mapChildren root node
            -- children(mapChildren root node) = map root (children node)
            simp only [AmoLean.EGraph.VerifiedExtraction.ENode.mapChildren,
              AmoLean.EGraph.VerifiedExtraction.NodeOps.mapChildren_children] at hc
            obtain ⟨c', hc'mem, rfl⟩ := List.mem_map.mp hc
            exact Nat.lt_succ_of_lt (hwf.root_bounded c' (hbnd c' hc'mem))
        · -- cid ≠ newId: old class
          have hcls' : g.classes.get? cid = some cls := by rwa [Std.HashMap.get?_eq_getElem?]
          exact Nat.lt_succ_of_lt (hpmi.children_bounded cid cls hcls' nd hnd c hc)
      · -- hashcons_entries_valid
        unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add
        simp only []  -- zeta-reduce let-bindings (L-676)
        intro nd' id' hget'
        simp only [Array.size_push]
        -- Split hashcons.insert on key equality
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget'
        split at hget'
        all_goals (
          split at hget'
          · -- nd' = canonical: some size = some id'
            cases hget'; exact Nat.lt.base _
          · -- nd' ≠ canonical: old entry
            exact Nat.lt_succ_of_lt (hpmi.hashcons_entries_valid nd' id'
              (by rw [Std.HashMap.get?_eq_getElem?]; exact hget')))
      · -- classes_entries_valid
        unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add
        intro id' hcont
        simp only [Array.size_push, Std.HashMap.contains_insert] at hcont ⊢
        rcases Bool.or_eq_true_iff.mp hcont with heq | hc
        · rw [beq_iff_eq] at heq; subst heq; simp_all [Nat.lt_succ_of_le]
        · exact Nat.lt_succ_of_lt (hpmi.classes_entries_valid id' hc)
    · -- v'(newId) = NodeEvalM node env v'
      change (if g.unionFind.parent.size = g.unionFind.parent.size
        then NodeEvalM node env v else v g.unionFind.parent.size) =
        NodeEvalM node env (fun i => if i = g.unionFind.parent.size
          then NodeEvalM node env v else v i)
      simp only [ite_true]
      -- NodeEvalM node env v = NodeEvalM node env v' where v' = v on children (< oldSize)
      unfold NodeEvalM AmoLean.EGraph.VerifiedExtraction.NodeEval
      symm
      exact NodeSemantics.evalOp_ext node.op env _ _
        (fun c hc => if_neg (Nat.ne_of_lt (hbnd c hc)))
    · -- newId < new size
      unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add; simp [Array.size_push]
    · -- oldSize ≤ new size
      unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add; simp [Array.size_push]
    · -- v' backward compat
      intro i hi; exact if_neg (Nat.ne_of_lt hi)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

example : (AmoLean.EGraph.VerifiedExtraction.EGraph.empty : MGraph).unionFind.parent.size ≤
    ((AmoLean.EGraph.VerifiedExtraction.EGraph.empty : MGraph).add
      ⟨MixedNodeOp.constGate 42⟩).2.unionFind.parent.size :=
  add_size_le _ _

end AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple
