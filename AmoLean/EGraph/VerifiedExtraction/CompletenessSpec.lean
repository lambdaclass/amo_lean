/-
  AMO-Lean — Completeness Specification
  Fase 16: Extraction Completeness (v2.5.1)

  Proves bestNode DAG acyclicity after cost computation and fuel
  sufficiency for extraction completeness. Ported from OptiSat v1.5.1
  CompletenessSpec.lean, adapted to amo-lean's fold-based computeCostsF.

  Key results (G1 — DAG acyclicity):
  - `BestNodeChild`: child relationship via bestNode pointers
  - `AcyclicBestNodeDAG`: acyclicity via ranking function
  - `BestCostLowerBound`: bestCost ≥ costFn(bestNode) + Σ children costs
  - `bestCostLowerBound_acyclic`: lower bound + positive costs → acyclic (0 sorry, 0 axioms)

  Key results (G2 — fuel sufficiency):
  - `extractF_of_rank`: fuel > rank(id) → extractF succeeds (0 sorry, 0 axioms)
  - `extractAuto_complete`: extractAuto succeeds when rank < numClasses (0 sorry, 0 axioms)

  Reference: L-519 (HashMap nodup bridge), L-520 (omega + struct projection),
  L-521 (parasitic rewrite guard).
-/
import AmoLean.EGraph.VerifiedExtraction.Greedy

namespace AmoLean.EGraph.VerifiedExtraction.CompletenessSpec

set_option linter.unusedSectionVars false

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.VerifiedExtraction.Greedy

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

-- Local copy of infinityCost (private in Core.lean)
private def infinityCost : Nat := 1000000000

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Definitions
-- ══════════════════════════════════════════════════════════════════

/-- Look up the bestCost of the canonical representative of `cid`. -/
def bestCostOf (g : EGraph Op) (cid : EClassId) : Nat :=
  match g.classes.get? (UnionFind.root g.unionFind cid) with
  | some cls => cls.bestCost
  | none => infinityCost

/-- Child relationship via bestNode pointers: `parentId` has a bestNode
    whose children include `childId`. -/
def BestNodeChild (g : EGraph Op) (parentId childId : EClassId) : Prop :=
  ∃ cls nd,
    g.classes.get? (UnionFind.root g.unionFind parentId) = some cls ∧
    cls.bestNode = some nd ∧
    childId ∈ (NodeOps.children nd.op)

/-- The bestNode DAG is acyclic: there exists a ranking function that
    strictly decreases along `BestNodeChild` edges. -/
def AcyclicBestNodeDAG (g : EGraph Op) : Prop :=
  ∃ (rank : EClassId → Nat),
    ∀ parentId childId, BestNodeChild g parentId childId →
      rank childId < rank parentId

/-- After cost computation, bestCost satisfies a lower bound:
    bestCost(cid) ≥ costFn(bestNode) + Σ bestCostOf(children of bestNode).
    This is the key invariant for acyclicity. -/
def BestCostLowerBound (g : EGraph Op) (costFn : ENode Op → Nat) : Prop :=
  ∀ cid cls nd, g.classes.get? cid = some cls →
    cls.bestNode = some nd →
    cls.bestCost ≥ costFn nd +
      (NodeOps.children nd.op).foldl (fun sum c => sum + bestCostOf g c) 0

-- ══════════════════════════════════════════════════════════════════
-- Section 2: BestCostLowerBound implies acyclicity
-- ══════════════════════════════════════════════════════════════════

/-- Foldl with non-negative additions is ≥ init. -/
private theorem foldl_ge_init (g : EGraph Op) (children : List EClassId) (init : Nat) :
    children.foldl (fun sum c => sum + bestCostOf g c) init ≥ init := by
  induction children generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_add_right _ _) (ih _)

/-- If `childId` is in a list, then the fold sum ≥ bestCostOf childId. -/
private theorem foldl_sum_ge_mem (g : EGraph Op) (children : List EClassId)
    (childId : EClassId) (hmem : childId ∈ children) :
    children.foldl (fun sum c => sum + bestCostOf g c) 0 ≥ bestCostOf g childId := by
  suffices h : ∀ init, childId ∈ children →
      children.foldl (fun sum c => sum + bestCostOf g c) init ≥ init + bestCostOf g childId by
    have := h 0 hmem; omega
  intro init hmem
  induction children generalizing init with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with heq | hmem_tl
    · subst heq
      exact foldl_ge_init g tl _
    · have := ih hmem_tl (init + bestCostOf g hd) hmem_tl
      omega

/-- **BestCostLowerBound with positive cost function implies acyclic DAG.**
    Uses bestCostOf as the ranking function: if bestCost(parent) ≥ costFn(nd) + Σ children
    and costFn ≥ 1, then bestCost(parent) > bestCost(child). -/
theorem bestCostLowerBound_acyclic (g : EGraph Op) (costFn : ENode Op → Nat)
    (hlb : BestCostLowerBound g costFn)
    (hcost_pos : ∀ (nd : ENode Op), 0 < costFn nd) :
    AcyclicBestNodeDAG g := by
  refine ⟨bestCostOf g, ?_⟩
  intro parentId childId ⟨cls, nd, hcls, hbn, hchild⟩
  have hlb' := hlb (UnionFind.root g.unionFind parentId) cls nd hcls hbn
  have hsum := foldl_sum_ge_mem g (NodeOps.children nd.op) childId hchild
  have hpos := hcost_pos nd
  have hparent : bestCostOf g parentId = cls.bestCost := by
    unfold bestCostOf; rw [hcls]
  rw [hparent]
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 2.5: computeCostsF bridge to BestCostLowerBound
-- ══════════════════════════════════════════════════════════════════

variable [EquivBEq Op] [LawfulHashable Op]

/-- HashMap insert: get? at same key returns inserted value. -/
private theorem get?_insert_self (m : Std.HashMap EClassId (EClass Op))
    (k : EClassId) (v : EClass Op) :
    (m.insert k v).get? k = some v := by
  simp [Std.HashMap.get?_eq_getElem?]

/-- HashMap insert: get? at different key is unchanged. -/
private theorem get?_insert_ne (m : Std.HashMap EClassId (EClass Op))
    (k k' : EClassId) (v : EClass Op) (h : k ≠ k') :
    (m.insert k v).get? k' = m.get? k' := by
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq, h]

/-- updateBest only decreases bestCost. -/
private theorem updateBest_bestCost_le (ec : EClass Op) (node : ENode Op) (cost : Nat) :
    (ec.updateBest node cost).bestCost ≤ ec.bestCost := by
  unfold EClass.updateBest
  split
  · dsimp; omega
  · exact Nat.le_refl _

/-- updateBest: if it changes, bestCost = cost and bestNode = some node. -/
private theorem updateBest_eq_of_lt (ec : EClass Op) (node : ENode Op) (cost : Nat)
    (h : cost < ec.bestCost) :
    (ec.updateBest node cost).bestCost = cost ∧
    (ec.updateBest node cost).bestNode = some node := by
  unfold EClass.updateBest; simp [h]

/-- updateBest: if it doesn't change, ec is unchanged. -/
private theorem updateBest_eq_of_ge (ec : EClass Op) (node : ENode Op) (cost : Nat)
    (h : ¬ cost < ec.bestCost) :
    ec.updateBest node cost = ec := by
  simp only [EClass.updateBest, h, ite_false]

/-- Pointwise f ≤ g implies foldl sum with f ≤ foldl sum with g. -/
private theorem foldl_sum_le_pointwise (children : List EClassId) {f g : EClassId → Nat}
    (hle : ∀ c, f c ≤ g c) :
    children.foldl (fun sum c => sum + f c) 0 ≤
    children.foldl (fun sum c => sum + g c) 0 := by
  suffices h : ∀ i1 i2, i1 ≤ i2 →
      children.foldl (fun s c => s + f c) i1 ≤ children.foldl (fun s c => s + g c) i2 by
    exact h 0 0 (Nat.le_refl _)
  intro i1 i2 hi
  induction children generalizing i1 i2 with
  | nil => exact hi
  | cons hd tl ih =>
    simp only [List.foldl_cons]; apply ih; have := hle hd; omega

/-- Cost lookup helper matching computeCostsF's inline pattern. -/
private def getCost (classes : Std.HashMap EClassId (EClass Op))
    (uf : UnionFind) (cid : EClassId) : Nat :=
  match classes.get? (UnionFind.root uf cid) with
  | some ec => ec.bestCost
  | none => infinityCost

/-- Self-referential lower bound on a classes HashMap.
    This is the key invariant: for every class with bestNode set,
    bestCost ≥ costFn(bestNode) + Σ children costs (looked up in same map). -/
private def SelfLB (uf : UnionFind) (classes : Std.HashMap EClassId (EClass Op))
    (costFn : ENode Op → Nat) : Prop :=
  ∀ cid cls nd, classes.get? cid = some cls → cls.bestNode = some nd →
    cls.bestCost ≥ costFn nd + (NodeOps.children nd.op).foldl
      (fun sum c => sum + getCost classes uf c) 0

/-- getCost monotonicity: inserting a class with lower bestCost doesn't increase any getCost. -/
private theorem getCost_insert_le (classes : Std.HashMap EClassId (EClass Op))
    (uf : UnionFind) (k : EClassId) (v : EClass Op) (old : EClass Op)
    (hget : classes.get? k = some old) (hle : v.bestCost ≤ old.bestCost) :
    ∀ c, getCost (classes.insert k v) uf c ≤ getCost classes uf c := by
  intro c
  simp only [getCost]
  by_cases heq : k = UnionFind.root uf c
  · subst heq; rw [get?_insert_self, hget]; exact hle
  · rw [get?_insert_ne _ _ _ _ heq]; exact Nat.le_refl _

/-- Processing one node of a class preserves SelfLB.
    This is the innermost step of computeCostsF's fold. -/
private theorem processNode_preserves_SelfLB
    (uf : UnionFind) (costFn : ENode Op → Nat)
    (classes : Std.HashMap EClassId (EClass Op))
    (classId : EClassId) (node : ENode Op)
    (hslb : SelfLB uf classes costFn) :
    let nodeCost := costFn node + (NodeOps.children node.op).foldl
      (fun sum c => sum + getCost classes uf c) 0
    match classes.get? classId with
    | some ec =>
      SelfLB uf (classes.insert classId (ec.updateBest node nodeCost)) costFn
    | none => SelfLB uf classes costFn := by
  intro nodeCost
  split
  · next ec hec =>
    intro cid cls nd hget hbn
    have hcost_le := updateBest_bestCost_le ec node nodeCost
    have hmono : ∀ c, getCost (classes.insert classId (ec.updateBest node nodeCost)) uf c
        ≤ getCost classes uf c :=
      getCost_insert_le classes uf classId _ ec hec hcost_le
    by_cases heq : classId = cid
    · -- cid = classId: the updated class
      subst heq; rw [get?_insert_self] at hget
      have hcls := Option.some.inj hget; subst hcls
      by_cases hlt : nodeCost < ec.bestCost
      · -- updateBest changed
        have ⟨hbc, hbnd⟩ := updateBest_eq_of_lt ec node nodeCost hlt
        rw [hbnd] at hbn; cases hbn
        have hfold := foldl_sum_le_pointwise (NodeOps.children node.op) hmono
        omega
      · -- updateBest unchanged
        have hunch := updateBest_eq_of_ge ec node nodeCost hlt
        rw [hunch] at hbn hmono ⊢
        have hold := hslb classId ec nd hec hbn
        have hfold := foldl_sum_le_pointwise (NodeOps.children nd.op) hmono
        omega
    · -- cid ≠ classId: unchanged class
      rw [get?_insert_ne _ _ _ _ heq] at hget
      have hold := hslb cid cls nd hget hbn
      have hfold := foldl_sum_le_pointwise (NodeOps.children nd.op) hmono
      omega
  · next hnone => exact hslb

/-- Option.map/getD = match. Bridge between computeCostsF's inline form and getCost. -/
private theorem option_map_getD_eq_getCost (classes : Std.HashMap EClassId (EClass Op))
    (uf : UnionFind) (cid : EClassId) :
    (classes.get? (UnionFind.root uf cid) |>.map (·.bestCost) |>.getD infinityCost) =
    getCost classes uf cid := by
  simp only [getCost]; cases classes.get? (UnionFind.root uf cid) <;> rfl

/-- Bridge: Option.map.getD 1000000000 = getCost (pointwise). -/
private theorem cost_form_eq (classes : Std.HashMap EClassId (EClass Op))
    (uf : UnionFind) (cid : EClassId) :
    (classes.get? (UnionFind.root uf cid) |>.map (·.bestCost) |>.getD 1000000000) =
    getCost classes uf cid := by
  unfold getCost infinityCost; cases classes.get? (UnionFind.root uf cid) <;> rfl

/-- Bridge: foldl with Option.map.getD 1000000000 form = foldl with getCost. -/
private theorem foldl_cost_bridge (children : List EClassId)
    (classes : Std.HashMap EClassId (EClass Op)) (uf : UnionFind) (init : Nat) :
    children.foldl (fun sum childId =>
      sum + (classes.get? (UnionFind.root uf childId) |>.map (·.bestCost) |>.getD 1000000000)) init =
    children.foldl (fun sum c => sum + getCost classes uf c) init := by
  induction children generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, cost_form_eq]

/-- Bridge with unionFind substitution: raw foldl (with different uf) = getCost foldl. -/
private theorem foldl_raw_eq_getCost (children : List EClassId)
    (classes : Std.HashMap EClassId (EClass Op)) (uf_a uf_g : UnionFind)
    (huf : uf_a = uf_g) (init : Nat) :
    children.foldl (fun sum childId =>
      sum + (classes.get? (UnionFind.root uf_a childId) |>.map (·.bestCost) |>.getD 1000000000)) init =
    children.foldl (fun sum c => sum + getCost classes uf_g c) init := by
  subst huf; exact foldl_cost_bridge children classes uf_a init

/-- Single pass of computeCostsF — fold body matches computeCostsF exactly. -/
private def singlePass (g : EGraph Op) (costFn : ENode Op → Nat) : EGraph Op :=
  g.classes.fold (init := g) fun acc classId eclass =>
    eclass.nodes.foldl (init := acc) fun acc2 node =>
      let nodeCost := costFn node +
        node.children.foldl (fun sum childId =>
          let canonId := UnionFind.root acc2.unionFind childId
          sum + (acc2.classes.get? canonId |>.map (·.bestCost) |>.getD 1000000000)) 0
      match acc2.classes.get? classId with
      | some ec =>
        let ec' := ec.updateBest node nodeCost
        { acc2 with classes := acc2.classes.insert classId ec' }
      | none => acc2

/-- One step of computeCostsF = singlePass + recursion. -/
private theorem computeCostsF_succ_eq (g : EGraph Op) (costFn : ENode Op → Nat) (n : Nat) :
    EGraph.computeCostsF g costFn (n + 1) =
    EGraph.computeCostsF (singlePass g costFn) costFn n := by rfl

/-- singlePass preserves unionFind — fold only modifies classes. -/
private theorem singlePass_preserves_uf (g : EGraph Op) (costFn : ENode Op → Nat) :
    (singlePass g costFn).unionFind = g.unionFind := by
  unfold singlePass; rw [Std.HashMap.fold_eq_foldl_toList]
  suffices h : ∀ (pairs : List (EClassId × EClass Op)) (acc : EGraph Op),
      acc.unionFind = g.unionFind →
      (pairs.foldl (fun (a : EGraph Op) (p : EClassId × EClass Op) =>
        p.2.nodes.foldl (init := a) fun (acc2 : EGraph Op) (node : ENode Op) =>
          let nodeCost := costFn node +
            node.children.foldl (fun sum childId =>
              let canonId := UnionFind.root acc2.unionFind childId
              sum + (acc2.classes.get? canonId |>.map (·.bestCost) |>.getD 1000000000)) 0
          match acc2.classes.get? p.1 with
          | some ec =>
            let ec' := ec.updateBest node nodeCost
            { acc2 with classes := acc2.classes.insert p.1 ec' }
          | none => acc2) acc).unionFind = g.unionFind by
    exact h g.classes.toList g rfl
  intro pairs; induction pairs with
  | nil => intro acc huf; exact huf
  | cons hd tl ih =>
    intro acc huf; simp only [List.foldl_cons]; apply ih
    rw [← Array.foldl_toList]
    suffices hI : ∀ (nodes : List (ENode Op)) (a : EGraph Op),
        a.unionFind = g.unionFind →
        (nodes.foldl (fun (acc2 : EGraph Op) (node : ENode Op) =>
          let nodeCost := costFn node +
            node.children.foldl (fun sum childId =>
              let canonId := UnionFind.root acc2.unionFind childId
              sum + (acc2.classes.get? canonId |>.map (·.bestCost) |>.getD 1000000000)) 0
          match acc2.classes.get? hd.1 with
          | some ec =>
            let ec' := ec.updateBest node nodeCost
            { acc2 with classes := acc2.classes.insert hd.1 ec' }
          | none => acc2) a).unionFind = g.unionFind by
      exact hI hd.2.nodes.toList acc huf
    intro nodes; induction nodes with
    | nil => intro a ha; exact ha
    | cons nd rest ih_n =>
      intro a ha; simp only [List.foldl_cons]; apply ih_n; split <;> exact ha

/-- singlePass preserves SelfLB. The key bridge theorem. -/
private theorem singlePass_preserves_selfLB (g : EGraph Op) (costFn : ENode Op → Nat)
    (hslb : SelfLB g.unionFind g.classes costFn) :
    SelfLB (singlePass g costFn).unionFind (singlePass g costFn).classes costFn := by
  rw [singlePass_preserves_uf]
  -- Goal: SelfLB g.unionFind (singlePass g costFn).classes costFn
  unfold singlePass; rw [Std.HashMap.fold_eq_foldl_toList]
  -- Compound invariant: uf preserved ∧ SelfLB preserved
  suffices hOuter : ∀ (pairs : List (EClassId × EClass Op)) (acc : EGraph Op),
      acc.unionFind = g.unionFind → SelfLB g.unionFind acc.classes costFn →
      SelfLB g.unionFind (pairs.foldl (fun (a : EGraph Op) (p : EClassId × EClass Op) =>
        p.2.nodes.foldl (init := a) fun (acc2 : EGraph Op) (node : ENode Op) =>
          let nodeCost := costFn node +
            node.children.foldl (fun sum childId =>
              let canonId := UnionFind.root acc2.unionFind childId
              sum + (acc2.classes.get? canonId |>.map (·.bestCost) |>.getD 1000000000)) 0
          match acc2.classes.get? p.1 with
          | some ec =>
            let ec' := ec.updateBest node nodeCost
            { acc2 with classes := acc2.classes.insert p.1 ec' }
          | none => acc2) acc).classes costFn by
    exact hOuter g.classes.toList g rfl hslb
  intro pairs; induction pairs with
  | nil => intro acc _ hslb_acc; exact hslb_acc
  | cons hd tl ih_pairs =>
    intro acc huf_a hslb_a; simp only [List.foldl_cons]
    -- Inner fold preserves both uf and SelfLB; need both for ih_pairs
    have hInner : ∀ (nodes : List (ENode Op)) (a : EGraph Op),
        a.unionFind = g.unionFind → SelfLB g.unionFind a.classes costFn →
        let result := nodes.foldl (fun (acc2 : EGraph Op) (node : ENode Op) =>
          let nodeCost := costFn node +
            node.children.foldl (fun sum childId =>
              let canonId := UnionFind.root acc2.unionFind childId
              sum + (acc2.classes.get? canonId |>.map (·.bestCost) |>.getD 1000000000)) 0
          match acc2.classes.get? hd.1 with
          | some ec =>
            let ec' := ec.updateBest node nodeCost
            { acc2 with classes := acc2.classes.insert hd.1 ec' }
          | none => acc2) a
        result.unionFind = g.unionFind ∧ SelfLB g.unionFind result.classes costFn := by
      intro nodes; induction nodes with
      | nil => intro a ha hslb_a'; exact ⟨ha, hslb_a'⟩
      | cons nd rest ih_n =>
        intro a ha hslb_a'; simp only [List.foldl_cons]
        apply ih_n
        · -- uf preserved for this step
          split <;> exact ha
        · -- SelfLB preserved for this step
          split
          · next ec hec =>
            -- Bridge: raw foldl cost → getCost foldl
            rw [foldl_raw_eq_getCost nd.children a.classes a.unionFind g.unionFind ha 0]
            -- Now goal uses getCost form; apply processNode
            have hproc := processNode_preserves_SelfLB g.unionFind costFn a.classes hd.fst nd hslb_a'
            simp only [hec] at hproc
            exact hproc
          · exact hslb_a'
    rw [← Array.foldl_toList]
    have ⟨huf_inner, hslb_inner⟩ := hInner hd.2.nodes.toList acc huf_a hslb_a
    exact ih_pairs _ huf_inner hslb_inner

/-- `EGraph.computeCostsF` preserves unionFind (only modifies classes).
    Each step of the fold returns `{ acc with classes := ... }`, preserving unionFind. -/
theorem computeCostsF_preserves_uf (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat) :
    (EGraph.computeCostsF g costFn fuel).unionFind = g.unionFind := by
  induction fuel generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [EGraph.computeCostsF]; rw [ih]
    rw [Std.HashMap.fold_eq_foldl_toList]
    -- Outer fold (over class list) preserves unionFind
    suffices hOuter : ∀ (pairs : List (EClassId × EClass Op)) (acc : EGraph Op),
        acc.unionFind = g.unionFind →
        (pairs.foldl (fun a p => p.2.nodes.foldl (init := a) fun acc2 node =>
          let nodeCost := costFn node +
            node.children.foldl (fun sum childId =>
              let canonId := UnionFind.root acc2.unionFind childId
              sum + (acc2.classes.get? canonId |>.map (fun ec => ec.bestCost) |>.getD infinityCost)) 0
          match acc2.classes.get? p.1 with
          | some ec =>
            { acc2 with classes := acc2.classes.insert p.1 (ec.updateBest node nodeCost) }
          | none => acc2) acc).unionFind = g.unionFind by
      exact hOuter g.classes.toList g rfl
    intro pairs
    induction pairs with
    | nil => intro acc huf; exact huf
    | cons hd rest ih_pairs =>
      intro acc huf; simp only [List.foldl_cons]
      apply ih_pairs
      -- Inner fold (over nodes array) preserves unionFind
      suffices hInner : ∀ (nodes : List (ENode Op)) (a : EGraph Op),
          a.unionFind = g.unionFind →
          (nodes.foldl (fun acc2 node =>
            let nodeCost := costFn node +
              node.children.foldl (fun sum childId =>
                let canonId := UnionFind.root acc2.unionFind childId
                sum + (acc2.classes.get? canonId |>.map (fun ec => ec.bestCost) |>.getD infinityCost)) 0
            match acc2.classes.get? hd.1 with
            | some ec =>
              { acc2 with classes := acc2.classes.insert hd.1 (ec.updateBest node nodeCost) }
            | none => acc2) a).unionFind = g.unionFind by
        rw [← Array.foldl_toList]; exact hInner hd.2.nodes.toList acc huf
      intro nodes
      induction nodes with
      | nil => intro a ha; exact ha
      | cons nd tl ih_nodes =>
        intro a ha; simp only [List.foldl_cons]
        apply ih_nodes; split <;> exact ha

/-- computeCostsF preserves SelfLB through all fuel iterations. -/
private theorem computeCostsF_preserves_selfLB (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat) (hslb : SelfLB g.unionFind g.classes costFn) :
    SelfLB (EGraph.computeCostsF g costFn fuel).unionFind
           (EGraph.computeCostsF g costFn fuel).classes costFn := by
  induction fuel generalizing g with
  | zero => exact hslb
  | succ n ih =>
    rw [computeCostsF_succ_eq]
    exact ih (singlePass g costFn) (singlePass_preserves_selfLB g costFn hslb)

theorem computeCostsF_bestCost_lower_bound (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat)
    (h_fresh : ∀ cid cls, g.classes.get? cid = some cls → cls.bestNode = none) :
    BestCostLowerBound (EGraph.computeCostsF g costFn fuel) costFn := by
  apply computeCostsF_preserves_selfLB
  intro cid cls nd hcls hbn
  exact absurd hbn (by simp [h_fresh cid cls hcls])

/-- **computeCostsF with positive cost function produces an acyclic bestNode DAG.** -/
theorem computeCostsF_acyclic (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat)
    (h_fresh : ∀ cid cls, g.classes.get? cid = some cls → cls.bestNode = none)
    (hcost_pos : ∀ (nd : ENode Op), 0 < costFn nd) :
    AcyclicBestNodeDAG (EGraph.computeCostsF g costFn fuel) :=
  bestCostLowerBound_acyclic _ costFn
    (computeCostsF_bestCost_lower_bound g costFn fuel h_fresh) hcost_pos

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Fuel sufficiency for extractF
-- ══════════════════════════════════════════════════════════════════

variable {Expr : Type} [Extractable Op Expr]

/-- mapOption succeeds when f succeeds on all elements. -/
private theorem mapOption_some_of_forall {α β : Type} {f : α → Option β} {l : List α}
    (h : ∀ a, a ∈ l → ∃ b, f a = some b) :
    ∃ bs, mapOption f l = some bs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons hd tl ih =>
    obtain ⟨b, hb⟩ := h hd (List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))
    obtain ⟨bs, hbs⟩ := ih'
    exact ⟨b :: bs, by simp [mapOption, hb, hbs]⟩

/-- **Fuel sufficiency**: if the bestNode DAG is acyclic (via rank function),
    every class has bestNode set, and reconstruct always succeeds,
    then extractF returns `some` when fuel > rank(id). -/
theorem extractF_of_rank (g : EGraph Op)
    (rank : EClassId → Nat)
    (hrank : ∀ parentId childId, BestNodeChild g parentId childId →
      rank childId < rank parentId)
    (hset : ∀ cid cls, g.classes.get? (UnionFind.root g.unionFind cid) = some cls →
      ∃ nd, cls.bestNode = some nd)
    (hclass : ∀ cid, ∃ cls, g.classes.get? (UnionFind.root g.unionFind cid) = some cls)
    (hrecon : ∀ (nd : ENode Op) (childExprs : List Expr),
      (Extractable.reconstruct nd.op childExprs).isSome = true)
    : ∀ (id : EClassId) (fuel : Nat), fuel > rank id →
      (extractF (Expr := Expr) g id fuel).isSome = true := by
  suffices h : ∀ n, ∀ id, rank id = n → ∀ fuel, fuel > n →
      (extractF (Expr := Expr) g id fuel).isSome = true by
    intro id fuel hfuel; exact h (rank id) id rfl fuel hfuel
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro id hrn fuel hfuel
    match fuel, hfuel with
    | fuel + 1, hfuel =>
      obtain ⟨cls, hcls⟩ := hclass id
      obtain ⟨nd, hnd⟩ := hset id cls hcls
      have hmop : ∃ bs, mapOption (fun c => extractF (Expr := Expr) g c fuel)
          (NodeOps.children nd.op) = some bs := by
        apply mapOption_some_of_forall
        intro c hc
        have hbnc : BestNodeChild g id c := ⟨cls, nd, hcls, hnd, hc⟩
        have hrc : rank c < n := by rw [← hrn]; exact hrank id c hbnc
        have hfc : fuel > rank c := by omega
        have := ih (rank c) hrc c rfl fuel hfc
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
        exact ⟨v, hv⟩
      obtain ⟨bs, hbs⟩ := hmop
      simp only [extractF, hcls, hnd, hbs]
      exact hrecon nd bs

/-- **extractAuto completeness**: if the bestNode DAG is acyclic with rank bounded
    by `numClasses`, all classes have bestNode set, and reconstruct always succeeds,
    then `extractAuto` returns `some`. -/
theorem extractAuto_complete (g : EGraph Op)
    (rank : EClassId → Nat)
    (hrank : ∀ parentId childId, BestNodeChild g parentId childId →
      rank childId < rank parentId)
    (hbound : ∀ id, rank id < g.numClasses)
    (hset : ∀ cid cls, g.classes.get? (UnionFind.root g.unionFind cid) = some cls →
      ∃ nd, cls.bestNode = some nd)
    (hclass : ∀ cid, ∃ cls, g.classes.get? (UnionFind.root g.unionFind cid) = some cls)
    (hrecon : ∀ (nd : ENode Op) (childExprs : List Expr),
      (Extractable.reconstruct nd.op childExprs).isSome = true)
    (rootId : EClassId) :
    (extractAuto (Expr := Expr) g rootId).isSome = true := by
  unfold extractAuto
  exact extractF_of_rank g rank hrank hset hclass hrecon rootId
    (g.numClasses + 1) (by have := hbound rootId; omega)

end AmoLean.EGraph.VerifiedExtraction.CompletenessSpec
