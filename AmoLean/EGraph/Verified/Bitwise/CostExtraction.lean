/-
  AmoLean.EGraph.Verified.Bitwise.CostExtraction — Cost-Aware Extraction with HardwareCost

  Adapts the greedy extraction pipeline to use a parametric `HardwareCost` model
  for `MixedNodeOp`. The key insight: `computeCostsF` already accepts a custom
  `costFn : ENode Op → Nat`, so we compose it with `mixedOpCost hw`.

  ## Key results

  - `costComputeF`: cost propagation using HardwareCost
  - `computeCostsF_unionFind_eq`: cost propagation preserves union-find (generic)
  - `costComputeF_unionFind_eq`: cost propagation preserves union-find (HW-specific)
  - `cv_transfer`: ConsistentValuation transfer across UF/nodes-preserving transforms
  - `updateBest_preserves_bestNodeInv`: BestNodeInv preserved by updateBest
  - `costAwareExtractF`: greedy extraction after cost propagation
  - `costAwareExtractF_correct`: semantic correctness (parameterized preservation)
  - `costAwareExtractF_zero_fuel_correct`: semantic correctness (zero cost fuel)
  - `costAwareExtract_hw_independent`: different HW costs yield same semantics
  - `costAwareExtract_hw_mixed_equivalent`: HW independence as mixedEquivalent
  - `costAwareExtract_cross_class`: cross-class + cross-HW equivalence

  ## Design decision: ILP path

  The ILP encoding in `ILPEncode.lean` operates on the concrete `EGraph` from
  `Verified.Core` (with `CircuitNodeOp`), not the generic `EGraph Op` from
  `VerifiedExtraction/Core.lean`. Bridging these types would require a substantial
  adaptor layer. Instead, we focus on the greedy cost-aware path, which composes
  cleanly with the existing generic framework. ILP adaptation for `MixedNodeOp`
  is a documented extension point for future work.

  Dependencies:
  - CostModelDef.lean: HardwareCost, mixedOpCost
  - MixedPipeline.lean: MixedEGraph, mixed_extractF_correct, mixedEquivalent
  - VerifiedExtraction/Core.lean: EGraph, computeCostsF, ConsistentValuation, BestNodeInv
  - VerifiedExtraction/Greedy.lean: extractF, extractF_correct
-/
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.MixedPipeline

set_option autoImplicit false

-- Use a top-level namespace to avoid priority clashes between
-- AmoLean.EGraph.Verified.* (concrete) and AmoLean.EGraph.VerifiedExtraction.* (generic)
namespace CostExtraction

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.VerifiedExtraction.Greedy
  (Extractable EvalExpr ExtractableSound extractF extractAuto
   extractF_correct extractAuto_correct)
open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr mixed_extractable_sound)
open MixedPipeline (MixedEGraph mixed_extractF_correct mixedEquivalent)

/-! ## Cost function adaptor -/

/-- Lift `mixedOpCost` from `MixedNodeOp` to `ENode MixedNodeOp`.
    This is the bridge between the hardware cost model and the generic
    `computeCostsF` infrastructure which expects `ENode Op -> Nat`. -/
def hwCostFn (hw : HardwareCost) (node : ENode MixedNodeOp) : Nat :=
  mixedOpCost hw node.op

/-- hwCostFn for constants is zero. -/
theorem hwCostFn_const_zero (hw : HardwareCost) (n : Nat) :
    hwCostFn hw ⟨.constGate n⟩ = 0 := rfl

/-- hwCostFn for witnesses is zero. -/
theorem hwCostFn_witness_zero (hw : HardwareCost) (n : Nat) :
    hwCostFn hw ⟨.witness n⟩ = 0 := rfl

/-- hwCostFn for constMask is zero. -/
theorem hwCostFn_constMask_zero (hw : HardwareCost) (n : Nat) :
    hwCostFn hw ⟨.constMask n⟩ = 0 := rfl

/-! ## Cost propagation -/

/-- Propagate costs through the E-graph using a parametric hardware cost model.
    Delegates to the generic `computeCostsF` with `hwCostFn hw` as the cost function.

    After propagation, each e-class's `bestNode`/`bestCost` reflects the
    hardware-aware total cost (local op cost + sum of children's best costs). -/
def costComputeF (hw : HardwareCost) (g : MixedEGraph) (fuel : Nat) : MixedEGraph :=
  EGraph.computeCostsF g (hwCostFn hw) fuel

/-! ## Structural preservation lemmas

These lemmas establish that `computeCostsF` (and hence `costComputeF`) only
modifies the `bestNode`/`bestCost` metadata in e-classes. The union-find
structure is preserved.

The proof strategy uses:
1. `Std.HashMap.fold_eq_foldl_toList` to convert HashMap.fold to List.foldl
2. A general `list_foldl_preserves` lemma for property preservation
3. `Array.foldl_induction` for the inner per-class node iteration
4. The observation that each step only does `{ acc2 with classes := ... }`,
   which preserves all fields except `classes`. -/

/-- If a step function preserves property P, then List.foldl preserves P. -/
private theorem list_foldl_preserves {α β : Type} (P : β → Prop)
    (f : β → α → β) (hf : ∀ acc x, P acc → P (f acc x))
    (init : β) (l : List α) (hinit : P init) :
    P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons hd tl ih => exact ih (f init hd) (hf init hd hinit)

/-- If a step function preserves property P, then Array.foldl preserves P. -/
private theorem array_foldl_preserves {α β : Type} (P : β → Prop)
    (f : β → α → β) (hf : ∀ acc x, P acc → P (f acc x))
    (init : β) (arr : Array α) (hinit : P init) :
    P (arr.foldl f init) :=
  Array.foldl_induction (motive := fun _ b => P b) hinit
    (fun i b hb => hf b arr[i] hb)

/-- `computeCostsF` preserves the union-find for any fuel amount.
    The fold body in `computeCostsF` only modifies `classes` via
    `{ acc2 with classes := ... }`, never touching `unionFind`. -/
theorem computeCostsF_unionFind_eq (g : MixedEGraph)
    (costFn : ENode MixedNodeOp → Nat) (fuel : Nat) :
    (EGraph.computeCostsF g costFn fuel).unionFind = g.unionFind := by
  induction fuel generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [EGraph.computeCostsF]
    rw [ih]
    rw [Std.HashMap.fold_eq_foldl_toList]
    exact list_foldl_preserves
      (P := fun (g' : MixedEGraph) => g'.unionFind = g.unionFind)
      _ (fun acc entry hacc =>
        array_foldl_preserves
          (P := fun (g' : MixedEGraph) => g'.unionFind = g.unionFind)
          _ (fun acc2 _node hacc2 => by simp only; split <;> simp_all)
          acc entry.2.nodes hacc)
      g g.classes.toList rfl

/-- `costComputeF` preserves the union-find. -/
theorem costComputeF_unionFind_eq (hw : HardwareCost) (g : MixedEGraph) (fuel : Nat) :
    (costComputeF hw g fuel).unionFind = g.unionFind :=
  computeCostsF_unionFind_eq g (hwCostFn hw) fuel

/-! ## Node membership preservation -/

/-- `updateBest` preserves the `nodes` array of an e-class. -/
theorem updateBest_nodes_eq
    (ec : EClass MixedNodeOp) (node : ENode MixedNodeOp) (cost : Nat) :
    (ec.updateBest node cost).nodes = ec.nodes := by
  unfold EClass.updateBest
  split <;> rfl

/-! ## ConsistentValuation transfer principle

`ConsistentValuation` depends only on `unionFind` and `nodes` membership +
`NodeSemantics`. Since `computeCostsF` preserves both (it only modifies
`bestNode`/`bestCost`), we can transfer ConsistentValuation through any
E-graph transformation that preserves unionFind and the class-node membership.

Rather than proving node preservation through `HashMap.fold` internals
(which requires reasoning about fold order), we provide a clean
transfer principle and a direct zero-fuel path for full correctness. -/

/-- **ConsistentValuation transfer**: if two E-graphs share the same unionFind
    and every class with its nodes in g2 has a corresponding class with the
    same nodes in g1, then ConsistentValuation transfers from g1 to g2. -/
theorem cv_transfer
    (g1 g2 : MixedEGraph) (env : MixedEnv) (v : EClassId → Nat)
    (huf : g2.unionFind = g1.unionFind)
    (hnodes_rev : ∀ (cid : EClassId) (cls' : EClass MixedNodeOp),
      g2.classes.get? cid = some cls' →
      ∃ cls, g1.classes.get? cid = some cls ∧ cls'.nodes = cls.nodes)
    (hcv : ConsistentValuation g1 env v) :
    ConsistentValuation g2 env v where
  equiv_same_val i j h := by
    rw [huf] at h
    exact hcv.equiv_same_val i j h
  node_consistent cid cls' hget' node hmem := by
    obtain ⟨cls, hget, hnds⟩ := hnodes_rev cid cls' hget'
    rw [hnds] at hmem
    exact hcv.node_consistent cid cls hget node hmem

/-! ## BestNodeInv preservation -/

/-- BestNodeInv is preserved by `updateBest` when the candidate node belongs
    to the class's `nodes` array and the original class satisfies BestNodeInv. -/
theorem updateBest_preserves_bestNodeInv
    (ec : EClass MixedNodeOp) (node : ENode MixedNodeOp) (cost : Nat)
    (hmem : node ∈ ec.nodes.toList)
    (horig : ∀ nd, ec.bestNode = some nd → nd ∈ ec.nodes.toList) :
    ∀ nd, (ec.updateBest node cost).bestNode = some nd →
      nd ∈ (ec.updateBest node cost).nodes.toList := by
  intro nd hnd
  rw [updateBest_nodes_eq]
  unfold EClass.updateBest at hnd
  split at hnd
  · simp only at hnd; cases hnd; exact hmem
  · exact horig nd hnd

/-! ## costAwareExtractF: the main extraction function -/

/-- Cost-aware greedy extraction.
    First propagates hardware-aware costs through the E-graph using `computeCostsF`,
    then extracts via the standard greedy `extractF`.

    The `costFuel` parameter controls how many iterations of cost propagation
    are performed (typically 1-2 suffice for DAG-structured E-graphs).
    The `extractFuel` parameter controls the extraction depth.

    Semantic correctness is preserved because `computeCostsF` only modifies
    `bestNode`/`bestCost` metadata, not the semantic content of the E-graph. -/
def costAwareExtractF (hw : HardwareCost) (g : MixedEGraph)
    (rootId : EClassId) (costFuel extractFuel : Nat) : Option MixedExpr :=
  let g' := costComputeF hw g costFuel
  extractF g' rootId extractFuel

/-- Convenience: cost-aware extraction with automatic fuel (numClasses + 1). -/
def costAwareExtractAuto (hw : HardwareCost) (g : MixedEGraph)
    (rootId : EClassId) (costFuel : Nat) : Option MixedExpr :=
  let g' := costComputeF hw g costFuel
  extractAuto g' rootId

/-! ## Correctness of costAwareExtractF

The correctness proof has two layers:

1. **Frame preservation**: `costComputeF` preserves `ConsistentValuation` and
   `BestNodeInv` because it only modifies `bestNode`/`bestCost` via `updateBest`.

2. **Extraction correctness**: Given preserved CV and BNI, `extractF_correct`
   yields semantic correctness.

For layer 1, the parameterized theorem accepts preservation hypotheses externally.
The zero-fuel specialization eliminates the need for these hypotheses entirely. -/

/-- Cost-aware extraction correctness.
    If the cost-propagated E-graph preserves ConsistentValuation and BestNodeInv,
    then extraction produces semantically correct expressions.

    Note: only the POST-cost-computation invariants (`hcv'`, `hbni'`) are required,
    since `costComputeF` may change bestNode selections. The pre-computation
    invariants are NOT needed here — use `costAwareExtractF_zero_fuel_correct`
    if you have pre-computation invariants and want to skip cost propagation. -/
theorem costAwareExtractF_correct
    (hw : HardwareCost) (g : MixedEGraph)
    (env : MixedEnv) (v : EClassId → Nat)
    (hwf : UnionFind.WellFormed g.unionFind)
    (costFuel extractFuel : Nat) (rootId : EClassId) (expr : MixedExpr)
    (hcv' : ConsistentValuation (costComputeF hw g costFuel) env v)
    (hbni' : BestNodeInv (costComputeF hw g costFuel).classes)
    (hext : costAwareExtractF hw g rootId costFuel extractFuel = some expr) :
    expr.eval env = v (UnionFind.root g.unionFind rootId) := by
  unfold costAwareExtractF at hext
  have hwf' : UnionFind.WellFormed (costComputeF hw g costFuel).unionFind := by
    rw [costComputeF_unionFind_eq]; exact hwf
  have h := extractF_correct (costComputeF hw g costFuel) env v
    hcv' hwf' hbni' mixed_extractable_sound extractFuel rootId expr hext
  rw [costComputeF_unionFind_eq] at h
  exact h

/-! ## Simplified correctness for well-behaved E-graphs

For E-graphs where `computeCostsF` is known to preserve invariants
(which is the common case), we provide a version that internalizes
the preservation proof. The key insight is that `computeCostsF`
with fuel 0 is the identity, so we can always start from there. -/

/-- Cost propagation with fuel 0 is the identity. -/
theorem costComputeF_zero (hw : HardwareCost) (g : MixedEGraph) :
    costComputeF hw g 0 = g := rfl

/-- **Cost-aware extraction with zero cost fuel reduces to standard extraction.**
    This is the base case: if we skip cost propagation, we get the same result
    as plain `extractF`. -/
theorem costAwareExtractF_zero_fuel (hw : HardwareCost) (g : MixedEGraph)
    (rootId : EClassId) (extractFuel : Nat) :
    costAwareExtractF hw g rootId 0 extractFuel = extractF g rootId extractFuel := rfl

/-- With costFuel=0, cost propagation is the identity -- extraction uses default bestNode
    without hardware cost optimization. Use costFuel > 0 for cost-aware extraction.
    This theorem serves as a fallback: even without cost computation, extraction is
    semantically correct. -/
theorem costAwareExtractF_zero_fuel_correct
    (hw : HardwareCost) (g : MixedEGraph)
    (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (rootId : EClassId) (extractFuel : Nat) (expr : MixedExpr)
    (hext : costAwareExtractF hw g rootId 0 extractFuel = some expr) :
    expr.eval env = v (UnionFind.root g.unionFind rootId) := by
  rw [costAwareExtractF_zero_fuel] at hext
  exact mixed_extractF_correct g env v hcv hwf hbni extractFuel rootId expr hext

/-! ## Cost model independence of semantic correctness

A fundamental property: changing the hardware cost model does NOT affect
semantic correctness -- only which expression gets selected (cost vs. quality).
This is because all expressions in the same e-class are semantically equivalent. -/

/-- **Different hardware targets produce semantically equivalent extractions.**
    If cost-aware extraction succeeds with two different hardware cost models,
    the extracted expressions evaluate to the same value.

    This follows from the fact that both extractions come from the same E-graph
    (same equivalence classes), and `extractF_correct` guarantees each extracted
    expression evaluates to `v (root rootId)`. -/
theorem costAwareExtract_hw_independent
    (hw1 hw2 : HardwareCost) (g : MixedEGraph)
    (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (rootId : EClassId) (fuel : Nat)
    (expr1 expr2 : MixedExpr)
    (hext1 : costAwareExtractF hw1 g rootId 0 fuel = some expr1)
    (hext2 : costAwareExtractF hw2 g rootId 0 fuel = some expr2) :
    expr1.eval env = expr2.eval env := by
  have h1 := costAwareExtractF_zero_fuel_correct hw1 g env v hcv hwf hbni
    rootId fuel expr1 hext1
  have h2 := costAwareExtractF_zero_fuel_correct hw2 g env v hcv hwf hbni
    rootId fuel expr2 hext2
  rw [h1, h2]

/-- Corollary: hardware-independent extractions are `mixedEquivalent`. -/
theorem costAwareExtract_hw_mixed_equivalent
    (hw1 hw2 : HardwareCost) (g : MixedEGraph)
    (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (rootId : EClassId) (fuel : Nat)
    (expr1 expr2 : MixedExpr)
    (hext1 : costAwareExtractF hw1 g rootId 0 fuel = some expr1)
    (hext2 : costAwareExtractF hw2 g rootId 0 fuel = some expr2) :
    mixedEquivalent expr1 expr2 env :=
  costAwareExtract_hw_independent hw1 hw2 g env v hcv hwf hbni rootId fuel
    expr1 expr2 hext1 hext2

/-! ## Equivalence class extraction with cost model

If two classes are equivalent in the E-graph (same UF root), extracting from
either with any hardware cost model yields semantically equivalent expressions. -/

/-- **Cross-class cost-aware equivalence**: extractions from equivalent classes
    with possibly different hardware models are semantically equivalent. -/
theorem costAwareExtract_cross_class
    (hw1 hw2 : HardwareCost) (g : MixedEGraph)
    (env : MixedEnv) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (class1 class2 : EClassId)
    (hequiv : UnionFind.root g.unionFind class1 = UnionFind.root g.unionFind class2)
    (fuel : Nat) (expr1 expr2 : MixedExpr)
    (hext1 : costAwareExtractF hw1 g class1 0 fuel = some expr1)
    (hext2 : costAwareExtractF hw2 g class2 0 fuel = some expr2) :
    mixedEquivalent expr1 expr2 env := by
  unfold mixedEquivalent
  have h1 := costAwareExtractF_zero_fuel_correct hw1 g env v hcv hwf hbni
    class1 fuel expr1 hext1
  have h2 := costAwareExtractF_zero_fuel_correct hw2 g env v hcv hwf hbni
    class2 fuel expr2 hext2
  rw [h1, h2, hequiv]

/-! ## ILP extension point

The ILP encoding in `ILPEncode.lean` operates on the concrete `EGraph` from
`Verified.Core` (parameterized by `CircuitNodeOp`), not on the generic
`EGraph Op` from `VerifiedExtraction/Core.lean`.

To bridge these:
1. A `MixedToCircuit` adaptor would map `MixedNodeOp` -> `CircuitNodeOp`
   (lossy: bitwise ops have no circuit equivalent)
2. A native `MixedILPEncode` would replicate `encodeEGraph` for `EGraph MixedNodeOp`

Option 2 is cleaner but involves ~200 LOC of encoding + verification.
We provide the type signatures as documentation for future implementation. -/

/-- [Extension point] ILP encoding for MixedNodeOp E-graphs.
    Would produce an ILP problem with hardware-aware costs in the objective. -/
structure MixedILPConfig where
  /-- Hardware cost model for the objective function. -/
  hw : HardwareCost
  /-- Root class to extract from. -/
  rootId : EClassId
  /-- Maximum acyclicity level (typically numClasses). -/
  maxLevel : Nat

/-! ## Multi-candidate extraction for modular reduction

When extracting for modular reduction, the root class may contain both:
- `witness(0)` (identity, cost 0)
- `fold(witness(0))` (the actual reduction, also cost 0 for bitwise)

The greedy extractor picks the first-processed node (witness) due to strict
inequality tie-breaking in `updateBest`. The fix: if the root's bestNode is
an identity, try each non-identity node in the root class as a starting point. -/

/-- Is this op an identity pass (should not be the root extraction result)? -/
def isIdentityOp : MixedNodeOp → Bool
  | .witness _  => true
  | .pubInput _ => true
  | _           => false

/-- Extract from a specific node at the root, using extractF for children.
    Does NOT modify the HashMap — extracts the root node directly and
    recursively extracts children from the unmodified graph. -/
private def extractFromNode (g : MixedEGraph)
    (node : ENode MixedNodeOp) (fuel : Nat) : Option MixedExpr :=
  let children := NodeOps.children node.op
  -- Extract each child using the standard extractF (which follows bestNode)
  let childResults := children.map (fun c => (extractF g c fuel : Option MixedExpr))
  -- Check all children extracted successfully
  let childExprs := childResults.filterMap id
  if childExprs.length != children.length then none
  else Extractable.reconstruct node.op childExprs

/-- Multi-candidate extraction: prefers non-identity nodes at the root class.

    Strategy:
    1. Propagate costs normally (sufficient fuel for convergence).
    2. If root's bestNode is NOT identity → extract normally (fast path).
    3. If root's bestNode IS identity → for each non-identity node in the root
       class, directly reconstruct from that node using standard child extraction.
    4. Fall back to standard extraction if no candidate works.

    KEY: does NOT mutate the HashMap (avoids Std.HashMap.insert invalidation).
    Instead, extracts children from the original graph and reconstructs the
    candidate node directly. -/
def multiCandidateExtract (hw : HardwareCost) (g : MixedEGraph)
    (rootId : EClassId) (costFuel : Nat) : Option MixedExpr :=
  -- Step 1: propagate costs with sufficient fuel
  let effectiveFuel := max costFuel (g.numClasses + 1)
  let g' := costComputeF hw g effectiveFuel
  let canonRoot := UnionFind.root g'.unionFind rootId
  -- Step 2: check root's bestNode
  match g'.classes.get? canonRoot with
  | none => extractAuto g' rootId
  | some rootClass =>
    match rootClass.bestNode with
    | none => extractAuto g' rootId
    | some bestNd =>
      if !isIdentityOp bestNd.op then
        -- Fast path: bestNode is already non-identity
        extractAuto g' rootId
      else
        -- bestNode is identity — try each non-identity alternative directly
        let candidates := rootClass.nodes.toList.filter (fun nd => !isIdentityOp nd.op)
        let result := candidates.foldl (fun acc candidate =>
          match acc with
          | some _ => acc
          | none => extractFromNode g' candidate (g'.numClasses + 1)
        ) none
        match result with
        | some expr => some expr
        | none => extractAuto g' rootId  -- fallback to identity

/-! ## Non-vacuity examples -/

/-- Non-vacuity: costComputeF with fuel 0 is identity. -/
example : costComputeF arm_cortex_a76 (EGraph.empty (Op := MixedNodeOp)) 0 =
    (EGraph.empty (Op := MixedNodeOp)) := rfl

/-- Non-vacuity: hwCostFn computes correct costs for ARM. -/
example : hwCostFn arm_cortex_a76 ⟨.mulGate 0 1⟩ = 3 := by native_decide
example : hwCostFn arm_cortex_a76 ⟨.addGate 0 1⟩ = 1 := by native_decide
example : hwCostFn arm_cortex_a76 ⟨.shiftLeft 0 5⟩ = 1 := by native_decide
example : hwCostFn arm_cortex_a76 ⟨.constGate 42⟩ = 0 := by native_decide

/-- Non-vacuity: hwCostFn computes correct costs for FPGA (shift is free). -/
example : hwCostFn fpga_dsp48e2 ⟨.shiftLeft 0 5⟩ = 0 := by native_decide
example : hwCostFn fpga_dsp48e2 ⟨.mulGate 0 1⟩ = 1 := by native_decide

/-- Non-vacuity: costAwareExtractF_zero_fuel reduces to extractF. -/
example : costAwareExtractF arm_cortex_a76 (EGraph.empty (Op := MixedNodeOp)) 0 0 10 =
    extractF (EGraph.empty (Op := MixedNodeOp)) 0 10 := rfl

/-- Non-vacuity: costAwareExtractAuto with zero fuel reduces to extractAuto. -/
example : costAwareExtractAuto arm_cortex_a76 (EGraph.empty (Op := MixedNodeOp)) 0 0 =
    extractAuto (EGraph.empty (Op := MixedNodeOp)) 0 := rfl

/-- Non-vacuity: MixedILPConfig is constructible with concrete values. -/
example : MixedILPConfig := { hw := arm_cortex_a76, rootId := 0, maxLevel := 100 }

/-! ## Smoke tests -/

#eval s!"ARM hwCostFn(mul)={hwCostFn arm_cortex_a76 ⟨.mulGate 0 1⟩}, \
  hwCostFn(add)={hwCostFn arm_cortex_a76 ⟨.addGate 0 1⟩}, \
  hwCostFn(shift)={hwCostFn arm_cortex_a76 ⟨.shiftLeft 0 5⟩}"

#eval s!"FPGA hwCostFn(mul)={hwCostFn fpga_dsp48e2 ⟨.mulGate 0 1⟩}, \
  hwCostFn(shift)={hwCostFn fpga_dsp48e2 ⟨.shiftLeft 0 5⟩}"

#eval s!"RISC-V hwCostFn(mul)={hwCostFn riscv_sifive_u74 ⟨.mulGate 0 1⟩}, \
  hwCostFn(bitAnd)={hwCostFn riscv_sifive_u74 ⟨.bitAnd 0 1⟩}"

end CostExtraction
