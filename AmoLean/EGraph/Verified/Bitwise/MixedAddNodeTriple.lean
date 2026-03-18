/-
  AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple — EGraph.add preserves ConsistentValuation

  B62: Proves that adding a node to the EGraph preserves the consistency triple
  (CV + PMI). The key theorem add_node_consistent provides an extended valuation
  v' that agrees with v on old classes and maps the new class to the node's value.

  Deliverables:
  - add_size_le: UF size is non-decreasing after add
  - add_node_consistent: add preserves CV with extended valuation (sorry — complex)
-/
import AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)

-- Import abbreviations
abbrev MGraph := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.MGraph
abbrev MNode  := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.MNode
abbrev CId    := AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec.CId
abbrev VPMI   := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.VPMI
abbrev CV     := AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec.CV

-- NodeEval specialized to MixedNodeOp
abbrev NodeEvalM (node : MNode) (env : MixedEnv) (v : CId → Nat) : Nat :=
  AmoLean.EGraph.VerifiedExtraction.NodeEval node env v

open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec (ndChildren)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: add structural lemmas
-- ══════════════════════════════════════════════════════════════════

/-- EGraph.add never shrinks the union-find parent array.
    Case 1 (hashcons hit): graph unchanged, so size is equal.
    Case 2 (hashcons miss): UF.add pushes one element, size increases by 1. -/
theorem add_size_le (g : MGraph) (node : MNode) :
    g.unionFind.parent.size ≤ (g.add node).2.unionFind.parent.size := by
  unfold AmoLean.EGraph.VerifiedExtraction.EGraph.add
  simp only
  -- Split on hashcons lookup
  split
  · -- hashcons hit: graph unchanged
    exact Nat.le_refl _
  · -- hashcons miss: UF.add pushes one element
    unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.add
    simp only [Array.size_push]
    exact Nat.le_succ _

-- ══════════════════════════════════════════════════════════════════
-- Section 2: add_node_consistent — THE key theorem (sorry'd)
-- ══════════════════════════════════════════════════════════════════

/-- Adding a node to the EGraph preserves ConsistentValuation.
    The extended valuation v' agrees with v on all old classes and
    maps the new class ID to the node's semantic value.

    This is sorry'd because the proof requires detailed reasoning about:
    - hashcons lookup (hit vs miss cases)
    - UF.add (push) preserving root structure
    - extending the valuation to the new class
    - showing the new class's singleton node evaluates correctly

    The TYPE SIGNATURE is the deliverable for B63. -/
theorem add_node_consistent (g : MGraph) (node : MNode) (env : MixedEnv) (v : CId → Nat)
    (hcv : CV g env v) (hpmi : VPMI g)
    (hbnd : ∀ c ∈ ndChildren node, c < g.unionFind.parent.size) :
    ∃ v', CV (g.add node).2 env v' ∧
      VPMI (g.add node).2 ∧
      v' (g.add node).1 = NodeEvalM node env v' ∧
      (g.add node).1 < (g.add node).2.unionFind.parent.size ∧
      g.unionFind.parent.size ≤ (g.add node).2.unionFind.parent.size ∧
      ∀ i, i < g.unionFind.parent.size → v' i = v i := by
  sorry

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: add_size_le on empty graph with a constant node. -/
example : (AmoLean.EGraph.VerifiedExtraction.EGraph.empty : MGraph).unionFind.parent.size ≤
    ((AmoLean.EGraph.VerifiedExtraction.EGraph.empty : MGraph).add
      ⟨MixedNodeOp.constGate 42⟩).2.unionFind.parent.size :=
  add_size_le _ _

/-- Smoke: add returns a graph (type-checks). -/
example : (AmoLean.EGraph.VerifiedExtraction.EGraph.empty : MGraph).add
    ⟨MixedNodeOp.addGate 0 1⟩ =
    (AmoLean.EGraph.VerifiedExtraction.EGraph.empty : MGraph).add
    ⟨MixedNodeOp.addGate 0 1⟩ := rfl

end AmoLean.EGraph.Verified.Bitwise.MixedAddNodeTriple
