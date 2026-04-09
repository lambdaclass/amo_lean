/-
  AMO-Lean Ultra — Colored Extraction
  Extract optimal MixedExpr considering colored merges for a specific hardware target.

  The colored e-graph has per-color union-finds (SmallUF) that represent merges
  visible only to specific hardware targets:
  - Color 1 (scalar): reduceGate ≡ solinasFold (cheaper for scalar)
  - Color 2 (SIMD): reduceGate ≡ montyReduce (Montgomery preferred for u32 lanes)
  - Color 5 (largeArray): reduceGate ≡ montyReduce (cache pressure)

  Extraction creates a temporary graph with colored merges applied, then uses
  the existing costAwareExtractF for hardware-cost-aware extraction.

  Consumes: CostExtraction (costAwareExtractF), MultiRelMixed (State, ColoredLayer)
  Consumed by: UltraPipeline (color-aware extraction step)
-/
import AmoLean.EGraph.Verified.Bitwise.CostExtraction
import AmoLean.EGraph.Verified.Bitwise.MultiRelMixed

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.ColoredExtraction

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified.Bitwise.Colored (ColoredLayer ColorId)
open AmoLean.EGraph.Verified.Bitwise.MultiRel (State)
open MixedPipeline (MixedEGraph)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp HardwareCost)
open CostExtraction (costAwareExtractF)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Apply Colored Merges to Base Graph
-- ══════════════════════════════════════════════════════════════════

/-- Apply colored merges to a base graph for a target color.
    For each pair of e-classes that are equivalent under the target color
    (via ColoredLayer.findUnderColor), merge them in the base graph.
    After merging, rebuild to propagate merges to class maps.

    This creates a view of the e-graph as seen by a specific hardware target,
    where color-specific equivalences are materialized. -/
def applyColoredMerges (g : MixedEGraph) (cl : ColoredLayer) (targetColor : ColorId)
    : MixedEGraph :=
  let baseFind : EClassId → EClassId :=
    fun id => AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind id
  let classIds := g.classes.toList.map (·.1)
  let withReps := classIds.map fun id =>
    (cl.findUnderColor baseFind targetColor id, id)
  let g' := withReps.foldl
    (fun (acc : MixedEGraph × Std.HashMap EClassId EClassId)
         (pair : EClassId × EClassId) =>
      let (rep, id) := pair
      let (graph, seen) := acc
      match seen.get? rep with
      | some prevId => (graph.merge prevId id, seen)
      | none => (graph, seen.insert rep id))
    (g, Std.HashMap.ofList []) |>.1
  MixedSaturation.rebuildF g' 10

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Color-Aware Extraction
-- ══════════════════════════════════════════════════════════════════

/-- Extract optimal MixedExpr from saturated colored state for a hardware target.
    1. Applies colored merges for targetColor to the base graph
    2. Runs cost-aware extraction with the given HardwareCost
    3. Returns the optimal expression considering both cost and color preferences -/
def coloredCostAwareExtractF (hw : HardwareCost) (state : State) (rootId : EClassId)
    (targetColor : ColorId) (costFuel extractFuel : Nat := 50) : Option MixedExpr :=
  let coloredGraph := applyColoredMerges state.baseGraph state.coloredLayer targetColor
  costAwareExtractF hw coloredGraph rootId costFuel extractFuel

/-- Convenience: extract for SIMD hardware (color=2, Montgomery preferred). -/
def simdExtract (hw : HardwareCost) (state : State) (rootId : EClassId) : Option MixedExpr :=
  coloredCostAwareExtractF hw state rootId 2

/-- Convenience: extract for scalar hardware (color=1, Solinas preferred). -/
def scalarExtract (hw : HardwareCost) (state : State) (rootId : EClassId) : Option MixedExpr :=
  coloredCostAwareExtractF hw state rootId 1

end AmoLean.EGraph.Verified.Bitwise.ColoredExtraction
