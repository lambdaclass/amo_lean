/-
  AMO-Lean Ultra — Phase 24 Integration
  Top-level consumer connecting joint optimization to the full pipeline.

  Consumes ALL Phase 24 exports:
  - MatNodeOps: TransformId, MatOp, FactorizationTree, BreakdownRule,
    cooleyTukeyRule, baseCase2Rule, radix4Rule, standardRules, exploreFact
  - CrossEGraphProtocol: queryArithmeticCost, ArithmeticCostQuery/Response,
    jointOptimize, jointOptimizeToNTTPlan, factorizationTotalCost

  Also consumes Phase 22+23 via transitive imports.
-/
import AmoLean.EGraph.Verified.Matrix.CrossEGraphProtocol
import AmoLean.EGraph.Verified.Bitwise.Phase23Integration

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Matrix.Phase24

open AmoLean.EGraph.Verified.Matrix (TransformId MatOp FactorizationTree BreakdownRule
  cooleyTukeyRule baseCase2Rule radix4Rule standardRules exploreFact)
open AmoLean.EGraph.Verified.Matrix.CrossEGraph (queryArithmeticCost ArithmeticCostQuery
  ArithmeticCostResponse jointOptimize jointOptimizeToNTTPlan factorizationTotalCost)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan mkBoundAwarePlan)
open AmoLean.EGraph.Verified.Bitwise.PlanCodeGen (generateNTTFromPlan emitCFromPlan)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise (HardwareCost arm_cortex_a76)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Full Joint Pipeline
-- ══════════════════════════════════════════════════════════════════

/-- THE top-level function: jointly optimize and generate code.
    1. Explore factorizations at algorithmic level
    2. Query arithmetic level for per-butterfly costs (cross-e-graph)
    3. Select best factorization
    4. Convert to NTTPlan
    5. Generate C code from plan -/
def jointPipelineToC (n p : Nat) (mulCost addCost : Nat)
    (hw : HardwareCost := arm_cortex_a76) (funcName : String := "ntt_joint") : String :=
  let plan := jointOptimizeToNTTPlan n p hw
  emitCFromPlan plan funcName

/-- Report: joint optimization analysis. -/
def jointReport (n p : Nat) (hw : HardwareCost := arm_cortex_a76) : String :=
  let (tree, totalCost, bfResp) := jointOptimize n p hw
  let plan := jointOptimizeToNTTPlan n p hw
  s!"=== Joint Optimization Report ===\n" ++
  s!"N={n}, p={p}, SIMD={hw.isSimd}\n" ++
  s!"Factorization: {tree.size} nodes, {tree.mulCount} muls\n" ++
  s!"Total cost: {totalCost} cycles\n" ++
  s!"Butterfly cost: {bfResp.cycleCost} cycles/bf\n" ++
  s!"Reduction: {repr bfResp.chosenReduction}\n" ++
  s!"Plan: {plan.numStages} stages, {plan.lazyStages} lazy\n" ++
  s!"Plan well-formed: {plan.wellFormed}\n" ++
  s!"Generated code: {(emitCFromPlan plan "ntt_joint").length} chars"

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Joint pipeline produces non-empty C code. -/
theorem joint_produces_code :
    (jointPipelineToC 1024 2013265921 3 1).length > 0 := by native_decide

/-- Joint plan is well-formed. -/
theorem joint_plan_wellformed :
    (jointOptimizeToNTTPlan 1024 2013265921).wellFormed = true := by native_decide

/-- Exploration finds factorizations for N=8. -/
theorem explore_finds_8 : (exploreFact 8 0).2.2 > 0 := by native_decide

/-- CT(2,4) produces 11-node tree. -/
theorem ct_2_4_size : ((cooleyTukeyRule 2 4).decompose 8 0).nodes.size = 11 := rfl

/-- Base case produces 1-node tree. -/
theorem base2_size : (baseCase2Rule.decompose 2 0).nodes.size = 1 := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- Full joint pipeline for BabyBear. -/
example : (jointPipelineToC 1024 2013265921 3 1).length > 0 := by native_decide

/-- Joint report is non-empty. -/
example : (jointReport 1024 2013265921).length > 0 := by native_decide

/-- TransformId comparison. -/
example : TransformId.dft 8 == TransformId.dft 8 := by native_decide

/-- Cross-query returns positive cost. -/
example : (queryArithmeticCost { radix := .r2, field := 2013265921 }).cycleCost > 0 := by
  native_decide

/-- Factorization cost is positive. -/
example : factorizationTotalCost (baseCase2Rule.decompose 2 0) 2 2013265921 > 0 := by
  native_decide

/-- standardRules generates rules for N=8. -/
example : (standardRules 8).length > 0 := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Matrix.Phase24
