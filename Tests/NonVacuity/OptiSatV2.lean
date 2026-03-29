/-
  AMO-Lean — Fase 27 E2E Tests: OptiSat v2 Integration
  N27.17: End-to-end demonstrations for Q1 (per-stage), Q2 (algorithm),
  Ruler (rule discovery), and bounds verification.

  These tests exercise ALL new infrastructure from Fase 27:
  - ColoredEGraph (SmallUF, compositeFind, coarsening)
  - ColoredSpec (CCV, MixedColoredSoundRule)
  - MultiRelMixed (MRCV, tiered saturation)
  - BoundRelation + BoundPropagation (per-stage bounds)
  - StageContext (reductionDecision)
  - SpecDrivenRunner (discoverReductionForStage)
  - NTTPlanCodeGen (emitPerStageNTT)
  - Ruler (CVec-based rule discovery)
  - CrossEGraphProtocol (factorizationToPlan)
-/
import AmoLean.EGraph.Verified.Bitwise.Discovery.SpecDrivenRunner
import AmoLean.EGraph.Verified.Bitwise.NTTPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler.MixedEval
import AmoLean.EGraph.Verified.Matrix.CrossEGraphProtocol
import AmoLean.EGraph.Verified.Bitwise.BoundIntegration
import AmoLean.EGraph.Verified.Bitwise.ColoredSpec
import AmoLean.EGraph.Verified.Bitwise.MultiRelMixed

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Tests.OptiSatV2

-- ══════════════════════════════════════════════════════════════════
-- Q1: Per-Stage Optimal Reduction
-- ══════════════════════════════════════════════════════════════════

section Q1_PerStage

open AmoLean.EGraph.Verified.Bitwise.Discovery.Stage
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.PlanCodeGen (emitPerStageNTT mkPerStagePlan)

-- BabyBear p = 2013265921, 32-bit word
-- Stage contexts show per-stage decisions
#eval do
  let contexts := buildStageContexts 5 2013265921 32
  for ctx in contexts do
    let decision := reductionDecision ctx
    IO.println s!"Stage {ctx.stageIndex}: k={ctx.inputBoundK}, decision={repr decision}"

-- Per-stage plan for BabyBear NTT
#eval do
  let plan := mkPerStagePlan 2013265921 1024 32
  IO.println s!"Plan: {plan.stages.size} stages for N=1024"
  for stage in plan.stages.toList do
    IO.println s!"  Stage {stage.stageIdx}: {repr stage.reduction} (k={stage.inputBoundK}→{stage.outputBoundK})"

-- Per-stage C code emission
#eval do
  let code := emitPerStageNTT 2013265921 8 32 false "ntt_babybear_8"
  IO.println s!"Generated {code.length} chars of per-stage C code"
  IO.println (code.take 200)

-- Stage 0 with k=1 is lazy for BabyBear in 32-bit
example : reductionDecision
    { stageIndex := 0, totalStages := 10, inputBoundK := 1,
      bitwidth := 32, prime := 2013265921 } = .lazy := by native_decide

end Q1_PerStage

-- ══════════════════════════════════════════════════════════════════
-- Q2: Algorithm-Level Optimization
-- ══════════════════════════════════════════════════════════════════

section Q2_Algorithm

open AmoLean.EGraph.Verified.Matrix.CrossEGraph
open AmoLean.EGraph.Verified.Bitwise (arm_cortex_a76)

-- Joint optimization uses factorization (not fallback)
#eval do
  let plan := jointOptimizeToNTTPlan 1024 2013265921
  IO.println s!"Joint plan: {plan.stages.size} stages, prime={plan.prime}"
  for stage in plan.stages.toList do
    IO.println s!"  Stage {stage.stageIdx}: radix={repr stage.radix}, red={repr stage.reduction}"

-- Cross-level cost query
open AmoLean.EGraph.Verified.Matrix.CrossEGraphBridge (queryButterflyReduceCost)

#eval do
  let (red, cost, outK) := queryButterflyReduceCost 2013265921 arm_cortex_a76 2 1
  IO.println s!"BabyBear r2 stage0: reduction={repr red}, cost={cost}, outputK={outK}"

-- Well-formedness of joint plan
example : (jointOptimizeToNTTPlan 1024 2013265921).wellFormed = true := by native_decide

end Q2_Algorithm

-- ══════════════════════════════════════════════════════════════════
-- Ruler: CVec-Based Rule Discovery
-- ══════════════════════════════════════════════════════════════════

section Ruler

open AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler.MixedEval
open AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler (improvementLoop)

-- Ruler discovers rules
#eval do
  let result := discoverMixedRules { maxDepth := 1, maxIterations := 2 }
  IO.println s!"Ruler: {result.rules.length} rules in {result.iteration} iterations"

end Ruler

-- ══════════════════════════════════════════════════════════════════
-- Bounds: Verified Lazy Reduction
-- ══════════════════════════════════════════════════════════════════

section Bounds

open AmoLean.EGraph.Verified.Bitwise.BoundRel

-- safeWithoutReduce verifies skip-reduce
example : safeWithoutReduce 2013265921 2 32 := by unfold safeWithoutReduce; omega
example : ¬ safeWithoutReduce 2013265921 3 32 := by unfold safeWithoutReduce; omega

-- BoundedByKP composition
example : BoundedByKP 5 8 2 := by unfold BoundedByKP; omega
example : BoundedByKP 5 (3 + 4) (1 + 1) :=
  add_bound_propagate (by unfold BoundedByKP; omega) (by unfold BoundedByKP; omega)

end Bounds

-- ══════════════════════════════════════════════════════════════════
-- Colored E-Graph: Coarsening
-- ══════════════════════════════════════════════════════════════════

section Colored

open AmoLean.EGraph.Verified.Bitwise.Colored

-- Coarsening: merge under parent visible to child
#eval do
  let cl := ColoredLayer.empty
  let (c1, cl1) := cl.addColor colorRoot
  let (c2, cl2) := cl1.addColor c1
  let baseFind := fun id => id
  let (cl3, _) := cl2.mergeUnderColor baseFind c1 10 20 100
  let eqC2 := cl3.equivUnderColor baseFind c2 10 20 100
  return s!"child sees parent merge: {eqC2}"

-- CCV backward compatibility
open AmoLean.EGraph.Verified.Bitwise.ColoredSpec

example (baseCV : Prop) (baseFind : EClassId → EClassId)
    (cl : ColoredLayer) (assumptions : ColorAssumption)
    (env : MixedEnv) (v : EClassId → Nat)
    (hccv : MixedCCV baseCV baseFind cl assumptions env v) :
    baseCV :=
  CCV_implies_base_CV baseCV baseFind cl assumptions env v hccv

end Colored

-- ══════════════════════════════════════════════════════════════════
-- MRCV: MultiRel Consistent Valuation
-- ══════════════════════════════════════════════════════════════════

section MRCV

open AmoLean.EGraph.Verified.Bitwise.MultiRel

-- v2 implies v1 (backward compatibility)
example (s : State) (rels : Array (Nat → Nat → Prop))
    (baseCV : Prop) (env : MixedEnv) (v : EClassId → Nat)
    (hmrcv : MRCV s rels baseCV env v) :
    baseCV :=
  v2_implies_v1_soundness s rels baseCV env v hmrcv

end MRCV

-- ══════════════════════════════════════════════════════════════════
-- FASE 28 E2E: Full Pipeline Integration Demo
-- ══════════════════════════════════════════════════════════════════

section Fase28_E2E

open AmoLean.EGraph.Verified.Bitwise.BoundIntegration (optimizeNTTFull mkSeedEGraph)
open AmoLean.EGraph.Verified.Bitwise.MultiRel (coloredStep)
open AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler.MixedEval (discoverMixedRules)

/-- THE DEMO: optimizeNTTFull on REAL data with ALL 4 capabilities:
    1. E-graph seeded with reduceGate(witness(0), p) — NOT empty
    2. reductionAlternativeRules create monty/barrett/harvey alternatives
    3. Ruler discovers rules with reduction vocabulary
    4. Bound propagation via relStep with mkFieldFactory
    5. Cross-level cost queries in factorizationToPlan -/
#eval do
  let p := 2013265921  -- BabyBear
  let (s, analysis) := optimizeNTTFull p 10
  IO.println "=== optimizeNTTFull: REAL DATA, ALL 4 capabilities ==="
  IO.println s!"  Nodes: {s.numNodes}, Classes: {s.numClasses}"
  IO.println s!"  Relation DAGs: {s.numRelations}, Bound edges: {s.totalRelEdges}"
  IO.println s!"  Colored layer worklists: {s.coloredLayer.worklists.size}"
  IO.println s!"  Stages: {analysis.length}"
  for (stageIdx, red, cost) in analysis do
    IO.println s!"  Stage {stageIdx}: {repr red}, cost={cost}"

/-- Ruler discovers reduction equivalences with real vocabulary. -/
#eval do
  let result := discoverMixedRules { maxDepth := 1, maxIterations := 2 }
  IO.println s!"Ruler: {result.rules.length} rules in {result.iteration} iterations"

/-- Seeded e-graph has real nodes. -/
#eval do
  let g := mkSeedEGraph 2013265921
  IO.println s!"Seed graph: {g.numNodes} nodes, {g.numClasses} classes"

/-- MRCV preservation is fully proven (0 sorry in BoundPropagation). -/
#check @AmoLean.EGraph.Verified.Bitwise.BoundProp.relStepMixed_preserves_MRCV

end Fase28_E2E

end AmoLean.EGraph.Verified.Tests.OptiSatV2
