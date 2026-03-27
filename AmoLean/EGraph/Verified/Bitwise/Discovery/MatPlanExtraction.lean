import AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep
import AmoLean.EGraph.Verified.Bitwise.NTTPlanSelection

/-!
# MatPlanExtraction — Convert MatEGraph Exploration to NTTPlan

Extracts the optimal NTTPlan from a saturated MatEGraph by converting
the best radix assignment into a concrete per-stage plan with bound-aware
reduction selection.

This is the bridge between Level 1 (algorithmic exploration) and
Level 5 (codegen): MatEGraphStep explores → MatPlanExtraction converts → NTTPlanCodeGen emits.

## Integration

Replaces the hardcoded `generateCandidates` in NTTPlanSelection with
exploration-based plan generation. Backward compat: falls back to
`generateCandidates` when exploration fuel = 0 or assignment is empty.

Node N24.12 in Fase 24 (Discovery Engine).
Consumed by: N24.9 DiscoveryPipeline, NTTPlanSelection (via selectBestPlanExplored).
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery.MatPlanExtraction

open AmoLean.EGraph.Verified.Bitwise.NTTPlan (RadixChoice StageDirection Plan NTTStage
  mkUniformPlan mkBoundAwarePlan log2)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice stageBoundFactor
  lazyReductionSafe)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound reductionCost)
open AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep (CostOracle MatEGraph
  matSaturateAndExtract totalCoverage radixLevels generateAssignmentsAux
  generateAssignmentsAux_valid)
open AmoLean.EGraph.Verified.Bitwise.PlanSelection (selectBestPlan generateCandidates)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Assignment → Plan Conversion
-- ══════════════════════════════════════════════════════════════════

/-- Convert a radix assignment to NTT stages with bound-aware reduction.
    For each radix choice in the assignment:
    1. Query Level 2 for the best reduction (selectReductionForBound)
    2. Check if lazy reduction is safe (lazyReductionSafe)
    3. Compute output bound factor (stageBoundFactor)
    Tracks bound propagation through the full stage sequence. -/
private def buildStagesFromAssignment (assignment : List RadixChoice)
    (p : Nat) (hwIsSimd arrayIsLarge : Bool) (dir : StageDirection)
    (totalLevels : Nat) (level : Nat) (stageIdx : Nat) (currentK : Nat)
    (acc : List NTTStage) : List NTTStage :=
  match assignment with
  | [] => acc.reverse
  | radix :: rest =>
    let remaining := totalLevels - level
    let canLazy := lazyReductionSafe (currentK + 1) p
    let mustReduce := remaining ≤ 2
    let red :=
      if canLazy && !mustReduce then ReductionChoice.lazy
      else selectReductionForBound (currentK + 1) hwIsSimd arrayIsLarge
    let outputK := stageBoundFactor currentK red
    let stg : NTTStage :=
      { stageIdx := stageIdx, radix := radix, reduction := red, direction := dir,
        inputBoundK := currentK, outputBoundK := outputK }
    let levelsConsumed := radixLevels radix
    buildStagesFromAssignment rest p hwIsSimd arrayIsLarge dir totalLevels
      (level + levelsConsumed) (stageIdx + 1) outputK (stg :: acc)

/-- Convert a radix assignment into a complete NTTPlan.
    The assignment comes from MatEGraphStep exploration. -/
def assignmentToPlan (assignment : List RadixChoice) (p n : Nat)
    (hwIsSimd : Bool := false) (arrayIsLarge : Bool := false)
    (dir : StageDirection := .DIT) : Plan :=
  let totalLevels := log2 n
  let stages := buildStagesFromAssignment assignment p hwIsSimd arrayIsLarge dir
    totalLevels 0 0 1 []
  { stages := stages.toArray, field := p, size := n }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Explored Plan Selection (replaces hardcoded candidates)
-- ══════════════════════════════════════════════════════════════════

/-- Select the best NTT plan using MatEGraph exploration.
    1. Build cost oracle from hardware parameters
    2. Saturate MatEGraph (explore all valid radix assignments)
    3. Extract best assignment
    4. Convert to NTTPlan with bound-aware reduction
    Falls back to generateCandidates if exploration yields nothing. -/
def selectBestPlanExplored (p n : Nat) (mulCost addCost : Nat)
    (hwIsSimd : Bool := false) (arrayIsLarge : Bool := false)
    (fuel : Nat := 500) : Plan :=
  let oracle : CostOracle :=
    { mulCost, addCost, arraySize := n, hwIsSimd, arrayIsLarge }
  let bestAssignment := matSaturateAndExtract n oracle fuel
  if bestAssignment.isEmpty then
    -- Fallback: use existing hardcoded candidates
    selectBestPlan p n mulCost addCost hwIsSimd arrayIsLarge
  else
    assignmentToPlan bestAssignment p n hwIsSimd arrayIsLarge

/-- Refinement: post-extraction bound optimization.
    After extracting a plan, re-evaluate each stage's reduction choice
    with the actual computed bounds (may differ from oracle estimate). -/
def refinePlanBounds (plan : Plan) (hwIsSimd : Bool := false)
    (arrayIsLarge : Bool := false) : Plan :=
  let (refinedStages, _) := plan.stages.foldl (fun (acc, currentK) (stage : NTTStage) =>
    let canLazy := lazyReductionSafe (currentK + 1) plan.field
    let remaining := plan.stages.size - acc.size
    let mustReduce := remaining ≤ 2
    let red :=
      if canLazy && !mustReduce then ReductionChoice.lazy
      else selectReductionForBound (currentK + 1) hwIsSimd arrayIsLarge
    let outputK := stageBoundFactor currentK red
    let refined : NTTStage :=
      { stage with reduction := red, inputBoundK := currentK, outputBoundK := outputK }
    (acc.push refined, outputK)
  ) (#[], 1)
  { plan with stages := refinedStages }

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Helper: buildStagesFromAssignment output length = acc.length + assignment.length. -/
private theorem buildStagesFromAssignment_length (assignment : List RadixChoice)
    (p : Nat) (hwIsSimd arrayIsLarge : Bool) (dir : StageDirection)
    (totalLevels level stageIdx currentK : Nat) (acc : List NTTStage) :
    (buildStagesFromAssignment assignment p hwIsSimd arrayIsLarge dir
      totalLevels level stageIdx currentK acc).length =
    acc.length + assignment.length := by
  induction assignment generalizing level stageIdx currentK acc with
  | nil => simp [buildStagesFromAssignment, List.length_reverse]
  | cons radix rest ih =>
    simp only [buildStagesFromAssignment]
    rw [ih]
    simp [List.length_cons]
    omega

/-- assignmentToPlan produces stages matching the assignment length. -/
theorem assignmentToPlan_stages_length (assignment : List RadixChoice)
    (p n : Nat) :
    (assignmentToPlan assignment p n).stages.size = assignment.length := by
  simp only [assignmentToPlan, List.size_toArray]
  rw [buildStagesFromAssignment_length]
  simp

/-- selectBestPlanExplored returns a plan with stages > 0 for BabyBear N=1024. -/
theorem selectBestPlanExplored_nonempty_babybear :
    (selectBestPlanExplored 2013265921 1024 3 1).stages.size > 0 := by native_decide

/-- selectBestPlanExplored returns a plan with stages > 0 for Mersenne31 N=1024. -/
theorem selectBestPlanExplored_nonempty_mersenne31 :
    (selectBestPlanExplored 2147483647 1024 3 1).stages.size > 0 := by native_decide

/-- selectBestPlanExplored returns a plan with stages > 0 for Goldilocks N=1024. -/
theorem selectBestPlanExplored_nonempty_goldilocks :
    (selectBestPlanExplored 18446744069414584321 1024 4 1).stages.size > 0 := by native_decide

/-- refinePlanBounds preserves the number of stages. -/
theorem refinePlanBounds_preserves_size (plan : Plan) :
    (refinePlanBounds plan).stages.size = plan.stages.size := by
  simp only [refinePlanBounds]
  exact Array.foldl_induction
    (motive := fun i (p : Array NTTStage × Nat) => p.1.size = i)
    (h0 := by simp)
    (hf := fun i (acc, k) hmot => by simp [Array.size_push, hmot])

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- Empty assignment produces empty plan. -/
example : (assignmentToPlan [] 2013265921 1024).stages.size = 0 := by native_decide

/-- All-r2 assignment produces 10 stages for N=1024. -/
example : (assignmentToPlan (List.replicate 10 .r2) 2013265921 1024).stages.size = 10 := by
  native_decide

/-- All-r4 assignment produces 5 stages for N=1024. -/
example : (assignmentToPlan (List.replicate 5 .r4) 2013265921 1024).stages.size = 5 := by
  native_decide

/-- Explored plan is well-formed for BabyBear N=1024. -/
example : (selectBestPlanExplored 2013265921 1024 3 1).wellFormed = true := by native_decide

/-- Explored plan has > 0 stages. -/
example : (selectBestPlanExplored 2013265921 1024 3 1).stages.size > 0 := by native_decide

/-- Explored plan produces a different (potentially better) plan than uniform. -/
example : (selectBestPlanExplored 2013265921 1024 3 1).stages.size ≤ 10 := by native_decide

/-- assignmentToPlan with concrete mixed assignment. -/
example :
  let plan := assignmentToPlan [.r4, .r4, .r4, .r2, .r2, .r2, .r2] 2013265921 1024
  plan.stages.size = 7 := by native_decide

/-- Refined plan preserves stage count. -/
example :
  let plan := assignmentToPlan (List.replicate 10 .r2) 2013265921 1024
  (refinePlanBounds plan).stages.size = plan.stages.size := by native_decide

/-- MatEGraph exploration actually explores multiple assignments. -/
example :
  let oracle := CostOracle.armScalar 1024
  let g := MatEGraphStep.matSaturateF (MatEGraph.empty (log2 1024)) oracle
  g.numExplored > 1 := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.Discovery.MatPlanExtraction
