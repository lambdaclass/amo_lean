/-
  AMO-Lean Ultra — Phase 23, Node 23.1: NTTPlan
  Per-stage NTT plan carrying algorithmic decisions to codegen.

  An NTTPlan specifies, for each NTT stage:
  - Which radix to use (2 or 4)
  - Which reduction to apply (solinasFold, montgomery, harvey, or lazy)
  - Which direction (DIT or DIF)
  - What bound factor the output has

  The plan is the bridge between Level 1 (algorithmic choice) and
  Level 2 (arithmetic optimization) → Level 5 (codegen).

  Consumes:
  - NTTFactorizationRules.NTTStrategy (algorithmic level)
  - BoundPropagation.ReductionChoice (arithmetic level)
  - BoundPropagation.stageBoundFactor (bound analysis)
  - CrossRelNTT.selectReductionForBound (per-stage selection)

  Consumed by:
  - N23.3 NTTPlanSelection (plan generation + cache model)
  - N23.4 NTTPlanCodeGen (codegen from plan)
  - BoundIntegration (top-level consumer)
-/
import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.NTTPlan

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice stageBoundFactor
  lazyReductionSafe boundAfterReduction)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound
  costAwareReductionForBound reductionCostForHW butterflyREDCCost)
open AmoLean.EGraph.Verified.Bitwise (HardwareCost arm_neon_simd arm_cortex_a76)

-- ══════════════════════════════════════════════════════════════════
-- Section 0: Utilities (avoid Mathlib dependency for Nat.log)
-- ══════════════════════════════════════════════════════════════════

/-- Simple log₂ for powers of 2. Returns the exponent. -/
def log2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + log2 ((n + 2) / 2)
  termination_by n => n

/-- log₄(n) = log₂(n) / 2. -/
def log4 (n : Nat) : Nat := log2 n / 2

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Core Types
-- ══════════════════════════════════════════════════════════════════

inductive RadixChoice where
  | r2   -- radix-2: 2-point butterfly (a ± wb)
  | r4   -- radix-4: 4-point butterfly (2× composed radix-2)
  deriving Repr, BEq, Inhabited

inductive StageDirection where
  | DIT  -- Decimation-In-Time (Cooley-Tukey): bit-rev input, natural output
  | DIF  -- Decimation-In-Frequency (Gentleman-Sande): natural input, bit-rev output
  deriving Repr, BEq, Inhabited

/-- A single NTT stage with all decisions specified. -/
structure NTTStage where
  stageIdx : Nat              -- 0-indexed stage number
  radix : RadixChoice         -- 2-point or 4-point butterfly
  reduction : ReductionChoice -- what reduction after this stage
  direction : StageDirection  -- DIT or DIF
  inputBoundK : Nat           -- bound factor of inputs to this stage
  outputBoundK : Nat          -- bound factor of outputs (after reduction)
  ilpFactor : Nat := 1        -- v3.5.0: independent butterflies per loop iteration (1 or 2)
  deriving Repr, BEq, Inhabited

/-- Memory access ordering for the NTT. -/
inductive NTTOrdering where
  | standard   -- bit-reversal input, natural output (classic DIT)
  | bowers     -- natural input, natural output (Bowers: extra memory passes)
  | reversed   -- natural input, bit-reversal output (classic DIF)
  deriving Repr, BEq, Inhabited

/-- A complete NTT plan: all stages with their decisions. -/
structure Plan where
  stages : Array NTTStage
  field : Nat                 -- prime p
  size : Nat                  -- N (power of 2)
  ordering : NTTOrdering := .standard
  deriving Repr, BEq, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Plan Construction
-- ══════════════════════════════════════════════════════════════════

/-- Number of stages in the plan. -/
def Plan.numStages (plan : Plan) : Nat := plan.stages.size

/-- Set ilpFactor on all stages. Used by generateCandidates to create
    ILP-enabled plan variants. -/
def Plan.withILP (plan : Plan) (ilp : Nat := 2) : Plan :=
  { plan with stages := plan.stages.map fun s => { s with ilpFactor := ilp } }

/-- Total butterflies across all stages. -/
def Plan.totalButterflies (plan : Plan) : Nat :=
  plan.stages.foldl (fun acc stage =>
    let bfsPerStage := match stage.radix with
      | .r2 => plan.size / 2
      | .r4 => plan.size / 4
    acc + bfsPerStage
  ) 0

/-- Count lazy stages (reductions saved). -/
def Plan.lazyStages (plan : Plan) : Nat :=
  plan.stages.foldl (fun acc stage =>
    if stage.reduction == .lazy then acc + 1 else acc) 0

/-- Generate a uniform plan: all stages use the same radix and reduction. -/
def mkUniformPlan (p n : Nat) (radix : RadixChoice) (red : ReductionChoice)
    (dir : StageDirection := .DIT) : Plan :=
  let numStages := match radix with
    | .r2 => log2 n
    | .r4 => log4 n
  let stages := Array.range numStages |>.map fun i =>
    let inputK := if i == 0 then 1 else stageBoundFactor 1 red
    { stageIdx := i, radix, reduction := red, direction := dir,
      inputBoundK := inputK,
      outputBoundK := stageBoundFactor inputK red }
  { stages, field := p, size := n }

/-- Build stages recursively with bound tracking.
    When `hw` is provided, uses costAwareReductionForBound (picks cheapest per-stage).
    When `hw` is none, falls back to heuristic selectReductionForBound (backward compat). -/
private def buildBoundAwareStages (numStages p : Nat) (hw : Option HardwareCost)
    (arrayIsLarge : Bool) (dir : StageDirection) (stage : Nat) (currentK : Nat)
    (acc : List NTTStage) : List NTTStage :=
  if stage ≥ numStages then acc.reverse
  else
    let canLazy := lazyReductionSafe (currentK + 1) p
    let mustReduce := stage ≥ numStages - 2
    let red := match hw with
      | some hwCost =>
        -- Cost-aware: pick cheapest reduction for current bounds
        costAwareReductionForBound hwCost (currentK + 1) p
      | none =>
        -- Heuristic fallback (no hw info)
        if canLazy && !mustReduce then .lazy
        else selectReductionForBound (currentK + 1) false arrayIsLarge
    let outputK := stageBoundFactor currentK red
    let stg : NTTStage :=
      { stageIdx := stage, radix := .r2, reduction := red, direction := dir,
        inputBoundK := currentK, outputBoundK := outputK }
    buildBoundAwareStages numStages p hw arrayIsLarge dir
      (stage + 1) outputK (stg :: acc)
  termination_by numStages - stage

def mkBoundAwarePlan (p n : Nat) (hw : Option HardwareCost := none)
    (arrayIsLarge : Bool := false) (dir : StageDirection := .DIT) : Plan :=
  let numStages := log2 n
  let stages := buildBoundAwareStages numStages p hw arrayIsLarge dir 0 1 []
  { stages := stages.toArray, field := p, size := n }

/-- Build stages with mixed radix: radix-4 for early stages (covers 2 levels each),
    radix-2 for late stages (covers 1 level each). Uses bound-aware reduction.
    Strategy: radix-4 while ≥4 levels remain AND in first half of levels. -/
private def buildMixedRadixStages (totalLevels p : Nat)
    (hw : Option HardwareCost) (arrayIsLarge : Bool) (dir : StageDirection)
    (level : Nat) (stageIdx : Nat) (currentK : Nat)
    (acc : List NTTStage) : List NTTStage :=
  if level ≥ totalLevels then acc.reverse
  else
    let remaining := totalLevels - level
    let useR4 := remaining ≥ 4 && level * 2 < totalLevels
    let radix := if useR4 then RadixChoice.r4 else RadixChoice.r2
    let canLazy := lazyReductionSafe (currentK + 1) p
    let mustReduce := remaining ≤ 2
    let red := match hw with
      | some hwCost => costAwareReductionForBound hwCost (currentK + 1) p
      | none =>
        if canLazy && !mustReduce then ReductionChoice.lazy
        else selectReductionForBound (currentK + 1) false arrayIsLarge
    let outputK := stageBoundFactor currentK red
    let stg : NTTStage :=
      { stageIdx := stageIdx, radix := radix, reduction := red, direction := dir,
        inputBoundK := currentK, outputBoundK := outputK }
    if useR4 then
      buildMixedRadixStages totalLevels p hw arrayIsLarge dir
        (level + 2) (stageIdx + 1) outputK (stg :: acc)
    else
      buildMixedRadixStages totalLevels p hw arrayIsLarge dir
        (level + 1) (stageIdx + 1) outputK (stg :: acc)
  termination_by totalLevels - level

/-- Mixed-radix plan: radix-4 for early stages, radix-2 for late stages.
    Combines ILP benefits of radix-4 (fewer stages, better pipelining) with
    simplicity of radix-2 for cache-hostile late stages. -/
def mkMixedRadixPlan (p n : Nat) (hw : Option HardwareCost := none)
    (arrayIsLarge : Bool := false) (dir : StageDirection := .DIT) : Plan :=
  let totalLevels := log2 n
  let stages := buildMixedRadixStages totalLevels p hw arrayIsLarge dir 0 0 1 []
  { stages := stages.toArray, field := p, size := n }

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Plan Cost
-- ══════════════════════════════════════════════════════════════════

/-- Total reduction cost of a plan using hardware-aware costs. -/
def Plan.totalReductionCost (plan : Plan) (hw : HardwareCost) : Nat :=
  plan.stages.foldl (fun acc stage =>
    acc + reductionCostForHW hw stage.reduction) 0

/-- Butterfly arithmetic cost per stage INCLUDING product REDC.
    R2: 1 twiddle mul (→REDC) + add + sub = mul + 2*add + REDC
    R4: 3 twiddle muls (→3 REDC) + 8 add/subs + 1 extra REDC = 3*mul + 8*add + 4*REDC -/
def butterflyCost (radix : RadixChoice) (hw : HardwareCost) : Nat :=
  let redc := butterflyREDCCost hw
  match radix with
  | .r2 => hw.mul32 + 2 * hw.add + redc
  | .r4 => 3 * hw.mul32 + 8 * hw.add + 4 * redc

/-- Whether a stage at NTT level `level` would be SIMD-vectorized.
    Mirrors SIMDEmitter.emitStageC eligibility (after normalizePlan):
    R2 AND halfSize >= lanes, where halfSize = n / 2^(level+1).
    Always false when hw.isSimd = false (scalar hardware). -/
def stageSimdEligibleAtLevel (n : Nat) (radix : RadixChoice) (level : Nat)
    (hw : HardwareCost) : Bool :=
  hw.isSimd && radix == .r2 && n / (2 ^ (level + 1)) >= hw.simdLanes

/-- stageSimdEligibleAtLevel is always false for non-SIMD hardware. -/
theorem stageSimdEligible_scalar (n : Nat) (radix : RadixChoice) (level : Nat)
    (hw : HardwareCost) (h : hw.isSimd = false) :
    stageSimdEligibleAtLevel n radix level hw = false := by
  simp [stageSimdEligibleAtLevel, h]

/-- Total arithmetic + reduction cost using hardware-aware model.
    Reduction cost is 2× per butterfly (applied to both sum and diff).
    SIMD throughput: when a stage is SIMD-eligible (R2, halfSize >= lanes),
    effective cost is divided by (simdLanes - 1) — conservative estimate.
    ILP discount: when ilpFactor > 1 on SIMD, V1 absorbs add/sub of butterfly A
    while V0 does REDC of butterfly B → ~25% discount (calibrated in B35-4).
    Level tracking mirrors normalizePlan: R2 consumes 1 level, R4 consumes 2.
    v3.10.0 T7: Refactored into totalCostWith (parametric costFn) + totalCost (static wrapper).
    lazy_eq_solinas_cost uses reductionCostForHW DIRECTLY — NOT affected by this refactoring. -/
def Plan.totalCostWith (plan : Plan) (hw : HardwareCost)
    (costFn : HardwareCost → ReductionChoice → Nat) : Nat :=
  let (cost, _) := plan.stages.foldl (fun (acc : Nat × Nat) stage =>
    let (total, level) := acc
    let bfs := match stage.radix with | .r2 => plan.size / 2 | .r4 => plan.size / 4
    let bfCost := butterflyCost stage.radix hw
    let redCost := costFn hw stage.reduction
    let rawStageCost := bfs * (bfCost + 2 * redCost)
    let eligible := stageSimdEligibleAtLevel plan.size stage.radix level hw
    let simdDivisor := if eligible then Nat.max 2 (hw.simdLanes - 1) else 1
    let afterSimd := rawStageCost / simdDivisor
    let withIlp := afterSimd
    let levelsConsumed := match stage.radix with | .r2 => 1 | .r4 => 2
    (total + withIlp, level + levelsConsumed)
  ) (0, 0)
  cost

/-- Backward-compatible wrapper: uses static reductionCostForHW. -/
def Plan.totalCost (plan : Plan) (hw : HardwareCost) : Nat :=
  Plan.totalCostWith plan hw reductionCostForHW

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Plan Validation
-- ══════════════════════════════════════════════════════════════════

/-- Check that all stage bounds are consistent: each stage's inputBoundK
    matches the previous stage's outputBoundK. -/
def Plan.boundsConsistent (plan : Plan) : Bool :=
  if plan.stages.size ≤ 1 then true
  else
    let pairs := plan.stages.toList.zip (plan.stages.toList.drop 1)
    pairs.all fun (prev, next) => next.inputBoundK == prev.outputBoundK

/-- The last stage must produce fully reduced output (k ≤ 2). -/
def Plan.outputFullyBounded (plan : Plan) : Bool :=
  match plan.stages.back? with
  | some last => last.outputBoundK ≤ 2
  | none => true

/-- All stages use the same direction (no DIT+DIF mixing). -/
def Plan.directionUniform (plan : Plan) : Bool :=
  plan.stages.toList.all (·.direction == .DIT) ||
  plan.stages.toList.all (·.direction == .DIF)

/-- A plan is well-formed if bounds are consistent, output is bounded,
    and direction is uniform (no DIT+DIF mixing). -/
def Plan.wellFormed (plan : Plan) : Bool :=
  plan.boundsConsistent && plan.outputFullyBounded && plan.directionUniform

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Uniform radix-2 plan has log₂(n) stages. -/
theorem mkUniformPlan_numStages (p n : Nat) (red : ReductionChoice) :
    (mkUniformPlan p n .r2 red).numStages = log2 n := by
  simp [mkUniformPlan, Plan.numStages, Array.size_map, Array.size_range]

/-- Bound-aware plan produces a plan (operational check via native_decide). -/
example : (mkBoundAwarePlan 2013265921 1024).numStages = 10 := by native_decide

/-- Lazy cost = Solinas cost in hw-aware model (codegen does Solinas fold). -/
theorem lazy_eq_solinas_cost (hw : HardwareCost) :
    reductionCostForHW hw .lazy = reductionCostForHW hw .solinasFold := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- Uniform plan for BabyBear N=1024 has 10 stages. -/
example : (mkUniformPlan 2013265921 1024 .r2 .solinasFold).numStages = 10 := by native_decide

/-- Bound-aware plan for BabyBear N=1024 is well-formed. -/
example : (mkBoundAwarePlan 2013265921 1024).wellFormed = true := by native_decide

/-- Bound-aware plan (no hw) saves lazy reductions. -/
example : (mkBoundAwarePlan 2013265921 1024).lazyStages > 0 := by native_decide

/-- With hw, bound-aware plan uses Harvey (cheaper than Solinas for NEON). -/
example : (mkBoundAwarePlan 2013265921 1024 (some arm_neon_simd)).totalReductionCost arm_neon_simd <
    (mkUniformPlan 2013265921 1024 .r2 .solinasFold).totalReductionCost arm_neon_simd := by
  native_decide

/-- Plan validates: bounds consistent. -/
example : (mkBoundAwarePlan 2013265921 1024).boundsConsistent = true := by native_decide

/-- Plan validates: output bounded. -/
example : (mkBoundAwarePlan 2013265921 1024).outputFullyBounded = true := by native_decide

/-- Uniform radix-4 plan for BabyBear N=1024 has 5 stages. -/
example : (mkUniformPlan 2013265921 1024 .r4 .solinasFold).numStages = 5 := by native_decide

/-- Uniform radix-4 plan is well-formed. -/
example : (mkUniformPlan 2013265921 1024 .r4 .solinasFold).wellFormed = true := by native_decide

/-- Radix-4 plan has fewer total butterflies than radix-2. -/
example : (mkUniformPlan 2013265921 1024 .r4 .solinasFold).totalButterflies <
    (mkUniformPlan 2013265921 1024 .r2 .solinasFold).totalButterflies := by native_decide

/-- Mixed-radix plan uses both radix-4 and radix-2 stages. -/
example :
  let plan := mkMixedRadixPlan 2013265921 1024
  plan.stages.any (fun s => s.radix == .r4) &&
  plan.stages.any (fun s => s.radix == .r2) = true := by native_decide

/-- Mixed-radix plan is well-formed. -/
example : (mkMixedRadixPlan 2013265921 1024).wellFormed = true := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.NTTPlan
