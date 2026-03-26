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
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound reductionCost)

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
  deriving Repr, Inhabited

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
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Plan Construction
-- ══════════════════════════════════════════════════════════════════

/-- Number of stages in the plan. -/
def Plan.numStages (plan : Plan) : Nat := plan.stages.size

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
    Per-stage: check lazy safety → select reduction → compute output bound. -/
private def buildBoundAwareStages (numStages p : Nat) (hwIsSimd arrayIsLarge : Bool)
    (dir : StageDirection) (stage : Nat) (currentK : Nat)
    (acc : List NTTStage) : List NTTStage :=
  if stage ≥ numStages then acc.reverse
  else
    let canLazy := lazyReductionSafe (currentK + 1) p
    let mustReduce := stage ≥ numStages - 2
    let red :=
      if canLazy && !mustReduce then .lazy
      else selectReductionForBound (currentK + 1) hwIsSimd arrayIsLarge
    let outputK := stageBoundFactor currentK red
    let stg : NTTStage :=
      { stageIdx := stage, radix := .r2, reduction := red, direction := dir,
        inputBoundK := currentK, outputBoundK := outputK }
    buildBoundAwareStages numStages p hwIsSimd arrayIsLarge dir
      (stage + 1) outputK (stg :: acc)
  termination_by numStages - stage

def mkBoundAwarePlan (p n : Nat) (hwIsSimd : Bool := false)
    (arrayIsLarge : Bool := false) (dir : StageDirection := .DIT) : Plan :=
  let numStages := log2 n
  let stages := buildBoundAwareStages numStages p hwIsSimd arrayIsLarge dir 0 1 []
  { stages := stages.toArray, field := p, size := n }

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Plan Cost
-- ══════════════════════════════════════════════════════════════════

/-- Total reduction cost of a plan (sum of per-stage reduction costs). -/
def Plan.totalReductionCost (plan : Plan) (hwIsSimd : Bool) : Nat :=
  plan.stages.foldl (fun acc stage =>
    acc + reductionCost stage.reduction stage.inputBoundK hwIsSimd) 0

/-- Butterfly arithmetic cost per stage (excluding reduction). -/
def butterflyCost (radix : RadixChoice) (mulCost addCost : Nat) : Nat :=
  match radix with
  | .r2 => mulCost + 2 * addCost   -- 1 twiddle mul + add + sub
  | .r4 => 3 * mulCost + 8 * addCost  -- 3 twiddle muls + 8 add/subs

/-- Total arithmetic + reduction cost. -/
def Plan.totalCost (plan : Plan) (mulCost addCost : Nat) (hwIsSimd : Bool) : Nat :=
  plan.stages.foldl (fun acc stage =>
    let bfs := match stage.radix with | .r2 => plan.size / 2 | .r4 => plan.size / 4
    let bfCost := butterflyCost stage.radix mulCost addCost
    let redCost := reductionCost stage.reduction stage.inputBoundK hwIsSimd
    acc + bfs * (bfCost + redCost)
  ) 0

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

/-- A plan is well-formed if bounds are consistent and output is bounded. -/
def Plan.wellFormed (plan : Plan) : Bool :=
  plan.boundsConsistent && plan.outputFullyBounded

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Uniform radix-2 plan has log₂(n) stages. -/
theorem mkUniformPlan_numStages (p n : Nat) (red : ReductionChoice) :
    (mkUniformPlan p n .r2 red).numStages = log2 n := by
  simp [mkUniformPlan, Plan.numStages, Array.size_map, Array.size_range]

/-- Bound-aware plan produces a plan (operational check via native_decide). -/
example : (mkBoundAwarePlan 2013265921 1024).numStages = 10 := by native_decide

/-- Lazy butterfly cost is 0. -/
theorem lazy_no_reduction_cost (k : Nat) (hw : Bool) :
    reductionCost .lazy k hw = 0 := rfl

/-- Radix-2 butterfly cost. -/
theorem radix2_bf_cost (m a : Nat) :
    butterflyCost .r2 m a = m + 2 * a := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- Uniform plan for BabyBear N=1024 has 10 stages. -/
example : (mkUniformPlan 2013265921 1024 .r2 .solinasFold).numStages = 10 := by native_decide

/-- Bound-aware plan for BabyBear N=1024 is well-formed. -/
example : (mkBoundAwarePlan 2013265921 1024).wellFormed = true := by native_decide

/-- Bound-aware plan saves lazy reductions. -/
example : (mkBoundAwarePlan 2013265921 1024).lazyStages > 0 := by native_decide

/-- Bound-aware plan costs less than uniform Solinas. -/
example : (mkBoundAwarePlan 2013265921 1024).totalReductionCost false <
    (mkUniformPlan 2013265921 1024 .r2 .solinasFold).totalReductionCost false := by
  native_decide

/-- Plan validates: bounds consistent. -/
example : (mkBoundAwarePlan 2013265921 1024).boundsConsistent = true := by native_decide

/-- Plan validates: output bounded. -/
example : (mkBoundAwarePlan 2013265921 1024).outputFullyBounded = true := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.NTTPlan
