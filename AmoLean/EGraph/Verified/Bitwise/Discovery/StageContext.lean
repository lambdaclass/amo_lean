/-
  AMO-Lean — StageContext: Per-Stage NTT Reduction Context
  Fase 27 N27.11: Provides per-stage context for reduction decisions.

  A `StageContext` carries all the information needed to decide whether
  to apply modular reduction at a given NTT butterfly stage:
  - Stage index and total stages
  - Current accumulated bound (from relational DAG)
  - Target bitwidth and hardware context

  The `reductionDecision` function uses verified bounds:
  if the accumulated bound fits in the target word, skip reduction.

  Consumes: BoundRelation (safeWithoutReduce), LazyReduction (canDeferReduction)
  Consumed by: N27.12 (discoverReductionForStage), N27.13 (emitPerStageNTT)
-/
import AmoLean.EGraph.Verified.Bitwise.BoundRelation
import AmoLean.EGraph.Verified.Bitwise.BoundPropagation

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery.Stage

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.BoundRel (safeWithoutReduce)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: StageContext
-- ══════════════════════════════════════════════════════════════════

/-- Per-stage context for NTT reduction decisions.
    Carries all information needed to decide the reduction strategy. -/
structure StageContext where
  stageIndex : Nat
  totalStages : Nat
  inputBoundK : Nat       -- current k such that value < k*p
  bitwidth : Nat           -- target word size (32 or 64)
  prime : Nat              -- field prime
  hwIsSimd : Bool := false
  cacheLevel : Nat := 0   -- 0=L1, 1=L2, 2=L3
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Reduction Decision
-- ══════════════════════════════════════════════════════════════════

/-- Decide reduction strategy for a stage based on verified bounds.
    Priority:
    1. Skip (lazy) if accumulated bound fits in target word
    2. Solinas fold (cheap, output < 2p) if scalar or default
    3. Montgomery (output < p) if SIMD or large array
    4. Always reduce at last stage -/
def reductionDecision (ctx : StageContext) : ReductionChoice :=
  -- Always reduce at last stage
  if ctx.stageIndex + 1 = ctx.totalStages then .solinasFold
  -- Check if we can skip reduction (bounds fit in word width)
  else if (ctx.inputBoundK + 1) * ctx.prime < 2 ^ ctx.bitwidth then .lazy
  -- Small bounds after previous reduction: Harvey is cheapest (3 cycles)
  else if ctx.inputBoundK ≤ 2 then .harvey
  -- SIMD: Montgomery stays in u32 lanes (no widening penalty)
  else if ctx.hwIsSimd then .montgomery
  -- Default scalar: Solinas fold
  else .solinasFold

/-- Output bound after applying the reduction decision. -/
def outputBoundK (ctx : StageContext) : Nat :=
  match reductionDecision ctx with
  | .lazy => ctx.inputBoundK + 1  -- one more addition without reduce
  | .solinasFold => 2             -- output < 2p
  | .montgomery => 1              -- output < p
  | .harvey => 1                  -- output < p (harveyReduceSpec postcondition)

/-- Build stage contexts for a full NTT. -/
def buildStageContexts (numStages prime bitwidth : Nat)
    (hwIsSimd : Bool := false) : List StageContext :=
  go 0 1 []  -- initial bound k=1 (input in [0, p))
where
  go (stage : Nat) (currentK : Nat) (acc : List StageContext) : List StageContext :=
    if stage ≥ numStages then acc.reverse
    else
      let ctx : StageContext := {
        stageIndex := stage
        totalStages := numStages
        inputBoundK := currentK
        bitwidth := bitwidth
        prime := prime
        hwIsSimd := hwIsSimd
      }
      let nextK := outputBoundK ctx
      go (stage + 1) nextK (ctx :: acc)
  termination_by numStages - stage

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Verified Properties
-- ══════════════════════════════════════════════════════════════════

/-- Last stage always reduces (never lazy). -/
theorem last_stage_reduces (ctx : StageContext) (hlast : ctx.stageIndex + 1 = ctx.totalStages) :
    reductionDecision ctx ≠ .lazy := by
  simp [reductionDecision, hlast]

/-- When reduction decision is lazy, the bound is safe. -/
theorem lazy_implies_safe (ctx : StageContext)
    (hlazy : reductionDecision ctx = .lazy) :
    safeWithoutReduce ctx.prime (ctx.inputBoundK + 1) ctx.bitwidth := by
  simp only [reductionDecision] at hlazy
  split at hlazy
  · contradiction
  · split at hlazy
    · rename_i _ h; exact h
    · split at hlazy
      · contradiction
      · split at hlazy <;> contradiction

/-- Output bound is always ≤ max(inputBound + 1, 2). -/
theorem outputBoundK_le_max (ctx : StageContext) :
    outputBoundK ctx ≤ max (ctx.inputBoundK + 1) 2 := by
  simp [outputBoundK]
  cases reductionDecision ctx <;> simp <;> omega

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

-- BabyBear p = 2^31 - 2^27 + 1 = 2013265921
-- In 32-bit: 2*p = 4026531842 > 2^31 but < 2^32
-- So k=1 is safe (p < 2^31), k=2 is NOT safe in 31-bit

private def bbCtx (stage k : Nat) : StageContext :=
  { stageIndex := stage, totalStages := 10, inputBoundK := k,
    bitwidth := 32, prime := 2013265921 }

-- Stage 0 with k=1: can skip (1*p + 1*p < 2^32)
example : reductionDecision (bbCtx 0 1) = .lazy := by native_decide

-- Stage 9 (last): always reduces
example : reductionDecision { bbCtx 9 1 with totalStages := 10 } = .solinasFold := by native_decide

-- Build 3-stage BabyBear NTT contexts
#eval (buildStageContexts 3 2013265921 32).map fun ctx =>
  (ctx.stageIndex, ctx.inputBoundK, reductionDecision ctx)

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.Discovery.Stage
