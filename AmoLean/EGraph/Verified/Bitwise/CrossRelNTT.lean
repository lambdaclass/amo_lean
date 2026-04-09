/-
  AMO-Lean Ultra — Phase 22, Node 22.6: Cross-Relation NTT Rules
  NTT-specific rules connecting bound information to optimization decisions.

  These rules use bound factors from BoundPropagation to inform:
  - Harvey branch count selection (1-branch if < 2p, 2-branch if < 4p)
  - Lazy reduction safety (defer reduction if bound stays < 2^64)
  - Per-stage reduction strategy selection

  Key functions:
  - `selectReductionForBound`: given bound factor k, select optimal reduction
  - `nttStageBoundAnalysis`: analyze bounds through a sequence of NTT stages
  - `boundInformedCost`: cost function that uses bound info
-/
import AmoLean.EGraph.Verified.Bitwise.BoundPropagation
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
-- Note: BoundPropagation transitively imports MultiRelMixed

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.CrossRelNTT

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice stageBoundFactor
  lazyReductionSafe computeStageBounds boundAfterReduction)
open AmoLean.EGraph.Verified.Bitwise (HardwareCost MixedNodeOp mixedOpCost)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Bound-Informed Reduction Selection
-- ══════════════════════════════════════════════════════════════════

/-- Select the optimal reduction strategy given the current bound factor.

    Decision logic:
    - k = 1 (fully reduced): any reduction works, prefer cheapest
    - k ≤ 2: Harvey 1-branch is cheapest (just a conditional sub)
    - k ≤ 4: Harvey 2-branch or Solinas fold
    - k > 4: must reduce (Solinas or Montgomery)

    The `hwIsSimd` flag shifts preference toward Montgomery (stays in u32).
    The `arrayIsLarge` flag also shifts toward Montgomery (cache pressure). -/
def selectReductionForBound (boundK : Nat) (hwIsSimd : Bool) (arrayIsLarge : Bool) :
    ReductionChoice :=
  if boundK ≤ 2 then
    -- Can use Harvey 1-branch (cheapest for bounded inputs)
    .harvey
  else if boundK ≤ 4 && !hwIsSimd then
    -- Solinas fold is good for scalar with moderate bounds
    .solinasFold
  else if hwIsSimd || arrayIsLarge then
    -- Solinas fold: Montgomery REDC is unsound for sums/diffs (only valid for products).
    -- costAwareReductionForBound correctly excludes Montgomery; this path must match.
    .solinasFold
  else
    .solinasFold

/-- Cost-aware reduction selection: enumerate feasible reductions,
    compute actual hardware cost for each, pick cheapest.
    `serialContext` adds branch penalties for serial patterns (FRI fold, dot product).
    For NTT butterflies (data-parallel), pass `serialContext := false` (default). -/
def costAwareReductionForBound (hw : HardwareCost) (boundK p : Nat)
    (serialContext : Bool := false) : ReductionChoice :=
  -- Feasibility: Harvey needs boundK ≤ 2.
  -- Montgomery EXCLUDED: REDC gives x*R⁻¹ mod p, only correct for products (tw*b),
  -- NOT for sums/diffs. All callers use this for per-stage sum/diff reduction.
  let candidates : List (Nat × ReductionChoice) :=
    (if boundK ≤ 2 then [(mixedOpCost hw (.harveyReduce 0 p), .harvey)] else []) ++
    [(mixedOpCost hw (.reduceGate 0 p), .solinasFold)]
  -- Branch penalties only in serial context (FRI fold, dot product — NOT NTT)
  let withBranch := if serialContext then
    candidates.map fun (baseCost, choice) =>
      let branchAdj := match choice with
        | .solinasFold => 2 * hw.branchPenalty  -- output < 2p → 2 cond subs
        | _ => hw.branchPenalty                  -- output < p → 1 cond sub
      (baseCost + branchAdj, choice)
  else candidates
  -- Pick cheapest
  withBranch.foldl (fun (bestC, bestR) (c, r) =>
    if c < bestC then (c, r) else (bestC, bestR))
    (100000, .solinasFold) |>.2

-- ══════════════════════════════════════════════════════════════════
-- Section 1b: Hardware-Aware Reduction Cost (SINGLE SOURCE OF TRUTH)
-- ══════════════════════════════════════════════════════════════════

/-- Hardware-aware reduction cost. SINGLE SOURCE OF TRUTH for plan costing.
    Maps ReductionChoice to cycle count using mixedOpCost from HardwareCost.
    .lazy cost = Solinas fold cost (matching lowerReductionChoice codegen in
    VerifiedPlanCodeGen.lean:82-85 which redirects .lazy to Solinas fold). -/
def reductionCostForHW (hw : HardwareCost) (red : ReductionChoice) : Nat :=
  match red with
  | .solinasFold => mixedOpCost hw (.reduceGate 0 0)
  | .montgomery => mixedOpCost hw (.montyReduce 0 0 0)
  | .harvey => mixedOpCost hw (.harveyReduce 0 0)
  | .lazy => mixedOpCost hw (.reduceGate 0 0)  -- codegen does Solinas fold

/-- Instruction profile for modelling execution cost on dual-pipe ARM NEON.
    Calibrated empirically in B35-2 (bench_redc_isolated.c).
    Key insight: V0 throughput dominates, not critical path, because OoO hides latency. -/
structure InstructionProfile where
  v0OnlyInstructions : Nat    -- instructions exclusive to V0 (mul, sqdmulh, mls)
  dualIssueInstructions : Nat -- instructions for V0 or V1 (add, sub, cmp, and, shsub)
  deriving Repr

/-- Effective cost on dual-pipe NEON: V0 throughput is the bottleneck.
    Empirically validated: vmull(6 V0) → 6.8ns, sqdmulh(3 V0) → 3.8ns.
    Ratio 6/3 = 2.0× predicted, 1.79× measured. V0 throughput explains ~90%. -/
def InstructionProfile.effectiveCost (p : InstructionProfile) : Nat :=
  p.v0OnlyInstructions

/-- vmull widening REDC profile (measured: 6.80 ns/call on Cortex-A76).
    V0-only: vmull×4 + vmul×2 = 6 instructions. -/
def redcProfile_vmull : InstructionProfile :=
  { v0OnlyInstructions := 6, dualIssueInstructions := 12 }

/-- sqdmulh Montgomery REDC profile (measured: 3.80 ns/call on Cortex-A76).
    V0-only: sqdmulh×2 + mul×1 = 3 instructions. -/
def redcProfile_sqdmulh : InstructionProfile :=
  { v0OnlyInstructions := 3, dualIssueInstructions := 4 }

/-- Butterfly REDC cost (product reduction, always Montgomery subtraction variant).
    Used by Plan.totalCost to include the REDC in butterfly cost (previously omitted). -/
def butterflyREDCCost (hw : HardwareCost) : Nat :=
  mixedOpCost hw (.montyReduce 0 0 0)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: NTT Stage Bound Analysis
-- ══════════════════════════════════════════════════════════════════

/-- Configuration for NTT bound analysis. -/
structure NTTBoundConfig where
  numStages : Nat        -- log₂(N)
  prime : Nat            -- field prime p
  hwIsSimd : Bool := false
  arrayIsLarge : Bool := false

/-- Analyze an NTT: for each stage, determine the optimal reduction
    strategy based on accumulated bounds.

    Returns a list of (stageIndex, reduction, boundFactorAfter). -/
def nttStageBoundAnalysis (cfg : NTTBoundConfig) : List (Nat × ReductionChoice × Nat) :=
  let go : Nat → Nat → List (Nat × ReductionChoice × Nat) → List (Nat × ReductionChoice × Nat) :=
    fun stage boundK acc =>
      -- Can we defer reduction (lazy)?
      let canLazy := lazyReductionSafe (boundK + 1) cfg.prime
      -- Is this the last 2 stages? (Must reduce for final output)
      let mustReduce := stage ≥ cfg.numStages - 2
      let reduction :=
        if canLazy && !mustReduce then .lazy
        else selectReductionForBound (boundK + 1) cfg.hwIsSimd cfg.arrayIsLarge
      let newBound := stageBoundFactor boundK reduction
      acc ++ [(stage, reduction, newBound)]
  List.range cfg.numStages |>.foldl (fun (acc, boundK) stage =>
    let result := go stage boundK []
    match result with
    | [(_, red, newK)] => (acc ++ [(stage, red, newK)], newK)
    | _ => (acc, boundK)  -- shouldn't happen
  ) ([], 1) |>.1

/-- Count how many reductions are saved by lazy strategy. -/
def lazyReductionSavings (analysis : List (Nat × ReductionChoice × Nat)) : Nat :=
  analysis.foldl (fun acc (_, red, _) =>
    if red == .lazy then acc + 1 else acc) 0

/-- FRI fold bound analysis: after alpha * b, the result is < p * p.
    After add (a + alpha*b), result is < p + p*p = p(1+p).
    Need to reduce if p(1+p) > word_max.
    For 31-bit primes: p(1+p) < 2^31 * 2^31 = 2^62 < 2^64. Fits in u64.
    For Goldilocks: p(1+p) ≈ 2^128. Needs u128 and reduction after mul. -/
def friFoldReductionChoice (p : Nat) (bitwidth : Nat := 64) : ReductionChoice :=
  if p * (1 + p) < 2^bitwidth then .lazy  -- no reduction needed
  else .solinasFold  -- need to reduce after mul

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Bound-Informed Cost
-- ══════════════════════════════════════════════════════════════════

/-- DEPRECATED: Use reductionCostForHW instead. Hardcoded costs diverge from
    mixedOpCost for SIMD (Solinas: 8 vs real 14 on NEON). Kept for backward compat
    with olean-only callers (Phase23Integration, etc.). -/
def reductionCost (reduction : ReductionChoice) (boundK : Nat)
    (hwIsSimd : Bool) : Nat :=
  match reduction with
  | .solinasFold => if hwIsSimd then 8 else 6  -- shift + mul + mask + add (+ widening)
  | .montgomery => 7                            -- mul_lo + mul + sub (constant)
  | .harvey =>
    if boundK ≤ 2 then 3                       -- 1 comparison + conditional sub
    else if boundK ≤ 4 then 5                  -- 2 comparisons
    else 7                                      -- multiple comparisons
  | .lazy => 0                                  -- no reduction = free

/-- Total reduction cost for an NTT (sum over all stages).
    Uses reductionCostForHW (SSOT) instead of legacy reductionCost. -/
def nttTotalReductionCost (analysis : List (Nat × ReductionChoice × Nat))
    (hw : HardwareCost) : Nat :=
  analysis.foldl (fun acc (_, red, _) =>
    acc + reductionCostForHW hw red) 0

/-- Improvement ratio: cost with bound-informed selection vs naive (all Solinas).
    Uses reductionCostForHW (SSOT) for both informed and naive costs. -/
def improvementVsNaive (analysis : List (Nat × ReductionChoice × Nat))
    (hw : HardwareCost) : Nat × Nat :=
  let informed := nttTotalReductionCost analysis hw
  let naive := analysis.length * (reductionCostForHW hw .solinasFold)
  (informed, naive)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Predefined NTT Configurations
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear NTT N=2^20, scalar. -/
def babyBear_20_scalar : NTTBoundConfig where
  numStages := 20
  prime := 2013265921

/-- BabyBear NTT N=2^20, NEON SIMD. -/
def babyBear_20_neon : NTTBoundConfig where
  numStages := 20
  prime := 2013265921
  hwIsSimd := true

/-- Goldilocks NTT N=2^20, scalar. -/
def goldilocks_20_scalar : NTTBoundConfig where
  numStages := 20
  prime := 18446744069414584321

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Lazy reduction is always free (0 cost). -/
theorem lazy_cost_zero (k : Nat) (hw : Bool) :
    reductionCost .lazy k hw = 0 := rfl

/-- Harvey 1-branch is cheapest when bound ≤ 2. -/
theorem harvey_cheapest_tight (hw : Bool) :
    reductionCost .harvey 1 hw = 3 := rfl

/-- Montgomery cost is constant regardless of bounds. -/
theorem monty_constant (k₁ k₂ : Nat) (hw : Bool) :
    reductionCost .montgomery k₁ hw = reductionCost .montgomery k₂ hw := rfl

/-- selectReductionForBound with k ≤ 2 selects Harvey. -/
theorem select_tight_is_harvey (hw : Bool) (large : Bool) :
    selectReductionForBound 1 hw large = .harvey := rfl

/-- selectReductionForBound with k ≤ 2 selects Harvey (k=2 case). -/
theorem select_k2_is_harvey (hw : Bool) (large : Bool) :
    selectReductionForBound 2 hw large = .harvey := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- BabyBear scalar: lazy is safe with k=100. -/
example : lazyReductionSafe 100 2013265921 = true := by native_decide

/-- Stage bounds: lazy, lazy, solinas → [1, 2, 3, 2]. -/
example : computeStageBounds [.lazy, .lazy, .solinasFold] 1 = [1, 2, 3, 2] := by
  native_decide

/-- Harvey is cheapest for tight bounds. -/
example : reductionCost .harvey 1 false < reductionCost .solinasFold 1 false := by
  native_decide

/-- Lazy saves over Solinas (NOTE: legacy — lazy cost=0 is the bug being fixed). -/
example : reductionCost .lazy 1 false < reductionCost .solinasFold 1 false := by
  native_decide

/-- reductionCostForHW: ARM NEON Solinas costs 14 (not 8 as reductionCost claims). -/
example : reductionCostForHW arm_neon_simd .solinasFold = 14 := by native_decide
/-- reductionCostForHW: ARM NEON Montgomery costs 7. -/
example : reductionCostForHW arm_neon_simd .montgomery = 7 := by native_decide
/-- reductionCostForHW: ARM NEON Harvey costs 3 (cheapest for SIMD). -/
example : reductionCostForHW arm_neon_simd .harvey = 3 := by native_decide
/-- reductionCostForHW: lazy cost = Solinas cost (matching codegen). -/
example : reductionCostForHW arm_neon_simd .lazy = reductionCostForHW arm_neon_simd .solinasFold := by native_decide
/-- reductionCostForHW: ARM scalar Solinas costs 6. -/
example : reductionCostForHW arm_cortex_a76 .solinasFold = 6 := by native_decide
/-- costAwareReductionForBound: NEON with tight bounds picks Harvey (cheapest at 3 ops). -/
example : costAwareReductionForBound arm_neon_simd 2 2013265921 = .harvey := by native_decide
/-- costAwareReductionForBound: NEON with loose bounds picks Solinas (Montgomery excluded — REDC only valid for products). -/
example : costAwareReductionForBound arm_neon_simd 5 2013265921 = .solinasFold := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.CrossRelNTT
