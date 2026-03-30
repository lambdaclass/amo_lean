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
-- Note: BoundPropagation transitively imports MultiRelMixed

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.CrossRelNTT

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice stageBoundFactor
  lazyReductionSafe computeStageBounds boundAfterReduction)

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
    -- Montgomery preferred for SIMD (u32 lanes) and large arrays (cache)
    .montgomery
  else
    .solinasFold

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

/-- Cost of a reduction operation, informed by the current bound factor.
    Harvey is cheap when bounds are tight; Montgomery is constant cost. -/
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

/-- Total reduction cost for an NTT (sum over all stages). -/
def nttTotalReductionCost (analysis : List (Nat × ReductionChoice × Nat))
    (hwIsSimd : Bool) : Nat :=
  analysis.foldl (fun acc (_, red, boundK) =>
    acc + reductionCost red boundK hwIsSimd) 0

/-- Improvement ratio: cost with bound-informed selection vs naive (all Solinas). -/
def improvementVsNaive (analysis : List (Nat × ReductionChoice × Nat))
    (hwIsSimd : Bool) : Nat × Nat :=
  let informed := nttTotalReductionCost analysis hwIsSimd
  let naive := analysis.length * (if hwIsSimd then 8 else 6)
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

/-- Lazy saves over Solinas. -/
example : reductionCost .lazy 1 false < reductionCost .solinasFold 1 false := by
  native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.CrossRelNTT
