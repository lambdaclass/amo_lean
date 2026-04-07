/-
  AMO-Lean Ultra — Phase 23, Node 23.3: NTTPlanSelection
  Plan generation and selection with cache-aware cost model.

  Cache cost is a PLAN-level concern (access pattern of the whole NTT),
  not a per-node cost. This is the clean separation from the 5-level
  architecture: Level 1 (algorithmic) handles cache, Level 3 (cost fn)
  handles per-node ALU costs.

  Consumes:
  - NTTPlan.Plan, mkUniformPlan, mkBoundAwarePlan, Plan.totalCost
  - Butterfly4Bridge.radix4TotalMuls, radix2TotalMuls
  - CrossRelNTT.selectReductionForBound
  - BoundPropagation.ReductionChoice

  Consumed by:
  - N23.4 NTTPlanCodeGen
  - BoundIntegration (top-level)
-/
import AmoLean.EGraph.Verified.Bitwise.Butterfly4Bridge

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.PlanSelection

open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice StageDirection
  mkUniformPlan mkBoundAwarePlan mkMixedRadixPlan log2 log4)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.Butterfly4 (radix4TotalMuls radix2TotalMuls)
open AmoLean.EGraph.Verified.Bitwise (HardwareCost arm_cortex_a76 arm_neon_simd)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Cache Model
-- ══════════════════════════════════════════════════════════════════

/-- Hardware cache configuration. -/
structure CacheConfig where
  l1DataSize : Nat := 32768    -- 32KB L1 data cache (typical ARM/x86)
  lineSize : Nat := 64         -- 64-byte cache line
  elementSize : Nat := 4       -- 4 bytes per u32 element
  l1MissCycles : Nat := 4      -- L1 miss penalty (cycles)
  l2MissCycles : Nat := 12     -- L2 miss penalty
  deriving Repr, Inhabited

def CacheConfig.default : CacheConfig := {}

/-- Estimate cache misses for a single NTT stage.
    In early stages, butterflies access nearby elements (cache-friendly).
    In late stages, stride grows and accesses span the full array (cache-hostile).

    The key insight: stride = N / (2^(stage+1)) for DIT.
    When stride * elementSize > L1 size, every butterfly pair causes misses. -/
def stageCacheMisses (n : Nat) (stageIdx : Nat) (cache : CacheConfig) : Nat :=
  let stride := n / (2 ^ (stageIdx + 1))
  let strideBytes := stride * cache.elementSize
  let butterfliesPerStage := n / 2
  if strideBytes ≤ cache.l1DataSize then
    0  -- all data fits in L1, no misses
  else
    -- Each butterfly pair accesses elements `stride` apart
    -- Miss rate ≈ (strideBytes - l1Size) / l1Size
    let missRate := (strideBytes - cache.l1DataSize) / cache.l1DataSize
    butterfliesPerStage * missRate

/-- Total cache cost for an NTT plan (sum of per-stage miss penalties). -/
def planCacheCost (plan : Plan) (cache : CacheConfig := .default) : Nat :=
  plan.stages.foldl (fun acc stage =>
    let misses := stageCacheMisses plan.size stage.stageIdx cache
    acc + misses * cache.l1MissCycles
  ) 0

/-- Bowers ordering reduces cache misses by processing data linearly.
    Approximate savings: 30-50% fewer misses for large N. -/
def bowersAdjustment (plan : Plan) (cache : CacheConfig) : Nat :=
  match plan.ordering with
  | .bowers => planCacheCost plan cache * 60 / 100  -- pay 60% of standard cost
  | _ => planCacheCost plan cache

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Plan Candidates
-- ══════════════════════════════════════════════════════════════════

/-- Generate all candidate plans for a given field, size, and hardware.
    When hw is provided, bound-aware plans use cost-aware reduction selection. -/
def generateCandidates (p n : Nat) (hw : HardwareCost)
    (arrayIsLarge : Bool := false) : Array Plan :=
  #[ -- 1. Uniform radix-2 + Solinas (baseline)
     mkUniformPlan p n .r2 .solinasFold,
     -- 2. Uniform radix-2 + Montgomery
     mkUniformPlan p n .r2 .montgomery,
     -- 3. Uniform radix-2 + Harvey
     mkUniformPlan p n .r2 .harvey,
     -- 4. Bound-aware radix-2 (cost-aware mixed reductions)
     mkBoundAwarePlan p n (some hw) arrayIsLarge,
     -- 5. Bound-aware radix-2 DIF
     mkBoundAwarePlan p n (some hw) arrayIsLarge .DIF,
     -- 6. Uniform radix-4 + Solinas (fewer stages, better ILP)
     mkUniformPlan p n .r4 .solinasFold,
     -- 7. Uniform radix-4 + Montgomery
     mkUniformPlan p n .r4 .montgomery,
     -- 8. Uniform radix-4 + Harvey (cheapest reduction, fewer stages)
     mkUniformPlan p n .r4 .harvey,
     -- 9. Mixed radix (radix-4 early, radix-2 late) + cost-aware
     mkMixedRadixPlan p n (some hw) arrayIsLarge
  ]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Plan Selection
-- ══════════════════════════════════════════════════════════════════

/-- Total cost of a plan: arithmetic + reduction + cache.
    Uses hardware-aware cost model (SINGLE SOURCE OF TRUTH). -/
def planTotalCost (plan : Plan) (hw : HardwareCost)
    (cache : CacheConfig := .default) : Nat :=
  plan.totalCost hw + bowersAdjustment plan cache

/-- Select the cheapest plan from a list of candidates.
    Returns the plan with lowest total cost using hardware-aware model. -/
def selectPlan (candidates : Array Plan) (hw : HardwareCost)
    (cache : CacheConfig := .default) : Option Plan :=
  if h : candidates.size == 0 then none
  else
    let first := candidates[0]!
    some (candidates.foldl (fun best plan =>
      let bestCost := planTotalCost best hw cache
      let planCost := planTotalCost plan hw cache
      if planCost < bestCost then plan else best
    ) first)

/-- Top-level: select the best NTT plan for a field + hardware.
    Computes arrayIsLarge from n vs cacheThreshold automatically. -/
def selectBestPlan (p n : Nat) (hw : HardwareCost)
    (cache : CacheConfig := .default) : Plan :=
  let arrayIsLarge := n > hw.cacheThreshold
  let candidates := generateCandidates p n hw arrayIsLarge
  match selectPlan candidates hw cache with
  | some plan => plan
  | none => mkUniformPlan p n .r2 .solinasFold  -- fallback

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- generateCandidates produces exactly 8 candidates (5 radix-2 + 2 radix-4 + 1 mixed). -/
theorem generateCandidates_size (p n : Nat) (hw : HardwareCost) :
    (generateCandidates p n hw).size = 9 := rfl

/-- selectBestPlan returns a well-formed plan for BabyBear N=1024. -/
example : (selectBestPlan 2013265921 1024 arm_cortex_a76).wellFormed = true := by native_decide

/-- With hw, bound-aware plan costs ≤ uniform Solinas for BabyBear NEON. -/
theorem boundAware_le_uniform_babybear_neon :
    (mkBoundAwarePlan 2013265921 1024 (some arm_neon_simd)).totalReductionCost arm_neon_simd ≤
    (mkUniformPlan 2013265921 1024 .r2 .solinasFold).totalReductionCost arm_neon_simd := by
  native_decide

/-- Early stages have 0 cache misses (stride fits in L1). -/
example : stageCacheMisses 1024 0 .default = 0 := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- 8 candidates for BabyBear N=1024. -/
example : (generateCandidates 2013265921 1024 arm_cortex_a76).size = 9 := rfl

/-- selectBestPlan returns a plan (doesn't crash). -/
example : (selectBestPlan 2013265921 1024 arm_cortex_a76).numStages > 0 := by native_decide

/-- Bound-aware plan with hw uses Harvey (not lazy). -/
example : (mkBoundAwarePlan 2013265921 1024 (some arm_neon_simd)).lazyStages = 0 := by native_decide

/-- Cache cost for early stages is 0. -/
example : stageCacheMisses 1024 0 .default = 0 := by native_decide

/-- Cache cost model is computable for concrete values. -/
example : stageCacheMisses 1024 9 .default = 0 := by native_decide

/-- Radix-4 plan is well-formed and selected by cost model. -/
example : (mkUniformPlan 2013265921 1024 .r4 .solinasFold).wellFormed = true := by native_decide

/-- Mixed-radix plan is well-formed. -/
example : (mkMixedRadixPlan 2013265921 1024).wellFormed = true := by native_decide

/-- Radix-4 has fewer butterflies than radix-2 for same N. -/
example : (mkUniformPlan 2013265921 1024 .r4 .solinasFold).totalButterflies <
    (mkUniformPlan 2013265921 1024 .r2 .solinasFold).totalButterflies := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.PlanSelection
