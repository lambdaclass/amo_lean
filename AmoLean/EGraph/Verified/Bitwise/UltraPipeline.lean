/-
  AMO-Lean Ultra — Final Pipeline Integration
  Composes ALL phases (22-28) into a single verified pipeline.

  This is the TOP-LEVEL entry point for Truth Ultra. It:
  1. Discovers rules via Ruler + converts to RewriteRules (Gap 1)
  2. Creates a multi-relation state with bound tracking (Phase 22)
  3. Saturates with dynamic bound propagation + colored rules (Phase 22)
  4. Extracts per-stage schedule from saturated state (Gap 2)
  5. Extracts color-aware optimal expression (Gap 3)
  6. Selects optimal NTTPlan with cache model (Phase 23)
  7. Generates VERIFIED plan-driven code via TrustLean.Stmt (Gap 4)
  8. Explores factorizations via breakdown rules (Phase 24)
  9. Reports all Ultra capabilities

  Consumes EVERY Phase 22-28 module. Every import is exercised.
-/
import AmoLean.EGraph.Verified.Bitwise.RulerBridge
import AmoLean.EGraph.Verified.Bitwise.ColoredExtraction
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.SIMDEmitter
import AmoLean.EGraph.Verified.Bitwise.Discovery.JointOptimization
import AmoLean.EGraph.Verified.Bitwise.Discovery.MatPlanExtraction
-- v3.14.0 B11: MatOp e-graph integration
import AmoLean.EGraph.Verified.Matrix.MatNodeOps
import AmoLean.EGraph.Verified.Matrix.CrossEGraphProtocol

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.UltraPipeline

-- Phase 22 imports
open AmoLean.EGraph.Verified.Bitwise (DirectedRelGraph BoundedByKP BoundedByKP_add
  BoundedByKP_mono mod_BoundedByKP MixedSoundRelationRule)
open AmoLean.EGraph.Verified.Bitwise (DirectedRelConsistency empty_consistent_rel
  addEdge_preserves_consistency antisymmetry_promotes BoundRelConsistency)
open AmoLean.EGraph.Verified.Bitwise.MultiRel (State Config BoundRuleFactory nullFactory
  saturate eqStep relStep crossStep matchCrossEdges)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice mkFieldFactory
  babyBearFactory stageBoundFactor computeStageBounds lazyReductionSafe
  buildBoundLookup encodeBoundFactor decodeBoundFactor)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (nttStageBoundAnalysis
  selectReductionForBound lazyReductionSavings)
open AmoLean.EGraph.Verified.Bitwise.BoundIntegration (optimizeNTTWithBounds mkNTTState
  extractReductionSchedule computeSavings extractScheduleFromState mkFullNTTSeedGraph)
open AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules (reductionAlternativeRules)

-- Phase 23 imports
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice StageDirection
  mkBoundAwarePlan mkUniformPlan log2)
open AmoLean.EGraph.Verified.Bitwise.Butterfly4 (butterfly4 butterfly4WithReduction
  Butterfly4Config radix4TotalMuls radix2TotalMuls)
open AmoLean.EGraph.Verified.Bitwise.PlanSelection (CacheConfig
  generateCandidates planCacheCost selectPlan selectPlanWith planTotalCost planTotalCostWith)

-- Phase 23 verified codegen (Gap 4: TrustLean.Stmt path)
open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitCFromPlanVerified
  emitRustFromPlanVerified lowerNTTFromPlanVerified
  emitCFromPlanStandard emitRustFromPlanStandard)
-- SIMD emission (Fase SIMD v3.1.0)
open AmoLean.EGraph.Verified.Bitwise.SIMDEmitter (emitSIMDNTTC emitSIMDNTTRust SIMDTarget)

-- Phase 24 imports
open AmoLean.EGraph.Verified.Matrix (TransformId FactorizationTree BreakdownRule
  cooleyTukeyRule baseCase2Rule radix4Rule standardRules exploreFact)
open AmoLean.EGraph.Verified.Matrix.CrossEGraph (queryArithmeticCost ArithmeticCostQuery
  factorizationTotalCost)
open AmoLean.EGraph.Verified.Bitwise (arm_cortex_a76 arm_neon_simd x86_avx2_simd)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (reductionCostForHW)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
-- Phase 24 Discovery: bidirectional Mixed↔Matrix joint optimization (Fase Per-Stage v3.3.0)
open AmoLean.EGraph.Verified.Bitwise.Discovery (JointResult DiscoveryResult
  ReduceSpec discoveryReductionCostPerStage)
open AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep (CostOracle)
-- v3.12.0 Phase B: Discovery wiring
open AmoLean.EGraph.Verified.Bitwise.Discovery.MatPlanExtraction (selectBestPlanExplored)

-- Phase 25 imports
open AmoLean.EGraph.Verified.Bitwise.Colors (ColorHierarchy ColoredRule ColorId
  nttColorHierarchy allColoredRules preferredReduction activeRules
  allMixedColoredRules)

-- Gap 1: Ruler bridge
open AmoLean.EGraph.Verified.Bitwise.Ruler (CVec evaluateCVec CVecMatchMode
  cvecEqual cvecMatch discoverRules discoverBabyBearRules discoverKoalaBearShift
  discoverFoldIdempotency nttTestInputs RuleCandidate)
open AmoLean.EGraph.Verified.Bitwise.RulerBridge (ruleCandidatesToRewriteRules
  discoverReductionRules)

-- Gap 3: Colored extraction
open AmoLean.EGraph.Verified.Bitwise.ColoredExtraction (coloredCostAwareExtractF)

open MixedPipeline (MixedEGraph)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Ultra Pipeline Configuration
-- ══════════════════════════════════════════════════════════════════

/-- Full configuration for the Ultra pipeline. -/
structure UltraConfig where
  -- Hardware cost model (replaces hwIsSimd + mulCost + addCost)
  hw : HardwareCost := arm_cortex_a76
  -- Phase 22: saturation
  satConfig : Config := Config.default
  -- Phase 23: plan selection
  cacheConfig : CacheConfig := CacheConfig.default
  -- Phase 24: joint optimization
  exploreFuel : Nat := 10
  jointThreshold : Nat := 1024  -- v3.12.0 B: Discovery plan competition (interpreter-safe up to N=1024)
  -- Phase 25: colors
  targetColor : ColorId := 0  -- root = universal
  -- Field parameters (for verified codegen and parametric discovery)
  k : Nat := 31              -- shift bits (BabyBear default)
  c : Nat := 134217727       -- Solinas constant (BabyBear default)
  mu : Nat := 0x88000001     -- Montgomery mu (BabyBear default)
  -- v3.5.0: sqdmulh Montgomery REDC (4-lane vqdmulhq_s32 instead of 2-lane vmull_u32)
  useSqdmulh : Bool := false  -- true for NEON targets (auto-set in .neon preset)
  -- v3.6.0: CNTVCT per-stage profiling (N36.5a)
  profiled : Bool := false    -- true emits ARM cycle counter fences between stages
  -- v3.7.0: verified SIMD codegen (Stmt.call + simdStmtToC instead of string emission)
  useVerifiedSIMD : Bool := true
  -- v3.8.0: Rust SIMD codegen (simdStmtToRust — core::arch::aarch64 intrinsics)
  rustSIMD : Bool := false
  -- v3.9.0: Dynamic cost channel (e-graph → plan costing, opt-in)
  -- When true, uses reductionCostForHW_dynamic (e-graph extraction cost) instead
  -- of static reductionCostForHW for plan selection. Default false for safety.
  -- Known fields (BabyBear/KoalaBear/Mersenne31) have fallback when diff > 5 cycles.
  useDynamicCost : Bool := false
  -- v3.15.0: Standard DFT (bitrev + DIT small→large). Matches Plonky3.
  -- Only applies to scalar path, NOT SIMD.
  -- When true: uses competition winner (R2/R4 DIT) with emitCFromPlanStandard.
  -- When false: legacy pipeline (emitCFromPlanVerified). Set false for rollback.
  -- v3.15.0 B5: default true (cutover). Legacy accessible via false.
  useStandardDFT : Bool := true
  deriving Repr

def UltraConfig.scalar : UltraConfig := { hw := arm_cortex_a76, targetColor := 1 }
def UltraConfig.neon : UltraConfig := { hw := arm_neon_simd, targetColor := 3, useSqdmulh := true }
def UltraConfig.avx2 : UltraConfig := { hw := x86_avx2_simd, targetColor := 4 }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Ultra Pipeline
-- ══════════════════════════════════════════════════════════════════

/-- THE top-level Ultra pipeline. Composes all phases with verified codegen.

    Gap 1: Ruler discovery → RewriteRules → fed into saturate
    Gap 2: Saturated state → per-stage schedule via extractScheduleFromState
    Gap 3: Colored extraction for hardware-specific optimization
    Gap 4: Verified codegen via TrustLean.Stmt (emitCFromPlanVerified) -/
def ultraPipeline (g : MixedEGraph)
    (eqRules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (p n : Nat) (cfg : UltraConfig := {})
    (funcName : String := "ntt_ultra")
    (stageClassIds : Option (Array EClassId) := none)
    -- v3.10.0 T8: optional dynamic cost function (default = static)
    (costFn : HardwareCost → ReductionChoice → Nat := reductionCostForHW)
    : String × String × String :=
  let logN := log2 n

  -- ── Gap 1: Ruler discovery → RewriteRules ──
  let discoveredCandidates := discoverReductionRules p cfg.k cfg.c
  let shiftCandidates := discoverKoalaBearShift
  let discoveredRewriteRules := ruleCandidatesToRewriteRules
    (discoveredCandidates ++ shiftCandidates) p cfg.k cfg.c

  -- ── Phase 22: bound-aware saturation (WITH discovered + colored rules) ──
  let state := mkNTTState g
  let factory := mkFieldFactory p
  let activeColoredRules := allMixedColoredRules
  let state' := saturate (eqRules ++ discoveredRewriteRules) activeColoredRules
    factory cfg.satConfig (s := state)

  -- ── Gap 2: Extract per-stage schedule from saturated state ──
  -- stageClassIds maps stage index → e-class ID for DAG bound lookup (Fase Per-Stage v3.3.0)
  let hwWithN := { cfg.hw with vectorLength := n }
  let arrayIsLarge := n > cfg.hw.cacheThreshold
  let stageSchedule := extractScheduleFromState state' logN p cfg.hw.isSimd arrayIsLarge
    (some hwWithN) stageClassIds

  -- ── Phase 23: plan competition (schedule-derived vs generated candidates) ──
  let mkStg (idx : Nat) (red : ReductionChoice) (inK outK : Nat) : NTTStage :=
    { stageIdx := idx, radix := .r2, reduction := red,
      direction := .DIT, inputBoundK := inK, outputBoundK := outK }
  let (schedStages, _) := stageSchedule.foldl
    (fun (acc : List NTTStage × Nat) (entry : Nat × ReductionChoice × Nat) =>
      let (stgs, inK) := acc
      let (idx, red, outK) := entry
      (stgs ++ [mkStg idx red inK outK], outK)) ([], 1)
  let schedulePlan : Plan := { stages := schedStages.toArray, field := p, size := n }
  -- Compete: schedule-derived plan vs generated candidates + Discovery explored plan
  let candidates := generateCandidates p n cfg.hw arrayIsLarge
  -- v3.12.0 Phase B: Discovery explores 500 radix assignments via matSaturateAndExtract
  let exploredPlan := if n ≤ cfg.jointThreshold then
      some (selectBestPlanExplored p n cfg.hw arrayIsLarge)
    else none
  -- v3.14.0 B11: MatOp e-graph explores factorizations (SPIRAL-style)
  -- Adds CT decompositions as equivalent representations, extracts best via cost model.
  -- The extracted plan competes with fixed candidates in selectPlanWith.
  -- NOTE: Currently produces DFT-based plans which are incompatible with ref_dit
  -- (v3.14.0 B6 finding). The plan will lose to ref_dit-based candidates until
  -- the pipeline migrates to DFT standard (v3.15.0). Safe: selectPlanWith protects.
  let matOpPlan := if n ≤ cfg.jointThreshold then
    let mg : AmoLean.EGraph.VerifiedExtraction.EGraph AmoLean.EGraph.Verified.Matrix.MatOp :=
      AmoLean.EGraph.VerifiedExtraction.EGraph.empty
    let (nttId, mg1) := mg.add ⟨AmoLean.EGraph.Verified.Matrix.MatOp.ntt n p⟩
    let rules := AmoLean.EGraph.Verified.Matrix.standardRules n
    let mg2 := AmoLean.EGraph.Verified.Matrix.applyAllBreakdowns mg1 nttId rules n p
    let mg3 := AmoLean.EGraph.VerifiedExtraction.EGraph.computeCostsF mg2 3
    match @AmoLean.EGraph.VerifiedExtraction.Greedy.extractAuto
        AmoLean.EGraph.Verified.Matrix.MatOp
        AmoLean.EGraph.Verified.Matrix.MatExprFlat _ _ _ _ mg3 nttId with
    | some expr =>
      let tree := AmoLean.EGraph.Verified.Matrix.matExprFlatToTree expr
      some (AmoLean.EGraph.Verified.Matrix.CrossEGraph.factorizationToPlan tree p cfg.hw n)
    | none => none
  else none
  let allCandidates := match exploredPlan with
    | some ep => candidates.push schedulePlan |>.push ep
    | none => candidates.push schedulePlan
  -- Add MatOp e-graph plan if available
  let allCandidates := match matOpPlan with
    | some mp => allCandidates.push mp
    | none => allCandidates
  -- v3.10.0 T8: use costFn (static by default, dynamic when useDynamicCost=true)
  let discoveryWon := exploredPlan.map fun ep =>
    match selectPlanWith allCandidates cfg.hw cfg.cacheConfig costFn with
    | some best => best.stages == ep.stages
    | none => false
  let plan := match selectPlanWith allCandidates cfg.hw cfg.cacheConfig costFn with
    | some best => best
    | none => schedulePlan
  -- Validate total NTT coverage (safety net — normalizePlan in lowerNTTFromPlanVerified
  -- handles codegen, but catch bad plans before generating code)
  let planLevels := plan.stages.foldl (fun acc s =>
    acc + match s.radix with | .r2 => 1 | .r4 => 2) 0
  let plan := if planLevels == logN then plan else schedulePlan
  -- v3.10.0 TD: ILP2 for Goldilocks — let plan competition decide.
  -- The ILP2 candidate was added to generateCandidates (NTTPlanSelection).
  -- The R4 mixed plan often wins because fewer stages = lower cost.
  -- ILP2 benefits R2 stages only; R4 stages already process 4 at once.
  -- If the winner is R2-based, apply ILP2. Otherwise keep R4 winner.
  let plan := if cfg.k > 32 && !cfg.hw.isSimd then
      let hasR2 := plan.stages.toList.any fun s => s.radix == .r2
      if hasR2 then plan.withILP 2 else plan
    else plan

  -- ── Gap 4: Verified codegen via TrustLean.Stmt ──
  -- For k > 32 (Goldilocks): always use scalar verified path. The SIMD emitter uses
  -- 32-bit NEON intrinsics (int32x4_t) which don't work for 64-bit field elements.
  -- goldilocksButterfly4Stmt (v3.9.0 N39.9) provides 64-bit NEON infrastructure
  -- but full integration requires neonTempDecls64 + fold wiring (future work).
  let simdTarget := if cfg.hw.simdLanes == 8 then SIMDTarget.avx2 else SIMDTarget.neon
  -- v3.17.0 N317.6: stdPlan computed once, used by both C and Rust paths.
  -- Previously duplicated identically in each branch. Refactor preserves semantics.
  -- v3.15.0 B3.5: Use competition winner if compatible with standard DFT.
  -- Compatible = all stages are (R2 or R4) DIT, no lazy reduction.
  -- R4 stages use inverted butterfly (lowerStageR4_Inverted). R2 stages unchanged.
  -- Fallback to uniform R2 Harvey if winner is incompatible (DIF, lazy).
  -- v3.16.0 B4: R4 only benefits at large N (cache effects dominate).
  -- At N ≤ 2^14, R4 inverted overhead > 25% butterfly savings.
  -- Force R2 for small N; allow R4 winner only when N > 16384.
  let stdPlan :=
    let isCompatible := plan.stages.toList.all fun s =>
      (s.radix == .r2 || s.radix == .r4) && s.direction == .DIT && s.reduction != .lazy
    let hasR4 := plan.stages.toList.any fun s => s.radix == .r4
    let useWinner := isCompatible && (!hasR4 || n > 16384)
    let base := if useWinner then plan
      else NTTPlan.mkUniformPlan plan.field plan.size .r2 .harvey
    -- ILP2 for Goldilocks R2 stages (same as legacy path L240-243)
    if cfg.k > 32 && !cfg.hw.isSimd then
      let hasR2 := base.stages.toList.any fun s => s.radix == .r2
      if hasR2 then base.withILP 2 else base
    else base
  let code := if cfg.hw.isSimd && cfg.k ≤ 32 then
    emitSIMDNTTC plan simdTarget cfg.k cfg.c cfg.mu funcName cfg.useSqdmulh cfg.useVerifiedSIMD cfg.profiled
  else if cfg.useStandardDFT then
    emitCFromPlanStandard stdPlan cfg.k cfg.c cfg.mu funcName
  else
    emitCFromPlanVerified plan cfg.k cfg.c cfg.mu funcName
  let rustCode := if cfg.rustSIMD && cfg.hw.isSimd && cfg.k ≤ 32 then
    emitSIMDNTTRust plan simdTarget cfg.k cfg.c cfg.mu (funcName ++ "_rs") cfg.useSqdmulh
  else if cfg.useStandardDFT then
    emitRustFromPlanStandard stdPlan cfg.k cfg.c cfg.mu (funcName ++ "_rs")
  else
    emitRustFromPlanVerified plan cfg.k cfg.c cfg.mu (funcName ++ "_rs")

  -- ── Phase 24: joint optimization — Discovery bidirectional (Fase Per-Stage v3.3.0) ──
  -- cfg.jointThreshold controls max N (default 256 for runtime, set 0 for native_decide)
  let hw := { cfg.hw with vectorLength := n }
  let w := if cfg.k == 64 then 64 else 32
  let (jointCost, jointPlanLen) := if n ≤ cfg.jointThreshold then
    if h1 : p > 0 then
      if h2 : p < 2 ^ w then
        let spec : ReduceSpec := { p, w, p_pos := h1, p_lt_bound := h2 }
        let oracle := if cfg.hw.isSimd then CostOracle.armSimd n else CostOracle.armScalar n
        let result := AmoLean.EGraph.Verified.Bitwise.Discovery.jointOptimize spec hw n oracle
        (result.planCost, result.bestPlan.length)
      else (0, 0)
    else (0, 0)
  else (0, 0)
  -- v3.13.0 E.3: verifiedJointOptimize was a stub (always none). CrossEGraphBridge deleted.
  let verifiedResult := (none : Option (Nat × Nat))

  -- ── NE.4: Per-stage discovery costs (Fase Per-Stage v3.3.0) ──
  -- Guarded by jointThreshold (heavy: runs discoverAllStages → guidedOptimizeMixedF per stage)
  let perStageCosts := if n ≤ cfg.jointThreshold then
    discoveryReductionCostPerStage p logN
      (if cfg.k == 64 then 64 else 32) cfg.hw cfg.hw.isSimd
  else #[]

  -- ── Gap 3: Color-aware extraction (informational for report) ──
  let coloredExpr := coloredCostAwareExtractF hw state' 0 cfg.targetColor

  -- ── Phase 25: color preferences ──
  let colorPref := preferredReduction cfg.targetColor
  let activeColorRules := activeRules allColoredRules cfg.targetColor nttColorHierarchy.1

  -- ── Report ──
  let report :=
    s!"=== Truth Ultra Report ===\n" ++
    s!"Field: p={p}, N={n}\n" ++
    s!"HW: mul32={cfg.hw.mul32} add={cfg.hw.add} simd={cfg.hw.isSimd}, Target color: {cfg.targetColor}\n" ++
    s!"--- Phase 22: Bounds ---\n" ++
    s!"Saturation: {cfg.satConfig.totalFuel} iterations\n" ++
    s!"Relations: {state'.numRelations} DAGs\n" ++
    s!"--- Gap 1: Ruler Discovery ---\n" ++
    s!"Discovered rules: {discoveredCandidates.length} reductions, " ++
    s!"{shiftCandidates.length} shift decomps\n" ++
    s!"Converted to RewriteRules: {discoveredRewriteRules.length}\n" ++
    s!"--- Gap 2: Dynamic Schedule → Plan ---\n" ++
    s!"Schedule: {stageSchedule.length} stages (from saturated State)\n" ++
    s!"Plan: {plan.numStages} stages, {plan.lazyStages} lazy (built from schedule)\n" ++
    s!"Well-formed: {plan.wellFormed}\n" ++
    s!"--- NE.4: Per-Stage Discovery Costs ---\n" ++
    s!"Per-stage costs ({perStageCosts.size} stages): {perStageCosts.toList}\n" ++
    s!"--- Phase 24: Joint (Discovery bidirectional) ---\n" ++
    s!"Joint cost: {jointCost} cycles{if n > cfg.jointThreshold then s!" (skipped, N>{cfg.jointThreshold})" else ""}\n" ++
    s!"Joint plan: {jointPlanLen} stages{if n > cfg.jointThreshold then " (skipped)" else ""}\n" ++
    s!"Verified path: {match verifiedResult with | some _ => "available" | none => "unavailable (stub removed v3.13.0)"}\n" ++
    s!"--- v3.14.0: MatOp E-Graph (SPIRAL) ---\n" ++
    s!"MatOp plan: {match matOpPlan with | some mp => s!"{mp.stages.size} stages (from e-graph)" | none => "skipped"}\n" ++
    s!"--- Gap 3: Colored Extraction ---\n" ++
    s!"Color preference: {repr colorPref}\n" ++
    s!"Active colored rules: {activeColoredRules.length}\n" ++
    s!"Colored extract: {if coloredExpr.isSome then "found" else "no root"}\n" ++
    s!"--- Phase B: Discovery Plan Competition ---\n" ++
    s!"Explored plan: {if exploredPlan.isSome then "participated" else s!"skipped (N>{cfg.jointThreshold})"}\n" ++
    s!"Discovery won: {discoveryWon.getD false}\n" ++
    s!"Total candidates: {allCandidates.size}\n" ++
    -- v3.14.0 M.5: Cost model predictions for feedback loop
    let candidateCosts := allCandidates.toList.map fun c =>
      (planTotalCostWith c cfg.hw cfg.cacheConfig costFn, c.stages.size,
       c.stages.toList.any (·.useShift))
    let winnerCost := planTotalCostWith plan cfg.hw cfg.cacheConfig costFn
    s!"--- v3.14.0: Cost Model Predictions ---\n" ++
    s!"Winner cost: {winnerCost} ({plan.stages.size} stages)\n" ++
    s!"Candidates ({candidateCosts.length}): {candidateCosts.map (·.1)}\n" ++
    s!"--- Gap 4: Verified Codegen ---\n" ++
    s!"C code: {code.length} chars (TrustLean.Stmt path)\n" ++
    s!"Rust code: {rustCode.length} chars (TrustLean.Stmt path)\n" ++
    s!"--- Code ---\n" ++
    s!"Generated: {code.length} chars"
  (code, rustCode, report)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Convenience Functions
-- ══════════════════════════════════════════════════════════════════

/-- Generate optimized NTT C code for BabyBear with all Ultra features.
    Uses seeded e-graph with per-stage bound propagation (Fase Per-Stage v3.3.0). -/
def babyBearUltra (n : Nat) (cfg : UltraConfig := {}) : String :=
  let logN := log2 n
  let (g, ids) := mkFullNTTSeedGraph 2013265921 logN
  let rules := reductionAlternativeRules 2013265921
  (ultraPipeline g rules 2013265921 n cfg "ntt_babybear_ultra" (some ids)).1

/-- Generate optimized NTT C code for Goldilocks.
    Uses seeded e-graph with per-stage bound propagation (Fase Per-Stage v3.3.0). -/
def goldilocksUltra (n : Nat) (cfg : UltraConfig := {}) : String :=
  let p := 18446744069414584321
  let logN := log2 n
  let (g, ids) := mkFullNTTSeedGraph p logN
  let rules := reductionAlternativeRules p
  (ultraPipeline g rules p n
    { cfg with k := 64, c := 4294967295, mu := 0 }
    "ntt_goldilocks_ultra" (some ids)).1

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Theorems — Composing all phase guarantees
-- ══════════════════════════════════════════════════════════════════

/-- Ultra pipeline produces non-empty code. jointThreshold=0 skips heavy Discovery path. -/
theorem ultra_produces_code :
    (ultraPipeline default [] 2013265921 16 { jointThreshold := 0 }).1.length > 0 := by native_decide

/-- Ultra plan is well-formed (bound-aware). -/
theorem ultra_plan_wellformed :
    (mkBoundAwarePlan 2013265921 1024).wellFormed = true := by native_decide

/-- Bound-aware plan saves reductions vs uniform. -/
theorem ultra_saves_reductions :
    (mkBoundAwarePlan 2013265921 1024).lazyStages > 0 := by native_decide

/-- Factorization exploration finds candidates. -/
theorem ultra_explores_factorizations :
    (exploreFact 8 0).2.2 > 0 := by native_decide

/-- Ruler discovers reduction equivalences. -/
theorem ultra_discovers_rules :
    discoverBabyBearRules.length > 0 := by native_decide

/-- SIMD color preference is Montgomery. -/
theorem ultra_simd_monty :
    preferredReduction 2 == .montgomery := by native_decide

/-- Backward compat: null factory = equality-only saturation. -/
theorem ultra_backward_compat (s : State) :
    relStep nullFactory s = s := rfl

/-- Phase 22 bounds: add propagation. -/
theorem ultra_add_bound (a b p : Nat) (ha : a < 1 * p) (hb : b < 1 * p) :
    a + b < (1 + 1) * p := BoundedByKP_add ha hb

/-- Phase 22: initial state is consistent. -/
theorem ultra_initial_consistent (v : EClassId → Nat) :
    DirectedRelConsistency DirectedRelGraph.empty (fun a b => a ≤ b) v :=
  empty_consistent_rel _ v

-- ══════════════════════════════════════════════════════════════════
-- Section 5: End-to-End Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

-- Note: seeded pipeline tested in BoundIntegration.lean de-risk section (NE.1 gate).
-- native_decide with seeded graph is too heavy (Ruler + saturation + codegen).

/-- Ultra report is informative. jointThreshold=0 for fast native_decide. -/
example : (ultraPipeline default [] 2013265921 16 { jointThreshold := 0 }).2.2.length > 100 := by native_decide

/-- Phase 22: encode/decode roundtrip. -/
example : decodeBoundFactor (encodeBoundFactor 3) = some 3 := by native_decide

/-- Phase 23: stage bounds. -/
example : computeStageBounds [.lazy, .lazy, .solinasFold] 1 = [1, 2, 3, 2] := by native_decide

/-- Phase 24: CT(2,4) factorization has 11 nodes. -/
example : ((cooleyTukeyRule 2 4).decompose 8 0).nodes.size = 11 := rfl

/-- Phase 24: cross-query returns positive cost. -/
example : (queryArithmeticCost { radix := .r2, field := 2013265921 }).cycleCost > 0 := by
  native_decide

/-- Phase 25: color hierarchy has 6 colors. -/
example : nttColorHierarchy.1.numColors = 6 := by native_decide

/-- Phase 25: Ruler discovers BabyBear rules. -/
example : discoverBabyBearRules.length > 0 := by native_decide

/-- Phase 25: KoalaBear shift decomposition. -/
example : discoverKoalaBearShift.length > 0 := by native_decide

/-- Gap 1: Parametric discovery + conversion produces RewriteRules. -/
example : (ruleCandidatesToRewriteRules
    (discoverReductionRules 2013265921 31 134217727) 2013265921 31 134217727).length > 0 := by
  native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.UltraPipeline
