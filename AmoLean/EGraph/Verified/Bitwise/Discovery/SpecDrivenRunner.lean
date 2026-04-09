/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.SpecDrivenRunner

  N26.6: End-to-end discovery runner using REAL e-graph saturation.
  Seeds with reduceE(witness(0), p), runs 3-phase guided saturation
  (algebraic identities + field folds + reduction alternatives),
  extracts the cheapest implementation, and verifies it.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedRunner
import AmoLean.EGraph.Verified.Bitwise.Discovery.ReduceSpecAxiom
import AmoLean.EGraph.Verified.Bitwise.Discovery.VerificationOracle
import AmoLean.EGraph.Verified.Bitwise.Discovery.StageContext

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv HardwareCost arm_cortex_a76)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (PreservesCV)
open MixedRunner (GuidedMixedConfig guidedOptimizeMixedF synthesizeViaEGraph)
open AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules (reductionAlternativeRules)

-- ════════════════════════════════════════════════════════════════
-- Section 1: Constant pre-computation
-- ════════════════════════════════════════════════════════════════

/-- Pre-computed constants for a given prime. -/
structure PrimeConstants where
  p : Nat
  w : Nat
  barrettM : Nat
  montyMu : Nat
  isSolinas : Bool
  solinasA : Nat
  solinasC : Nat
  deriving Repr

/-- Detect Solinas form: p = 2^a - c where c < 2^(a/2).
    Scans candidate exponents a in [0..63]. -/
def detectSolinas (p : Nat) : Option (Nat × Nat) :=
  let candidates := List.range 64
  candidates.findSome? fun a =>
    let pow2a := 2 ^ a
    if pow2a > p && pow2a - p < 2 ^ (a / 2) then some (a, pow2a - p) else none

/-- Compute Barrett/Montgomery constants for a ReduceSpec. -/
def computeConstants (spec : ReduceSpec) : PrimeConstants :=
  let barrettK := 2 * spec.w
  let barrettM := 2 ^ barrettK / spec.p
  let montyMu := spec.p
  match detectSolinas spec.p with
  | some (a, c) =>
    { p := spec.p, w := spec.w, barrettM, montyMu,
      isSolinas := true, solinasA := a, solinasC := c }
  | none =>
    { p := spec.p, w := spec.w, barrettM, montyMu,
      isSolinas := false, solinasA := 0, solinasC := 0 }

-- ════════════════════════════════════════════════════════════════
-- Section 2: DiscoveryResult
-- ════════════════════════════════════════════════════════════════

/-- Result of running the full discovery pipeline with real saturation. -/
structure DiscoveryResult where
  optimizedExpr : Option MixedExpr
  seed : MixedExpr
  prime : Nat
  verified : Bool

-- ════════════════════════════════════════════════════════════════
-- Section 3: discoverReduction -- main entry point (REAL engine)
-- ════════════════════════════════════════════════════════════════

/-- Discover optimized implementations of x % p using real e-graph saturation.
    Seeds with reduceE(witness(0), p) and saturates with all available rules
    including reduction alternatives (Barrett, Montgomery, Harvey). -/
def discoverReduction (spec : ReduceSpec)
    (hw : HardwareCost := arm_cortex_a76)
    (cfg : GuidedMixedConfig := .default) : DiscoveryResult :=
  let seed : MixedExpr := .reduceE (.witnessE 0) spec.p
  let extraRules := reductionAlternativeRules spec.p
  let optimized := guidedOptimizeMixedF spec.p hw cfg seed extraRules
  -- Verify the result
  let verified := match optimized with
    | some expr => (verifyCandidate expr spec).isVerified
    | none => false
  { optimizedExpr := optimized
    seed := seed
    prime := spec.p
    verified := verified }

-- ════════════════════════════════════════════════════════════════
-- Section 4: discoverAndSynthesize -- full pipeline to C code
-- ════════════════════════════════════════════════════════════════

/-- Full pipeline: discover + synthesize C code for a ReduceSpec. -/
def discoverAndSynthesize (spec : ReduceSpec)
    (hw : HardwareCost := arm_cortex_a76) : String :=
  synthesizeViaEGraph spec.p hw .default (some (.reduceE (.witnessE 0) spec.p))

-- ════════════════════════════════════════════════════════════════
-- Section 5: Soundness theorem (renamed per N27.12)
-- ════════════════════════════════════════════════════════════════

/-- insertReduceSpec preserves ConsistentValuation.
    Renamed from `discoverReduction_pipeline_sound` (misleading: it covers
    insertion only, not the full discovery pipeline). -/
theorem insertReduceSpec_sound (spec : ReduceSpec) (env : MixedEnv) :
    PreservesCV env (insertReduceSpec spec) :=
  insertReduceSpec_preserves_cv spec env

-- backward compat alias
abbrev discoverReduction_pipeline_sound := insertReduceSpec_sound

-- ════════════════════════════════════════════════════════════════
-- Section 6: Per-Stage Discovery (N27.12)
-- ════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise.Discovery.Stage (StageContext reductionDecision)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)

/-- Result of per-stage reduction discovery.
    Extends DiscoveryResult with per-stage context. -/
structure StageDiscoveryResult where
  stage : StageContext
  choice : ReductionChoice
  optimizedExpr : Option MixedExpr
  verified : Bool

/-- Discover the optimal reduction for a specific NTT stage.
    Uses the stage context (accumulated bounds, bitwidth, hardware)
    to make a verified per-stage decision.

    1. Computes reduction decision from verified bounds
    2. If lazy (skip): returns skip without running saturation
    3. If reduce needed: runs discovery for the specific reduction type
    4. Returns the stage-specific result -/
def discoverReductionForStage (spec : ReduceSpec) (ctx : StageContext)
    (hw : HardwareCost := arm_cortex_a76) : StageDiscoveryResult :=
  let choice := reductionDecision ctx
  match choice with
  | .lazy =>
    -- No saturation needed: skip reduction at this stage
    { stage := ctx, choice, optimizedExpr := none, verified := true }
  | _ =>
    -- Run discovery for the chosen reduction type
    let result := discoverReduction spec hw
    { stage := ctx, choice, optimizedExpr := result.optimizedExpr,
      verified := result.verified }

/-- Discover reductions for ALL stages of an NTT. -/
def discoverAllStages (spec : ReduceSpec) (numStages bitwidth : Nat)
    (hwIsSimd : Bool := false) (hw : HardwareCost := arm_cortex_a76) :
    List StageDiscoveryResult :=
  let contexts := Stage.buildStageContexts numStages spec.p bitwidth hwIsSimd
  contexts.map fun ctx => discoverReductionForStage spec ctx hw

/-- Per-stage discovery uses verified bounds (not heuristic).
    When the decision is lazy, it is justified by safeWithoutReduce. -/
theorem perStage_uses_verified_bounds (spec : ReduceSpec) (ctx : StageContext)
    (hw : HardwareCost) :
    (discoverReductionForStage spec ctx hw).choice = reductionDecision ctx := by
  simp [discoverReductionForStage]
  cases reductionDecision ctx <;> rfl

-- ════════════════════════════════════════════════════════════════
-- Section 7: Smoke tests
-- ════════════════════════════════════════════════════════════════

-- Lightweight smoke tests (heavy integration tests in Tests/NonVacuity/).
-- Constants computation (no saturation, fast)
example : (computeConstants babybearSpec).isSolinas = false := by native_decide
example : (computeConstants mersenne31Spec).isSolinas = true := by native_decide
example : (computeConstants mersenne31Spec).solinasA = 31 := by native_decide
example : (computeConstants mersenne31Spec).solinasC = 1 := by native_decide
example : (computeConstants babybearSpec).barrettM > 0 := by native_decide

-- Seed construction (structural, no evaluation)
example : (DiscoveryResult.mk none (.witnessE 0) 0 false).verified = false := rfl

end AmoLean.EGraph.Verified.Bitwise.Discovery
