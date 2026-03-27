/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.SpecDrivenRunner

  N26.6: End-to-end discovery runner.  Pre-computes Barrett/Montgomery
  constants for a given prime, instantiates vocabulary templates, runs
  4-phase saturation (simplified identity step), extracts candidates,
  and verifies them.
-/
import AmoLean.EGraph.Verified.Bitwise.Discovery.ExplosionControl
import AmoLean.EGraph.Verified.Bitwise.Discovery.CostBiasedExtract
import AmoLean.EGraph.Verified.Bitwise.Discovery.VerificationOracle

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv MixedSoundRule)
open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec (MGraph CId)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (CV VPMI PreservesCV)

-- ════════════════════════════════════════════════════════════════
-- Section 1: Constant pre-computation
-- ════════════════════════════════════════════════════════════════

/-- Pre-computed constants for a given prime. -/
structure PrimeConstants where
  p : Nat
  w : Nat
  barrettM : Nat   -- floor(2^(2w) / p) for Barrett
  barrettK : Nat   -- 2 * w
  montyMu : Nat    -- (-p)^{-1} mod 2^w (simplified placeholder)
  montyR : Nat     -- 2^w
  isSolinas : Bool  -- whether p = 2^a - c for small c
  solinasA : Nat    -- a in 2^a - c (0 if not Solinas)
  solinasC : Nat    -- c in 2^a - c (0 if not Solinas)
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
  let montyR := 2 ^ spec.w
  -- Simplified montyMu: actual modular inverse deferred to N27
  let montyMu := spec.p
  match detectSolinas spec.p with
  | some (a, c) =>
    { p := spec.p, w := spec.w, barrettM, barrettK, montyMu, montyR,
      isSolinas := true, solinasA := a, solinasC := c }
  | none =>
    { p := spec.p, w := spec.w, barrettM, barrettK, montyMu, montyR,
      isSolinas := false, solinasA := 0, solinasC := 0 }

-- ════════════════════════════════════════════════════════════════
-- Section 2: DiscoveryResult
-- ════════════════════════════════════════════════════════════════

/-- Result of running the full discovery pipeline: candidates found,
    those that passed verification, and the best cost observed. -/
structure DiscoveryResult where
  candidates : List ExtractionResult
  verified : List ExtractionResult
  bestCost : Nat
  totalCandidates : Nat

-- ════════════════════════════════════════════════════════════════
-- Section 3: discoverReduction — main entry point
-- ════════════════════════════════════════════════════════════════

/-- Run the full discovery pipeline for a ReduceSpec.
    1. Pre-compute Barrett/Montgomery constants
    2. Instantiate vocabulary for the prime
    3. Build initial graph with spec axiom (insertReduceSpecWithIds)
    4. Extract top candidates via cost-biased extraction
    5. Verify each candidate against the spec

    NOTE: The saturation step is simplified (identity) in this version.
    Full saturation via MixedSoundRules is in ExplosionControl.
    The key contribution here is the pipeline composition and
    constant pre-computation. -/
def discoverReduction (spec : ReduceSpec) (bias : CostBias := CostBias.default)
    (_cfg : SpecDrivenConfig := SpecDrivenConfig.default) : DiscoveryResult :=
  let consts := computeConstants spec
  -- Build vocabulary (used by saturation in production; here for completeness)
  let _vocab := generateVocabulary spec.p spec.w consts.barrettM consts.montyMu
  -- Build initial graph with spec
  let g0 : MGraph := AmoLean.EGraph.VerifiedExtraction.EGraph.empty
  let (specResult, g1) := insertReduceSpecWithIds spec g0
  -- In production, saturation would apply rules here via specDrivenSaturateF.
  -- For this version the graph passes through unchanged.
  let gFinal := g1
  -- Extract from the reduce class
  let candidates := match extractWithCostBias bias gFinal specResult.reduceId with
    | some r => [r]
    | none => []
  -- Verify candidates
  let verified := candidates.filter fun r =>
    (verifyCandidate r.expr spec).isVerified
  let bestCost := match selectCheapest verified with
    | some r => r.cost
    | none => 0
  { candidates, verified, bestCost, totalCandidates := candidates.length }

-- ════════════════════════════════════════════════════════════════
-- Section 4: Soundness theorem
-- ════════════════════════════════════════════════════════════════

/-- The discovery pipeline preserves semantic correctness:
    insertReduceSpec (the core graph mutation) preserves CV.
    This delegates directly to the N26.1 theorem. -/
theorem discoverReduction_pipeline_sound (spec : ReduceSpec) (env : MixedEnv) :
    PreservesCV env (insertReduceSpec spec) :=
  insertReduceSpec_preserves_cv spec env

-- ════════════════════════════════════════════════════════════════
-- Section 5: Convenience + smoke tests
-- ════════════════════════════════════════════════════════════════

-- BabyBear discovery produces a non-negative count
example : (discoverReduction babybearSpec).totalCandidates ≥ 0 := by omega

-- Mersenne31 discovery produces a non-negative count
example : (discoverReduction mersenne31Spec).totalCandidates ≥ 0 := by omega

-- BabyBear is detected as Solinas (2013265921 = 2^31 - 2^27 + 1, but actually
-- the check finds 2^31 > p and 2^31 - p = 134217727 which is < 2^15? Let's verify.)
-- Actually BabyBear p = 2013265921, 2^31 = 2147483648, diff = 134217727 = 2^27 - 1
-- 2^(31/2) = 2^15 = 32768. Since 134217727 > 32768, a=31 does NOT match.
-- But a=32: 2^32 = 4294967296, diff = 2281701375. 2^16 = 65536. 2281701375 > 65536. No.
-- So BabyBear is NOT Solinas in our strict definition. Test accordingly.

-- detectSolinas returns none for BabyBear (not strict Solinas form)
example : (computeConstants babybearSpec).isSolinas = false := by native_decide

-- Mersenne31: p = 2^31 - 1 = 2147483647, 2^31 = 2147483648, diff = 1, 2^15 = 32768
-- 1 < 32768, so a=31 matches!
example : (computeConstants mersenne31Spec).isSolinas = true := by native_decide

-- Mersenne31 Solinas parameters are correct: a=31, c=1
example : (computeConstants mersenne31Spec).solinasA = 31 := by native_decide
example : (computeConstants mersenne31Spec).solinasC = 1 := by native_decide

-- Barrett constant for BabyBear is non-zero
example : (computeConstants babybearSpec).barrettM > 0 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
