/-
  AmoLean.EGraph.Verified.Bitwise.MixedRunner — End-to-End Guided E-Graph Pipeline

  v3.5.1: Full 3-phase guided saturation with auto-fuel adjustment.
  Phase 1: algebraic/bitwise identities (10 pattern rules)
  Phase 2: field-specific folds (1-3 pattern rules per prime)
  Phase 3: (extensible — shift-add rules once converted to pattern form)

  Pipeline: build → 3-phase saturate → cost-aware extract → emit C
-/
import AmoLean.EGraph.Verified.Bitwise.MixedSaturation
import AmoLean.EGraph.Verified.Bitwise.MixedPatternRules
import AmoLean.EGraph.Verified.Bitwise.FieldFoldPatternRules
import AmoLean.EGraph.Verified.Bitwise.MixedEGraphBuilder
import AmoLean.EGraph.Verified.Bitwise.CostExtraction
import AmoLean.EGraph.Verified.Bitwise.MixedExprToStmt

namespace MixedRunner

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.VerifiedExtraction.Greedy (extractAuto)
open AmoLean.EGraph.Verified.Bitwise
  (MixedNodeOp HardwareCost arm_cortex_a76 riscv_sifive_u74 fpga_dsp48e2
   mersenne31_prime babybear_prime goldilocks_prime emitCFunction)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open CostExtraction (costAwareExtractAuto hwCostFn)
open MixedEMatch (RewriteRule)
open MixedSaturation (saturateMixedF rebuildF)
open MixedEGraphBuilder (addMixedExpr buildEGraph)
open MixedPatternRules (allBitwisePatternRules allBitwisePatternRulesWithBridges)
open FieldFoldPatternRules (fieldFoldPatternRules allFieldFoldPatternRules)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Guided configuration
-- ══════════════════════════════════════════════════════════════════

/-- Configuration for the 3-phase guided saturation pipeline. -/
structure GuidedMixedConfig where
  /-- E-match fuel (depth for pattern matching) -/
  ematchFuel : Nat := 20
  /-- Phase 1: algebraic identities (AND/OR/XOR comm, shift compose, etc.) -/
  phase1Iters : Nat := 5
  phase1Rebuild : Nat := 3
  /-- Phase 2: field-specific fold rules -/
  phase2Iters : Nat := 10
  phase2Rebuild : Nat := 5
  /-- Phase 3: extensible (shift-add once pattern-converted) -/
  phase3Iters : Nat := 5
  phase3Rebuild : Nat := 3
  /-- Cost extraction fuel -/
  costFuel : Nat := 50
  deriving Repr, Inhabited

/-- Default: balanced for BabyBear/Mersenne31 (small word size). -/
def GuidedMixedConfig.default : GuidedMixedConfig := {}

/-- Aggressive: more fuel for Goldilocks (64-bit, larger expressions). -/
def GuidedMixedConfig.aggressive : GuidedMixedConfig :=
  { ematchFuel := 30, phase1Iters := 10, phase1Rebuild := 5,
    phase2Iters := 20, phase2Rebuild := 8,
    phase3Iters := 10, phase3Rebuild := 5, costFuel := 100 }

/-- Conservative: minimal fuel, fast. -/
def GuidedMixedConfig.conservative : GuidedMixedConfig :=
  { ematchFuel := 10, phase1Iters := 3, phase1Rebuild := 2,
    phase2Iters := 5, phase2Rebuild := 3,
    phase3Iters := 2, phase3Rebuild := 2, costFuel := 30 }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Seed expression builders
-- ══════════════════════════════════════════════════════════════════

/-- Simple seed: just witness(0) — a variable representing input x. -/
def mkCanonicalInput : MixedExpr := .witnessE 0

/-- Richer seed: x &&& (2^k - 1) — masked input (common in field reduction).
    This gives the saturation more structure to work with. -/
def mkMaskedInput (k : Nat) : MixedExpr :=
  .bitAndE (.witnessE 0) (.constMaskE k)

/-- Full fold seed: the complete Solinas fold expression.
    (x >> k) * c + (x &&& (2^k - 1)) -/
def mkSolinasFoldSeed (k c : Nat) : MixedExpr :=
  .addE
    (.mulE (.shiftRightE (.witnessE 0) k) (.constE c))
    (.bitAndE (.witnessE 0) (.constMaskE k))

-- ══════════════════════════════════════════════════════════════════
-- Section 3: 3-phase guided optimization pipeline
-- ══════════════════════════════════════════════════════════════════

/-- Core 3-phase guided optimization pipeline.
    Phase 1: Apply algebraic/bitwise identities (simplification)
    Phase 2: Apply field-specific fold rules (the key optimization)
    Phase 3: Apply additional rules (extensible)
    Then: cost-aware extraction. -/
def guidedOptimizeMixedF (p : Nat) (hw : HardwareCost)
    (cfg : GuidedMixedConfig := .default)
    (expr : MixedExpr)
    (extraRules : List (RewriteRule MixedNodeOp) := []) : Option MixedExpr :=
  let (g, rootId) := buildEGraph expr
  -- Phase 1: algebraic/bitwise identities (10 rules with bridges)
  let g1 := saturateMixedF cfg.ematchFuel cfg.phase1Iters cfg.phase1Rebuild g
    allBitwisePatternRulesWithBridges
  -- Phase 2: field-specific fold rules
  let g2 := saturateMixedF cfg.ematchFuel cfg.phase2Iters cfg.phase2Rebuild g1
    (fieldFoldPatternRules p)
  -- Phase 3: extra rules (shift-add, user-provided, etc.)
  let g3 := if extraRules.isEmpty then g2
    else saturateMixedF cfg.ematchFuel cfg.phase3Iters cfg.phase3Rebuild g2 extraRules
  -- Cost-aware extraction
  costAwareExtractAuto hw g3 rootId cfg.costFuel

/-- Legacy single-phase pipeline (backward compat). -/
def optimizeMixedF (ematchFuel maxIter rebuildFuel costFuel : Nat)
    (expr : MixedExpr) (rules : List (RewriteRule MixedNodeOp))
    (hw : HardwareCost) : Option MixedExpr :=
  let (g, rootId) := buildEGraph expr
  let g_sat := saturateMixedF ematchFuel maxIter rebuildFuel g rules
  costAwareExtractAuto hw g_sat rootId costFuel

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Full pipeline with C emission
-- ══════════════════════════════════════════════════════════════════

/-- Identity constLookup: constGate(n) emits literal n.
    In the Solinas pipeline, constGate values ARE the literal constants
    (e.g., constGate(134217727) = the BabyBear correction constant 2^27-1). -/
private def identityConstLookup : Nat → Int := fun n => ↑n

/-- Full pipeline: prime + hardware → optimized C code.
    Uses 3-phase guided saturation with Solinas fold seed. -/
def synthesizeViaEGraph (p : Nat) (hw : HardwareCost)
    (cfg : GuidedMixedConfig := .default)
    (seed : Option MixedExpr := none) : String :=
  let inputExpr := match seed with
    | some e => e
    | none => mkCanonicalInput
  match guidedOptimizeMixedF p hw cfg inputExpr with
  | some optExpr =>
    emitCFunction s!"reduce_mod_{p}" "x" optExpr identityConstLookup
  | none =>
    emitCFunction s!"reduce_mod_{p}" "x" inputExpr identityConstLookup

/-- Multi-target synthesis: emit C for all 3 hardware targets. -/
def synthesizeMultiTarget (p : Nat) (cfg : GuidedMixedConfig := .default)
    : List (String × String) :=
  let targets := [("ARM_Cortex_A76", arm_cortex_a76),
                  ("RISC-V_SiFive_U74", riscv_sifive_u74),
                  ("FPGA_DSP48E2", fpga_dsp48e2)]
  targets.map fun (name, hw) => (name, synthesizeViaEGraph p hw cfg)

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Per-field convenience (with Solinas fold seed)
-- ══════════════════════════════════════════════════════════════════

def synthesizeMersenne31 (hw : HardwareCost := arm_cortex_a76)
    (cfg : GuidedMixedConfig := .default) : String :=
  -- Mersenne31: 2^31 - 1, fold seed: (x >> 31) + (x & (2^31-1))
  synthesizeViaEGraph mersenne31_prime hw cfg
    (some (mkSolinasFoldSeed 31 1))

def synthesizeBabyBear (hw : HardwareCost := arm_cortex_a76)
    (cfg : GuidedMixedConfig := .default) : String :=
  -- BabyBear: 2^31 - 2^27 + 1, c = 2^27-1 = 134217727
  synthesizeViaEGraph babybear_prime hw cfg
    (some (mkSolinasFoldSeed 31 134217727))

def synthesizeGoldilocks (hw : HardwareCost := arm_cortex_a76)
    (cfg : GuidedMixedConfig := .default) : String :=
  -- Goldilocks: 2^64 - 2^32 + 1, c = 2^32-1 = 4294967295
  synthesizeViaEGraph goldilocks_prime hw cfg
    (some (mkSolinasFoldSeed 64 4294967295))

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Diagnostics — see what the e-graph is doing
-- ══════════════════════════════════════════════════════════════════

/-- Run the pipeline and report stats (classes/nodes at each phase). -/
def diagnose (p : Nat) (expr : MixedExpr) (cfg : GuidedMixedConfig := .default)
    : String :=
  let (g0, _rootId) := buildEGraph expr
  let stats0 := s!"Seed: {g0.numClasses} classes, {g0.numNodes} nodes"
  -- Phase 1
  let g1 := saturateMixedF cfg.ematchFuel cfg.phase1Iters cfg.phase1Rebuild g0
    allBitwisePatternRulesWithBridges
  let stats1 := s!"Phase1 (bitwise): {g1.numClasses} classes, {g1.numNodes} nodes"
  -- Phase 2
  let g2 := saturateMixedF cfg.ematchFuel cfg.phase2Iters cfg.phase2Rebuild g1
    (fieldFoldPatternRules p)
  let stats2 := s!"Phase2 (field): {g2.numClasses} classes, {g2.numNodes} nodes"
  s!"{stats0}\n{stats1}\n{stats2}"

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: buildEGraph on witness(0) creates 1 class. -/
example : (buildEGraph mkCanonicalInput).1.numClasses = 1 := by native_decide

/-- Smoke: mkCanonicalInput is witnessE 0. -/
example : mkCanonicalInput = MixedExpr.witnessE 0 := rfl

/-- Smoke: fieldFoldPatternRules returns 1 rule for Mersenne31. -/
example : (fieldFoldPatternRules mersenne31_prime).length = 1 := by native_decide

/-- Smoke: full pattern rules list is non-empty. -/
example : (allBitwisePatternRulesWithBridges ++ fieldFoldPatternRules mersenne31_prime).length = 11
    := by native_decide

/-- Smoke: Solinas fold seed for BabyBear builds a 7-class e-graph. -/
example : (buildEGraph (mkSolinasFoldSeed 31 134217727)).1.numClasses = 7 := by native_decide

end MixedRunner
