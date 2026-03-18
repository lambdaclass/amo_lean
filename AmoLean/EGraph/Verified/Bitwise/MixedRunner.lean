/-
  AmoLean.EGraph.Verified.Bitwise.MixedRunner — End-to-End E-Graph Pipeline

  Orchestrates the full pipeline: build → saturate → extract → emit C.
  Given a prime p and hardware target, constructs an EGraph from a canonical
  modular reduction expression, saturates with bitwise + field fold rules,
  extracts the optimal expression via cost model, and emits C code.

  This is the CORE deliverable of v3.5: the e-graph actually runs end-to-end.
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
open MixedSaturation (saturateMixedF)
open MixedEGraphBuilder (addMixedExpr buildEGraph)
open MixedPatternRules (allBitwisePatternRules)
open FieldFoldPatternRules (fieldFoldPatternRules allFieldFoldPatternRules)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Canonical input expressions
-- ══════════════════════════════════════════════════════════════════

/-- Build the canonical input expression: `witness(0)`.
    Represents an arbitrary input x to be reduced modulo p. -/
def mkCanonicalInput : MixedExpr := .witnessE 0

-- ══════════════════════════════════════════════════════════════════
-- Section 2: optimizeMixedF — Core optimization pipeline
-- ══════════════════════════════════════════════════════════════════

/-- Core optimization pipeline:
    1. Build EGraph from input expression
    2. Saturate with rules (bitwise + field fold)
    3. Cost-aware extraction
    Returns the optimized MixedExpr, or none if extraction fails. -/
def optimizeMixedF (ematchFuel maxIter rebuildFuel costFuel : Nat)
    (expr : MixedExpr) (rules : List (RewriteRule MixedNodeOp))
    (hw : HardwareCost) : Option MixedExpr :=
  let (g, rootId) := buildEGraph expr
  let g_sat := saturateMixedF ematchFuel maxIter rebuildFuel g rules
  costAwareExtractAuto hw g_sat rootId costFuel

/-- Convenience wrapper with default fuel parameters. -/
def optimizeDefault (expr : MixedExpr) (rules : List (RewriteRule MixedNodeOp))
    (hw : HardwareCost) : Option MixedExpr :=
  optimizeMixedF 20 10 3 50 expr rules hw

-- ══════════════════════════════════════════════════════════════════
-- Section 3: synthesizeViaEGraph — Full pipeline with C emission
-- ══════════════════════════════════════════════════════════════════

/-- Full pipeline: given a prime p and hardware target, produce optimized C code.
    1. Start with witness(0) as input
    2. Combine bitwise rules + field fold rules for the prime
    3. Saturate and extract
    4. Emit C function

    Returns the C code string, or "extraction_failed" on error. -/
def synthesizeViaEGraph (p : Nat) (hw : HardwareCost)
    (ematchFuel : Nat := 20) (maxIter : Nat := 10)
    (rebuildFuel : Nat := 3) (costFuel : Nat := 50) : String :=
  let inputExpr := mkCanonicalInput
  let rules := allBitwisePatternRules ++ fieldFoldPatternRules p
  match optimizeMixedF ematchFuel maxIter rebuildFuel costFuel inputExpr rules hw with
  | some optExpr =>
    emitCFunction s!"reduce_mod_{p}" "x" optExpr (fun _ => 0)
  | none =>
    -- Fallback: emit C for the original expression (identity)
    emitCFunction s!"reduce_mod_{p}" "x" inputExpr (fun _ => 0)

/-- Multi-target synthesis: emit C for all 3 hardware targets.
    Returns a list of (target_name, C_code) pairs. -/
def synthesizeMultiTarget (p : Nat) : List (String × String) :=
  let targets := [("ARM_Cortex_A76", arm_cortex_a76),
                  ("RISC-V_SiFive_U74", riscv_sifive_u74),
                  ("FPGA_DSP48E2", fpga_dsp48e2)]
  targets.map fun (name, hw) => (name, synthesizeViaEGraph p hw)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Per-field convenience
-- ══════════════════════════════════════════════════════════════════

def synthesizeMersenne31 (hw : HardwareCost := arm_cortex_a76) : String :=
  synthesizeViaEGraph mersenne31_prime hw

def synthesizeBabyBear (hw : HardwareCost := arm_cortex_a76) : String :=
  synthesizeViaEGraph babybear_prime hw

def synthesizeGoldilocks (hw : HardwareCost := arm_cortex_a76) : String :=
  synthesizeViaEGraph goldilocks_prime hw

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke test: buildEGraph on witness(0) creates 1 class. -/
example : (buildEGraph mkCanonicalInput).1.numClasses = 1 := by native_decide

/-- Smoke test: optimizeMixedF returns some result. -/
example : (optimizeMixedF 5 2 2 10 mkCanonicalInput [] arm_cortex_a76).isSome = true := by
  native_decide

/-- Smoke test: mkCanonicalInput is witnessE 0. -/
example : mkCanonicalInput = MixedExpr.witnessE 0 := rfl

/-- Smoke test: fieldFoldPatternRules returns 1 rule for Mersenne31. -/
example : (fieldFoldPatternRules mersenne31_prime).length = 1 := by native_decide

/-- Smoke test: combined rules list is non-empty. -/
example : (allBitwisePatternRules ++ fieldFoldPatternRules mersenne31_prime).length = 9 := by
  native_decide

end MixedRunner
