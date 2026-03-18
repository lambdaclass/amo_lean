/-
  Tests/NonVacuity/MixedRunner.lean — End-to-end tests for the MixedEGraph pipeline

  Non-vacuity tests and demo for v3.5: E-Graph Funcional.
  Verifies that the e-graph pipeline actually WORKS end-to-end:
  1. Build EGraph from expression
  2. Saturate with bitwise + field fold rules
  3. Extract optimized expression
  4. Emit C code

  Tests are executable (#eval) and compile without sorry.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedRunner

namespace MixedRunnerTests

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified.Bitwise
  (MixedNodeOp HardwareCost arm_cortex_a76 riscv_sifive_u74 fpga_dsp48e2
   mersenne31_prime babybear_prime goldilocks_prime)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open MixedEMatch (RewriteRule)
open MixedSaturation (saturateMixedF)
open MixedEGraphBuilder (addMixedExpr buildEGraph)
open MixedPatternRules (allBitwisePatternRules patAndSelf)
open MixedRunner

-- ══════════════════════════════════════════════════════════════════
-- Test 1: Build EGraph with bitAnd(witness(0), constMask(31))
-- ══════════════════════════════════════════════════════════════════

#eval do
  let expr := MixedExpr.bitAndE (.witnessE 0) (.constMaskE 31)
  let (g, rootId) := buildEGraph expr
  IO.println s!"Test 1: bitAnd(witness(0), constMask(31))"
  IO.println s!"  Classes: {g.numClasses}, Root: {rootId}"
  pure ()

-- ══════════════════════════════════════════════════════════════════
-- Test 2: Saturate with and_self rule
-- ══════════════════════════════════════════════════════════════════

#eval do
  let expr := MixedExpr.bitAndE (.witnessE 0) (.witnessE 0)
  let (g, _rootId) := buildEGraph expr
  let g_sat := saturateMixedF 10 3 2 g [patAndSelf]
  IO.println s!"Test 2: bitAnd(w0, w0) + and_self rule"
  IO.println s!"  Before: {g.numClasses} classes"
  IO.println s!"  After:  {g_sat.numClasses} classes"
  pure ()

-- ══════════════════════════════════════════════════════════════════
-- Test 3: Mersenne31 fold via e-graph
-- ══════════════════════════════════════════════════════════════════

#eval do
  let result := synthesizeMersenne31 arm_cortex_a76
  IO.println s!"Test 3: Mersenne31 C code ({result.length} chars):"
  IO.println result

-- ══════════════════════════════════════════════════════════════════
-- Test 4: BabyBear fold via e-graph
-- ══════════════════════════════════════════════════════════════════

#eval do
  let result := synthesizeBabyBear arm_cortex_a76
  IO.println s!"Test 4: BabyBear C code ({result.length} chars):"
  IO.println result

-- ══════════════════════════════════════════════════════════════════
-- Test 5: Goldilocks fold via e-graph
-- ══════════════════════════════════════════════════════════════════

#eval do
  let result := synthesizeGoldilocks arm_cortex_a76
  IO.println s!"Test 5: Goldilocks C code ({result.length} chars):"
  IO.println result

-- ══════════════════════════════════════════════════════════════════
-- Test 6: Multi-target synthesis
-- ══════════════════════════════════════════════════════════════════

#eval do
  let results := synthesizeMultiTarget mersenne31_prime
  IO.println s!"Test 6: Multi-target Mersenne31 ({results.length} targets)"
  for (name, code) in results do
    IO.println s!"  {name}: {code.length} chars"
  pure ()

-- ══════════════════════════════════════════════════════════════════
-- Non-vacuity examples (compile-time)
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: buildEGraph produces correct number of classes for a leaf. -/
example : (buildEGraph (.witnessE 0)).1.numClasses = 1 := by native_decide

/-- Non-vacuity: buildEGraph produces correct number of classes for binary. -/
example : (buildEGraph (.bitAndE (.witnessE 0) (.constMaskE 31))).1.numClasses = 3 := by
  native_decide

/-- Non-vacuity: optimizeMixedF returns some for empty rules. -/
example : (MixedRunner.optimizeMixedF 5 2 2 10 (.witnessE 0) [] arm_cortex_a76).isSome = true := by
  native_decide

/-- Non-vacuity: synthesizeMersenne31 produces non-empty output. -/
example : (synthesizeMersenne31 arm_cortex_a76).length > 0 := by native_decide

end MixedRunnerTests
