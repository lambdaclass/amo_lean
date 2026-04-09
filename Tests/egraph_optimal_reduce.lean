/-
  Test: ¿Qué produce el e-graph para reduce(x) con KoalaBear en ARM scalar?
  Run: lake env lean --run Tests/egraph_optimal_reduce.lean
-/
import AmoLean.EGraph.Verified.Bitwise.MixedRunner
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.CostExtraction

open MixedRunner
open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)

def koalabear_prime : Nat := 2130706433  -- 2^31 - 2^24 + 1
def koalabear_c : Nat := 2^24 - 1       -- 16777215

-- Pretty-print MixedExpr as pseudo-code
def ppExpr : MixedExpr → String
  | .witnessE n => s!"x{n}"
  | .constE n => s!"{n}"
  | .constMaskE n => s!"(2^{n}-1)"
  | .addE a b => s!"({ppExpr a} + {ppExpr b})"
  | .subE a b => s!"({ppExpr a} - {ppExpr b})"
  | .mulE a b => s!"({ppExpr a} * {ppExpr b})"
  | .smulE k a => s!"({k} * {ppExpr a})"
  | .shiftRightE a n => s!"({ppExpr a} >> {n})"
  | .shiftLeftE a n => s!"({ppExpr a} << {n})"
  | .bitAndE a b => s!"({ppExpr a} & {ppExpr b})"
  | .reduceE a p => s!"reduce({ppExpr a}, {p})"
  | .harveyReduceE a p => s!"harvey({ppExpr a}, {p})"
  | .montyReduceE a p mu => s!"monty({ppExpr a}, {p})"
  | .barrettReduceE a p m => s!"barrett({ppExpr a}, {p})"
  | _ => "<other>"

-- Count operations in a MixedExpr
def countOps : MixedExpr → Nat
  | .witnessE _ | .constE _ | .constMaskE _ | .pubInputE _ => 0
  | .addE a b | .subE a b | .mulE a b | .bitAndE a b
  | .bitOrE a b | .bitXorE a b => 1 + countOps a + countOps b
  | .smulE _ a | .shiftRightE a _ | .shiftLeftE a _
  | .reduceE a _ | .harveyReduceE a _ | .negE a => 1 + countOps a
  | .montyReduceE a _ _ | .barrettReduceE a _ _ => 1 + countOps a
  | .kronPackE a b _ => 1 + countOps a + countOps b
  | .kronUnpackLoE a _ | .kronUnpackHiE a _ => 1 + countOps a

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  E-Graph Optimal Reduce: KoalaBear on ARM Cortex-A76"
  IO.println "  Input: reduceGate(x, 2130706433)"
  IO.println "  p = 2^31 - 2^24 + 1, c = 2^24 - 1 = 16777215"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- The input expression: reduce(witness(0), koalabear)
  let inputExpr : MixedExpr := .reduceE (.witnessE 0) koalabear_prime

  IO.println s!"Input:  {ppExpr inputExpr}"
  IO.println s!"  ops: {countOps inputExpr}"
  IO.println ""

  -- Run with conservative config to avoid e-graph explosion
  -- The fold rules have lhs := .patVar 0 (matches everything),
  -- so we limit phase2 to 1 iteration to prevent blowup.
  let cfg : GuidedMixedConfig := {
    GuidedMixedConfig.default with
    phase2Iters := 1
    phase2Rebuild := 5
    maxNodes := 200
  }
  let result_scalar := guidedOptimizeMixedF koalabear_prime arm_cortex_a76 cfg inputExpr

  IO.println "── ARM Cortex-A76 (conservative, phase2Iters=1) ──"
  match result_scalar with
  | some expr =>
    IO.println s!"Output: {ppExpr expr}"
    IO.println s!"  ops: {countOps expr}"
  | none =>
    IO.println "  (no extraction result)"

  IO.println ""

  -- Test 2: Give the fold as input, let Phase 3 decompose the smulGate
  let foldExpr : MixedExpr :=
    .addE (.smulE koalabear_c (.shiftRightE (.witnessE 0) 31))
          (.bitAndE (.witnessE 0) (.constMaskE 31))

  IO.println s!"Input (fold): {ppExpr foldExpr}"
  IO.println s!"  ops: {countOps foldExpr}"

  -- Use higher phase3 iters to ensure shift-sub decomposition fires
  let cfg3 : GuidedMixedConfig := {
    GuidedMixedConfig.default with
    phase1Iters := 1
    phase2Iters := 0      -- skip Phase 2 (fold already decomposed)
    phase3Iters := 3      -- Phase 3: shift-add decomposition
    phase3Rebuild := 5
    maxNodes := 500
  }
  let result_fold := guidedOptimizeMixedF koalabear_prime arm_cortex_a76 cfg3 foldExpr
  IO.println "── Phase 3 on fold (should decompose smul → shift-sub) ──"
  match result_fold with
  | some expr =>
    IO.println s!"Output: {ppExpr expr}"
    IO.println s!"  ops: {countOps expr}"
  | none =>
    IO.println "  (no extraction result)"

  IO.println ""

  -- Test 3: Full 3-phase pipeline on reduceGate
  -- Phase 2 produces fold (with smulGate), Phase 3 decomposes to shift-sub
  let cfg_full : GuidedMixedConfig := {
    GuidedMixedConfig.default with
    phase1Iters := 1
    phase2Iters := 1      -- Phase 2: introduce fold
    phase3Iters := 3      -- Phase 3: decompose smul → shift-sub
    maxNodes := 500
  }
  IO.println "── Full 3-phase: reduce(x) → fold → shift-sub ──"
  let result_full := guidedOptimizeMixedF koalabear_prime arm_cortex_a76 cfg_full inputExpr
  match result_full with
  | some expr =>
    IO.println s!"Output: {ppExpr expr}"
    IO.println s!"  ops: {countOps expr}"
  | none =>
    IO.println "  (no extraction result)"

  IO.println ""

  -- Show the cost model values for reference
  IO.println "── Cost model reference (ARM Cortex-A76) ──"
  IO.println s!"  reduceGate cost:  {mixedOpCost arm_cortex_a76 (.reduceGate 0 0)}"
  IO.println s!"  montyReduce cost: {mixedOpCost arm_cortex_a76 (.montyReduce 0 0 0)}"
  IO.println s!"  harveyReduce cost:{mixedOpCost arm_cortex_a76 (.harveyReduce 0 0)}"
  IO.println s!"  mulGate cost:     {mixedOpCost arm_cortex_a76 (.mulGate 0 0)}"
  IO.println s!"  shiftRight cost:  {mixedOpCost arm_cortex_a76 (.shiftRight 0 0)}"
  IO.println s!"  subGate cost:     {mixedOpCost arm_cortex_a76 (.subGate 0 0)}"
  IO.println s!"  addGate cost:     {mixedOpCost arm_cortex_a76 (.addGate 0 0)}"
  IO.println s!"  bitAnd cost:      {mixedOpCost arm_cortex_a76 (.bitAnd 0 0)}"
  IO.println s!"  shiftLeft cost:   {mixedOpCost arm_cortex_a76 (.shiftLeft 0 0)}"
  IO.println s!"  fusedShiftSub:    {arm_cortex_a76.fusedShiftSub} (HW param, not a MixedNodeOp)"
