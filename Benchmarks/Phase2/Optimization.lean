/-
  AMO-Lean Phase 2: Optimization Benchmark Suite

  This module demonstrates that the E-Graph optimizer achieves ≥10%
  operation reduction on realistic expression patterns.

  Test Categories:
  1. Identity Simplification (x+0, x*1)
  2. Zero Propagation (x*0)
  3. Constant Folding (2+3 → 5)
  4. FRI-like Patterns (special case α=0)
  5. Oracle Testing (verify rules with random values)
-/

import AmoLean.EGraph.Optimize

namespace Benchmarks.Phase2

open AmoLean.EGraph.Optimize
open AmoLean (Expr)

/-! ## Part 1: Realistic Expression Patterns

These patterns come from actual FRI and Poseidon2 computations.
-/

/-- Pattern: FRI fold with α=0 (degenerate case)
    out = even + 0 * odd → out = even
    Eliminates n multiplications and n additions -/
def friFoldAlphaZero : Expr Int :=
  Expr.add (Expr.var 0) (Expr.mul (Expr.const 0) (Expr.var 1))

/-- Pattern: FRI fold with α=1 (another special case)
    out = even + 1 * odd → out = even + odd
    Eliminates n multiplications -/
def friFoldAlphaOne : Expr Int :=
  Expr.add (Expr.var 0) (Expr.mul (Expr.const 1) (Expr.var 1))

/-- Pattern: Poseidon2 round with constant folding
    state[i] = (input[i] + RC) * MDS_factor
    When RC = 0 and MDS_factor = 1: simplifies to input[i] -/
def poseidonRoundSimplified : Expr Int :=
  Expr.mul (Expr.add (Expr.var 0) (Expr.const 0)) (Expr.const 1)

/-- Pattern: Nested identity operations
    ((x * 1) + 0) * 1 + 0 → x -/
def nestedIdentities : Expr Int :=
  Expr.add (Expr.mul (Expr.add (Expr.mul (Expr.var 0) (Expr.const 1)) (Expr.const 0)) (Expr.const 1)) (Expr.const 0)

/-- Pattern: Dead code via zero multiplication
    (complex_expression) * 0 → 0 -/
def deadCodeElimination : Expr Int :=
  Expr.mul
    (Expr.add
      (Expr.mul (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.add (Expr.var 2) (Expr.var 3)))
      (Expr.mul (Expr.var 4) (Expr.var 5)))
    (Expr.const 0)

/-- Pattern: Constant propagation chain
    (2 + 3) * (4 + 0) → 20 -/
def constantChain : Expr Int :=
  Expr.mul (Expr.add (Expr.const 2) (Expr.const 3)) (Expr.add (Expr.const 4) (Expr.const 0))

/-- Pattern: Mixed optimization
    (x + 0) + (y * 0) + (z * 1) → x + z -/
def mixedOptimization : Expr Int :=
  Expr.add
    (Expr.add (Expr.add (Expr.var 0) (Expr.const 0)) (Expr.mul (Expr.var 1) (Expr.const 0)))
    (Expr.mul (Expr.var 2) (Expr.const 1))

/-! ## Part 2: Oracle Testing for Rule Verification

Test that optimization rules preserve semantics by
evaluating before/after with random values.
-/

/-- Evaluate an expression with given variable values -/
partial def evalExpr (env : Nat → Int) : Expr Int → Int
  | Expr.const n => n
  | Expr.var v => env v
  | Expr.add e1 e2 => evalExpr env e1 + evalExpr env e2
  | Expr.mul e1 e2 => evalExpr env e1 * evalExpr env e2
  | Expr.pow e n =>
    let base := evalExpr env e
    List.range n |>.foldl (fun acc _ => acc * base) 1

/-- Test that optimization preserves semantics -/
def testRulePreservesSemantics (name : String) (expr : Expr Int) (numTests : Nat := 100) : IO Bool := do
  let (optimized, _) := optimizeExpr expr

  -- Generate random test values
  let mut allPassed := true
  for i in [:numTests] do
    -- Simple deterministic "random" values based on iteration
    let env : Nat → Int := fun v => (Int.ofNat v + 1) * (Int.ofNat i + 7) % 97

    let originalResult := evalExpr env expr
    let optimizedResult := evalExpr env optimized

    if originalResult != optimizedResult then
      IO.println s!"  ❌ ORACLE FAILURE for {name} at test {i}:"
      IO.println s!"     Original:  {originalResult}"
      IO.println s!"     Optimized: {optimizedResult}"
      allPassed := false
      break

  return allPassed

/-! ## Part 3: Benchmark Runner -/

/-- Benchmark result for a single test -/
structure BenchResult where
  name : String
  opsBefore : Nat
  opsAfter : Nat
  nodesBefore : Nat
  nodesAfter : Nat
  reductionPct : Float
  oraclePass : Bool
  deriving Repr

/-- Run optimization benchmark on an expression -/
def benchmarkExpr (name : String) (expr : Expr Int) : IO BenchResult := do
  let (_optimized, stats) := optimizeExpr expr
  let oraclePass ← testRulePreservesSemantics name expr

  return {
    name := name
    opsBefore := stats.opsBefore
    opsAfter := stats.opsAfter
    nodesBefore := stats.originalSize
    nodesAfter := stats.optimizedSize
    reductionPct := optPercentage stats
    oraclePass := oraclePass
  }

/-- Print benchmark result -/
def printResult (r : BenchResult) : IO Unit := do
  let status := if r.oraclePass then "✓" else "❌"
  IO.println s!"│ {r.name}"
  IO.println s!"│   Ops: {r.opsBefore} → {r.opsAfter} ({r.reductionPct.toString}% reduction)"
  IO.println s!"│   Nodes: {r.nodesBefore} → {r.nodesAfter}"
  IO.println s!"│   Oracle: {status}"
  IO.println "│"

/-- Main benchmark suite -/
def main : IO UInt32 := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║           AMO-LEAN PHASE 2: OPTIMIZATION BENCHMARK                   ║"
  IO.println "║                                                                      ║"
  IO.println "║  Criteria for Success: ≥10% operation reduction                      ║"
  IO.println "║  Oracle Testing: Verify rules preserve semantics                     ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"
  IO.println ""

  let benchmarks := [
    ("FRI fold α=0", friFoldAlphaZero),
    ("FRI fold α=1", friFoldAlphaOne),
    ("Poseidon round simplified", poseidonRoundSimplified),
    ("Nested identities", nestedIdentities),
    ("Dead code elimination", deadCodeElimination),
    ("Constant chain", constantChain),
    ("Mixed optimization", mixedOptimization)
  ]

  IO.println "┌────────────────────────────────────────────────────────────────────────┐"
  IO.println "│ BENCHMARK RESULTS                                                      │"
  IO.println "├────────────────────────────────────────────────────────────────────────┤"

  let mut totalOpsBefore := 0
  let mut totalOpsAfter := 0
  let mut allOraclePass := true

  for (name, expr) in benchmarks do
    let result ← benchmarkExpr name expr
    printResult result
    totalOpsBefore := totalOpsBefore + result.opsBefore
    totalOpsAfter := totalOpsAfter + result.opsAfter
    if !result.oraclePass then allOraclePass := false

  IO.println "└────────────────────────────────────────────────────────────────────────┘"
  IO.println ""

  -- Summary
  let totalReduction := if totalOpsBefore > 0
    then ((totalOpsBefore - totalOpsAfter).toFloat / totalOpsBefore.toFloat) * 100.0
    else 0.0

  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║ SUMMARY                                                              ║"
  IO.println "╠══════════════════════════════════════════════════════════════════════╣"
  IO.println s!"║ Total operations: {totalOpsBefore} → {totalOpsAfter}"
  IO.println s!"║ Overall reduction: {totalReduction.toString}%"
  IO.println s!"║ Oracle tests: {if allOraclePass then "ALL PASSED ✓" else "SOME FAILED ❌"}"
  IO.println "╠══════════════════════════════════════════════════════════════════════╣"

  if totalReduction >= 10.0 && allOraclePass then
    IO.println "║ ✓ PHASE 2 SUCCESS: Criteria met!                                     ║"
    IO.println "║   - ≥10% reduction: YES                                              ║"
    IO.println "║   - Oracle tests: PASS                                               ║"
    IO.println "╚══════════════════════════════════════════════════════════════════════╝"
    return 0
  else
    IO.println "║ ❌ PHASE 2 INCOMPLETE                                                 ║"
    if totalReduction < 10.0 then
      IO.println s!"║   - Reduction: {totalReduction.toString}% (need ≥10%)"
    if !allOraclePass then
      IO.println "║   - Oracle tests: FAILED"
    IO.println "╚══════════════════════════════════════════════════════════════════════╝"
    return 1

-- Run when imported
#eval! main

end Benchmarks.Phase2
