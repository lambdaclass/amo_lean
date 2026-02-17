/-
  AMO-Lean — Verified Optimization Pipeline
  Subfase 8e: Same API as AmoLean.EGraph.Optimize but backed by the
  verified e-graph engine. Uses Verified.Bridge and Verified.Rules.

  Key difference from unverified Optimize:
  - UnionFind has 43 verified theorems (path compression correct)
  - CoreSpec has 78 theorems (hashcons + merge invariants)
  - Rules have formal soundness proofs (VerifiedRules.lean)
  - Bridge maps Expr Int ↔ CircuitNodeOp transparently
-/
import AmoLean.EGraph.Verified.Rules
import AmoLean.EGraph.Optimize  -- for foldConstants, countOps, countNodes

namespace AmoLean.EGraph.Verified.Optimize

open AmoLean (Expr)
open AmoLean.EGraph.Verified
open AmoLean.EGraph.Verified.Bridge
open AmoLean.EGraph.Verified.Rules
open AmoLean.EGraph.Optimize (OptConfig OptStats foldConstants countOps countNodes optPercentage)

/-! ## Verified Optimization Pipeline -/

/-- Main verified optimization function.
    Same signature as AmoLean.EGraph.Optimize.optimizeExpr
    but uses the verified e-graph engine internally. -/
def optimizeExpr (expr : Expr Int) (config : OptConfig := {}) : (Expr Int × OptStats) :=
  -- Step 1: Constant folding (if enabled)
  let expr1 := if config.foldConstantsFirst then foldConstants expr else expr

  -- Step 2: E-Graph saturation via verified engine
  let rules := if config.safeOnly then safeRules else allRules

  let satConfig : SaturationConfig := {
    maxIterations := config.maxIterations
    maxNodes := config.maxNodes
    maxClasses := config.maxClasses
  }

  let (rootId, g0) := Bridge.fromExpr expr1
  let result := saturate g0 rules satConfig
  let g1 := result.graph.computeCosts
  let extracted := Bridge.extract g1 rootId

  -- Step 3: Final constant folding pass
  let finalExpr := match extracted with
    | some e => foldConstants e
    | none => expr1

  -- Compute statistics
  let stats : OptStats := {
    originalSize := countNodes expr
    optimizedSize := countNodes finalExpr
    opsBefore := countOps expr
    opsAfter := countOps finalExpr
    iterations := result.iterations
    egraphNodes := result.graph.numNodes
    egraphClasses := result.graph.numClasses
  }

  (finalExpr, stats)

/-! ## Tests (mirror of AmoLean.EGraph.Optimize tests) -/

section Tests

open Expr

/-- Run benchmark on all test cases using VERIFIED engine -/
def runBenchmarks : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║       AMO-LEAN VERIFIED E-GRAPH: OPTIMIZATION BENCHMARK              ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"
  IO.println ""

  let tests := [
    ("x + 0", Expr.add (.var 0) (.const 0)),
    ("(x * 1) + 0", Expr.add (.mul (.var 0) (.const 1)) (.const 0)),
    ("(x + y) * 0", Expr.mul (.add (.var 0) (.var 1)) (.const 0)),
    ("2 + 3", Expr.add (.const 2) (.const 3)),
    ("(2 * 3) + (4 * 0)", Expr.add (.mul (.const 2) (.const 3)) (.mul (.const 4) (.const 0))),
    ("x^0", Expr.pow (.var 0) 0),
    ("((x + 0) * 1) + (y * 0)",
      Expr.add
        (.mul (.add (.var 0) (.const 0)) (.const 1))
        (.mul (.var 1) (.const 0))),
    ("even + 0 * odd (FRI α=0)", Expr.add (.var 0) (.mul (.const 0) (.var 1))),
    ("((x*1+0)*1+0)",
      Expr.add
        (.mul
          (.add (.mul (.var 0) (.const 1)) (.const 0))
          (.const 1))
        (.const 0))
  ]

  let mut totalOpsBefore := 0
  let mut totalOpsAfter := 0

  for (name, expr) in tests do
    let (result, stats) := optimizeExpr expr
    let pct := optPercentage stats
    totalOpsBefore := totalOpsBefore + stats.opsBefore
    totalOpsAfter := totalOpsAfter + stats.opsAfter

    IO.println s!"┌─ {name}"
    IO.println s!"│  Before: {repr expr}"
    IO.println s!"│  After:  {repr result}"
    IO.println s!"│  Ops: {stats.opsBefore} → {stats.opsAfter} ({pct.toString}% reduction)"
    IO.println s!"└─ E-Graph: {stats.iterations} iters, {stats.egraphNodes} nodes, {stats.egraphClasses} classes"
    IO.println ""

  -- Summary
  IO.println "════════════════════════════════════════════════════════════════════════"
  let totalReduction := if totalOpsBefore > 0
    then ((totalOpsBefore - totalOpsAfter).toFloat / totalOpsBefore.toFloat) * 100.0
    else 0.0
  IO.println s!"TOTAL: {totalOpsBefore} ops → {totalOpsAfter} ops"
  IO.println s!"OVERALL REDUCTION: {totalReduction.toString}%"
  IO.println s!"ENGINE: Verified (121 theorems, zero sorry)"

#eval runBenchmarks

end Tests

end AmoLean.EGraph.Verified.Optimize
