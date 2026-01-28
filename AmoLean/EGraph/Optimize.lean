/-
  AMO-Lean: Optimization Engine
  Phase 2 - Optimization Rules with Termination Guarantees

  This module implements optimization rules for the E-Graph with
  mitigations against common pitfalls:

  1. **Commutativity Cycles**: No pure commutativity rules (a+b → b+a).
     Instead, use canonical ordering (sort operands by hash).

  2. **Associativity Explosion**: Directed rules with preferred form.
     For matrix-vector: prefer right-associative (A*(B*v)).

  3. **Constant Folding**: Syntactic folding first (Const + Const),
     before any MetaM evaluation.

  References:
  - "Term Rewriting and All That" (Baader & Nipkow)
  - egg: Fast and Extensible Equality Saturation (Willsey et al.)
-/

import AmoLean.EGraph.Basic
import AmoLean.EGraph.EMatch
import AmoLean.EGraph.Saturate

namespace AmoLean.EGraph.Optimize

open AmoLean.EGraph

/-! ## Part 1: Canonical Ordering (Mitigation for Commutativity)

Instead of bidirectional commutativity rules that cause infinite cycles,
we use canonical ordering: operands are sorted by a hash/ID so that
equivalent expressions have a unique canonical form.

This follows the approach from Baader & Nipkow: use term orderings
to ensure termination.
-/

/-- Hash function for expressions (simple structural hash) -/
partial def exprHash : Expr Int → UInt64
  | .const n => hash n
  | .var v => hash (v + 1000)  -- Offset to distinguish from constants
  | .add e1 e2 => mixHash (exprHash e1) (exprHash e2) + 1
  | .mul e1 e2 => mixHash (exprHash e1) (exprHash e2) + 2
  | .pow e n => mixHash (exprHash e) (hash n) + 3

/-- Canonical ordering predicate: should e1 come before e2? -/
def shouldComeBefore (e1 e2 : Expr Int) : Bool :=
  exprHash e1 < exprHash e2

/-- Canonicalize commutative operation by sorting operands -/
def canonicalizeAdd (e1 e2 : Expr Int) : Expr Int :=
  if shouldComeBefore e1 e2 then .add e1 e2 else .add e2 e1

def canonicalizeMul (e1 e2 : Expr Int) : Expr Int :=
  if shouldComeBefore e1 e2 then .mul e1 e2 else .mul e2 e1

/-! ## Part 2: Directed Rewrite Rules (Mitigation for Explosions)

All rules are DIRECTED: they have a clear "from" and "to" that
reduces complexity. We track rule direction explicitly.
-/

/-- Rule direction indicates whether the rule reduces complexity -/
inductive RuleDirection where
  | reducing    -- Guaranteed to reduce operation count
  | structural  -- May not reduce count, but normalizes form
  | expanding   -- May increase count (use carefully)
  deriving Repr, BEq

/-- Enhanced rewrite rule with direction and cost delta -/
structure OptRule where
  name : String
  lhs : Pattern
  rhs : Pattern
  direction : RuleDirection
  costDelta : Int  -- Negative = reduces cost
  deriving Repr

namespace OptRule

/-! ### 2.1 Identity Rules (REDUCING) -/

/-- a + 0 → a (removes one add operation) -/
def addZeroRight : OptRule := {
  name := "add_zero_right"
  lhs := .add (.patVar 0) (.const 0)
  rhs := .patVar 0
  direction := .reducing
  costDelta := -1
}

/-- 0 + a → a -/
def addZeroLeft : OptRule := {
  name := "add_zero_left"
  lhs := .add (.const 0) (.patVar 0)
  rhs := .patVar 0
  direction := .reducing
  costDelta := -1
}

/-- a * 1 → a (removes one mul operation) -/
def mulOneRight : OptRule := {
  name := "mul_one_right"
  lhs := .mul (.patVar 0) (.const 1)
  rhs := .patVar 0
  direction := .reducing
  costDelta := -1
}

/-- 1 * a → a -/
def mulOneLeft : OptRule := {
  name := "mul_one_left"
  lhs := .mul (.const 1) (.patVar 0)
  rhs := .patVar 0
  direction := .reducing
  costDelta := -1
}

/-! ### 2.2 Zero Rules (REDUCING) -/

/-- a * 0 → 0 (eliminates entire subtree) -/
def mulZeroRight : OptRule := {
  name := "mul_zero_right"
  lhs := .mul (.patVar 0) (.const 0)
  rhs := .const 0
  direction := .reducing
  costDelta := -10  -- Large reduction: eliminates subtree
}

/-- 0 * a → 0 -/
def mulZeroLeft : OptRule := {
  name := "mul_zero_left"
  lhs := .mul (.const 0) (.patVar 0)
  rhs := .const 0
  direction := .reducing
  costDelta := -10
}

/-! ### 2.3 Power Rules (REDUCING) -/

/-- a^0 → 1 -/
def powZero : OptRule := {
  name := "pow_zero"
  lhs := .pow (.patVar 0) 0
  rhs := .const 1
  direction := .reducing
  costDelta := -5  -- Eliminates power computation
}

/-- a^1 → a -/
def powOne : OptRule := {
  name := "pow_one"
  lhs := .pow (.patVar 0) 1
  rhs := .patVar 0
  direction := .reducing
  costDelta := -1
}

/-- 0^n → 0 (for n > 0) -/
def zeroPow : OptRule := {
  name := "zero_pow"
  lhs := .pow (.const 0) 1  -- Specific case: 0^1
  rhs := .const 0
  direction := .reducing
  costDelta := -1
}

/-- 1^n → 1 -/
def onePow : OptRule := {
  name := "one_pow"
  lhs := .pow (.const 1) 2  -- Specific case: 1^2
  rhs := .const 1
  direction := .reducing
  costDelta := -2
}

/-! ### 2.4 Distributivity (STRUCTURAL - use with caution) -/

/-- a * (b + c) → a*b + a*c (EXPANDING - only use when beneficial) -/
def distribLeft : OptRule := {
  name := "distrib_left"
  lhs := .mul (.patVar 0) (.add (.patVar 1) (.patVar 2))
  rhs := .add (.mul (.patVar 0) (.patVar 1)) (.mul (.patVar 0) (.patVar 2))
  direction := .expanding
  costDelta := 1  -- Adds one operation
}

/-- a*b + a*c → a*(b+c) (REDUCING - factorization) -/
def factorLeft : OptRule := {
  name := "factor_left"
  lhs := .add (.mul (.patVar 0) (.patVar 1)) (.mul (.patVar 0) (.patVar 2))
  rhs := .mul (.patVar 0) (.add (.patVar 1) (.patVar 2))
  direction := .reducing
  costDelta := -1  -- Removes one multiplication
}

/-! ### Rule Collections -/

/-- Only rules that reduce operation count -/
def reducingRules : List OptRule := [
  addZeroRight, addZeroLeft,
  mulOneRight, mulOneLeft,
  mulZeroRight, mulZeroLeft,
  powZero, powOne, zeroPow, onePow,
  factorLeft
]

/-- All rules including structural -/
def allRules : List OptRule := reducingRules ++ [distribLeft]

/-- Safe rules that won't cause explosion -/
def safeRules : List OptRule := reducingRules

end OptRule

/-! ## Part 3: Constant Folding (Syntactic First)

Following Gemini's advice: implement syntactic folding first
(Const op Const → Const) without MetaM complexity.
-/

/-- Fold constants in an expression (syntactic level) -/
partial def foldConstants : Expr Int → Expr Int
  | .const n => .const n
  | .var v => .var v
  | .add e1 e2 =>
    let e1' := foldConstants e1
    let e2' := foldConstants e2
    match e1', e2' with
    | .const a, .const b => .const (a + b)
    | .const 0, e => e
    | e, .const 0 => e
    | _, _ => .add e1' e2'
  | .mul e1 e2 =>
    let e1' := foldConstants e1
    let e2' := foldConstants e2
    match e1', e2' with
    | .const a, .const b => .const (a * b)
    | .const 0, _ => .const 0
    | _, .const 0 => .const 0
    | .const 1, e => e
    | e, .const 1 => e
    | _, _ => .mul e1' e2'
  | .pow e n =>
    let e' := foldConstants e
    match e' with
    | .const a =>
      -- Compute a^n directly
      let result := List.range n |>.foldl (fun acc _ => acc * a) 1
      .const result
    | _ =>
      if n == 0 then .const 1
      else if n == 1 then e'
      else .pow e' n

/-! ## Part 4: Optimization Pipeline -/

/-- Configuration for the optimization pipeline -/
structure OptConfig where
  /-- Maximum E-Graph saturation iterations -/
  maxIterations : Nat := 10
  /-- Maximum E-Graph nodes -/
  maxNodes : Nat := 500
  /-- Maximum E-Graph classes -/
  maxClasses : Nat := 200
  /-- Apply constant folding before E-Graph? -/
  foldConstantsFirst : Bool := true
  /-- Use only safe (reducing) rules? -/
  safeOnly : Bool := true
  deriving Repr, Inhabited

/-- Statistics from optimization -/
structure OptStats where
  /-- Original expression size (node count) -/
  originalSize : Nat
  /-- Optimized expression size -/
  optimizedSize : Nat
  /-- Operations before -/
  opsBefore : Nat
  /-- Operations after -/
  opsAfter : Nat
  /-- E-Graph iterations used -/
  iterations : Nat
  /-- E-Graph final size -/
  egraphNodes : Nat
  /-- E-Graph final classes -/
  egraphClasses : Nat
  deriving Repr

/-- Count operations in an expression -/
partial def countOps : Expr Int → Nat
  | .const _ => 0
  | .var _ => 0
  | .add e1 e2 => 1 + countOps e1 + countOps e2
  | .mul e1 e2 => 1 + countOps e1 + countOps e2
  | .pow e n => n + countOps e  -- n multiplications (naive count)

/-- Count nodes in an expression -/
partial def countNodes : Expr Int → Nat
  | .const _ => 1
  | .var _ => 1
  | .add e1 e2 => 1 + countNodes e1 + countNodes e2
  | .mul e1 e2 => 1 + countNodes e1 + countNodes e2
  | .pow e _ => 1 + countNodes e

/-- Convert OptRule to RewriteRule for E-Graph -/
def optRuleToRewriteRule (r : OptRule) : RewriteRule :=
  { name := r.name, lhs := r.lhs, rhs := r.rhs }

/-- Main optimization function -/
def optimizeExpr (expr : Expr Int) (config : OptConfig := {}) : (Expr Int × OptStats) :=
  -- Step 1: Constant folding (if enabled)
  let expr1 := if config.foldConstantsFirst then foldConstants expr else expr

  -- Step 2: E-Graph saturation
  let rules := if config.safeOnly
    then OptRule.safeRules.map optRuleToRewriteRule
    else OptRule.allRules.map optRuleToRewriteRule

  let satConfig : SaturationConfig := {
    maxIterations := config.maxIterations
    maxNodes := config.maxNodes
    maxClasses := config.maxClasses
  }

  let (result, satResult) := optimize expr1 rules satConfig

  -- Step 3: Final constant folding pass
  let finalExpr := match result with
    | some e => foldConstants e
    | none => expr1

  -- Compute statistics
  let stats : OptStats := {
    originalSize := countNodes expr
    optimizedSize := countNodes finalExpr
    opsBefore := countOps expr
    opsAfter := countOps finalExpr
    iterations := satResult.iterations
    egraphNodes := satResult.graph.numNodes
    egraphClasses := satResult.graph.numClasses
  }

  (finalExpr, stats)

/-- Calculate optimization percentage -/
def optPercentage (stats : OptStats) : Float :=
  if stats.opsBefore == 0 then 0.0
  else
    let reduction := stats.opsBefore - stats.opsAfter
    (reduction.toFloat / stats.opsBefore.toFloat) * 100.0

/-! ## Part 5: Tests and Benchmarks -/

section Tests

open Expr

/-- Test case: x + 0 → x -/
def test1 : Expr Int := .add (.var 0) (.const 0)

/-- Test case: (x * 1) + 0 → x -/
def test2 : Expr Int := .add (.mul (.var 0) (.const 1)) (.const 0)

/-- Test case: (x + y) * 0 → 0 -/
def test3 : Expr Int := .mul (.add (.var 0) (.var 1)) (.const 0)

/-- Test case: 2 + 3 → 5 (constant folding) -/
def test4 : Expr Int := .add (.const 2) (.const 3)

/-- Test case: (2 * 3) + (4 * 0) → 6 -/
def test5 : Expr Int := .add (.mul (.const 2) (.const 3)) (.mul (.const 4) (.const 0))

/-- Test case: x^0 → 1 -/
def test6 : Expr Int := .pow (.var 0) 0

/-- Test case: Complex expression with multiple optimizations
    ((x + 0) * 1) + (y * 0) → x -/
def test7 : Expr Int :=
  .add
    (.mul (.add (.var 0) (.const 0)) (.const 1))
    (.mul (.var 1) (.const 0))

/-- Test case: FRI-like pattern with constants
    (even + alpha * odd) where alpha = 0 → even -/
def testFRIZeroAlpha : Expr Int :=
  .add (.var 0) (.mul (.const 0) (.var 1))

/-- Test case: Nested optimization
    ((x * 1 + 0) * 1 + 0) → x -/
def testNested : Expr Int :=
  .add
    (.mul
      (.add (.mul (.var 0) (.const 1)) (.const 0))
      (.const 1))
    (.const 0)

/-- Run benchmark on all test cases -/
def runBenchmarks : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║              AMO-LEAN PHASE 2: OPTIMIZATION BENCHMARK                ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"
  IO.println ""

  let tests := [
    ("x + 0", test1),
    ("(x * 1) + 0", test2),
    ("(x + y) * 0", test3),
    ("2 + 3", test4),
    ("(2 * 3) + (4 * 0)", test5),
    ("x^0", test6),
    ("((x + 0) * 1) + (y * 0)", test7),
    ("even + 0 * odd (FRI α=0)", testFRIZeroAlpha),
    ("((x*1+0)*1+0)", testNested)
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
    IO.println s!"│  Nodes: {stats.originalSize} → {stats.optimizedSize}"
    IO.println s!"└─ E-Graph: {stats.iterations} iters, {stats.egraphNodes} nodes, {stats.egraphClasses} classes"
    IO.println ""

  -- Summary
  IO.println "════════════════════════════════════════════════════════════════════════"
  let totalReduction := if totalOpsBefore > 0
    then ((totalOpsBefore - totalOpsAfter).toFloat / totalOpsBefore.toFloat) * 100.0
    else 0.0
  IO.println s!"TOTAL: {totalOpsBefore} ops → {totalOpsAfter} ops"
  IO.println s!"OVERALL REDUCTION: {totalReduction.toString}%"

  if totalReduction >= 10.0 then
    IO.println "✓ PHASE 2 SUCCESS: ≥10% reduction achieved!"
  else
    IO.println "⚠ PHASE 2 TARGET: Need ≥10% reduction"

#eval runBenchmarks

end Tests

/-! ## Part 6: Integration with VecExpr (FRI Fold Optimization)

This section shows how to optimize VecExpr using the scalar optimizer.
The key insight: VecExpr operations contain scalar sub-expressions
that can be optimized.
-/

/-- Optimize the scalar part of a VecExpr smul operation -/
def optimizeSmulScalar (scalarExpr : Expr Int) : Expr Int :=
  let (result, _) := optimizeExpr scalarExpr
  result

/-- Example: Optimize FRI fold when alpha has special value -/
def exampleFRIOptimization : IO Unit := do
  IO.println ""
  IO.println "═══ FRI FOLD OPTIMIZATION EXAMPLE ═══"
  IO.println ""

  -- FRI fold: out = even + alpha * odd
  -- If alpha = 0, this simplifies to: out = even

  -- Scalar expression for alpha * odd[i]
  let alphaTimesOdd : Expr Int := .mul (.const 0) (.var 1)  -- 0 * odd_i

  let (optimized, stats) := optimizeExpr alphaTimesOdd
  IO.println s!"α * odd when α=0:"
  IO.println s!"  Before: {repr alphaTimesOdd}"
  IO.println s!"  After:  {repr optimized}"
  IO.println s!"  Reduction: {stats.opsBefore} → {stats.opsAfter} ops"

  -- Full fold expression: even + alpha * odd
  let fullFold : Expr Int := .add (.var 0) (.mul (.const 0) (.var 1))
  let (optimizedFold, foldStats) := optimizeExpr fullFold
  IO.println ""
  IO.println s!"Full FRI fold (even + α*odd) when α=0:"
  IO.println s!"  Before: {repr fullFold}"
  IO.println s!"  After:  {repr optimizedFold}"
  IO.println s!"  Reduction: {foldStats.opsBefore} → {foldStats.opsAfter} ops ({optPercentage foldStats}%)"

#eval exampleFRIOptimization

end AmoLean.EGraph.Optimize
