/-
  AMO-Lean — Verified E-Graph Integration Test
  Tests the Bridge adapter: Expr Int → Verified EGraph → Expr Int
-/
import AmoLean.EGraph.Verified.Bridge

open AmoLean (Expr)
open AmoLean.EGraph.Verified
open AmoLean.EGraph.Verified.Bridge

/-! ## Test 1: Basic embedding and extraction -/

/-- x + 0 -/
def testExpr1 : Expr Int := .add (.var 0) (.const 0)

/-- x * 1 + y * 0 -/
def testExpr2 : Expr Int :=
  .add (.mul (.var 0) (.const 1))
       (.mul (.var 1) (.const 0))

/-- (x + y) * (x + y) — should share subexpressions -/
def testExpr3 : Expr Int :=
  .mul (.add (.var 0) (.var 1))
       (.add (.var 0) (.var 1))

-- Test: embedding produces valid e-graph
#eval do
  let (rootId, g) := fromExpr testExpr1
  IO.println s!"Test 1: rootId={rootId}, classes={g.numClasses}, nodes={g.numNodes}"
  return ()

#eval do
  let (rootId, g) := fromExpr testExpr2
  IO.println s!"Test 2: rootId={rootId}, classes={g.numClasses}, nodes={g.numNodes}"
  return ()

-- Test: shared subexpressions detected
#eval do
  let (rootId, g) := fromExpr testExpr3
  -- (x+y) should be shared: 3 distinct classes (x, y, x+y) + 1 mul = 4 classes
  IO.println s!"Test 3 (sharing): rootId={rootId}, classes={g.numClasses}, nodes={g.numNodes}"
  return ()

/-! ## Test 2: Cost computation and extraction -/

#eval do
  let (rootId, g) := fromExpr testExpr2
  let g' := g.computeCosts
  let result := extract g' rootId
  IO.println s!"Test 4 (extract): {repr result}"
  return ()

/-! ## Test 3: E-matching through bridge -/

-- Rule: ?a + constGate(0) → ?a  (additive identity)
def ruleAddZero : RewriteRule :=
  mkRule "add_zero" (.add (.var 0) (.const 0)) (.var 0)

-- Rule: ?a * constGate(1) → ?a  (multiplicative identity)
def ruleMulOne : RewriteRule :=
  mkRule "mul_one" (.mul (.var 0) (.const 1)) (.var 0)

-- Rule: ?a * constGate(0) → constGate(0) (multiply by zero)
def ruleMulZero : RewriteRule :=
  mkRule "mul_zero" (.mul (.var 0) (.const 0)) (.const 0)

#eval do
  -- Optimize: x + 0 → x
  let result := optimize testExpr1 [ruleAddZero]
  IO.println s!"Test 5 (x+0 → x): {repr result}"
  return ()

#eval do
  -- Optimize: x*1 + y*0 → should simplify (needs enough iterations)
  let result := optimize testExpr2 [ruleAddZero, ruleMulOne, ruleMulZero]
    { maxIterations := 10, maxNodes := 100, maxClasses := 50 }
  IO.println s!"Test 6 (x*1+y*0): {repr result}"
  return ()

/-! ## Test 4: EGraph stats -/

#eval do
  let (_, g) := fromExpr testExpr2
  let s := g.stats
  IO.println s!"Stats: classes={s.numClasses}, nodes={s.numNodes}, uf={s.unionFindSize}, worklist={s.worklistSize}"
  return ()

/-! ## Test 5: Power decomposition -/

/-- x^3 should decompose into x * x * x via mulGate chain -/
def testPow : Expr Int := .pow (.var 0) 3

#eval do
  let (rootId, g) := fromExpr testPow
  IO.println s!"Test 7 (x^3): rootId={rootId}, classes={g.numClasses}, nodes={g.numNodes}"
  -- x appears once (shared), so classes should be small
  return ()

/-! ## Test 6: Saturation config -/

#eval do
  let (rootId, g) := fromExpr (.add (.add (.var 0) (.const 0)) (.const 0))
  let result := saturate g [ruleAddZero] { maxIterations := 5 }
  IO.println s!"Test 8 (nested add_zero): saturated={result.saturated}, iters={result.iterations}, reason={result.reason}"
  let g' := result.graph.computeCosts
  let extracted := extract g' rootId
  IO.println s!"  Result: {repr extracted}"
  return ()
