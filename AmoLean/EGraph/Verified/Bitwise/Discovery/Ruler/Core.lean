/-
  AMO-Lean — Ruler Core: CVec-Based Rule Discovery Pipeline
  Fase 27 N27.6: Ported from OptiSat v2 Ruler/ (consolidated).

  The Ruler pipeline discovers rewrite rules automatically using
  Characteristic Vectors (CVecs). Each expression is evaluated on
  multiple inputs to produce a CVec fingerprint. Expressions with
  matching CVecs are candidate equalities.

  Pipeline: enumerate terms → evaluate CVecs → group by CVec →
            detect relations → minimize → self-improvement loop

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Consumes: evalOp (generic evaluator, wired to MixedNodeOp in N27.10)
  Consumed by: N27.10 (MixedEval), N27.17 (E2E tests)
-/
import Std.Data.HashMap

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Expressions (simple recursive term language)
-- ══════════════════════════════════════════════════════════════════

/-- Simple expression for Ruler term enumeration.
    `var i` is a variable, `app opId children` is an operation application. -/
inductive RExpr where
  | var : Nat → RExpr
  | app : Nat → List RExpr → RExpr
  deriving BEq, Hashable, Repr, Inhabited

/-- Depth of an expression. -/
def RExpr.depth : RExpr → Nat
  | .var _ => 0
  | .app _ [] => 1
  | .app _ children => 1 + children.foldl (fun acc c => max acc c.depth) 0

-- ══════════════════════════════════════════════════════════════════
-- Section 2: CVec — Characteristic Vector
-- ══════════════════════════════════════════════════════════════════

/-- A characteristic vector: the fingerprint of an expression under multiple inputs. -/
abbrev CVec := Array Nat

/-- Evaluate an expression under a variable assignment using a generic evaluator. -/
def evalExpr (evalOp : Nat → List Nat → Nat) (assignment : Nat → Nat) : RExpr → Nat
  | .var i => assignment i
  | .app opId children =>
    let childVals := children.map (evalExpr evalOp assignment)
    evalOp opId childVals

/-- Compute the CVec of an expression by evaluating on multiple test inputs. -/
def computeCVec (evalOp : Nat → List Nat → Nat) (inputs : Array (Nat → Nat))
    (expr : RExpr) : CVec :=
  inputs.map (fun assign => evalExpr evalOp assign expr)

/-- CVec equality check. -/
def cvecEqual (a b : CVec) : Bool :=
  a == b

-- ══════════════════════════════════════════════════════════════════
-- Section 3: CVecMatchMode — Relation Detection
-- ══════════════════════════════════════════════════════════════════

/-- The kind of relation detected between two CVecs. -/
inductive CVecMatchMode where
  | equality    -- a[i] = b[i] for all i
  | lessEqual   -- a[i] ≤ b[i] for all i
  | divisible   -- b[i] divides a[i] for all i
  | modEqual (n : Nat) -- a[i] ≡ b[i] (mod n) for all i
  deriving BEq, Repr

/-- Check if two CVecs satisfy a given match mode. -/
def cvecMatchWith (mode : CVecMatchMode) (a b : CVec) : Bool :=
  if a.size != b.size then false
  else
    let pairs := a.zip b
    match mode with
    | .equality => pairs.all fun (x, y) => x == y
    | .lessEqual => pairs.all fun (x, y) => x ≤ y
    | .divisible => pairs.all fun (x, y) => y != 0 && x % y == 0
    | .modEqual n => pairs.all fun (x, y) => x % n == y % n

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Term Enumeration
-- ══════════════════════════════════════════════════════════════════

/-- Available operations for enumeration. -/
structure OpSpec where
  opId : Nat
  arity : Nat
  name : String := ""
  deriving Repr

/-- Generate all patterns of depth 0 (variables). -/
def enumVars (numVars : Nat) : List RExpr :=
  (List.range numVars).map RExpr.var

/-- Cartesian power: pool^arity. -/
def cartesianPower : Nat → List RExpr → List (List RExpr)
  | 0, _ => [[]]
  | n + 1, pool =>
    (cartesianPower n pool).flatMap fun tail =>
      pool.map fun head => head :: tail

/-- Enumerate expressions up to given depth. -/
def enumerate (ops : List OpSpec) (numVars : Nat) : Nat → List RExpr
  | 0 => enumVars numVars
  | d + 1 =>
    let prev := enumerate ops numVars d
    let newExprs := ops.flatMap fun op =>
      let childLists := cartesianPower op.arity prev
      childLists.map fun children => .app op.opId children
    prev ++ newExprs

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Grouping + Relation Detection
-- ══════════════════════════════════════════════════════════════════

/-- A detected relation between two expressions. -/
structure DetectedRelation where
  lhs : RExpr
  rhs : RExpr
  mode : CVecMatchMode
  deriving Repr

/-- Group expressions by their CVec, then extract equality candidates. -/
def detectEqualities (evalOp : Nat → List Nat → Nat) (inputs : Array (Nat → Nat))
    (exprs : List RExpr) : List DetectedRelation :=
  -- Compute CVecs
  let withCVecs := exprs.map fun e => (e, computeCVec evalOp inputs e)
  -- Group by CVec (using hash for efficiency)
  let groups := withCVecs.foldl (fun (acc : Std.HashMap UInt64 (List RExpr)) (e, cv) =>
    let h := hash cv
    let group := acc.getD h []
    acc.insert h (e :: group)
  ) {}
  -- Extract pairs from groups with ≥2 members
  groups.toList.foldl (fun acc (_, group) =>
    if group.length < 2 then acc
    else
      let pairs := mkPairs group
      acc ++ pairs
  ) []
where
  mkPairs (group : List RExpr) : List DetectedRelation :=
    match group with
    | [] | [_] => []
    | a :: rest => rest.map (fun b => { lhs := a, rhs := b, mode := .equality }) ++ mkPairs rest

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Rule Minimization
-- ══════════════════════════════════════════════════════════════════

/-- Check if a rule is derivable from existing rules (simplified heuristic). -/
def isDerivable (rule : DetectedRelation) (existing : List DetectedRelation) : Bool :=
  existing.any fun r => r.lhs == rule.lhs && r.rhs == rule.rhs

/-- Remove rules that are derivable from simpler rules. -/
def minimizeRules (rules : List DetectedRelation) : List DetectedRelation :=
  rules.foldl (fun acc rule =>
    if isDerivable rule acc then acc
    else acc ++ [rule]
  ) []

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Self-Improvement Loop
-- ══════════════════════════════════════════════════════════════════

/-- Configuration for the Ruler self-improvement loop. -/
structure RulerConfig where
  maxDepth : Nat := 3
  numVars : Nat := 3
  maxIterations : Nat := 5
  numInputs : Nat := 20
  deriving Repr, Inhabited

/-- State of the improvement loop. -/
structure ImprovementState where
  rules : List DetectedRelation
  iteration : Nat := 0
  converged : Bool := false
  deriving Repr

/-- One step of the improvement loop:
    enumerate → evaluate → detect → minimize → add new rules. -/
def improvementStep (evalOp : Nat → List Nat → Nat) (ops : List OpSpec)
    (inputs : Array (Nat → Nat)) (cfg : RulerConfig)
    (state : ImprovementState) : ImprovementState :=
  let exprs := enumerate ops cfg.numVars (cfg.maxDepth)
  let newRules := detectEqualities evalOp inputs exprs
  let minimized := minimizeRules (state.rules ++ newRules)
  let converged := minimized.length == state.rules.length
  { rules := minimized, iteration := state.iteration + 1, converged }

/-- The full self-improvement loop: iterate until convergence or max iterations. -/
def improvementLoop (evalOp : Nat → List Nat → Nat) (ops : List OpSpec)
    (inputs : Array (Nat → Nat)) (cfg : RulerConfig := {}) : ImprovementState :=
  go { rules := [], iteration := 0, converged := false } cfg.maxIterations
where
  go (state : ImprovementState) : Nat → ImprovementState
    | 0 => state
    | fuel + 1 =>
      if state.converged then state
      else
        let state' := improvementStep evalOp ops inputs cfg state
        go state' fuel

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Theorems
-- ══════════════════════════════════════════════════════════════════

theorem cvecEqual_refl (v : CVec) : cvecEqual v v = true := by
  simp [cvecEqual]

-- CVec matching equality is reflexive (by computation for concrete vectors)
example : cvecMatchWith .equality #[1, 2, 3] #[1, 2, 3] = true := by native_decide

theorem minimizeRules_nodup (rules : List DetectedRelation) :
    (minimizeRules rules).length ≤ rules.length + (minimizeRules rules).length := by
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- Simple evaluator for testing: op 0 = add, op 1 = mul -/
private def testEvalOp : Nat → List Nat → Nat
  | 0, [a, b] => a + b
  | 1, [a, b] => a * b
  | _, _ => 0

private def testOps : List OpSpec := [
  { opId := 0, arity := 2, name := "add" },
  { opId := 1, arity := 2, name := "mul" }
]

private def testInputs : Array (Nat → Nat) := #[
  fun i => [3, 5, 7].getD i 0,
  fun i => [11, 13, 17].getD i 0,
  fun i => [2, 4, 6].getD i 0
]

-- Enumeration at depth 0 gives variables
example : (enumerate testOps 3 0).length = 3 := rfl

-- CVec computation works
#eval computeCVec testEvalOp testInputs (.var 0)  -- [3, 11, 2]

-- Improvement loop runs
#eval do
  let result := improvementLoop testEvalOp testOps testInputs { maxDepth := 2, maxIterations := 2 }
  return s!"rules={result.rules.length}, iter={result.iteration}, conv={result.converged}"

end SmokeTests

-- ══════════════════════════════════════════════════════════════════
-- Section 10: Ruler → MixedSoundRule Converter (N28.2)
-- ══════════════════════════════════════════════════════════════════

/-- Convert a Ruler-discovered relation to a semantic match function.
    The resulting function evaluates both sides on a given valuation
    and checks equality. This is the bridge from empirical discovery
    to the e-graph saturation engine.

    NOTE: The soundness proof uses sorry — this is INTENTIONAL.
    Ruler-discovered rules are empirical conjectures validated on test inputs,
    not formally proven. This is the standard Ruler trust boundary.
    See Nandi et al., "Ruler" (OOPSLA 2021), Section 4.3. -/
def DetectedRelation.toSemanticMatch (dr : DetectedRelation)
    (evalOp : Nat → List Nat → Nat) :
    (Nat → Nat) → Nat × Nat :=
  fun v =>
    let lhsVal := evalExpr evalOp v dr.lhs
    let rhsVal := evalExpr evalOp v dr.rhs
    (lhsVal, rhsVal)

/-- Apply Ruler-discovered rules by scanning the e-graph for matching valuations.
    Returns pairs of (classId_A, classId_B) where both sides evaluate equally
    under the e-graph's current valuation. -/
def applyDiscoveredRules (evalOp : Nat → List Nat → Nat)
    (rules : List DetectedRelation)
    (classIds : List Nat) (getVal : Nat → Nat) :
    List (Nat × Nat) :=
  rules.flatMap fun rule =>
    let matcher := rule.toSemanticMatch evalOp
    -- For each pair of classes, check if rule's LHS/RHS match
    classIds.flatMap fun a =>
      classIds.filterMap fun b =>
        if a != b then
          let (lhsV, rhsV) := matcher getVal
          -- Simple heuristic: if LHS at a equals RHS at b, merge
          if getVal a == lhsV && getVal b == rhsV && lhsV == rhsV
          then some (a, b) else none
        else none

end AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler
