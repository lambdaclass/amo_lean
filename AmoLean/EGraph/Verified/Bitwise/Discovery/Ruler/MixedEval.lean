/-
  AMO-Lean — Ruler/MixedEval: Concrete Evaluator for MixedNodeOp
  Fase 27 N27.10: Wires Ruler's generic evalOp to AMO-Lean's concrete operations.

  Provides:
  - `mixedEvalOp`: concrete evaluator for MixedNodeOp operations
  - `mixedOps`: available operations for Ruler enumeration
  - `mixedWorkload`: standard test inputs for CVec computation
  - `discoverMixedRules`: end-to-end rule discovery for MixedNodeOp

  Reuses: VerificationOracle (test inputs), ShiftAddGen (CSD ops),
          RulerDiscovery (basic CVec from Fase 26)
  Consumed by: N27.17 (E2E tests)
-/
import AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler.Core
import AmoLean.EGraph.Verified.Bitwise.Discovery.VerificationOracle

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler.MixedEval

open AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: MixedNodeOp Evaluator
-- ══════════════════════════════════════════════════════════════════

/-- Concrete evaluator for MixedNodeOp, encoded as opId → childVals → result.
    OpIds:
    0 = add, 1 = sub, 2 = mul, 3 = bitwise AND, 4 = bitwise OR,
    5 = shift left, 6 = shift right, 7 = mod (reduceGate) -/
def mixedEvalOp : Nat → List Nat → Nat
  | 0, [a, b] => a + b        -- addGate
  | 1, [a, b] => a - b        -- subGate (wrapping)
  | 2, [a, b] => a * b        -- mulGate
  | 3, [a, b] => a &&& b      -- bitwiseAnd
  | 4, [a, b] => a ||| b      -- bitwiseOr
  | 5, [a, b] => a <<< b      -- shiftLeft
  | 6, [a, b] => a >>> b      -- shiftRight
  | 7, [a, b] => if b > 0 then a % b else 0  -- reduceGate (mod p)
  -- Reduction alternatives: ALL have same denotational semantics (x % p)
  -- Ruler discovers this equivalence automatically via CVec matching!
  | 8, [a, b] => if b > 0 then a % b else 0  -- solinasFold(x, p)
  | 9, [a, b, _] => if b > 0 then a % b else 0  -- montyReduce(x, p, mu)
  | 10, [a, b, _] => if b > 0 then a % b else 0  -- barrettReduce(x, p, m)
  | 11, [a, b] => if b > 0 then a % b else 0  -- harveyReduce(x, p)
  | _, _ => 0

/-- Available operations for Ruler enumeration.
    Includes ALL reduction alternatives so Ruler can discover their equivalence. -/
def mixedOps : List OpSpec := [
  { opId := 0, arity := 2, name := "add" },
  { opId := 1, arity := 2, name := "sub" },
  { opId := 2, arity := 2, name := "mul" },
  { opId := 3, arity := 2, name := "and" },
  { opId := 5, arity := 2, name := "shl" },
  { opId := 6, arity := 2, name := "shr" },
  { opId := 7, arity := 2, name := "mod" },
  { opId := 8, arity := 2, name := "solinasFold" },
  { opId := 9, arity := 2, name := "montyReduce" },   -- arity 2 for Ruler (p baked into input)
  { opId := 10, arity := 2, name := "barrettReduce" }, -- arity 2 for Ruler
  { opId := 11, arity := 2, name := "harveyReduce" }
]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Test Inputs for CVec Computation
-- ══════════════════════════════════════════════════════════════════

/-- Standard test inputs — includes BabyBear-range values for reduction discovery.
    var 0 = input value, var 1 = prime (or second operand), var 2 = third operand. -/
def mixedWorkloadInputs : Array (Nat → Nat) := #[
  -- Generic bitwise
  fun i => [5, 3, 7].getD i 0,
  fun i => [256, 16, 4].getD i 0,
  fun i => [0xFFFF, 0xFF, 8].getD i 0,
  -- BabyBear reduction: x mod p where p = 2013265921
  fun i => [1000000, 2013265921, 0].getD i 0,
  fun i => [3000000000, 2013265921, 0].getD i 0,
  fun i => [500, 2013265921, 0].getD i 0,
  -- Edge cases
  fun i => [0, 2013265921, 0].getD i 0,
  fun i => [2013265920, 2013265921, 0].getD i 0,  -- p-1
  -- Varied primes
  fun i => [100000, 2147483647, 0].getD i 0,  -- Mersenne31
  fun i => [65536, 256, 16].getD i 0
]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: End-to-End Rule Discovery
-- ══════════════════════════════════════════════════════════════════

/-- Discover rewrite rules for MixedNodeOp using the Ruler pipeline. -/
def discoverMixedRules (cfg : RulerConfig := { maxDepth := 2, maxIterations := 3 }) :
    ImprovementState :=
  improvementLoop mixedEvalOp mixedOps mixedWorkloadInputs cfg

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

-- mixedEvalOp basic tests
example : mixedEvalOp 0 [3, 5] = 8 := rfl      -- add
example : mixedEvalOp 2 [3, 5] = 15 := rfl     -- mul
example : mixedEvalOp 7 [17, 5] = 2 := rfl     -- mod
example : mixedEvalOp 3 [0xFF, 0x0F] = 0x0F := by native_decide  -- and

-- Ruler discovery smoke test
#eval do
  let result := discoverMixedRules { maxDepth := 1, maxIterations := 1 }
  return s!"Discovered {result.rules.length} rules in {result.iteration} iterations"

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.Discovery.Ruler.MixedEval
