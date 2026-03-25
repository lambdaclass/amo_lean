/-
  AmoLean.EGraph.Verified.Bitwise.Tests — Smoke tests for Fase 21 Bitwise Verification

  Verifies that the bitwise fold operations, evalMixedOp, and rule collections
  produce correct results on concrete inputs.

  Axiom census: 0 custom axioms, 0 sorry.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedPipeline
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Tests

open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified (CircuitEnv EClassId CircuitNodeOp)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Mersenne31 fold smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Helper: check fold identity for Mersenne31 -/
private def checkMersenne31 (x : Nat) : IO Unit := do
  let p := 2 ^ 31 - 1
  let fold := (x >>> 31) + (x &&& (2 ^ 31 - 1))
  if fold % p != x % p then
    throw <| IO.userError s!"Mersenne31 fold failed for x={x}"

#eval do
  checkMersenne31 0
  checkMersenne31 1
  checkMersenne31 (2 ^ 31 - 2)   -- p - 1
  checkMersenne31 (2 ^ 31)       -- p + 1
  checkMersenne31 (2 ^ 40)
  checkMersenne31 (2 ^ 62 - 1)
  IO.println "Mersenne31 fold: all 6 tests OK"

-- ══════════════════════════════════════════════════════════════════
-- Section 2: BabyBear fold smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Helper: check fold identity for BabyBear -/
private def checkBabyBear (x : Nat) : IO Unit := do
  let p := 2 ^ 31 - 2 ^ 27 + 1
  let fold := (x >>> 31) * (2 ^ 27 - 1) + (x &&& (2 ^ 31 - 1))
  if fold % p != x % p then
    throw <| IO.userError s!"BabyBear fold failed for x={x}"

#eval do
  checkBabyBear 0
  checkBabyBear 1
  checkBabyBear 2013265920   -- p - 1
  checkBabyBear (2 ^ 40)
  IO.println "BabyBear fold: all 4 tests OK"

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Goldilocks fold smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Helper: check fold identity for Goldilocks -/
private def checkGoldilocks (x : Nat) : IO Unit := do
  let p := 2 ^ 64 - 2 ^ 32 + 1
  let fold := (x >>> 64) * (2 ^ 32 - 1) + (x &&& (2 ^ 64 - 1))
  if fold % p != x % p then
    throw <| IO.userError s!"Goldilocks fold failed for x={x}"

#eval do
  checkGoldilocks 0
  checkGoldilocks 1
  checkGoldilocks (2 ^ 64)
  checkGoldilocks (2 ^ 96)
  IO.println "Goldilocks fold: all 4 tests OK"

-- ══════════════════════════════════════════════════════════════════
-- Section 4: evalMixedOp smoke tests
-- ══════════════════════════════════════════════════════════════════

private def testEnv : CircuitEnv Nat :=
  ⟨fun i => if i == 0 then 42 else 0,
   fun i => if i == 0 then 99 else 0,
   fun i => if i == 0 then 7 else 0⟩

private def testV : EClassId → Nat :=
  fun i => if i == 0 then 100 else if i == 1 then 7 else 0

private def checkEval (label : String) (op : MixedNodeOp) (expected : Nat) : IO Unit := do
  let result := evalMixedOp op testEnv testV
  if result != expected then
    throw <| IO.userError s!"evalMixedOp {label}: got {result}, expected {expected}"

#eval do
  checkEval "shiftLeft"  (.shiftLeft 0 3)  800    -- 100 <<< 3 = 800
  checkEval "shiftRight" (.shiftRight 0 2) 25     -- 100 >>> 2 = 25
  checkEval "bitAnd"     (.bitAnd 0 1)     4      -- 100 &&& 7 = 4
  checkEval "bitXor"     (.bitXor 0 1)     99     -- 100 ^^^ 7 = 99
  checkEval "bitOr"      (.bitOr 0 1)      103    -- 100 ||| 7 = 103
  checkEval "addGate"    (.addGate 0 1)    107    -- 100 + 7 = 107
  checkEval "mulGate"    (.mulGate 0 1)    700    -- 100 * 7 = 700
  checkEval "constMask"  (.constMask 8)    255    -- 2^8 - 1 = 255
  checkEval "constGate"  (.constGate 0)    42     -- env.constVal 0 = 42
  checkEval "witness"    (.witness 0)      99     -- env.witnessVal 0 = 99
  IO.println "evalMixedOp: all 10 tests OK"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Rule collection smoke tests
-- ══════════════════════════════════════════════════════════════════

#eval do
  let rules := allBitwiseRules
  let bitwiseCount := rules.length
  if bitwiseCount != 10 then
    throw <| IO.userError s!"Expected 10 bitwise rules, got {bitwiseCount}"
  let foldRules := allFieldFoldRules
  let foldCount := foldRules.length
  if foldCount != 3 then
    throw <| IO.userError s!"Expected 3 field fold rules, got {foldCount}"
  IO.println s!"Rule collections: {bitwiseCount} bitwise + {foldCount} fold rules, OK"

#eval do
  -- Verify each bitwise rule's soundness on testEnv/testV
  let rules := allBitwiseRules
  for r in rules do
    if r.lhsEval testEnv testV != r.rhsEval testEnv testV then
      throw <| IO.userError s!"Rule '{r.name}' soundness check failed on testEnv/testV"
  IO.println "allBitwiseRules soundness spot-check: all 10 OK"

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Embedding roundtrip smoke tests
-- ══════════════════════════════════════════════════════════════════

#eval do
  -- fromMixed (toMixed op) == some op for all 7 CircuitNodeOp constructors
  let ops : List CircuitNodeOp :=
    [.constGate 5, .witness 3, .pubInput 2, .addGate 0 1,
     .mulGate 0 1, .negGate 0, .smulGate 4 1]
  for op in ops do
    if fromMixed (toMixed op) != some op then
      throw <| IO.userError s!"fromMixed/toMixed roundtrip failed for {repr op}"
  IO.println s!"Embedding roundtrip: all {ops.length} constructors OK"

-- ══════════════════════════════════════════════════════════════════
-- Section 7: isAlgebraic / isBitwise classification
-- ══════════════════════════════════════════════════════════════════

#eval do
  -- All algebraic ops
  let alg : List MixedNodeOp :=
    [.constGate 0, .witness 0, .pubInput 0, .addGate 0 1,
     .mulGate 0 1, .negGate 0, .smulGate 3 0]
  for op in alg do
    if isAlgebraic op != true then
      throw <| IO.userError s!"isAlgebraic failed for {repr op}"
    if isBitwise op != false then
      throw <| IO.userError s!"isBitwise should be false for {repr op}"
  -- All bitwise ops
  let bw : List MixedNodeOp :=
    [.shiftLeft 0 4, .shiftRight 0 4, .bitAnd 0 1,
     .bitXor 0 1, .bitOr 0 1, .constMask 8]
  for op in bw do
    if isBitwise op != true then
      throw <| IO.userError s!"isBitwise failed for {repr op}"
    if isAlgebraic op != false then
      throw <| IO.userError s!"isAlgebraic should be false for {repr op}"
  IO.println s!"Classification: {alg.length} algebraic + {bw.length} bitwise, all correct"

end AmoLean.EGraph.Verified.Bitwise.Tests
