/-
  AMO-Lean: Oracle Testing for FRI Fold
  Phase 0 Differential Testing

  This module verifies that the generated C code produces
  the same results as the Lean reference implementation.

  The oracle testing process:
  1. Generate pseudo-random test inputs
  2. Compute expected result using Lean reference (friFoldArray)
  3. Run C implementation via subprocess (oracle_test)
  4. Compare results - they must match exactly
-/

namespace Tests.Oracle.FriFoldOracle

/-! ## Part 1: Test Vector Generation -/

/-- LCG pseudo-random number generator state -/
structure LCGState where
  seed : UInt64
  deriving Repr

/-- Advance LCG state and return next value -/
def LCGState.next (s : LCGState) : UInt64 × LCGState :=
  let newSeed := s.seed * 6364136223846793005 + 1442695040888963407
  (newSeed, { seed := newSeed })

/-- Generate array of pseudo-random UInt64 values -/
def generateArray (size : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut arr := Array.mkEmpty size
  let mut state : LCGState := { seed := seed }
  for _ in [0:size] do
    let (val, newState) := state.next
    arr := arr.push val
    state := newState
  return arr

/-! ## Part 2: Lean Reference Implementation -/

/-- Reference FRI fold: out[i] = even[i] + alpha * odd[i] -/
def friFoldRef (even odd : Array UInt64) (alpha : UInt64) : Array UInt64 :=
  Array.zipWith even odd (fun e o => e + alpha * o)

/-! ## Part 3: Oracle Interface (Subprocess) -/

/-- Format input for C oracle -/
def formatOracleInput (even odd : Array UInt64) (alpha : UInt64) : String :=
  let sizeLine := s!"{even.size} {alpha}"
  let evenLine := " ".intercalate (even.toList.map toString)
  let oddLine := " ".intercalate (odd.toList.map toString)
  s!"{sizeLine}\n{evenLine}\n{oddLine}\n"

/-- Parse output from C oracle -/
def parseOracleOutput (output : String) : Option (Array UInt64) :=
  let trimmed := output.trim
  if trimmed.isEmpty then none
  else
    let parts := trimmed.splitOn " "
    let vals := parts.filterMap String.toNat?
    if vals.isEmpty then none
    else some (vals.map (·.toUInt64) |>.toArray)

/-- Run C oracle and get result -/
def runCOracle (even odd : Array UInt64) (alpha : UInt64) : IO (Option (Array UInt64)) := do
  let oraclePath := "generated/oracle_test"
  let input := formatOracleInput even odd alpha

  -- Write input to temp file
  let tmpFile := "/tmp/oracle_input.txt"
  IO.FS.writeFile tmpFile input

  -- Run oracle with input from file
  let output ← IO.Process.output {
    cmd := "/bin/sh"
    args := #["-c", s!"{oraclePath} < {tmpFile}"]
    cwd := some "."
  }

  if output.exitCode != 0 then
    return none

  return parseOracleOutput output.stdout

/-! ## Part 4: Test Cases -/

/-- Result of a single oracle test -/
structure OracleTestResult where
  testName : String
  size : Nat
  passed : Bool
  leanResult : Array UInt64
  cResult : Option (Array UInt64)
  mismatchIndex : Option Nat
  deriving Repr

/-- Compare two arrays and find first mismatch -/
def findFirstMismatch (a b : Array UInt64) : Option Nat := Id.run do
  if a.size != b.size then
    return some 0
  for i in [0:a.size] do
    if a[i]! != b[i]! then
      return some i
  return none

/-- Run a single oracle test -/
def runOracleTest (testName : String) (even odd : Array UInt64) (alpha : UInt64) : IO OracleTestResult := do
  IO.println s!"  Running {testName}..."

  -- Compute Lean reference
  let leanResult := friFoldRef even odd alpha

  -- Run C oracle
  let cResultOpt ← runCOracle even odd alpha

  match cResultOpt with
  | none =>
    IO.println s!"    ❌ C oracle failed to execute"
    return {
      testName, size := even.size, passed := false
      leanResult, cResult := none, mismatchIndex := none
    }
  | some cResult =>
    let mismatch := findFirstMismatch leanResult cResult
    match mismatch with
    | none =>
      IO.println s!"    ✅ PASS: Lean and C match ({even.size} elements)"
      return {
        testName, size := even.size, passed := true
        leanResult, cResult := some cResult, mismatchIndex := none
      }
    | some idx =>
      IO.println s!"    ❌ FAIL: Mismatch at index {idx}"
      IO.println s!"       Lean[{idx}] = {leanResult[idx]!}"
      IO.println s!"       C[{idx}]    = {cResult[idx]!}"
      return {
        testName, size := even.size, passed := false
        leanResult, cResult := some cResult, mismatchIndex := some idx
      }

/-! ## Part 5: Predefined Test Cases -/

/-- Test case: small fixed values -/
def testSmallFixed : IO OracleTestResult := do
  let even := #[1, 2, 3, 4]
  let odd := #[10, 20, 30, 40]
  let alpha : UInt64 := 2
  runOracleTest "Small Fixed (size=4)" even odd alpha

/-- Test case: zero alpha -/
def testZeroAlpha : IO OracleTestResult := do
  let even := #[100, 200, 300, 400]
  let odd := #[1, 2, 3, 4]
  let alpha : UInt64 := 0
  runOracleTest "Zero Alpha (size=4)" even odd alpha

/-- Test case: random medium -/
def testRandomMedium : IO OracleTestResult := do
  let even := generateArray 16 12345
  let odd := generateArray 16 67890
  let alpha : UInt64 := 0xDEADBEEF
  runOracleTest "Random Medium (size=16)" even odd alpha

/-- Test case: random large -/
def testRandomLarge : IO OracleTestResult := do
  let even := generateArray 256 11111
  let odd := generateArray 256 22222
  let alpha : UInt64 := 0xCAFEBABE
  runOracleTest "Random Large (size=256)" even odd alpha

/-- Test case: overflow-prone values -/
def testOverflow : IO OracleTestResult := do
  let even := #[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 2]
  let odd := #[0xFFFFFFFFFFFFFFFF, 1, 0xFFFFFFFFFFFFFFFF, 3]
  let alpha : UInt64 := 0xFFFFFFFFFFFFFFFF
  runOracleTest "Overflow-Prone (size=4)" even odd alpha

/-- Test case: random very large -/
def testRandomVeryLarge : IO OracleTestResult := do
  let even := generateArray 1024 33333
  let odd := generateArray 1024 44444
  let alpha : UInt64 := 0x123456789ABCDEF0
  runOracleTest "Random Very Large (size=1024)" even odd alpha

/-! ## Part 6: Test Runner -/

/-- Run all oracle tests -/
def runAllTests : IO (List OracleTestResult) := do
  let mut results : List OracleTestResult := []

  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     ORACLE TESTING: FRI Fold (Lean vs C)                     ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  results := results ++ [← testSmallFixed]
  results := results ++ [← testZeroAlpha]
  results := results ++ [← testRandomMedium]
  results := results ++ [← testRandomLarge]
  results := results ++ [← testOverflow]
  results := results ++ [← testRandomVeryLarge]

  IO.println ""
  IO.println "════════════════════════════════════════════════════════════════"

  let passed := results.filter (·.passed) |>.length
  let total := results.length

  if passed == total then
    IO.println s!"ORACLE TESTING: ALL {total} TESTS PASSED ✅"
  else
    IO.println s!"ORACLE TESTING: {passed}/{total} TESTS PASSED ⚠️"

  IO.println "════════════════════════════════════════════════════════════════"

  return results

/-- Main entry point -/
def runOracleTests : IO UInt32 := do
  let results ← runAllTests

  let allPassed := results.all (·.passed)
  return if allPassed then 0 else 1

end Tests.Oracle.FriFoldOracle

/-- Main entry point for executable -/
def main : IO UInt32 := Tests.Oracle.FriFoldOracle.runOracleTests
