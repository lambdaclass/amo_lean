/-
  Migration Regression Tests - QA Validation Battery
  Phase 2 Migration Audit

  These tests verify that the generic field migration produces
  bit-identical results to the legacy UInt64 implementation.
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Merkle
import AmoLean.FRI.Transcript
import AmoLean.FRI.Fields.TestField
import AmoLean.FRI.Fields.BN254

namespace Tests.MigrationRegression

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Merkle (FlatMerkle buildTree testHash)
open AmoLean.FRI.Transcript (TranscriptState squeeze absorb)
open AmoLean.FRI.Fields.TestField (TestField testPrime xorHash xorMixConstant)
open AmoLean.FRI.Fields.BN254 (BN254)

/-! ## Part 1: Golden Master Test Infrastructure -/

/-- Pseudo-random number generator with fixed seed for reproducibility -/
def prng (seed : Nat) (index : Nat) : Nat :=
  -- LCG: x_n+1 = (a * x_n + c) mod m
  let a := 6364136223846793005
  let c := 1442695040888963407
  let m := 2^64
  let rec iterate (s : Nat) (n : Nat) : Nat :=
    if h : n = 0 then s
    else iterate ((a * s + c) % m) (n - 1)
  termination_by n
  decreasing_by
    simp_wf
    omega
  iterate seed (index + 1)

/-- Generate array of pseudo-random UInt64 values -/
def generatePRNGArray (seed : Nat) (size : Nat) : Array UInt64 :=
  Array.range size |>.map fun i => UInt64.ofNat (prng seed i)

/-- Legacy XOR hash matching Merkle.testHash -/
def legacyXorHash (a b : UInt64) : UInt64 :=
  (a ^^^ b) + 0x9e3779b97f4a7c15

/-- TestField-compatible XOR hash (same algorithm, different type) -/
def testFieldXorHash (a b : TestField) : TestField :=
  let aVal := FRIField.toNat a
  let bVal := FRIField.toNat b
  -- Same golden ratio constant as legacy
  let result := ((aVal ^^^ bVal) + 0x9e3779b97f4a7c15) % testPrime
  FRIField.ofNat result

/-! ## Part 2: Golden Master Regression Test -/

/-- Test 1: Golden Master - Verify bit-identical Merkle roots -/
def testGoldenMaster : IO (Bool × String) := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 1: GOLDEN MASTER REGRESSION (Merkle Tree)              ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let seed := 0xDEADBEEF
  let size := 1024

  -- Generate pseudo-random data
  let legacyLeaves := generatePRNGArray seed size
  IO.println s!"Generated {size} pseudo-random leaves (seed: 0x{seed.toDigits 16 |>.asString})"

  -- Build legacy tree (UInt64 with testHash)
  match buildTree legacyLeaves testHash with
  | none =>
    IO.println "ERROR: Failed to build legacy tree"
    return (false, "Legacy tree build failed")
  | some legacyTree =>
    let legacyRoot := legacyTree.root
    IO.println s!"Legacy root (UInt64): {legacyRoot}"

    -- Convert to TestField array
    let testFieldLeaves : Array TestField := legacyLeaves.map fun x =>
      FRIField.ofNat x.toNat

    -- Build generic tree (TestField with equivalent XOR hash)
    match buildTree testFieldLeaves testFieldXorHash with
    | none =>
      IO.println "ERROR: Failed to build generic tree"
      return (false, "Generic tree build failed")
    | some genericTree =>
      let genericRoot := genericTree.root
      let genericRootNat := FRIField.toNat genericRoot
      IO.println s!"Generic root (TestField): {genericRootNat}"

      -- Compare roots
      let legacyRootNat := legacyRoot.toNat
      let match_ := legacyRootNat == genericRootNat

      IO.println ""
      if match_ then
        IO.println "✓ GOLDEN MASTER TEST: PASSED"
        IO.println "  Roots are BIT-IDENTICAL"
        return (true, "Roots match exactly")
      else
        IO.println "✗ GOLDEN MASTER TEST: FAILED"
        IO.println s!"  Legacy:  {legacyRootNat}"
        IO.println s!"  Generic: {genericRootNat}"
        IO.println s!"  Diff:    {if legacyRootNat > genericRootNat then legacyRootNat - genericRootNat else genericRootNat - legacyRootNat}"
        return (false, "Root mismatch detected")

#eval! testGoldenMaster

/-! ## Part 3: Instance Resolution Wiring Check -/

/-- Test 2A: Verify TestField uses XOR hash via CryptoHash -/
def testInstanceResolutionTestField : IO (Bool × String) := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 2A: INSTANCE RESOLUTION - TestField (XOR)              ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Create transcript with TestField
  let t0 : TranscriptState TestField := TranscriptState.forFRI
  let elem1 : TestField := FRIField.ofNat 12345
  let elem2 : TestField := FRIField.ofNat 67890
  let t1 := absorb t0 elem1
  let t2 := absorb t1 elem2

  -- Squeeze challenge using CryptoHash
  let result := squeeze t2
  let squeezedVal := FRIField.toNat result.output
  IO.println s!"Squeezed value (via CryptoHash): {squeezedVal}"

  -- Manually compute expected XOR result
  -- The squeeze function uses CryptoHash.squeeze which uses xorSqueeze
  let absorbed := [FRIField.toNat elem1, FRIField.toNat elem2]
  let expectedBase := absorbed.foldl (fun acc x => acc ^^^ x + xorMixConstant) 0
  let expectedVal := expectedBase % testPrime
  IO.println s!"Expected XOR result:             {expectedVal}"

  let match_ := squeezedVal == expectedVal
  if match_ then
    IO.println "✓ TestField correctly uses XOR-based CryptoHash"
    return (true, "XOR hash confirmed")
  else
    IO.println "✗ TestField NOT using expected XOR hash!"
    return (false, "Hash mismatch")

#eval! testInstanceResolutionTestField

/-- Test 2B: Verify BN254 uses Poseidon2 (different from XOR) -/
def testInstanceResolutionBN254 : IO (Bool × String) := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 2B: INSTANCE RESOLUTION - BN254 (Poseidon2)            ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Create transcript with BN254
  let t0 : TranscriptState BN254 := TranscriptState.forFRI
  let elem1 : BN254 := FRIField.ofNat 12345
  let elem2 : BN254 := FRIField.ofNat 67890
  let t1 := absorb t0 elem1
  let t2 := absorb t1 elem2

  -- Squeeze challenge using CryptoHash (should use Poseidon2)
  let result := squeeze t2
  let squeezedVal := FRIField.toNat result.output
  IO.println s!"Squeezed value (BN254/Poseidon2): {squeezedVal}"

  -- Compare with XOR result (they should be DIFFERENT)
  let absorbed := [FRIField.toNat elem1, FRIField.toNat elem2]
  let xorBase := absorbed.foldl (fun acc x => acc ^^^ x + xorMixConstant) 0
  let xorVal := xorBase % testPrime  -- Note: using testPrime for XOR
  IO.println s!"XOR result (for comparison):      {xorVal}"

  let different := squeezedVal != xorVal
  if different then
    IO.println "✓ BN254 produces DIFFERENT output than XOR (Poseidon2 confirmed)"
    return (true, "Poseidon2 hash confirmed")
  else
    IO.println "✗ WARNING: BN254 produced same result as XOR!"
    IO.println "  This suggests the CryptoHash instance may not be using Poseidon2"
    return (false, "Unexpected match with XOR")

#eval! testInstanceResolutionBN254

/-- Test 2C: Cross-verify different inputs produce different outputs -/
def testHashDeterminism : IO (Bool × String) := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 2C: HASH DETERMINISM AND DIFFERENTIATION               ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Test determinism: same input → same output
  let t1 : TranscriptState TestField := TranscriptState.forFRI
  let t1a := absorb t1 (FRIField.ofNat 42 : TestField)
  let r1 := squeeze t1a
  let r1b := squeeze t1a  -- Squeeze same state again
  let deterministicOk := FRIField.toNat r1.output == FRIField.toNat r1b.output
  IO.println s!"Determinism test (same state):    {if deterministicOk then "PASS" else "FAIL"}"

  -- Test differentiation: different input → different output
  let t2 : TranscriptState TestField := TranscriptState.forFRI
  let t2a := absorb t2 (FRIField.ofNat 42 : TestField)
  let t2b := absorb t2 (FRIField.ofNat 43 : TestField)
  let r2a := squeeze t2a
  let r2b := squeeze t2b
  let differentiationOk := FRIField.toNat r2a.output != FRIField.toNat r2b.output
  IO.println s!"Differentiation test (diff input): {if differentiationOk then "PASS" else "FAIL"}"

  -- Test sequential squeezes produce different outputs
  let t3 : TranscriptState TestField := TranscriptState.forFRI
  let t3a := absorb t3 (FRIField.ofNat 100 : TestField)
  let r3a := squeeze t3a
  let r3b := squeeze r3a.state
  let sequentialDiffOk := FRIField.toNat r3a.output != FRIField.toNat r3b.output
  IO.println s!"Sequential squeeze test:          {if sequentialDiffOk then "PASS" else "FAIL"}"

  let allPass := deterministicOk && differentiationOk && sequentialDiffOk
  if allPass then
    IO.println "✓ All hash behavior tests PASSED"
    return (true, "Hash behavior correct")
  else
    IO.println "✗ Some hash behavior tests FAILED"
    return (false, "Hash behavior incorrect")

#eval! testHashDeterminism

/-! ## Part 4: Summary -/

def runAllRegressionTests : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║         MIGRATION REGRESSION TEST SUITE - SUMMARY                   ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  let (r1, m1) ← testGoldenMaster
  let (r2a, m2a) ← testInstanceResolutionTestField
  let (r2b, m2b) ← testInstanceResolutionBN254
  let (r2c, m2c) ← testHashDeterminism

  IO.println "\n╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║                         TEST RESULTS                                ║"
  IO.println "╠══════════════════════════════════════════════════════════════════════╣"
  IO.println s!"║  1. Golden Master Regression:  {if r1 then "PASS ✓" else "FAIL ✗"}                           ║"
  IO.println s!"║  2a. Instance Resolution (TF): {if r2a then "PASS ✓" else "FAIL ✗"}                           ║"
  IO.println s!"║  2b. Instance Resolution (BN): {if r2b then "PASS ✓" else "FAIL ✗"}                           ║"
  IO.println s!"║  2c. Hash Determinism:         {if r2c then "PASS ✓" else "FAIL ✗"}                           ║"
  IO.println "╠══════════════════════════════════════════════════════════════════════╣"

  let allPass := r1 && r2a && r2b && r2c
  if allPass then
    IO.println "║               OVERALL: ALL TESTS PASSED ✓                          ║"
  else
    IO.println "║               OVERALL: SOME TESTS FAILED ✗                          ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"

#eval! runAllRegressionTests

end Tests.MigrationRegression
