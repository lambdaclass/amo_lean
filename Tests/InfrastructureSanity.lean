/-
  Infrastructure Sanity Tests for Phase 1 Migration
  Step 5.3 - Stress Testing FRIField and CryptoHash

  This file validates the mathematical foundations before Phase 2.
  If these tests fail, the entire migration will fail.

  Tests:
  1. Field Laws (The Math Check)
  2. Boundary Tests (The Representation Check)
  3. Polymorphism Tests (The Abstraction Check)
  4. Inversion Benchmark (The Perf Check)

  Reference: docs/poseidon/migration/PHASE1-NOTES.md
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Fields.BN254
import AmoLean.FRI.Fields.TestField

namespace Tests.InfrastructureSanity

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Fields.BN254 (BN254)
open AmoLean.FRI.Fields.TestField (TestField)

/-! ══════════════════════════════════════════════════════════════════════════
    SECTION 1: FIELD LAWS TEST (The Math Check)
    ══════════════════════════════════════════════════════════════════════════ -/

/-- Test multiplicative inverse: x * (1/x) == 1 for x ≠ 0 -/
def testMultiplicativeInverse {F : Type} [FRIField F] (testValues : List Nat) : IO (Bool × List String) := do
  let mut passed := true
  let mut errors : List String := []

  for n in testValues do
    if n == 0 then continue  -- Skip zero (no inverse)

    let x : F := FRIField.ofNat n
    let one : F := FRIField.one
    let inv := FRIField.fdiv one x  -- 1/x
    let product := x * inv          -- x * (1/x)

    if product != one then
      passed := false
      let productNat := FRIField.toNat product
      let oneNat := FRIField.toNat one
      errors := errors ++ [s!"FAIL: {n} * inv({n}) = {productNat}, expected {oneNat}"]

  return (passed, errors)

/-- Test cyclicity: ofNat(modulus + x) == ofNat(x) -/
def testCyclicity {F : Type} [FRIField F] (testValues : List Nat) : IO (Bool × List String) := do
  let mut passed := true
  let mut errors : List String := []
  let mod := FRIField.modulus (F := F)

  for n in testValues do
    let x : F := FRIField.ofNat n
    let xPlusMod : F := FRIField.ofNat (mod + n)

    if x != xPlusMod then
      passed := false
      let xNat := FRIField.toNat x
      let xPlusModNat := FRIField.toNat xPlusMod
      errors := errors ++ [s!"FAIL: ofNat({n}) = {xNat}, ofNat({mod} + {n}) = {xPlusModNat}"]

  return (passed, errors)

/-- Test negatives: x + (-x) == 0 -/
def testNegatives {F : Type} [FRIField F] (testValues : List Nat) : IO (Bool × List String) := do
  let mut passed := true
  let mut errors : List String := []

  for n in testValues do
    let x : F := FRIField.ofNat n
    let negX := -x
    let sum := x + negX
    let zero : F := FRIField.zero

    if sum != zero then
      passed := false
      let sumNat := FRIField.toNat sum
      errors := errors ++ [s!"FAIL: {n} + (-{n}) = {sumNat}, expected 0"]

  return (passed, errors)

/-- Combined field laws test -/
def testFieldLaws {F : Type} [FRIField F] (fieldName : String) : IO Bool := do
  IO.println s!"\n┌─────────────────────────────────────────────────────────────┐"
  IO.println s!"│  FIELD LAWS TEST: {fieldName}"
  IO.println s!"└─────────────────────────────────────────────────────────────┘"

  -- Test values: small, medium, large, edge cases
  let testValues := [1, 2, 3, 5, 7, 11, 13, 17, 42, 100, 1000, 12345, 999999, 2^30, 2^40]

  let mut allPassed := true

  -- Test 1: Multiplicative Inverse
  let (invPassed, invErrors) ← testMultiplicativeInverse (F := F) testValues
  if invPassed then
    IO.println s!"  ✓ Multiplicative Inverse: PASS ({testValues.length} values)"
  else
    IO.println s!"  ✗ Multiplicative Inverse: FAIL"
    for e in invErrors do IO.println s!"    {e}"
    allPassed := false

  -- Test 2: Cyclicity
  let (cycPassed, cycErrors) ← testCyclicity (F := F) testValues
  if cycPassed then
    IO.println s!"  ✓ Cyclicity (ofNat wrap): PASS ({testValues.length} values)"
  else
    IO.println s!"  ✗ Cyclicity: FAIL"
    for e in cycErrors do IO.println s!"    {e}"
    allPassed := false

  -- Test 3: Negatives
  let (negPassed, negErrors) ← testNegatives (F := F) testValues
  if negPassed then
    IO.println s!"  ✓ Negatives (x + (-x) = 0): PASS ({testValues.length} values)"
  else
    IO.println s!"  ✗ Negatives: FAIL"
    for e in negErrors do IO.println s!"    {e}"
    allPassed := false

  return allPassed

/-! ══════════════════════════════════════════════════════════════════════════
    SECTION 2: BOUNDARY TESTS (The Representation Check)
    ══════════════════════════════════════════════════════════════════════════ -/

/-- Test that toNat always returns values < modulus -/
def testBoundaryInvariant {F : Type} [FRIField F] (fieldName : String) : IO Bool := do
  IO.println s!"\n┌─────────────────────────────────────────────────────────────┐"
  IO.println s!"│  BOUNDARY TEST: {fieldName}"
  IO.println s!"└─────────────────────────────────────────────────────────────┘"

  let mod := FRIField.modulus (F := F)
  let mut passed := true

  -- Test values that could leak representation
  let testCases := [
    (mod + 5, "modulus + 5"),
    (mod * 2 + 7, "modulus * 2 + 7"),
    (mod - 1, "modulus - 1"),
    (0, "zero"),
    (1, "one"),
    (mod / 2, "modulus / 2"),
    (2^64, "2^64"),
    (2^128, "2^128"),
    (2^200, "2^200")
  ]

  for (val, desc) in testCases do
    let x : F := FRIField.ofNat val
    let result := FRIField.toNat x

    if result >= mod then
      IO.println s!"  ✗ {desc}: toNat returned {result} >= modulus {mod}"
      passed := false
    else
      IO.println s!"  ✓ {desc}: ofNat({val}) → toNat = {result} (< {mod})"

  if passed then
    IO.println s!"\n  BOUNDARY INVARIANT: ALL VALUES < MODULUS ✓"
  else
    IO.println s!"\n  BOUNDARY INVARIANT: VIOLATED - ABSTRACTION LEAK!"

  return passed

/-! ══════════════════════════════════════════════════════════════════════════
    SECTION 3: POLYMORPHISM TESTS (The Abstraction Check)
    ══════════════════════════════════════════════════════════════════════════ -/

/-- Generic polynomial function: x² + x + 1 -/
def polyCheck {F : Type} [FRIField F] (x : F) : F :=
  x * x + x + FRIField.one

/-- More complex generic function: Horner's method for x³ + 2x² + 3x + 4 -/
def hornerPoly {F : Type} [FRIField F] (x : F) : F :=
  let c0 : F := FRIField.ofNat 4
  let c1 : F := FRIField.ofNat 3
  let c2 : F := FRIField.ofNat 2
  let c3 : F := FRIField.ofNat 1
  -- Horner: ((c3 * x + c2) * x + c1) * x + c0
  ((c3 * x + c2) * x + c1) * x + c0

/-- Generic FRI-like fold operation -/
def genericFold {F : Type} [FRIField F] (even odd alpha : F) : F :=
  even + alpha * odd

/-- Test polymorphism with both field types -/
def testPolymorphism : IO Bool := do
  IO.println s!"\n┌─────────────────────────────────────────────────────────────┐"
  IO.println s!"│  POLYMORPHISM TEST (Abstraction Check)"
  IO.println s!"└─────────────────────────────────────────────────────────────┘"

  let mut passed := true

  -- Test polyCheck with BN254
  let bn_x : BN254 := FRIField.ofNat 5
  let bn_result := polyCheck bn_x
  let bn_expected : Nat := 5 * 5 + 5 + 1  -- 31
  IO.println s!"  polyCheck (BN254):"
  IO.println s!"    Input: x = 5"
  IO.println s!"    Result: {FRIField.toNat bn_result}"
  IO.println s!"    Expected: {bn_expected}"
  if FRIField.toNat bn_result != bn_expected then
    IO.println s!"    ✗ MISMATCH!"
    passed := false
  else
    IO.println s!"    ✓ CORRECT"

  -- Test polyCheck with TestField
  let tf_x : TestField := FRIField.ofNat 5
  let tf_result := polyCheck tf_x
  IO.println s!"  polyCheck (TestField):"
  IO.println s!"    Input: x = 5"
  IO.println s!"    Result: {FRIField.toNat tf_result}"
  IO.println s!"    Expected: {bn_expected}"
  if FRIField.toNat tf_result != bn_expected then
    IO.println s!"    ✗ MISMATCH!"
    passed := false
  else
    IO.println s!"    ✓ CORRECT"

  -- Test hornerPoly with both
  let horner_bn := hornerPoly (FRIField.ofNat 2 : BN254)
  let horner_tf := hornerPoly (FRIField.ofNat 2 : TestField)
  let horner_expected : Nat := 1*8 + 2*4 + 3*2 + 4  -- 8 + 8 + 6 + 4 = 26
  IO.println s!"  hornerPoly (x³ + 2x² + 3x + 4) at x=2:"
  IO.println s!"    BN254 result: {FRIField.toNat horner_bn}"
  IO.println s!"    TestField result: {FRIField.toNat horner_tf}"
  IO.println s!"    Expected: {horner_expected}"
  if FRIField.toNat horner_bn != horner_expected || FRIField.toNat horner_tf != horner_expected then
    IO.println s!"    ✗ MISMATCH!"
    passed := false
  else
    IO.println s!"    ✓ BOTH CORRECT"

  -- Test genericFold (FRI-like operation)
  let fold_bn := genericFold (FRIField.ofNat 10 : BN254) (FRIField.ofNat 20 : BN254) (FRIField.ofNat 3 : BN254)
  let fold_tf := genericFold (FRIField.ofNat 10 : TestField) (FRIField.ofNat 20 : TestField) (FRIField.ofNat 3 : TestField)
  let fold_expected : Nat := 10 + 3 * 20  -- 70
  IO.println s!"  genericFold (even=10, odd=20, alpha=3):"
  IO.println s!"    BN254 result: {FRIField.toNat fold_bn}"
  IO.println s!"    TestField result: {FRIField.toNat fold_tf}"
  IO.println s!"    Expected: {fold_expected}"
  if FRIField.toNat fold_bn != fold_expected || FRIField.toNat fold_tf != fold_expected then
    IO.println s!"    ✗ MISMATCH!"
    passed := false
  else
    IO.println s!"    ✓ BOTH CORRECT"

  if passed then
    IO.println s!"\n  POLYMORPHISM: Generic functions work identically on both fields ✓"
  else
    IO.println s!"\n  POLYMORPHISM: FAILED - Instance ambiguity or computation error!"

  return passed

/-! ══════════════════════════════════════════════════════════════════════════
    SECTION 4: INVERSION BENCHMARK (The Perf Check)
    ══════════════════════════════════════════════════════════════════════════ -/

/-- Simple timing helper using IO.monoMsNow -/
def timeMs (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  return (result, stop - start)

/-- Benchmark modular inversion -/
def benchmarkInversion : IO Bool := do
  IO.println s!"\n┌─────────────────────────────────────────────────────────────┐"
  IO.println s!"│  INVERSION BENCHMARK (Performance Check)"
  IO.println s!"└─────────────────────────────────────────────────────────────┘"

  let iterations := 1000

  -- BN254 inversion benchmark
  IO.println s!"\n  BN254 Inversion ({iterations} iterations):"
  let (_, bn_time) ← timeMs do
    for _ in List.range iterations do
      let x : BN254 := FRIField.ofNat 12345
      let _ := FRIField.fdiv FRIField.one x
    return ()

  IO.println s!"    Total time: {bn_time} ms"
  IO.println s!"    Per inversion: {(bn_time * 1000) / iterations} μs"

  -- TestField inversion benchmark
  IO.println s!"\n  TestField Inversion ({iterations} iterations):"
  let (_, tf_time) ← timeMs do
    for _ in List.range iterations do
      let x : TestField := FRIField.ofNat 12345
      let _ := FRIField.fdiv FRIField.one x
    return ()

  IO.println s!"    Total time: {tf_time} ms"
  IO.println s!"    Per inversion: {(tf_time * 1000) / iterations} μs"

  -- Multiplication benchmark (for comparison)
  IO.println s!"\n  BN254 Multiplication ({iterations * 10} iterations):"
  let (_, mul_time) ← timeMs do
    for _ in List.range (iterations * 10) do
      let x : BN254 := FRIField.ofNat 12345
      let y : BN254 := FRIField.ofNat 67890
      let _ := x * y
    return ()

  IO.println s!"    Total time: {mul_time} ms"
  IO.println s!"    Per multiplication: {(mul_time * 1000) / (iterations * 10)} μs"

  -- Hash benchmark
  IO.println s!"\n  BN254 Hash (Poseidon2) ({iterations} iterations):"
  let (_, hash_time) ← timeMs do
    for i in List.range iterations do
      let a : BN254 := FRIField.ofNat i
      let b : BN254 := FRIField.ofNat (i + 1)
      let _ := CryptoHash.hash2to1 a b
    return ()

  IO.println s!"    Total time: {hash_time} ms"
  IO.println s!"    Per hash: {(hash_time * 1000) / iterations} μs"

  -- TestField hash benchmark (XOR, should be much faster)
  IO.println s!"\n  TestField Hash (XOR) ({iterations} iterations):"
  let (_, xor_time) ← timeMs do
    for i in List.range iterations do
      let a : TestField := FRIField.ofNat i
      let b : TestField := FRIField.ofNat (i + 1)
      let _ := CryptoHash.hash2to1 a b
    return ()

  IO.println s!"    Total time: {xor_time} ms"
  IO.println s!"    Per hash: {(xor_time * 1000) / iterations} μs"

  -- Performance analysis
  IO.println s!"\n  ╔═══════════════════════════════════════════════════════════╗"
  IO.println s!"  ║  PERFORMANCE ANALYSIS                                     ║"
  IO.println s!"  ╠═══════════════════════════════════════════════════════════╣"

  -- Check if BN254 inversion is reasonable (< 10ms per inversion is OK)
  let invPerOp := if iterations > 0 then (bn_time * 1000) / iterations else 0
  if invPerOp < 10000 then  -- < 10ms per inversion
    IO.println s!"  ║  BN254 inversion: {invPerOp} μs/op - ACCEPTABLE            ║"
  else
    IO.println s!"  ║  BN254 inversion: {invPerOp} μs/op - TOO SLOW!             ║"

  -- Hash comparison
  if hash_time > 0 && xor_time > 0 then
    let speedup := hash_time / (if xor_time > 0 then xor_time else 1)
    IO.println s!"  ║  TestField hash speedup: ~{speedup}x vs Poseidon2          ║"

  IO.println s!"  ╚═══════════════════════════════════════════════════════════╝"

  -- Pass if inversion doesn't take forever
  return bn_time < 60000  -- Less than 60 seconds for 1000 inversions

/-! ══════════════════════════════════════════════════════════════════════════
    SECTION 5: CRYPTOHASH CONSISTENCY TESTS
    ══════════════════════════════════════════════════════════════════════════ -/

/-- Test hash determinism and basic properties -/
def testCryptoHashConsistency : IO Bool := do
  IO.println s!"\n┌─────────────────────────────────────────────────────────────┐"
  IO.println s!"│  CRYPTOHASH CONSISTENCY TEST"
  IO.println s!"└─────────────────────────────────────────────────────────────┘"

  let mut passed := true

  -- Determinism test (BN254)
  let a : BN254 := FRIField.ofNat 1
  let b : BN254 := FRIField.ofNat 2
  let h1 := CryptoHash.hash2to1 a b
  let h2 := CryptoHash.hash2to1 a b
  if h1 == h2 then
    IO.println s!"  ✓ BN254 hash determinism: PASS"
  else
    IO.println s!"  ✗ BN254 hash determinism: FAIL (different results for same input)"
    passed := false

  -- Determinism test (TestField)
  let ta : TestField := FRIField.ofNat 1
  let tb : TestField := FRIField.ofNat 2
  let th1 := CryptoHash.hash2to1 ta tb
  let th2 := CryptoHash.hash2to1 ta tb
  if th1 == th2 then
    IO.println s!"  ✓ TestField hash determinism: PASS"
  else
    IO.println s!"  ✗ TestField hash determinism: FAIL"
    passed := false

  -- Non-trivial output test (hash shouldn't return input)
  let h_self := CryptoHash.hash2to1 a a
  if h_self != a then
    IO.println s!"  ✓ BN254 hash(a, a) != a: PASS (non-trivial)"
  else
    IO.println s!"  ✗ BN254 hash(a, a) = a: Suspicious identity!"
    passed := false

  -- Different inputs produce different outputs
  let h_ab := CryptoHash.hash2to1 a b
  let h_ba := CryptoHash.hash2to1 b a
  if h_ab != h_ba then
    IO.println s!"  ✓ hash(a,b) != hash(b,a): PASS (non-commutative)"
  else
    IO.println s!"  ✗ hash(a,b) = hash(b,a): WARNING - hash is commutative"
    -- Note: This might be OK for some use cases, but flag it

  -- Squeeze produces output
  let squeeze_result := CryptoHash.squeeze [a, b] 0
  if FRIField.toNat squeeze_result != 0 then
    IO.println s!"  ✓ BN254 squeeze produces non-zero output: PASS"
  else
    IO.println s!"  ✗ BN254 squeeze returned 0: Suspicious!"
    passed := false

  return passed

/-! ══════════════════════════════════════════════════════════════════════════
    MAIN TEST RUNNER
    ══════════════════════════════════════════════════════════════════════════ -/

/-- Run all infrastructure sanity tests -/
def runAllTests : IO UInt32 := do
  IO.println "╔══════════════════════════════════════════════════════════════════╗"
  IO.println "║     INFRASTRUCTURE SANITY TESTS - PHASE 1 VALIDATION            ║"
  IO.println "║     Step 5.3 Generic Field Migration                            ║"
  IO.println "╚══════════════════════════════════════════════════════════════════╝"

  let mut totalPassed := 0
  let mut totalTests := 0

  -- Test 1: Field Laws (BN254)
  totalTests := totalTests + 1
  let bn254_laws ← testFieldLaws (F := BN254) "BN254 (254-bit prime field)"
  if bn254_laws then totalPassed := totalPassed + 1

  -- Test 2: Field Laws (TestField)
  totalTests := totalTests + 1
  let tf_laws ← testFieldLaws (F := TestField) "TestField (61-bit Mersenne prime)"
  if tf_laws then totalPassed := totalPassed + 1

  -- Test 3: Boundary (BN254)
  totalTests := totalTests + 1
  let bn254_boundary ← testBoundaryInvariant (F := BN254) "BN254"
  if bn254_boundary then totalPassed := totalPassed + 1

  -- Test 4: Boundary (TestField)
  totalTests := totalTests + 1
  let tf_boundary ← testBoundaryInvariant (F := TestField) "TestField"
  if tf_boundary then totalPassed := totalPassed + 1

  -- Test 5: Polymorphism
  totalTests := totalTests + 1
  let poly ← testPolymorphism
  if poly then totalPassed := totalPassed + 1

  -- Test 6: CryptoHash Consistency
  totalTests := totalTests + 1
  let hash ← testCryptoHashConsistency
  if hash then totalPassed := totalPassed + 1

  -- Test 7: Performance Benchmark
  totalTests := totalTests + 1
  let perf ← benchmarkInversion
  if perf then totalPassed := totalPassed + 1

  -- Final Summary
  IO.println "\n╔══════════════════════════════════════════════════════════════════╗"
  IO.println "║     FINAL RESULTS                                               ║"
  IO.println "╠══════════════════════════════════════════════════════════════════╣"
  IO.println s!"║     Tests Passed: {totalPassed}/{totalTests}                                          ║"

  if totalPassed == totalTests then
    IO.println "║                                                                  ║"
    IO.println "║     ✓ ALL TESTS PASSED                                          ║"
    IO.println "║     Phase 1 Infrastructure is READY for Phase 2                 ║"
    IO.println "╚══════════════════════════════════════════════════════════════════╝"
    return 0
  else
    IO.println "║                                                                  ║"
    IO.println "║     ✗ SOME TESTS FAILED                                         ║"
    IO.println "║     DO NOT proceed to Phase 2 until all tests pass!             ║"
    IO.println "╚══════════════════════════════════════════════════════════════════╝"
    return 1

-- Entry point
#eval runAllTests

end Tests.InfrastructureSanity
