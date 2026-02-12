/-
  AMO-Lean QA Suite: Algebraic Validation
  Test ID: NTT-TEST-002
  Priority: CRITICAL (Algebraic Foundation)

  Validates that Goldilocks field behaves correctly for NTT:
  1. Primitive roots: ω^N = 1 and ω^(N/2) ≠ 1
  2. Orthogonality: Σᵢ ω^i = 0 for primitive roots
  3. Field arithmetic: Addition, multiplication, inversion
-/

import AmoLean.NTT.Goldilocks
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Field

namespace AmoLean.NTT.Tests.Algebra

open AmoLean.NTT
open AmoLean.Field.Goldilocks

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: TEST HELPER FUNCTIONS (no proofs needed)
═══════════════════════════════════════════════════════════════════════════ -/

/-- Compute primitive root for n (n must be > 0) -/
def getPrimitiveRoot (n : Nat) : GoldilocksField :=
  if n == 0 then ⟨1⟩
  else primitiveRoot n (by omega)

/-- Test that ω^N = 1 for a given N -/
def testRootPowN' (n : Nat) : Bool :=
  if n == 0 then true
  else
    let ω := getPrimitiveRoot n
    (GoldilocksField.pow ω n).value == 1

/-- Test that ω^(N/2) = -1 for even N > 2 -/
def testHalfPowNegOne' (n : Nat) : Bool :=
  if n <= 2 || n % 2 != 0 then true
  else
    let ω := getPrimitiveRoot n
    let half_pow := GoldilocksField.pow ω (n / 2)
    half_pow.value == ORDER - 1

/-- Test that ω^(N/2) ≠ 1 (critical: ensures ω is truly primitive) -/
def testHalfPowNotOne' (n : Nat) : Bool :=
  if n <= 2 then true
  else
    let ω := getPrimitiveRoot n
    let half_pow := GoldilocksField.pow ω (n / 2)
    half_pow.value != 1

/-- Compute Σᵢ₌₀^{n-1} ω^i -/
def sumOfPowers' (n : Nat) : GoldilocksField :=
  if n == 0 then ⟨0⟩
  else
    let ω := getPrimitiveRoot n
    (List.range n).foldl
      (fun acc i => GoldilocksField.add acc (GoldilocksField.pow ω i))
      GoldilocksField.zero

/-- Test orthogonality: sum of powers should be 0 -/
def testOrthogonality' (n : Nat) : Bool :=
  if n <= 1 then true
  else (sumOfPowers' n).value == 0

/-- Test: x * x^(-1) = 1 for x ≠ 0 -/
def testMulInverse' (x : UInt64) : Bool :=
  if x == 0 then true
  else
    let gf := GoldilocksField.ofUInt64 x
    let inv := GoldilocksField.inv gf
    let prod := GoldilocksField.mul gf inv
    prod.value == 1

/-- Extract value from Option -/
def optVal (x : Option GoldilocksField) : UInt64 :=
  match x with
  | some g => g.value
  | none => 0

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: RUNTIME VALIDATION SUITE
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     Algebra QA Suite - Goldilocks Field & Roots              ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  let mut allPassed := true

  -- Test 1: Primitive Root Property (ω^N = 1)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 1: Primitive Root (ω^N = 1)                             │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let testSizes := [4, 8, 16, 32, 64, 128, 256, 512, 1024]
  for n in testSizes do
    let passed := testRootPowN' n
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}: ω^{n} = 1 ? {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 2: Half Power Property (ω^(N/2) = -1)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 2: Half Power (ω^(N/2) = -1)                            │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in testSizes do
    if n > 2 then
      let passed := testHalfPowNegOne' n
      let passedNotOne := testHalfPowNotOne' n
      let status := if passed && passedNotOne then "✓ PASS" else "✗ FAIL"
      IO.println s!"│ N={n}: ω^{n/2} = -1, ω^{n/2} ≠ 1 ? {status}"
      if !passed || !passedNotOne then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 3: Orthogonality (Σᵢ ω^i = 0)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 3: Orthogonality (Σᵢ ω^i = 0)                           │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in [2, 4, 8, 16, 32, 64] do
    let passed := testOrthogonality' n
    let sum := sumOfPowers' n
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}: Σω^i = {sum.value} (expected 0) {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 4: Field Inversion
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 4: Field Inversion (x * x⁻¹ = 1)                        │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let testValues : List UInt64 := [1, 2, 3, 7, 42, 1000, 65536, 4294967295]
  for x in testValues do
    let passed := testMulInverse' x
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ x={x}: x * x⁻¹ = 1 ? {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 5: N^(-1) values (critical for INTT)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 5: N⁻¹ Values for INTT                                  │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in [4, 8, 16, 32, 64] do
    let n_gf : GoldilocksField := ⟨n.toUInt64⟩
    let n_inv := GoldilocksField.inv n_gf
    let prod := GoldilocksField.mul n_gf n_inv
    let passed := prod.value == 1
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}: {n} * {n}⁻¹ = {prod.value} (expected 1) {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 6: Twiddle Factor Consistency
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 6: Twiddle Factors ω^k consistency                      │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let n := 8
  let ω := getPrimitiveRoot n
  let twiddles := genTwiddleTable ω n

  -- Verify ω^0 = 1
  let t0_ok := optVal twiddles[0]? == 1
  IO.println s!"│ ω^0 = 1 ? {if t0_ok then "✓ PASS" else "✗ FAIL"}"
  if !t0_ok then allPassed := false

  -- Verify ω^(n/2) = -1
  let tn2_ok := optVal twiddles[n/2]? == ORDER - 1
  IO.println s!"│ ω^{n/2} = -1 ? {if tn2_ok then "✓ PASS" else "✗ FAIL"}"
  if !tn2_ok then allPassed := false

  -- Verify ω^n would equal ω^0
  let wn := GoldilocksField.pow ω n
  let cycle_ok := wn.value == 1
  IO.println s!"│ ω^{n} = 1 (cycle) ? {if cycle_ok then "✓ PASS" else "✗ FAIL"}"
  if !cycle_ok then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n══════════════════════════════════════════════════════════════"
  if allPassed then
    IO.println "   RESULT: ALL ALGEBRA TESTS PASSED ✓"
  else
    IO.println "   RESULT: SOME TESTS FAILED ✗"
  IO.println "══════════════════════════════════════════════════════════════"

  return allPassed

end AmoLean.NTT.Tests.Algebra
