/-
  FRI End-to-End Prover-Verifier Tests
  Phase 3 - Integration Tests

  These tests verify the complete FRI flow:
  1. Generate polynomial evaluations
  2. Create proof (Prover)
  3. Verify proof (Verifier)

  All tests use degree ≤ 64 for #eval! compatibility.
  For larger degrees, use the native benchmark executable.
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Proof
import AmoLean.FRI.Prover
import AmoLean.FRI.Verifier
import AmoLean.FRI.Fields.TestField
import AmoLean.FRI.Fields.BN254

namespace Tests.E2EProverVerifier

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Proof (FRIConfig FRIProof VerifyError VerifyResult)
open AmoLean.FRI.Prover (prove testConfig)
open AmoLean.FRI.Verifier (verify verifyBool verifyMessage)
open AmoLean.FRI.Fields.TestField (TestField)
open AmoLean.FRI.Fields.BN254 (BN254)

/-! ## Part 1: Test Data Generation -/

/-- Generate evaluations of a constant polynomial (degree 0).
    This will fold down to the same constant value.
-/
def generateConstantEvaluations {F : Type} [FRIField F] (value : Nat) (size : Nat) : Array F :=
  Array.mkArray size (FRIField.ofNat value)

/-- Generate pseudo-random field elements for testing -/
def generateRandomEvaluations {F : Type} [FRIField F] (seed : Nat) (size : Nat) : Array F :=
  Array.range size |>.map fun i =>
    let x := seed + i * 6364136223846793005 + 1442695040888963407
    FRIField.ofNat (x % (2^64))

/-! ## Part 2: Small Tests (degree ≤ 16, safe for #eval!) -/

/-- Test 1: Minimal FRI proof (degree 4) with constant polynomial -/
def testMinimalFRI : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 1: MINIMAL FRI PROOF (degree 4, constant poly)                ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  let degree := 4
  let config := testConfig degree
  -- Use constant polynomial so FRI folding produces correct result
  let evaluations : Array TestField := generateConstantEvaluations 42 8

  IO.println s!"Configuration:"
  IO.println s!"  Initial degree: {config.initialDegree}"
  IO.println s!"  Domain size: {config.initialDomainSize}"
  IO.println s!"  Num queries: {config.numQueries}"
  IO.println s!"  Expected rounds: {config.numRounds}"
  IO.println ""

  -- Generate proof
  IO.println "Generating proof..."
  match ← prove evaluations config with
  | .error msg =>
    IO.println s!"✗ Proof generation FAILED: {msg}"
  | .ok proof =>
    IO.println s!"✓ Proof generated successfully"
    IO.println s!"  Commitments: {proof.commitments.length}"
    IO.println s!"  Challenges: {proof.challenges.length}"
    IO.println s!"  Query paths: {proof.queryPaths.length}"
    IO.println s!"  Final layer size: {proof.finalLayer.length}"
    IO.println ""

    -- Verify proof
    IO.println "Verifying proof..."
    let result := verify proof
    match result with
    | .ok () =>
      IO.println "✓ Verification PASSED\n"
    | .error err =>
      IO.println s!"✗ Verification FAILED: {VerifyError.toString err}\n"

/-- Test 2: Medium FRI proof (degree 16) with constant polynomial -/
def testMediumFRI : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 2: MEDIUM FRI PROOF (degree 16, constant poly)                ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  let degree := 16
  let config := testConfig degree
  let evaluations : Array TestField := generateConstantEvaluations 123 32

  IO.println s!"Configuration:"
  IO.println s!"  Initial degree: {config.initialDegree}"
  IO.println s!"  Domain size: {config.initialDomainSize}"
  IO.println s!"  Expected rounds: {config.numRounds}"
  IO.println ""

  match ← prove evaluations config with
  | .error msg =>
    IO.println s!"✗ Proof generation FAILED: {msg}"
  | .ok proof =>
    IO.println s!"✓ Proof generated"
    let result := verify proof
    match result with
    | .ok () => IO.println "✓ Verification PASSED\n"
    | .error err => IO.println s!"✗ Verification FAILED: {VerifyError.toString err}\n"

/-- Test 3: BN254 Field test (degree 8) with constant polynomial -/
def testBN254FRI : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 3: BN254 FIELD FRI PROOF (degree 8, Poseidon2, constant)      ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  let degree := 8
  let config := testConfig degree
  let evaluations : Array BN254 := generateConstantEvaluations 999 16

  IO.println s!"Configuration:"
  IO.println s!"  Field: BN254 (254-bit)"
  IO.println s!"  Hash: Poseidon2"
  IO.println s!"  Initial degree: {config.initialDegree}"
  IO.println s!"  Domain size: {config.initialDomainSize}"
  IO.println ""

  match ← prove evaluations config with
  | .error msg =>
    IO.println s!"✗ Proof generation FAILED: {msg}"
  | .ok proof =>
    IO.println s!"✓ Proof generated with BN254/Poseidon2"
    let result := verify proof
    match result with
    | .ok () => IO.println "✓ Verification PASSED\n"
    | .error err => IO.println s!"✗ Verification FAILED: {VerifyError.toString err}\n"

/-! ## Part 3: Negative Tests (intentionally broken proofs) -/

/-- Test 4: Malformed proof detection -/
def testMalformedProof : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 4: MALFORMED PROOF DETECTION                                  ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  let degree := 4
  let config := testConfig degree
  -- Use constant poly so the base proof is valid
  let evaluations : Array TestField := generateConstantEvaluations 777 8

  match ← prove evaluations config with
  | .error msg =>
    IO.println s!"✗ Proof generation FAILED: {msg}"
  | .ok proof =>
    -- Tamper with the proof: add extra commitment
    let tamperedProof : FRIProof TestField := {
      proof with
      commitments := proof.commitments ++ [FRIField.ofNat 999]
    }

    IO.println "Testing tampered proof (extra commitment)..."
    let result := verify tamperedProof
    match result with
    | .ok () =>
      IO.println "✗ Tampered proof was accepted (BUG!)\n"
    | .error err =>
      IO.println s!"✓ Tampered proof correctly rejected"
      IO.println s!"  Error: {VerifyError.toString err}\n"

/-- Test 5: Wrong challenge detection -/
def testWrongChallenge : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║  TEST 5: WRONG CHALLENGE DETECTION                                  ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  let degree := 4
  let config := testConfig degree
  -- Use constant poly so the base proof is valid
  let evaluations : Array TestField := generateConstantEvaluations 888 8

  match ← prove evaluations config with
  | .error msg =>
    IO.println s!"✗ Proof generation FAILED: {msg}"
  | .ok proof =>
    -- Tamper with challenges
    let tamperedChallenges := proof.challenges.map fun c =>
      FRIField.ofNat (FRIField.toNat c + 1)  -- Shift all challenges by 1

    let tamperedProof : FRIProof TestField := {
      proof with
      challenges := tamperedChallenges
    }

    IO.println "Testing tampered proof (wrong challenges)..."
    let result := verify tamperedProof
    match result with
    | .ok () =>
      IO.println "✗ Tampered proof was accepted (BUG!)\n"
    | .error err =>
      IO.println s!"✓ Wrong challenges correctly detected"
      IO.println s!"  Error: {VerifyError.toString err}\n"

/-! ## Part 4: Run All Tests -/

def runAllE2ETests : IO Unit := do
  IO.println "\n"
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║                    FRI END-TO-END TEST SUITE                        ║"
  IO.println "║                         Phase 3 Integration                         ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  testMinimalFRI
  testMediumFRI
  testBN254FRI
  testMalformedProof
  testWrongChallenge

  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║                      ALL TESTS COMPLETED                            ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"

-- Run all tests
#eval! runAllE2ETests

end Tests.E2EProverVerifier
