/-
  Poseidon2 Integration Module
  Step 5.1 - Connecting Poseidon2 with FRI Infrastructure

  This module provides adapters to integrate Poseidon2 with:
  1. Merkle tree construction (HashFn interface)
  2. Fiat-Shamir transcript (squeeze function)

  The adapters convert between the generic `Nat` type used in Spec.lean
  and the infrastructure in FRI/Merkle.lean and FRI/Transcript.lean.

  Reference: ADR-007-step5-integration.md
-/

import AmoLean.Protocols.Poseidon.Spec
import AmoLean.Protocols.Poseidon.Constants.BN254

namespace AmoLean.Protocols.Poseidon.Integration

open AmoLean.Protocols.Poseidon.Spec
open AmoLean.Protocols.Poseidon.Constants.BN254

/-! ## Part 1: BN254 Parameters with Real Constants -/

/-- Production BN254 parameters using HorizenLabs constants -/
def bn254ParamsProduction : Params := {
  prime := p
  t := t
  alpha := alpha
  fullRounds := RF
  partialRounds := RP
  mds := Spec.mds3
  roundConstants := RC
}

/-! ## Part 2: Merkle Tree Hash Adapter

The Merkle tree infrastructure expects:
  HashFn (F : Type) := F → F → F

Poseidon2 provides:
  poseidon2Hash : Params → Array Nat → Nat

We create a 2-to-1 hash: hash(left, right) = squeeze(permute([left, right, 0]))
This matches the standard sponge construction for Merkle trees.
-/

/-- 2-to-1 hash for Merkle tree using Poseidon2 permutation.

    Construction:
    1. Create state [left, right, 0] (capacity element = 0)
    2. Apply permutation
    3. Return first element (squeeze)

    This is the standard Poseidon2 sponge construction for 2 inputs.
-/
def poseidon2Hash2to1 (params : Params) (left right : Nat) : Nat :=
  let state := #[left % params.prime, right % params.prime, 0]
  let result := poseidon2Permutation params state
  result.get! 0

/-- HashFn adapter for Merkle trees using BN254 Poseidon2.

    Usage:
    ```lean
    import AmoLean.FRI.Merkle
    import AmoLean.Protocols.Poseidon.Integration

    -- Build tree with Poseidon2
    let tree := buildTree leaves poseidon2MerkleHash
    ```
-/
def poseidon2MerkleHash : Nat → Nat → Nat :=
  poseidon2Hash2to1 bn254ParamsProduction

/-- Generic HashFn adapter parameterized by field parameters.

    For other fields (e.g., Goldilocks), create params and use this.
-/
def poseidon2HashFn (params : Params) : Nat → Nat → Nat :=
  poseidon2Hash2to1 params

/-! ## Part 3: Transcript Squeeze Adapter

The Fiat-Shamir transcript needs a cryptographic squeeze function.
Current implementation uses XOR, which is NOT secure.

Poseidon2 sponge construction:
1. Absorb all elements into state (pad if necessary)
2. Apply permutation after each rate-sized block
3. Squeeze from first position

For transcript:
- Rate = t - 1 = 2 (for t=3)
- Capacity = 1 (security parameter)
-/

/-- Sponge state type -/
abbrev SpongeState := Array Nat

/-- Initialize sponge state with zeros -/
def initSponge (params : Params) : SpongeState :=
  Array.mkArray params.t 0

/-- XOR-add values into state (sponge absorption)
    Only modifies rate positions [0..t-2] -/
def absorbIntoState (params : Params) (values : List Nat) (state : SpongeState) : SpongeState :=
  let rate := params.t - 1  -- Rate = t - 1
  values.enum.foldl (fun s (i, v) =>
    if i < rate && i < s.size then
      s.set! i (modAdd params.prime (s.get! i) (v % params.prime))
    else s
  ) state

/-- Poseidon2 sponge squeeze function for Fiat-Shamir transcript.

    Given a list of absorbed field elements, produces a pseudo-random output.

    Algorithm:
    1. Initialize state to zeros
    2. For each rate-sized block of input:
       a. XOR block into state positions [0..rate-1]
       b. Apply permutation
    3. Return state[0] (squeeze)

    Security: Capacity position (state[t-1]) is never directly modified,
    providing indifferentiability from a random oracle.
-/
def poseidon2Squeeze (params : Params) (absorbed : List Nat) : Nat :=
  let rate := params.t - 1
  let state := initSponge params

  -- Pad input to multiple of rate
  let padded := if absorbed.length % rate == 0 && absorbed.length > 0 then absorbed
                else absorbed ++ List.replicate (rate - absorbed.length % rate) 0

  -- Process blocks iteratively (avoiding termination issues)
  let numBlocks := (padded.length + rate - 1) / rate
  let finalState := (List.range numBlocks).foldl (fun st blockIdx =>
    let block := (padded.drop (blockIdx * rate)).take rate
    let stateWithBlock := absorbIntoState params block st
    poseidon2Permutation params stateWithBlock
  ) state

  finalState.get! 0

/-- Transcript squeeze using BN254 Poseidon2.

    Replacement for XOR-based squeeze in Transcript.lean.
-/
def poseidon2TranscriptSqueeze (absorbed : List Nat) : Nat :=
  poseidon2Squeeze bn254ParamsProduction absorbed

/-- Multi-squeeze: Get multiple pseudo-random outputs.

    After squeezing once, apply permutation again to get next output.
    This is the standard multi-output sponge construction.
-/
def poseidon2MultipleSqueeze (params : Params) (absorbed : List Nat) (count : Nat) : List Nat :=
  let rate := params.t - 1
  let state := initSponge params

  -- Pad input
  let padded := if absorbed.length % rate == 0 && absorbed.length > 0 then absorbed
                else absorbed ++ List.replicate (rate - absorbed.length % rate) 0

  -- Absorb all blocks
  let numBlocks := (padded.length + rate - 1) / rate
  let absorbedState := (List.range numBlocks).foldl (fun st blockIdx =>
    let block := (padded.drop (blockIdx * rate)).take rate
    let stateWithBlock := absorbIntoState params block st
    poseidon2Permutation params stateWithBlock
  ) state

  -- Squeeze count outputs
  (List.range count).foldl (fun (outputs, st) _ =>
    let output := st.get! 0
    let nextState := poseidon2Permutation params st
    (outputs ++ [output], nextState)
  ) ([], absorbedState) |>.1

/-! ## Part 4: Domain Separation

Domain separation prevents cross-protocol attacks by prefixing
different contexts with unique tags.

The existing DomainTag in Transcript.lean:
  merkleNode | friChallenge | friCommit | fieldElement | constraint | custom

We provide helper to convert tag to field element for absorption.
-/

/-- Domain tag to Nat conversion.

    Each tag gets a unique prime to avoid collisions.
    Using small primes for efficiency.
-/
def domainTagToNat : String → Nat
  | "merkleNode" => 2
  | "friChallenge" => 3
  | "friCommit" => 5
  | "fieldElement" => 7
  | "constraint" => 11
  | "queryResponse" => 13    -- New for query phase
  | "proofFinalize" => 17    -- New for proof finalization
  | custom => custom.hash.toNat  -- Hash custom string

/-- Poseidon2 hash with domain separation.

    Prepends domain tag to input before hashing.
-/
def poseidon2HashWithDomain (params : Params) (domain : String) (left right : Nat) : Nat :=
  let domainVal := domainTagToNat domain
  -- Absorb [domain, left, right] with capacity
  let state := #[domainVal % params.prime, left % params.prime, right % params.prime]
  let result := poseidon2Permutation params state
  result.get! 0

/-- Merkle hash with domain separation -/
def poseidon2MerkleHashWithDomain : Nat → Nat → Nat :=
  poseidon2HashWithDomain bn254ParamsProduction "merkleNode"

/-! ## Part 5: Tests -/

section Tests

/-- Test 1: Hash function produces expected output for test vector -/
def test_hash_known_vector : Bool :=
  let result := poseidon2Permutation bn254ParamsProduction testInput
  result == testOutput

/-- Test 2: 2-to-1 hash is deterministic -/
def test_hash_deterministic : Bool :=
  let h1 := poseidon2MerkleHash 1 2
  let h2 := poseidon2MerkleHash 1 2
  h1 == h2

/-- Test 3: Different inputs produce different outputs -/
def test_hash_different_inputs : Bool :=
  let h1 := poseidon2MerkleHash 1 2
  let h2 := poseidon2MerkleHash 2 1  -- Swapped
  let h3 := poseidon2MerkleHash 1 3
  h1 != h2 && h1 != h3 && h2 != h3

/-- Test 4: Squeeze produces non-zero output -/
def test_squeeze_nonzero : Bool :=
  let result := poseidon2TranscriptSqueeze [1, 2, 3]
  result != 0

/-- Test 5: Multiple squeezes produce different values -/
def test_multi_squeeze_different : Bool :=
  let results := poseidon2MultipleSqueeze bn254ParamsProduction [1, 2, 3] 3
  match results with
  | [a, b, c] => a != b && b != c && a != c
  | _ => false

/-- Test 6: Domain separation produces different hashes -/
def test_domain_separation : Bool :=
  let h1 := poseidon2HashWithDomain bn254ParamsProduction "merkleNode" 1 2
  let h2 := poseidon2HashWithDomain bn254ParamsProduction "friChallenge" 1 2
  h1 != h2

/-- Run all tests -/
def runAllTests : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║     POSEIDON2 INTEGRATION TESTS                            ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""

  let tests := [
    ("Test 1: Known vector", test_hash_known_vector),
    ("Test 2: Deterministic hash", test_hash_deterministic),
    ("Test 3: Different inputs → different outputs", test_hash_different_inputs),
    ("Test 4: Squeeze non-zero", test_squeeze_nonzero),
    ("Test 5: Multi-squeeze different", test_multi_squeeze_different),
    ("Test 6: Domain separation", test_domain_separation)
  ]

  let mut passed := 0
  let mut failed := 0

  for (name, result) in tests do
    if result then
      IO.println s!"  ✓ {name}: PASS"
      passed := passed + 1
    else
      IO.println s!"  ✗ {name}: FAIL"
      failed := failed + 1

  IO.println ""
  IO.println s!"Results: {passed}/{passed + failed} passed"
  if failed == 0 then
    IO.println "ALL TESTS PASSED"
  else
    IO.println s!"FAILED: {failed} tests"

end Tests

-- Run integration tests
#eval! runAllTests

-- Quick validation of hash output
#eval! poseidon2MerkleHash 0 1  -- Should produce non-trivial output

-- Validate squeeze output
#eval! poseidon2TranscriptSqueeze [1, 2, 3, 4, 5]

/-! ## Part 6: Summary -/

def integrationSummary : String :=
  "Poseidon2 Integration Module (Step 5.1)
   ========================================

   1. BN254 Production Parameters
      - Uses HorizenLabs round constants (64 rounds)
      - Validated against test vector [0, 1, 2]

   2. Merkle Tree Adapter
      - poseidon2MerkleHash : Nat → Nat → Nat
      - Standard 2-to-1 sponge construction
      - Drop-in replacement for testHash

   3. Transcript Squeeze Adapter
      - poseidon2TranscriptSqueeze : List Nat → Nat
      - Multi-output support via poseidon2MultipleSqueeze
      - Drop-in replacement for XOR-based squeeze

   4. Domain Separation
      - poseidon2HashWithDomain for context-tagged hashing
      - Unique tags for merkle, FRI, constraints

   Usage:
   - For Merkle: Replace testHash with poseidon2MerkleHash
   - For Transcript: Replace XOR squeeze with poseidon2TranscriptSqueeze

   All adapters use BN254 by default. For other fields,
   use poseidon2HashFn with custom params."

#eval IO.println integrationSummary

end AmoLean.Protocols.Poseidon.Integration
