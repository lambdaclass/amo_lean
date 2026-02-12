/-
  Transcript Security Audit - Step 5.2 Validation

  This file implements "black box" security tests for the Poseidon2
  transcript implementation, checking for cryptographic vulnerabilities.

  Tests:
  1. Amnesia Test - State preservation across absorb calls
  2. Avalanche Test - Sensitivity to single-bit changes
  3. Domain Separation Test - Different contexts produce different outputs

  Reference: ADR-008-domain-separation-audit.md
-/

import AmoLean.Protocols.Poseidon.Integration
import AmoLean.Protocols.Poseidon.DomainSeparation
import AmoLean.Protocols.Poseidon.Spec

namespace AmoLean.Tests.TranscriptSecurityAudit

open AmoLean.Protocols.Poseidon.Integration
open AmoLean.Protocols.Poseidon.DomainSeparation
open AmoLean.Protocols.Poseidon.Spec

/-! ## Test 1: Amnesia Test (State Preservation)

This test verifies that the transcript correctly preserves state.
If absorbing [A, B] produces the same challenge as absorbing [B],
then the transcript "forgot" A - a critical security failure.
-/

/-- Test values for amnesia test -/
def valueA : Nat := 0x123456789ABCDEF0
def valueB : Nat := 0xFEDCBA9876543210

/-- Scenario 1: absorb(A); absorb(B); squeeze() -/
def amnesiaScenario1 : Nat :=
  poseidon2TranscriptSqueeze [valueA, valueB]

/-- Scenario 2: absorb(B); squeeze() -/
def amnesiaScenario2 : Nat :=
  poseidon2TranscriptSqueeze [valueB]

/-- Scenario 3: absorb(A); squeeze() (additional check) -/
def amnesiaScenario3 : Nat :=
  poseidon2TranscriptSqueeze [valueA]

/-- Test 1A: [A, B] must differ from [B] -/
def test_amnesia_AB_vs_B : Bool :=
  amnesiaScenario1 != amnesiaScenario2

/-- Test 1B: [A, B] must differ from [A] -/
def test_amnesia_AB_vs_A : Bool :=
  amnesiaScenario1 != amnesiaScenario3

/-- Test 1C: [A] must differ from [B] -/
def test_amnesia_A_vs_B : Bool :=
  amnesiaScenario2 != amnesiaScenario3

/-- Test 1D: Order matters - [A, B] must differ from [B, A] -/
def test_amnesia_order_matters : Bool :=
  let ab := poseidon2TranscriptSqueeze [valueA, valueB]
  let ba := poseidon2TranscriptSqueeze [valueB, valueA]
  ab != ba

/-- Full amnesia test with detailed output -/
def runAmnesiaTest : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 1: AMNESIA TEST (State Preservation)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  IO.println s!"  Value A: 0x{Nat.toDigits 16 valueA |>.asString}"
  IO.println s!"  Value B: 0x{Nat.toDigits 16 valueB |>.asString}"
  IO.println ""

  let s1 := amnesiaScenario1
  let s2 := amnesiaScenario2
  let s3 := amnesiaScenario3
  let s4 := poseidon2TranscriptSqueeze [valueB, valueA]

  IO.println "  Scenario Results:"
  IO.println s!"    squeeze([A, B]) = {s1}"
  IO.println s!"    squeeze([B])    = {s2}"
  IO.println s!"    squeeze([A])    = {s3}"
  IO.println s!"    squeeze([B, A]) = {s4}"
  IO.println ""

  let t1a := test_amnesia_AB_vs_B
  let t1b := test_amnesia_AB_vs_A
  let t1c := test_amnesia_A_vs_B
  let t1d := test_amnesia_order_matters

  IO.println "  Sub-tests:"
  IO.println s!"    1A: [A,B] ≠ [B]   → {if t1a then "PASS ✓" else "FAIL ✗ CRITICAL"}"
  IO.println s!"    1B: [A,B] ≠ [A]   → {if t1b then "PASS ✓" else "FAIL ✗ CRITICAL"}"
  IO.println s!"    1C: [A] ≠ [B]     → {if t1c then "PASS ✓" else "FAIL ✗ CRITICAL"}"
  IO.println s!"    1D: [A,B] ≠ [B,A] → {if t1d then "PASS ✓" else "FAIL ✗ CRITICAL"}"
  IO.println ""

  let allPass := t1a && t1b && t1c && t1d
  if allPass then
    IO.println "  AMNESIA TEST: PASSED ✓"
    IO.println "  → Transcript correctly preserves state across absorb calls"
  else
    IO.println "  AMNESIA TEST: FAILED ✗"
    IO.println "  → CRITICAL: Transcript may be forgetting absorbed data!"

  IO.println ""
  pure allPass

/-! ## Test 2: Avalanche Test (Sensitivity)

This test verifies that changing a single bit in the input
produces radically different output (not just a single bit change).
A good hash should have ~50% of output bits change.
-/

/-- Count differing bits between two numbers -/
def countDifferingBits (a b : Nat) : Nat :=
  let xored := Nat.xor a b
  -- Count set bits (population count)
  let rec popcount (n : Nat) (acc : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if n == 0 then acc
      else popcount (n / 2) (acc + n % 2) fuel
  popcount xored 0 300  -- 300 bits should be enough for BN254

/-- Base value for avalanche test -/
def avalancheBase : Nat := 0xDEADBEEFCAFEBABE

/-- Flip bit at position i -/
def flipBit (n : Nat) (pos : Nat) : Nat :=
  Nat.xor n (1 <<< pos)

/-- Run avalanche test for a specific bit position -/
def avalancheTestBit (pos : Nat) : Nat × Nat × Nat :=
  let original := poseidon2TranscriptSqueeze [avalancheBase, 42]
  let mutated := poseidon2TranscriptSqueeze [flipBit avalancheBase pos, 42]
  let diffBits := countDifferingBits original mutated
  (original, mutated, diffBits)

/-- Full avalanche test -/
def runAvalancheTest : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 2: AVALANCHE TEST (Single-Bit Sensitivity)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  IO.println s!"  Base value: 0x{Nat.toDigits 16 avalancheBase |>.asString}"
  IO.println ""

  -- Test bit positions 0, 7, 15, 31, 63
  let testPositions := [0, 7, 15, 31, 63]

  IO.println "  Bit Position | Original Hash (last 16 hex) | Mutated Hash (last 16 hex) | Bits Changed"
  IO.println "  -------------|------------------------------|------------------------------|-------------"

  let results := testPositions.map fun pos =>
    let (orig, mutVal, diff) := avalancheTestBit pos
    (pos, orig, mutVal, diff)

  for (pos, orig, mutVal, diff) in results do
    let origHex := Nat.toDigits 16 (orig % (1 <<< 64)) |>.asString
    let mutHex := Nat.toDigits 16 (mutVal % (1 <<< 64)) |>.asString
    IO.println s!"       {pos}      |  ...{origHex.takeRight 16}  |  ...{mutHex.takeRight 16}  |     {diff}"

  let diffs := results.map fun (_, _, _, d) => d
  let minDiff := diffs.foldl min 1000
  let maxDiff := diffs.foldl max 0
  let totalDiff := diffs.foldl (· + ·) 0
  let avgDiff := totalDiff / testPositions.length

  IO.println ""
  IO.println s!"  Statistics:"
  IO.println s!"    Minimum bits changed: {minDiff}"
  IO.println s!"    Maximum bits changed: {maxDiff}"
  IO.println s!"    Average bits changed: {avgDiff}"
  IO.println ""

  -- For a 254-bit field, we expect ~127 bits to change (50%)
  -- Anything above 50 bits is acceptable for security
  let acceptable := minDiff >= 50

  if acceptable then
    IO.println "  AVALANCHE TEST: PASSED ✓"
    IO.println "  → Single-bit changes produce significant output differences"
    IO.println s!"  → Minimum {minDiff} bits changed (threshold: 50)"
  else
    IO.println "  AVALANCHE TEST: FAILED ✗"
    IO.println s!"  → Only {minDiff} bits changed, expected at least 50"
    IO.println "  → Hash may be vulnerable to differential attacks"

  IO.println ""
  pure acceptable

/-! ## Test 3: Domain Separation Test

This test verifies that different contexts (MerkleRoot, FRICommit, etc.)
use different domain constants and produce different outputs for same data.
-/

/-- Common test data -/
def domainTestData : Nat := 0xABCDEF0123456789

/-- Hash with MerkleTree domain -/
def hashAsMerkle : Nat :=
  poseidon2HashWithDomainTag bn254ParamsProduction DomainTag.merkleTree2to1 domainTestData 0

/-- Hash with FRI Commit domain -/
def hashAsFRICommit : Nat :=
  poseidon2HashWithDomainTag bn254ParamsProduction DomainTag.friCommit domainTestData 0

/-- Hash with FRI Fold domain -/
def hashAsFRIFold : Nat :=
  poseidon2HashWithDomainTag bn254ParamsProduction DomainTag.friFold domainTestData 0

/-- Hash with FRI Query domain -/
def hashAsFRIQuery : Nat :=
  poseidon2HashWithDomainTag bn254ParamsProduction DomainTag.friQuery domainTestData 0

/-- Hash without domain (raw) -/
def hashRaw : Nat :=
  poseidon2MerkleHash domainTestData 0

/-- Full domain separation test -/
def runDomainSeparationTest : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 3: DOMAIN SEPARATION TEST"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  IO.println s!"  Test data: 0x{Nat.toDigits 16 domainTestData |>.asString}"
  IO.println ""

  let hMerkle := hashAsMerkle
  let hCommit := hashAsFRICommit
  let hFold := hashAsFRIFold
  let hQuery := hashAsFRIQuery
  let hRaw := hashRaw

  IO.println "  Domain Tag Values (from DomainSeparation.lean):"
  IO.println s!"    merkleTree2to1: {DomainTag.merkleTree2to1.toCapacityValue}"
  IO.println s!"    friCommit:      {DomainTag.friCommit.toCapacityValue}"
  IO.println s!"    friFold:        {DomainTag.friFold.toCapacityValue}"
  IO.println s!"    friQuery:       {DomainTag.friQuery.toCapacityValue}"
  IO.println ""

  IO.println "  Hash Results:"
  IO.println s!"    MerkleTree2to1: {hMerkle}"
  IO.println s!"    FRI Commit:     {hCommit}"
  IO.println s!"    FRI Fold:       {hFold}"
  IO.println s!"    FRI Query:      {hQuery}"
  IO.println s!"    Raw (no tag):   {hRaw}"
  IO.println ""

  -- All pairs must be different
  let pairs := [
    ("Merkle ≠ FRICommit", hMerkle != hCommit),
    ("Merkle ≠ FRIFold", hMerkle != hFold),
    ("Merkle ≠ FRIQuery", hMerkle != hQuery),
    ("FRICommit ≠ FRIFold", hCommit != hFold),
    ("FRICommit ≠ FRIQuery", hCommit != hQuery),
    ("FRIFold ≠ FRIQuery", hFold != hQuery)
  ]

  IO.println "  Pairwise Uniqueness:"
  for (name, result) in pairs do
    IO.println s!"    {name}: {if result then "PASS ✓" else "FAIL ✗"}"

  let allUnique := pairs.foldl (fun acc (_, r) => acc && r) true

  IO.println ""

  -- Additional check: domain-tagged hash must differ from raw
  let taggedDiffersFromRaw := hMerkle != hRaw && hCommit != hRaw && hFold != hRaw
  IO.println s!"  Tagged hashes differ from raw: {if taggedDiffersFromRaw then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  let passed := allUnique && taggedDiffersFromRaw

  if passed then
    IO.println "  DOMAIN SEPARATION TEST: PASSED ✓"
    IO.println "  → Different contexts produce cryptographically distinct outputs"
    IO.println "  → Cross-protocol attacks are prevented by domain tags"
  else
    IO.println "  DOMAIN SEPARATION TEST: FAILED ✗"
    IO.println "  → CRITICAL: Domain separation may be compromised!"

  IO.println ""
  pure passed

/-! ## Test 4: Sponge State Continuity Test

Additional test to verify sponge state is maintained correctly
across multiple absorb-squeeze cycles.
-/

/-- Test multiple absorb-squeeze cycles -/
def runSpongeStateTest : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 4: SPONGE STATE CONTINUITY"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Simulate a realistic FRI transcript flow
  let commitment1 : Nat := 0x1111111111111111
  let commitment2 : Nat := 0x2222222222222222
  let commitment3 : Nat := 0x3333333333333333

  -- Full transcript: absorb all, then squeeze
  let fullTranscript := poseidon2TranscriptSqueeze [commitment1, commitment2, commitment3]

  -- Partial transcripts
  let partial1 := poseidon2TranscriptSqueeze [commitment1]
  let partial2 := poseidon2TranscriptSqueeze [commitment1, commitment2]
  let partial3 := poseidon2TranscriptSqueeze [commitment2, commitment3]

  IO.println "  Simulated FRI Commitments:"
  IO.println s!"    C1: 0x{Nat.toDigits 16 commitment1 |>.asString}"
  IO.println s!"    C2: 0x{Nat.toDigits 16 commitment2 |>.asString}"
  IO.println s!"    C3: 0x{Nat.toDigits 16 commitment3 |>.asString}"
  IO.println ""

  IO.println "  Challenges Derived:"
  IO.println s!"    squeeze([C1, C2, C3]): {fullTranscript}"
  IO.println s!"    squeeze([C1]):         {partial1}"
  IO.println s!"    squeeze([C1, C2]):     {partial2}"
  IO.println s!"    squeeze([C2, C3]):     {partial3}"
  IO.println ""

  -- All must be unique
  let allUnique :=
    fullTranscript != partial1 &&
    fullTranscript != partial2 &&
    fullTranscript != partial3 &&
    partial1 != partial2 &&
    partial1 != partial3 &&
    partial2 != partial3

  IO.println s!"  All challenges unique: {if allUnique then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  -- Test that squeezing multiple times gives different values
  let multiSqueeze := poseidon2MultipleSqueeze bn254ParamsProduction [commitment1] 3
  let multiUnique := match multiSqueeze with
    | [a, b, c] => a != b && b != c && a != c
    | _ => false

  IO.println "  Multi-squeeze test (3 consecutive squeezes):"
  match multiSqueeze with
  | [a, b, c] =>
    IO.println s!"    Squeeze 1: {a}"
    IO.println s!"    Squeeze 2: {b}"
    IO.println s!"    Squeeze 3: {c}"
  | _ => IO.println "    Error: unexpected result"
  IO.println s!"  All squeezes unique: {if multiUnique then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  let passed := allUnique && multiUnique

  if passed then
    IO.println "  SPONGE STATE TEST: PASSED ✓"
    IO.println "  → Sponge state is correctly preserved between operations"
  else
    IO.println "  SPONGE STATE TEST: FAILED ✗"
    IO.println "  → State may not be preserved correctly"

  IO.println ""
  pure passed

/-! ## Main Audit Runner -/

def runSecurityAudit : IO Unit := do
  IO.println ""
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║     TRANSCRIPT SECURITY AUDIT - STEP 5.2                      ║"
  IO.println "║     Black-Box Cryptographic Vulnerability Tests               ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let t1 ← runAmnesiaTest
  let t2 ← runAvalancheTest
  let t3 ← runDomainSeparationTest
  let t4 ← runSpongeStateTest

  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  SECURITY AUDIT SUMMARY"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println s!"  Test 1 (Amnesia/State Preservation): {if t1 then "PASS ✓" else "FAIL ✗"}"
  IO.println s!"  Test 2 (Avalanche/Sensitivity):      {if t2 then "PASS ✓" else "FAIL ✗"}"
  IO.println s!"  Test 3 (Domain Separation):          {if t3 then "PASS ✓" else "FAIL ✗"}"
  IO.println s!"  Test 4 (Sponge State Continuity):    {if t4 then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

  let allPass := t1 && t2 && t3 && t4

  if allPass then
    IO.println "  ╔═════════════════════════════════════════════════════════════╗"
    IO.println "  ║  OVERALL RESULT: ALL SECURITY TESTS PASSED ✓               ║"
    IO.println "  ╚═════════════════════════════════════════════════════════════╝"
    IO.println ""
    IO.println "  Security Properties Verified:"
    IO.println "  • Transcript is resistant to reordering and omission"
    IO.println "  • Sponge state is correctly preserved between calls"
    IO.println "  • Single-bit changes produce avalanche effect in output"
    IO.println "  • Different domains are cryptographically separated"
  else
    IO.println "  ╔═════════════════════════════════════════════════════════════╗"
    IO.println "  ║  OVERALL RESULT: SECURITY AUDIT FAILED ✗                   ║"
    IO.println "  ╚═════════════════════════════════════════════════════════════╝"
    IO.println ""
    IO.println "  CRITICAL: Review failed tests for potential vulnerabilities"

  IO.println ""

#eval! runSecurityAudit

end AmoLean.Tests.TranscriptSecurityAudit
