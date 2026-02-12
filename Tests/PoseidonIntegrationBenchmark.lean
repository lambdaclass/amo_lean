/-
  Poseidon2 Integration Benchmark - Step 5.1 Validation

  This test battery validates:
  1. Type Safety: Correct handling of inputs exceeding field modulus
  2. Correctness: Merkle tree construction with Poseidon2
  3. Performance: Slowdown factor vs XOR-based TestHash

  Reference: ADR-007-step5-integration.md
-/

import AmoLean.Protocols.Poseidon.Integration
import AmoLean.Protocols.Poseidon.Spec
import AmoLean.Protocols.Poseidon.Constants.BN254

namespace AmoLean.Tests.PoseidonIntegrationBenchmark

open AmoLean.Protocols.Poseidon.Integration
open AmoLean.Protocols.Poseidon.Spec
open AmoLean.Protocols.Poseidon.Constants.BN254

/-! ## Part 1: Type Safety Tests (Entropy Preservation) -/

/-- BN254 prime for reference -/
def bn254Prime : Nat := p

/-- Test values that stress the modular reduction -/
def testValuesTypeSafety : List (String × Nat) := [
  ("zero", 0),
  ("one", 1),
  ("small", 42),
  ("UInt64.max", 18446744073709551615),  -- 2^64 - 1
  ("UInt128 approx", 340282366920938463463374607431768211455),  -- 2^128 - 1
  ("near_prime", bn254Prime - 1),
  ("equal_prime", bn254Prime),
  ("above_prime", bn254Prime + 1),
  ("double_prime", bn254Prime * 2),
  ("large_random", 12345678901234567890123456789012345678901234567890)
]

/-- Test 1A: Verify that input reduction is mathematically correct (not truncation) -/
def test_modular_reduction_correct : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 1A: Modular Reduction Correctness"
  IO.println "═══════════════════════════════════════════════════════════════"

  let mut allPass := true

  for (name, val) in testValuesTypeSafety do
    -- The adapter should reduce val mod prime
    let reduced := val % bn254Prime

    -- Hash with original value
    let h1 := poseidon2MerkleHash val 0

    -- Hash with explicitly reduced value
    let h2 := poseidon2MerkleHash reduced 0

    -- They MUST be equal (mathematical reduction, not truncation)
    let pass := h1 == h2

    if pass then
      IO.println s!"  ✓ {name}: hash({val} mod p) == hash({reduced})"
    else
      IO.println s!"  ✗ {name}: MISMATCH! hash({val})={h1} ≠ hash({reduced})={h2}"
      allPass := false

  IO.println ""
  pure allPass

/-- Test 1B: Verify entropy is preserved (different inputs → different outputs) -/
def test_entropy_preservation : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 1B: Entropy Preservation"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- Generate hashes for various inputs
  let inputs := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 100, 1000, 10000]
  let hashes := inputs.map (fun x => poseidon2MerkleHash x 0)

  -- Check all hashes are unique
  let uniqueHashes := hashes.eraseDups
  let allUnique := uniqueHashes.length == hashes.length

  if allUnique then
    IO.println s!"  ✓ {inputs.length} distinct inputs → {uniqueHashes.length} distinct outputs"
    IO.println "  ✓ No entropy collapse detected"
  else
    IO.println s!"  ✗ COLLISION! {inputs.length} inputs → only {uniqueHashes.length} distinct outputs"

  -- Test that values differing by 1 produce very different hashes
  let h1 := poseidon2MerkleHash 12345 0
  let h2 := poseidon2MerkleHash 12346 0
  let diffBits := (Nat.xor h1 h2).log2 + 1  -- Approximate bit difference

  IO.println s!"  Adjacent inputs (12345 vs 12346): ~{diffBits} bits differ in hash"

  IO.println ""
  pure allUnique

/-- Test 1C: Verify no silent truncation for large values -/
def test_no_truncation : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 1C: No Silent Truncation"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- If there was truncation, these would produce same hash
  let val1 : Nat := 0x123456789ABCDEF0  -- 64-bit value
  let val2 : Nat := 0x123456789ABCDEF0 + (1 <<< 64)  -- Same low bits, different high

  let h1 := poseidon2MerkleHash val1 0
  let h2 := poseidon2MerkleHash val2 0

  let noTruncation := h1 != h2

  if noTruncation then
    IO.println s!"  ✓ Values with same low 64 bits produce different hashes"
    IO.println s!"    val1 = {val1}"
    IO.println s!"    val2 = {val2}"
    IO.println s!"    h(val1) = {h1}"
    IO.println s!"    h(val2) = {h2}"
  else
    IO.println s!"  ✗ TRUNCATION DETECTED! High bits ignored"

  IO.println ""
  pure noTruncation

/-! ## Part 2: Merkle Tree Correctness -/

/-- Simple Merkle tree builder for testing -/
def buildMerkleLayer (hashes : List Nat) (hashFn : Nat → Nat → Nat) : List Nat :=
  match hashes with
  | [] => []
  | [x] => [x]
  | a :: b :: rest => hashFn a b :: buildMerkleLayer rest hashFn

/-- Build complete Merkle tree, return root -/
def buildMerkleRoot (leaves : List Nat) (hashFn : Nat → Nat → Nat) : Nat :=
  let rec loop (layer : List Nat) (fuel : Nat) : Nat :=
    match fuel, layer with
    | 0, _ => 0  -- Shouldn't happen with reasonable input
    | _, [] => 0
    | _, [root] => root
    | fuel + 1, layer => loop (buildMerkleLayer layer hashFn) fuel
  loop leaves (leaves.length + 1)

/-- XOR-based test hash (matching Merkle.lean testHash) -/
def testHashNat (a b : Nat) : Nat :=
  (Nat.xor a b) + 0x9e3779b97f4a7c15

/-- Test 2: Merkle tree construction correctness -/
def test_merkle_correctness : IO Bool := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 2: Merkle Tree Construction Correctness"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- 8 leaves for testing
  let leaves : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]

  IO.println s!"  Leaves: {leaves}"
  IO.println ""

  -- Manual layer-by-layer construction with Poseidon2
  IO.println "  Layer-by-layer construction (Poseidon2):"

  -- Layer 0: leaves
  IO.println s!"    Layer 0 (leaves): {leaves}"

  -- Layer 1: hash pairs
  let layer1 := [
    poseidon2MerkleHash 1 2,
    poseidon2MerkleHash 3 4,
    poseidon2MerkleHash 5 6,
    poseidon2MerkleHash 7 8
  ]
  IO.println s!"    Layer 1 (4 nodes): computed"

  -- Layer 2: hash pairs
  let layer2 := [
    poseidon2MerkleHash layer1[0]! layer1[1]!,
    poseidon2MerkleHash layer1[2]! layer1[3]!
  ]
  IO.println s!"    Layer 2 (2 nodes): computed"

  -- Layer 3: root
  let manualRoot := poseidon2MerkleHash layer2[0]! layer2[1]!
  IO.println s!"    Layer 3 (root): {manualRoot}"

  -- Now build using the generic builder
  let autoRoot := buildMerkleRoot leaves poseidon2MerkleHash

  IO.println ""
  IO.println s!"  Manual root:    {manualRoot}"
  IO.println s!"  Auto-built root: {autoRoot}"

  let correct := manualRoot == autoRoot

  if correct then
    IO.println "  ✓ Manual and auto-built roots MATCH"
  else
    IO.println "  ✗ MISMATCH between manual and auto-built roots!"

  -- Verify tree structure is different from XOR-based
  let xorRoot := buildMerkleRoot leaves testHashNat
  IO.println ""
  IO.println s!"  XOR-based root: {xorRoot}"
  IO.println s!"  Poseidon2 root: {autoRoot}"

  if xorRoot != autoRoot then
    IO.println "  ✓ Poseidon2 produces different root than XOR (expected)"
  else
    IO.println "  ⚠ WARNING: Same root as XOR (possible issue)"

  IO.println ""
  pure correct

/-! ## Part 3: Performance Benchmark -/

/-- Get current time in nanoseconds (approximation using IO) -/
def getTimeNs : IO Nat := do
  -- Use a simple counter-based approach for timing
  -- In production, would use actual system time
  pure 0  -- Placeholder, actual timing below

/-- Benchmark helper: run operation n times and measure -/
def benchmark (name : String) (n : Nat) (op : Unit → Nat) : IO (Nat × Nat) := do
  -- Warm-up
  for _ in [0:10] do
    let _ := op ()

  -- Actual measurement using iteration count as proxy
  let startTime ← IO.monoNanosNow
  for _ in [0:n] do
    let _ := op ()
  let endTime ← IO.monoNanosNow

  let totalNs := endTime - startTime
  let perOpNs := totalNs / n

  pure (totalNs, perOpNs)

/-- Test 3: Performance benchmark -/
def test_performance_benchmark : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 3: Performance Benchmark (XOR vs Poseidon2)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Test parameters
  let treeSizes := [8, 64, 256, 1024, 4096]
  let iterations := 100  -- Per tree size

  IO.println "  Tree Size | XOR Hash (ns) | Poseidon2 (ns) | Slowdown"
  IO.println "  ----------|---------------|----------------|----------"

  for treeSize in treeSizes do
    -- Generate leaves
    let leaves := (List.range treeSize).map (· + 1)

    -- Benchmark XOR hash
    let (xorTotal, _) ← benchmark "XOR" iterations (fun _ => buildMerkleRoot leaves testHashNat)
    let xorPerTree := xorTotal / iterations

    -- Benchmark Poseidon2 hash
    let (poseidonTotal, _) ← benchmark "Poseidon2" iterations (fun _ => buildMerkleRoot leaves poseidon2MerkleHash)
    let poseidonPerTree := poseidonTotal / iterations

    -- Calculate slowdown
    let slowdown := if xorPerTree > 0 then poseidonPerTree / xorPerTree else 0

    IO.println s!"  {treeSize}       | {xorPerTree}         | {poseidonPerTree}          | {slowdown}x"

  IO.println ""
  IO.println "  Note: Poseidon2 is cryptographically secure, XOR is not."
  IO.println "  Expected slowdown: 100-1000x is normal for real crypto hash."
  IO.println "  If slowdown > 5000x, adapter implementation may need optimization."
  IO.println ""

/-- Single hash benchmark -/
def test_single_hash_benchmark : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  TEST 3B: Single Hash Benchmark"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  let iterations := 1000

  -- XOR hash timing
  let xorStart ← IO.monoNanosNow
  for i in [0:iterations] do
    let _ := testHashNat i (i + 1)
  let xorEnd ← IO.monoNanosNow
  let xorPerHash := (xorEnd - xorStart) / iterations

  -- Poseidon2 hash timing
  let poseidonStart ← IO.monoNanosNow
  for i in [0:iterations] do
    let _ := poseidon2MerkleHash i (i + 1)
  let poseidonEnd ← IO.monoNanosNow
  let poseidonPerHash := (poseidonEnd - poseidonStart) / iterations

  let slowdown := if xorPerHash > 0 then poseidonPerHash / xorPerHash else poseidonPerHash

  IO.println s!"  XOR hash:      {xorPerHash} ns/hash"
  IO.println s!"  Poseidon2:     {poseidonPerHash} ns/hash"
  IO.println s!"  Slowdown:      {slowdown}x"
  IO.println ""

  -- Throughput calculation
  let xorThroughput := if xorPerHash > 0 then 1000000000 / xorPerHash else 0
  let poseidonThroughput := if poseidonPerHash > 0 then 1000000000 / poseidonPerHash else 0

  IO.println s!"  XOR throughput:      {xorThroughput} hashes/sec"
  IO.println s!"  Poseidon2 throughput: {poseidonThroughput} hashes/sec"
  IO.println ""

/-! ## Main Test Runner -/

def runAllTests : IO Unit := do
  IO.println ""
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║     POSEIDON2 INTEGRATION BENCHMARK - STEP 5.1 VALIDATION     ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Part 1: Type Safety
  let test1a ← test_modular_reduction_correct
  let test1b ← test_entropy_preservation
  let test1c ← test_no_truncation

  -- Part 2: Correctness
  let test2 ← test_merkle_correctness

  -- Part 3: Performance
  test_single_hash_benchmark
  test_performance_benchmark

  -- Summary
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "  SUMMARY"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println s!"  Test 1A (Modular Reduction): {if test1a then "PASS ✓" else "FAIL ✗"}"
  IO.println s!"  Test 1B (Entropy Preservation): {if test1b then "PASS ✓" else "FAIL ✗"}"
  IO.println s!"  Test 1C (No Truncation): {if test1c then "PASS ✓" else "FAIL ✗"}"
  IO.println s!"  Test 2  (Merkle Correctness): {if test2 then "PASS ✓" else "FAIL ✗"}"
  IO.println "  Test 3  (Performance): See metrics above"
  IO.println ""

  let allPass := test1a && test1b && test1c && test2
  if allPass then
    IO.println "  OVERALL: ALL INTEGRITY TESTS PASSED ✓"
  else
    IO.println "  OVERALL: SOME TESTS FAILED ✗"

  IO.println ""

#eval! runAllTests

end AmoLean.Tests.PoseidonIntegrationBenchmark
