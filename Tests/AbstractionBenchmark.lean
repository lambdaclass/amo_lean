/-
  Abstraction Overhead Benchmark
  Phase 2 Migration Audit - Test 3

  Measures the performance cost of the generic field abstraction
  by comparing Legacy (UInt64), TestField, and BN254 implementations.
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Merkle
import AmoLean.FRI.Fields.TestField
import AmoLean.FRI.Fields.BN254

namespace Tests.AbstractionBenchmark

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Merkle (FlatMerkle buildTree testHash)
open AmoLean.FRI.Fields.TestField (TestField testPrime)
open AmoLean.FRI.Fields.BN254 (BN254)

/-! ## Part 1: Benchmark Infrastructure -/

/-- Left-pad a string to given width -/
def padLeft (width : Nat) (s : String) : String :=
  let len := s.length
  if len >= width then s
  else String.mk (List.replicate (width - len) ' ') ++ s

/-- High-resolution timing helper -/
def timeMs (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  return (result, stop - start)

/-- Generate pseudo-random array -/
def generateArray (seed : Nat) (size : Nat) : Array UInt64 :=
  Array.range size |>.map fun i =>
    -- Simple LCG mixing
    let x := seed + i * 6364136223846793005 + 1442695040888963407
    UInt64.ofNat (x % (2^64))

/-! ## Part 2: Hash Functions for Each Scenario -/

/-- TestField XOR hash (matching legacy behavior) -/
def testFieldHash (a b : TestField) : TestField :=
  let aVal := FRIField.toNat a
  let bVal := FRIField.toNat b
  FRIField.ofNat (((aVal ^^^ bVal) + 0x9e3779b97f4a7c15) % testPrime)

/-- BN254 XOR hash (for fair comparison - same algorithm, different field) -/
def bn254XorHash (a b : BN254) : BN254 :=
  let aVal := FRIField.toNat a
  let bVal := FRIField.toNat b
  FRIField.ofNat ((aVal ^^^ bVal) + 0x9e3779b97f4a7c15)

/-! ## Part 3: Benchmarks -/

/-- Benchmark: Legacy UInt64 Merkle Tree -/
def benchmarkLegacy (leaves : Array UInt64) : IO Nat := do
  let (_, time) ← timeMs do
    match buildTree leaves testHash with
    | some tree => pure tree.root
    | none => pure 0
  return time

/-- Benchmark: TestField Merkle Tree -/
def benchmarkTestField (leaves : Array TestField) : IO Nat := do
  let (_, time) ← timeMs do
    match buildTree leaves testFieldHash with
    | some tree => pure (FRIField.toNat tree.root)
    | none => pure 0
  return time

/-- Benchmark: BN254 Merkle Tree (with XOR for fair comparison) -/
def benchmarkBN254XorHash (leaves : Array BN254) : IO Nat := do
  let (_, time) ← timeMs do
    match buildTree leaves bn254XorHash with
    | some tree => pure (FRIField.toNat tree.root)
    | none => pure 0
  return time

/-- Benchmark: BN254 with CryptoHash.hash2to1 (Poseidon2) -/
def benchmarkBN254Poseidon (leaves : Array BN254) : IO Nat := do
  let (_, time) ← timeMs do
    match buildTree leaves CryptoHash.hash2to1 with
    | some tree => pure (FRIField.toNat tree.root)
    | none => pure 0
  return time

/-! ## Part 4: Main Benchmark Suite -/

def runAbstractionBenchmark : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║     ABSTRACTION OVERHEAD BENCHMARK - Phase 2 Migration Audit        ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  -- Test sizes: smaller for quick validation, 64k is the target
  let sizes := [1024, 4096, 16384, 65536]

  IO.println "Generating test data..."
  let seed := 0xCAFEBABE

  for size in sizes do
    IO.println s!"\n┌─────────────────────────────────────────────────────────────────────┐"
    IO.println s!"│  MERKLE TREE BENCHMARK: {size} leaves                                │"
    IO.println s!"└─────────────────────────────────────────────────────────────────────┘"

    -- Generate base data
    let legacyLeaves := generateArray seed size

    -- Convert to other types
    let testFieldLeaves : Array TestField := legacyLeaves.map fun x =>
      FRIField.ofNat x.toNat
    let bn254Leaves : Array BN254 := legacyLeaves.map fun x =>
      FRIField.ofNat x.toNat

    -- Run benchmarks (3 iterations each for stability)
    let mut legacyTimes : List Nat := []
    let mut testFieldTimes : List Nat := []
    let mut bn254XorTimes : List Nat := []
    let mut bn254PoseidonTimes : List Nat := []

    for _ in List.range 3 do
      let t1 ← benchmarkLegacy legacyLeaves
      let t2 ← benchmarkTestField testFieldLeaves
      let t3 ← benchmarkBN254XorHash bn254Leaves
      let t4 ← benchmarkBN254Poseidon bn254Leaves
      legacyTimes := t1 :: legacyTimes
      testFieldTimes := t2 :: testFieldTimes
      bn254XorTimes := t3 :: bn254XorTimes
      bn254PoseidonTimes := t4 :: bn254PoseidonTimes

    -- Calculate averages
    let avgLegacy := legacyTimes.foldl (· + ·) 0 / 3
    let avgTestField := testFieldTimes.foldl (· + ·) 0 / 3
    let avgBN254Xor := bn254XorTimes.foldl (· + ·) 0 / 3
    let avgBN254Poseidon := bn254PoseidonTimes.foldl (· + ·) 0 / 3

    -- Calculate ratios
    let tfOverhead := if avgLegacy > 0 then avgTestField * 100 / avgLegacy else 0
    let bn254XorOverhead := if avgLegacy > 0 then avgBN254Xor * 100 / avgLegacy else 0
    let poseidonOverhead := if avgTestField > 0 then avgBN254Poseidon * 100 / avgTestField else 0

    IO.println ""
    IO.println "  ┌─────────────────────────┬──────────┬──────────────────────┐"
    IO.println "  │ Scenario                │ Time(ms) │ Ratio vs Baseline    │"
    IO.println "  ├─────────────────────────┼──────────┼──────────────────────┤"
    IO.println s!"  │ A: Legacy (UInt64)      │ {padLeft 8 (toString avgLegacy)} │ 100% (baseline)      │"
    IO.println s!"  │ B: TestField (generic)  │ {padLeft 8 (toString avgTestField)} │ {padLeft 3 (toString tfOverhead)}% vs Legacy        │"
    IO.println s!"  │ C: BN254 XOR (generic)  │ {padLeft 8 (toString avgBN254Xor)} │ {padLeft 3 (toString bn254XorOverhead)}% vs Legacy        │"
    IO.println s!"  │ D: BN254 Poseidon2      │ {padLeft 8 (toString avgBN254Poseidon)} │ {padLeft 3 (toString poseidonOverhead)}% vs TestField    │"
    IO.println "  └─────────────────────────┴──────────┴──────────────────────┘"

    IO.println ""
    IO.println "  Analysis:"
    IO.println s!"    • Abstraction overhead (Legacy→TestField): {if tfOverhead > 100 then s!"+{tfOverhead - 100}%" else if tfOverhead < 100 then s!"-{100 - tfOverhead}%" else "0%"}"
    IO.println s!"    • BigInt overhead (Legacy→BN254 XOR):      {if bn254XorOverhead > 100 then s!"+{bn254XorOverhead - 100}%" else if bn254XorOverhead < 100 then s!"-{100 - bn254XorOverhead}%" else "0%"}"
    IO.println s!"    • Poseidon2 vs XOR (TestField→BN254 P2):   {if poseidonOverhead > 100 then s!"+{poseidonOverhead - 100}%" else if poseidonOverhead < 100 then s!"-{100 - poseidonOverhead}%" else "0%"}"

  IO.println "\n╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║                       BENCHMARK COMPLETE                            ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Interpretation:"
  IO.println "  • Legacy vs TestField: Pure typeclass/boxing overhead"
  IO.println "  • Legacy vs BN254 XOR: BigInt arithmetic overhead"
  IO.println "  • TestField vs BN254 Poseidon2: Real cryptographic hash cost"
  IO.println ""
  IO.println "Acceptable thresholds:"
  IO.println "  • Abstraction overhead < 20%: PASS"
  IO.println "  • Poseidon2 10-100x slower than XOR: Expected (crypto cost)"

#eval! runAbstractionBenchmark

end Tests.AbstractionBenchmark
