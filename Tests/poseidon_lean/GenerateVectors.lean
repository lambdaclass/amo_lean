/-
  Phase 4b.1: Edge Case Vector Generator

  Generates test vectors for Poseidon2 BN254 with:
  1. Trivial cases (0, 1, 2)
  2. Values near the prime P
  3. Limb boundary values (2^64, 2^128, etc.)
  4. Bit pattern stress tests
  5. Random values with fixed seed

  Output format: JSON for human readability and easy parsing.

  Usage:
    lake env lean --run Tests/poseidon_lean/GenerateVectors.lean > vectors_edge.json
-/

import AmoLean.Protocols.Poseidon.Spec
import AmoLean.Protocols.Poseidon.Constants.BN254

open AmoLean.Protocols.Poseidon.Spec
open AmoLean.Protocols.Poseidon.Constants.BN254

namespace GenerateVectors

/-! ## BN254 Parameters with Real Round Constants -/

/-- BN254 parameters using the real round constants from HorizenLabs -/
def bn254ParamsReal : Params := {
  prime := p
  t := 3
  alpha := 5
  fullRounds := 8
  partialRounds := 56
  mds := #[#[2, 1, 1], #[1, 2, 1], #[1, 1, 3]]
  roundConstants := RC
}

/-! ## Edge Case Inputs

  Categories of edge cases for BN254:
  1. Trivial: 0, 1, 2
  2. Near prime: P-1, P-2, P-3
  3. Limb boundaries: 2^64-1, 2^64, 2^128-1, 2^128, 2^192-1, 2^192
  4. Bit patterns: all 1s, alternating, high bit set
  5. Small primes: 3, 5, 7, 11, 13, 17 (for algebraic edge cases)
-/

/-- 2^64 -/
def pow2_64 : Nat := 18446744073709551616

/-- 2^128 -/
def pow2_128 : Nat := 340282366920938463463374607431768211456

/-- 2^192 -/
def pow2_192 : Nat := 6277101735386680763835789423207666416102355444464034512896

/-! ## Simple PRNG for reproducible "random" values

  Linear Congruential Generator: x_{n+1} = (a * x_n + c) mod m
  Parameters from Numerical Recipes (good statistical properties)
-/

def lcgA : Nat := 1664525
def lcgC : Nat := 1013904223
def lcgM : Nat := 4294967296  -- 2^32

/-- Generate next LCG value -/
def lcgNext (seed : Nat) : Nat := (lcgA * seed + lcgC) % lcgM

/-- Generate a "random" field element from seed (combine multiple LCG outputs) -/
def randomFieldElement (seed : Nat) : Nat × Nat :=
  let s1 := lcgNext seed
  let s2 := lcgNext s1
  let s3 := lcgNext s2
  let s4 := lcgNext s3
  let s5 := lcgNext s4
  let s6 := lcgNext s5
  let s7 := lcgNext s6
  let s8 := lcgNext s7
  -- Combine outputs to get a field element
  let value := s1 + s2 * lcgM + s3 * lcgM * lcgM + s4 * lcgM * lcgM * lcgM
  (value % p, s8)

/-- Generate 3 random field elements for a state -/
def random3 (seed : Nat) : Array Nat × Nat :=
  let (v0, s1) := randomFieldElement seed
  let (v1, s2) := randomFieldElement s1
  let (v2, s3) := randomFieldElement s2
  (#[v0, v1, v2], s3)

/-! ## Test Vector Generation -/

/-- A test vector: input state and expected output state -/
structure TestVector where
  input : Array Nat
  output : Array Nat
  deriving Repr

/-- Generate a test vector from 3 input values -/
def makeTestVector (a b c : Nat) : TestVector :=
  let input := #[a % p, b % p, c % p]
  let output := poseidon2Permutation bn254ParamsReal input
  { input := input, output := output }

/-- Edge case vectors - manually constructed for coverage -/
def edgeCaseVectors : Array TestVector := #[
  -- Known test vector (must match HorizenLabs)
  makeTestVector 0 1 2,
  -- All zeros
  makeTestVector 0 0 0,
  -- All ones
  makeTestVector 1 1 1,
  -- Near-prime in each position
  makeTestVector (p - 1) 0 0,
  makeTestVector 0 (p - 1) 0,
  makeTestVector 0 0 (p - 1),
  makeTestVector (p - 1) (p - 1) (p - 1),
  -- Limb boundaries
  makeTestVector pow2_64 0 0,
  makeTestVector pow2_128 0 0,
  makeTestVector pow2_192 0 0,
  makeTestVector (pow2_64 - 1) (pow2_128 - 1) (pow2_192 - 1),
  -- Mixed edge cases
  makeTestVector 0 1 (p - 1),
  makeTestVector 1 (p - 1) 0,
  makeTestVector (p - 1) 0 1,
  -- Bit patterns
  makeTestVector 0xFFFFFFFFFFFFFFFF 0 0,
  makeTestVector 0xAAAAAAAAAAAAAAAA 0x5555555555555555 0,
  -- Small primes (algebraic edge cases for S-box)
  makeTestVector 3 5 7,
  makeTestVector 11 13 17
]

/-- Generate random vectors using LCG -/
def generateRandomVectors (seed : Nat) (count : Nat) : Array TestVector :=
  let rec go (s : Nat) (n : Nat) (acc : Array TestVector) : Array TestVector :=
    if n == 0 then acc
    else
      let (vals, newSeed) := random3 s
      let tv := makeTestVector (vals.get! 0) (vals.get! 1) (vals.get! 2)
      go newSeed (n - 1) (acc.push tv)
  termination_by n
  go seed count #[]

/-! ## JSON Output -/

/-- Convert Nat to hex string using a simple iterative approach -/
def natToHex (n : Nat) : String :=
  if n == 0 then "0x0"
  else
    let hexDigits := "0123456789abcdef"
    let rec go (n : Nat) (acc : String) : String :=
      if n == 0 then acc
      else
        let digit := n % 16
        let c := hexDigits.get! ⟨digit⟩
        go (n / 16) (String.mk [c] ++ acc)
    termination_by n
    "0x" ++ go n ""

/-- Convert test vector to JSON object -/
def testVectorToJson (tv : TestVector) : String :=
  let i0 := natToHex (tv.input.get! 0)
  let i1 := natToHex (tv.input.get! 1)
  let i2 := natToHex (tv.input.get! 2)
  let o0 := natToHex (tv.output.get! 0)
  let o1 := natToHex (tv.output.get! 1)
  let o2 := natToHex (tv.output.get! 2)
  s!"    \{\"input\": [\"{i0}\", \"{i1}\", \"{i2}\"], \"output\": [\"{o0}\", \"{o1}\", \"{o2}\"]}"

/-- Join strings with separator -/
def joinStrings (sep : String) (strs : List String) : String :=
  match strs with
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ joinStrings sep rest

/-- Generate full JSON output -/
def generateJson (edge random : Array TestVector) (seed : Nat) : String :=
  let all := edge ++ random
  let vectorsJson := joinStrings ",\n" (all.toList.map testVectorToJson)

  s!"\{
  \"description\": \"Poseidon2 BN254 t=3 test vectors for Phase 4b.1\",
  \"field\": \"BN254\",
  \"prime\": \"{natToHex p}\",
  \"state_size\": 3,
  \"full_rounds\": 8,
  \"partial_rounds\": 56,
  \"seed\": {seed},
  \"edge_case_count\": {edge.size},
  \"random_count\": {random.size},
  \"total_count\": {all.size},
  \"vectors\": [
{vectorsJson}
  ]
}"

/-! ## Main -/

def main : IO Unit := do
  let seed : Nat := 42  -- Fixed seed for reproducibility

  IO.eprintln "Generating edge case vectors..."
  let edgeVecs := edgeCaseVectors

  IO.eprintln s!"Generated {edgeVecs.size} edge case vectors"

  IO.eprintln "Generating random vectors..."
  let randomVecs := generateRandomVectors seed 100

  IO.eprintln s!"Generated {randomVecs.size} random vectors"

  let json := generateJson edgeVecs randomVecs seed

  IO.println json

  IO.eprintln "Done!"

end GenerateVectors

-- Run with: lake env lean --run Tests/poseidon_lean/GenerateVectors.lean
#eval! GenerateVectors.main
