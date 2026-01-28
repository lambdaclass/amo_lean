/-
  AMO-Lean: BN254 Field Implementation for FRI
  Phase 1 of Step 5.3 Migration

  This module implements the BN254 scalar field as an instance of FRIField
  and CryptoHash, enabling FRI to work with BN254 and Poseidon2.

  BN254 (also known as alt_bn128):
  - Prime: p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
  - ~254 bits (hence the name)
  - Used in Ethereum precompiles (ecAdd, ecMul, ecPairing)

  Design Decisions:
  - Uses Nat internally (Lean's arbitrary precision)
  - All operations mod p
  - Modular inverse via Fermat's Little Theorem: a^(-1) = a^(p-2) mod p
  - CryptoHash uses Poseidon2 from Integration.lean

  Reference: docs/poseidon/ADR-009-step53-generic-field-migration.md
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.Protocols.Poseidon.Constants.BN254
import AmoLean.Protocols.Poseidon.Integration

namespace AmoLean.FRI.Fields.BN254

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.Protocols.Poseidon.Constants.BN254 (p)
open AmoLean.Protocols.Poseidon.DomainSeparation (DomainTag)
open AmoLean.Protocols.Poseidon.Integration

/-! ## Part 1: BN254 Field Element Type -/

/-- BN254 scalar field element.
    Value is always in range [0, p).
-/
structure BN254 where
  val : Nat
  deriving Repr, Inhabited

namespace BN254

/-! ## Part 2: Basic Arithmetic -/

/-- Reduce a natural number mod p -/
@[inline]
def ofNat (n : Nat) : BN254 := ⟨n % p⟩

/-- Extract canonical representative -/
@[inline]
def toNat (x : BN254) : Nat := x.val

/-- Zero element -/
def zero : BN254 := ⟨0⟩

/-- One element -/
def one : BN254 := ⟨1⟩

/-- Addition mod p -/
@[inline]
def add (a b : BN254) : BN254 := ofNat (a.val + b.val)

/-- Subtraction mod p (handles underflow) -/
@[inline]
def sub (a b : BN254) : BN254 := ofNat (p + a.val - b.val)

/-- Multiplication mod p -/
@[inline]
def mul (a b : BN254) : BN254 := ofNat (a.val * b.val)

/-- Negation mod p -/
@[inline]
def neg (a : BN254) : BN254 :=
  if a.val == 0 then ⟨0⟩ else ofNat (p - a.val)

/-! ## Part 3: Modular Exponentiation and Inverse -/

/-- Modular exponentiation: base^exp mod p
    Uses square-and-multiply algorithm.
-/
def modPow (base exp : Nat) : Nat :=
  let rec go (b : Nat) (e : Nat) (acc : Nat) : Nat :=
    if h : e = 0 then acc
    else if e % 2 = 1 then
      go ((b * b) % p) (e / 2) ((acc * b) % p)
    else
      go ((b * b) % p) (e / 2) acc
  termination_by e
  decreasing_by
    all_goals simp_wf
    all_goals omega
  go (base % p) exp 1

/-- Modular multiplicative inverse using Fermat's Little Theorem.
    For prime p: a^(-1) = a^(p-2) mod p

    SAFETY: Returns 0 for a = 0 (no inverse exists).
    Caller must ensure divisor is non-zero.
-/
def modInverse (a : Nat) : Nat :=
  if a % p == 0 then 0  -- No inverse for 0
  else modPow a (p - 2)

/-- Field division: a / b = a * b^(-1) mod p -/
@[inline]
def fdiv (a b : BN254) : BN254 :=
  if b.val == 0 then ⟨0⟩  -- Division by zero → 0 (convention)
  else ofNat (a.val * modInverse b.val)

/-! ## Part 4: Equality -/

/-- BEq instance for BN254 -/
instance : BEq BN254 where
  beq a b := a.val == b.val

/-- DecidableEq for theorem proving (if needed) -/
instance : DecidableEq BN254 := fun a b =>
  if h : a.val = b.val then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by cases a; cases b; simp_all)

end BN254

/-! ## Part 5: Typeclass Instances -/

/-- Add instance -/
instance : Add BN254 where
  add := BN254.add

/-- Sub instance -/
instance : Sub BN254 where
  sub := BN254.sub

/-- Mul instance -/
instance : Mul BN254 where
  mul := BN254.mul

/-- Neg instance -/
instance : Neg BN254 where
  neg := BN254.neg

/-- FRIField instance for BN254 -/
instance : FRIField BN254 where
  zero := BN254.zero
  one := BN254.one
  fdiv := BN254.fdiv
  ofNat := BN254.ofNat
  toNat := BN254.toNat
  modulus := p

/-! ## Part 6: CryptoHash Instance (Poseidon2) -/

/-- CryptoHash instance for BN254 using Poseidon2.

    This connects BN254 to the cryptographically secure Poseidon2
    hash function from Integration.lean.
-/
instance : CryptoHash BN254 where
  hash2to1 := fun a b =>
    BN254.ofNat (poseidon2MerkleHash a.toNat b.toNat)

  hashWithDomain := fun tag a b =>
    BN254.ofNat (poseidon2HashWithDomainTag bn254ParamsProduction tag a.toNat b.toNat)

  squeeze := fun xs count =>
    let nats := xs.map BN254.toNat
    -- Use the counter as additional entropy
    let absorbed := nats ++ [count]
    BN254.ofNat (poseidon2TranscriptSqueeze absorbed)

  squeezeMany := fun xs startCount count =>
    let nats := xs.map BN254.toNat
    let results := poseidon2MultipleSqueeze bn254ParamsProduction (nats ++ [startCount]) count
    results.map BN254.ofNat

/-! ## Part 7: Tests -/

section Tests

-- Basic arithmetic tests
#eval BN254.add ⟨5⟩ ⟨7⟩        -- Should be ⟨12⟩
#eval BN254.mul ⟨3⟩ ⟨4⟩        -- Should be ⟨12⟩
#eval BN254.sub ⟨5⟩ ⟨3⟩        -- Should be ⟨2⟩
#eval BN254.sub ⟨3⟩ ⟨5⟩        -- Should be ⟨p - 2⟩
#eval BN254.neg ⟨5⟩            -- Should be ⟨p - 5⟩

-- Modular inverse test: 2 * inv(2) = 1
def testInverse : Bool :=
  let two := BN254.ofNat 2
  let invTwo := BN254.ofNat (BN254.modInverse 2)
  (BN254.mul two invTwo).val == 1

#eval testInverse  -- Should be true

-- Field division test: 6 / 2 = 3
def testDivision : Bool :=
  let six := BN254.ofNat 6
  let two := BN254.ofNat 2
  (BN254.fdiv six two).val == 3

#eval testDivision  -- Should be true

-- FRIField instance test
def testFRIField : Bool :=
  let x : BN254 := FRIField.ofNat 10
  let y : BN254 := FRIField.ofNat 5
  let sum := x + y
  let diff := x - y
  let prod := x * y
  sum.val == 15 && diff.val == 5 && prod.val == 50

#eval testFRIField  -- Should be true

-- CryptoHash test: hash is deterministic
def testHashDeterministic : Bool :=
  let a := BN254.ofNat 1
  let b := BN254.ofNat 2
  let h1 := CryptoHash.hash2to1 a b
  let h2 := CryptoHash.hash2to1 a b
  h1 == h2

#eval testHashDeterministic  -- Should be true

-- CryptoHash test: different inputs produce different outputs
def testHashDifferent : Bool :=
  let a := BN254.ofNat 1
  let b := BN254.ofNat 2
  let c := BN254.ofNat 3
  let h1 := CryptoHash.hash2to1 a b
  let h2 := CryptoHash.hash2to1 a c
  h1 != h2

#eval testHashDifferent  -- Should be true

-- Run all tests
def runBN254Tests : IO Unit := do
  IO.println "BN254 Field Tests"
  IO.println "================="
  IO.println s!"  Inverse test: {if testInverse then "PASS" else "FAIL"}"
  IO.println s!"  Division test: {if testDivision then "PASS" else "FAIL"}"
  IO.println s!"  FRIField test: {if testFRIField then "PASS" else "FAIL"}"
  IO.println s!"  Hash deterministic: {if testHashDeterministic then "PASS" else "FAIL"}"
  IO.println s!"  Hash different: {if testHashDifferent then "PASS" else "FAIL"}"

#eval runBN254Tests

end Tests

/-! ## Part 8: Summary -/

def bn254Summary : String :=
  "BN254 Field Implementation (Step 5.3 Phase 1)
   =============================================

   1. Type: BN254 structure wrapping Nat
      - val: Nat in range [0, p)
      - p = 21888242871839275222246405745257275088548364400416034343698204186575808495617

   2. Arithmetic (all mod p):
      - add, sub, mul, neg: Standard field operations
      - fdiv: a/b = a * b^(p-2) mod p (Fermat's Little Theorem)
      - modPow: Square-and-multiply exponentiation

   3. FRIField Instance:
      - zero, one: Field identity elements
      - ofNat, toNat: Conversion functions
      - modulus: Returns p

   4. CryptoHash Instance (Poseidon2):
      - hash2to1: 2-to-1 Merkle hash
      - hashWithDomain: Domain-separated hashing
      - squeeze, squeezeMany: Fiat-Shamir challenges

   Security:
   - Full 254-bit field (no truncation)
   - Collision resistance: ~127 bits
   - Uses production Poseidon2 parameters"

#eval IO.println bn254Summary

end AmoLean.FRI.Fields.BN254
