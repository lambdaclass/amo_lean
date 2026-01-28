/-
  AMO-Lean: TestField Implementation for Fast Testing
  Phase 1 of Step 5.3 Migration

  This module provides a small, fast field for testing purposes.
  It uses a Mersenne prime (2^61 - 1) and XOR-based hashing.

  ╔═══════════════════════════════════════════════════════════════════╗
  ║  WARNING: NOT CRYPTOGRAPHICALLY SECURE                            ║
  ║                                                                   ║
  ║  TestField is designed for:                                       ║
  ║  - Fast unit tests                                                ║
  ║  - CI pipeline speed                                              ║
  ║  - Algorithm verification                                         ║
  ║                                                                   ║
  ║  Do NOT use in production or security-sensitive contexts!         ║
  ╚═══════════════════════════════════════════════════════════════════╝

  Design Rationale:
  - Same FRIField/CryptoHash interface as BN254
  - Tests written with TestField work identically with BN254
  - XOR hash is deterministic and fast (~10x faster than Poseidon2)
  - Mersenne prime arithmetic is efficient (no modular reduction needed for XOR)

  Reference: docs/poseidon/ADR-009-step53-generic-field-migration.md
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.Protocols.Poseidon.DomainSeparation

namespace AmoLean.FRI.Fields.TestField

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.Protocols.Poseidon.DomainSeparation (DomainTag)

/-! ## Part 1: Field Parameters -/

/-- Mersenne prime: 2^61 - 1 = 2305843009213693951
    Fits in 64 bits, efficient arithmetic.
-/
def testPrime : Nat := 2305843009213693951

/-! ## Part 2: TestField Type -/

/-- Test field element for fast testing.
    Value is always in range [0, testPrime).
-/
structure TestField where
  val : Nat
  deriving Repr, Inhabited

namespace TestField

/-! ## Part 3: Basic Arithmetic -/

/-- Reduce a natural number mod testPrime -/
@[inline]
def ofNat (n : Nat) : TestField := ⟨n % testPrime⟩

/-- Extract canonical representative -/
@[inline]
def toNat (x : TestField) : Nat := x.val

/-- Zero element -/
def zero : TestField := ⟨0⟩

/-- One element -/
def one : TestField := ⟨1⟩

/-- Addition mod testPrime -/
@[inline]
def add (a b : TestField) : TestField := ofNat (a.val + b.val)

/-- Subtraction mod testPrime (handles underflow) -/
@[inline]
def sub (a b : TestField) : TestField := ofNat (testPrime + a.val - b.val)

/-- Multiplication mod testPrime -/
@[inline]
def mul (a b : TestField) : TestField := ofNat (a.val * b.val)

/-- Negation mod testPrime -/
@[inline]
def neg (a : TestField) : TestField :=
  if a.val == 0 then ⟨0⟩ else ofNat (testPrime - a.val)

/-! ## Part 4: Modular Exponentiation and Inverse -/

/-- Modular exponentiation: base^exp mod testPrime -/
def modPow (base exp : Nat) : Nat :=
  let rec go (b : Nat) (e : Nat) (acc : Nat) : Nat :=
    if h : e = 0 then acc
    else if e % 2 = 1 then
      go ((b * b) % testPrime) (e / 2) ((acc * b) % testPrime)
    else
      go ((b * b) % testPrime) (e / 2) acc
  termination_by e
  decreasing_by
    all_goals simp_wf
    all_goals omega
  go (base % testPrime) exp 1

/-- Modular multiplicative inverse: a^(p-2) mod p -/
def modInverse (a : Nat) : Nat :=
  if a % testPrime == 0 then 0
  else modPow a (testPrime - 2)

/-- Field division: a / b = a * b^(-1) mod testPrime -/
@[inline]
def fdiv (a b : TestField) : TestField :=
  if b.val == 0 then ⟨0⟩
  else ofNat (a.val * modInverse b.val)

/-! ## Part 5: Equality -/

instance : BEq TestField where
  beq a b := a.val == b.val

instance : DecidableEq TestField := fun a b =>
  if h : a.val = b.val then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by cases a; cases b; simp_all)

end TestField

/-! ## Part 6: Typeclass Instances -/

instance : Add TestField where
  add := TestField.add

instance : Sub TestField where
  sub := TestField.sub

instance : Mul TestField where
  mul := TestField.mul

instance : Neg TestField where
  neg := TestField.neg

/-- FRIField instance for TestField -/
instance : FRIField TestField where
  zero := TestField.zero
  one := TestField.one
  fdiv := TestField.fdiv
  ofNat := TestField.ofNat
  toNat := TestField.toNat
  modulus := testPrime

/-! ## Part 7: XOR-Based Hash (NOT SECURE) -/

/-- XOR-based hash mixing constant (golden ratio prime).
    Used to ensure hash function has good avalanche properties
    even though it's not cryptographically secure.
-/
def xorMixConstant : Nat := 0x9e3779b97f4a7c15

/-- Simple XOR-rotate-mix hash.
    NOT SECURE - only for testing!
-/
def xorHash (a b : Nat) : Nat :=
  let mixed := (a ^^^ b) + xorMixConstant
  let rotated := (mixed <<< 13) ^^^ (mixed >>> 7)
  rotated % testPrime

/-- XOR hash with domain tag injection -/
def xorHashWithDomain (tag : DomainTag) (a b : Nat) : Nat :=
  let tagVal := tag.toCapacityValue
  let mixedA := (a ^^^ tagVal) + xorMixConstant
  xorHash mixedA b

/-- XOR-based squeeze function -/
def xorSqueeze (absorbed : List Nat) (count : Nat) : Nat :=
  let base := absorbed.foldl (fun acc x => acc ^^^ x + xorMixConstant) count
  base % testPrime

/-- XOR-based multi-squeeze -/
def xorSqueezeMany (absorbed : List Nat) (startCount : Nat) (count : Nat) : List Nat :=
  (List.range count).map fun i =>
    xorSqueeze absorbed (startCount + i)

/-! ## Part 8: CryptoHash Instance -/

/-- CryptoHash instance for TestField using XOR-based hash.

    ╔═══════════════════════════════════════════════════════════════╗
    ║  NOT CRYPTOGRAPHICALLY SECURE - FOR TESTING ONLY              ║
    ╚═══════════════════════════════════════════════════════════════╝
-/
instance : CryptoHash TestField where
  hash2to1 := fun a b =>
    TestField.ofNat (xorHash a.toNat b.toNat)

  hashWithDomain := fun tag a b =>
    TestField.ofNat (xorHashWithDomain tag a.toNat b.toNat)

  squeeze := fun xs count =>
    let nats := xs.map TestField.toNat
    TestField.ofNat (xorSqueeze nats count)

  squeezeMany := fun xs startCount count =>
    let nats := xs.map TestField.toNat
    (xorSqueezeMany nats startCount count).map TestField.ofNat

/-! ## Part 9: Tests -/

section Tests

-- Basic arithmetic
#eval TestField.add ⟨5⟩ ⟨7⟩     -- Should be ⟨12⟩
#eval TestField.mul ⟨3⟩ ⟨4⟩     -- Should be ⟨12⟩
#eval TestField.sub ⟨5⟩ ⟨3⟩     -- Should be ⟨2⟩

-- Modular inverse test
def testInverse : Bool :=
  let two := TestField.ofNat 2
  let invTwo := TestField.ofNat (TestField.modInverse 2)
  (TestField.mul two invTwo).val == 1

#eval testInverse  -- Should be true

-- Division test
def testDivision : Bool :=
  let six := TestField.ofNat 6
  let two := TestField.ofNat 2
  (TestField.fdiv six two).val == 3

#eval testDivision  -- Should be true

-- FRIField test
def testFRIField : Bool :=
  let x : TestField := FRIField.ofNat 10
  let y : TestField := FRIField.ofNat 5
  let sum := x + y
  let diff := x - y
  let prod := x * y
  sum.val == 15 && diff.val == 5 && prod.val == 50

#eval testFRIField  -- Should be true

-- Hash deterministic test
def testHashDeterministic : Bool :=
  let a := TestField.ofNat 1
  let b := TestField.ofNat 2
  let h1 := CryptoHash.hash2to1 a b
  let h2 := CryptoHash.hash2to1 a b
  h1 == h2

#eval testHashDeterministic  -- Should be true

-- Hash different inputs test
def testHashDifferent : Bool :=
  let a := TestField.ofNat 1
  let b := TestField.ofNat 2
  let c := TestField.ofNat 3
  let h1 := CryptoHash.hash2to1 a b
  let h2 := CryptoHash.hash2to1 a c
  h1 != h2

#eval testHashDifferent  -- Should be true

-- Domain separation test
def testDomainSeparation : Bool :=
  let a := TestField.ofNat 1
  let b := TestField.ofNat 2
  let h1 := CryptoHash.hashWithDomain DomainTag.merkleTree2to1 a b
  let h2 := CryptoHash.hashWithDomain DomainTag.friFold a b
  h1 != h2

#eval testDomainSeparation  -- Should be true

-- Run all tests
def runTestFieldTests : IO Unit := do
  IO.println "TestField Tests (NOT SECURE)"
  IO.println "============================"
  IO.println s!"  Inverse test: {if testInverse then "PASS" else "FAIL"}"
  IO.println s!"  Division test: {if testDivision then "PASS" else "FAIL"}"
  IO.println s!"  FRIField test: {if testFRIField then "PASS" else "FAIL"}"
  IO.println s!"  Hash deterministic: {if testHashDeterministic then "PASS" else "FAIL"}"
  IO.println s!"  Hash different: {if testHashDifferent then "PASS" else "FAIL"}"
  IO.println s!"  Domain separation: {if testDomainSeparation then "PASS" else "FAIL"}"

#eval runTestFieldTests

end Tests

/-! ## Part 10: Summary -/

def testFieldSummary : String :=
  "TestField Implementation (Step 5.3 Phase 1)
   ==========================================

   ╔═══════════════════════════════════════════════════════════════╗
   ║  WARNING: NOT CRYPTOGRAPHICALLY SECURE - FOR TESTING ONLY     ║
   ╚═══════════════════════════════════════════════════════════════╝

   1. Type: TestField structure wrapping Nat
      - val: Nat in range [0, testPrime)
      - testPrime = 2^61 - 1 = 2305843009213693951 (Mersenne prime)

   2. Arithmetic (all mod testPrime):
      - add, sub, mul, neg: Standard field operations
      - fdiv: Fermat's Little Theorem inverse

   3. FRIField Instance:
      - Same interface as BN254
      - Tests written for TestField work with BN254

   4. CryptoHash Instance (XOR-based):
      - hash2to1: XOR-mix hash
      - hashWithDomain: Tag injected before hashing
      - squeeze, squeezeMany: XOR-based squeeze

   Use Cases:
   - Fast CI tests (~10x faster than Poseidon2)
   - Algorithm verification
   - Debugging

   NOT for:
   - Production
   - Security testing
   - Cryptographic validation"

#eval IO.println testFieldSummary

end AmoLean.FRI.Fields.TestField
