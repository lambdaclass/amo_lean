/-
  AMO-Lean: Goldilocks Field Instance for NTT
  Phase 5: NTT Core - Task 1.4

  This module provides:
  1. NTTField instance for GoldilocksField
  2. Primitive roots for power-of-2 NTT sizes
  3. Precomputed twiddle factors

  Goldilocks Field: p = 2^64 - 2^32 + 1

  For NTT, we need primitive n-th roots of unity where n | (p-1).
  p - 1 = 2^32 × 3 × 5 × 17 × 257 × 65537

  So Goldilocks supports NTT sizes up to 2^32 (4 billion elements!).

  The generator g = 7 has order p-1, so:
    ω_n = g^((p-1)/n) is a primitive n-th root for any n | (p-1)
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.Field.Goldilocks

namespace AmoLean.NTT

open AmoLean.Field.Goldilocks

/-! ## Part 1: NTTField Instance for Goldilocks -/

/-- NTTField instance for GoldilocksField -/
instance : NTTField GoldilocksField where
  add := GoldilocksField.add
  sub := GoldilocksField.sub
  neg := GoldilocksField.neg
  mul := GoldilocksField.mul
  zero := GoldilocksField.zero
  one := GoldilocksField.one
  inv := GoldilocksField.inv
  pow := GoldilocksField.pow
  char := ORDER.toNat
  isZero := fun a => a.value == 0

/-! ## Part 2: Primitive Root Generator

The multiplicative group of Goldilocks has order p-1 = 2^64 - 2^32.
A generator is g = 7.

For NTT of size n (power of 2), the primitive n-th root is:
  ω_n = 7^((p-1)/n)
-/

/-- The multiplicative generator of Goldilocks: g = 7 -/
def GENERATOR : GoldilocksField := ⟨7⟩

/-- p - 1, the order of the multiplicative group -/
def P_MINUS_ONE : Nat := ORDER.toNat - 1

/-- Compute primitive n-th root of unity: ω = g^((p-1)/n)

Note: This only works when n divides (p-1), which includes
all powers of 2 up to 2^32.
-/
def primitiveRoot (n : Nat) (hn : n > 0) : GoldilocksField :=
  let exp := P_MINUS_ONE / n
  GoldilocksField.pow GENERATOR exp

/-! ## Part 3: Precomputed Roots for Common NTT Sizes -/

/-- 2^10 = 1024-th primitive root -/
def OMEGA_1024 : GoldilocksField := primitiveRoot 1024 (by decide)

/-- 2^16 = 65536-th primitive root -/
def OMEGA_65536 : GoldilocksField := primitiveRoot 65536 (by decide)

/-- 2^20 = 1048576-th primitive root -/
def OMEGA_1M : GoldilocksField := primitiveRoot 1048576 (by decide)

/-! ## Part 4: Verification Tests -/

/-- Test: ω^n = 1 for the primitive root -/
def testRootPowN (n : Nat) (hn : n > 0) : Bool :=
  let ω := primitiveRoot n hn
  (GoldilocksField.pow ω n).value == 1

/-- Test: ω^(n/2) = -1 for even n > 2 -/
def testHalfPowNegOne (n : Nat) (hn : n > 2) (h_even : 2 ∣ n) : Bool :=
  let ω := primitiveRoot n (by omega)
  let half_pow := GoldilocksField.pow ω (n / 2)
  -- -1 in Goldilocks is ORDER - 1
  half_pow.value == ORDER - 1

/-! ## Part 5: NTT Twiddle Table Generator -/

/-- Generate twiddle factors ω^0, ω^1, ..., ω^(n-1) -/
def genTwiddleTable (ω : GoldilocksField) (n : Nat) : List GoldilocksField :=
  (List.range n).map fun i => GoldilocksField.pow ω i

/-- Generate inverse twiddle factors ω^(-0), ω^(-1), ..., ω^(-(n-1))
    Using ω^(-k) = ω^(n-k) -/
def genInvTwiddleTable (ω : GoldilocksField) (n : Nat) : List GoldilocksField :=
  (List.range n).map fun i =>
    if i == 0 then GoldilocksField.one
    else GoldilocksField.pow ω (n - i)

/-! ## Part 6: Quick Tests -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   Goldilocks NTT Root Tests"
  IO.println "═══════════════════════════════════════════════════════════"

  -- Test 1: ω^n = 1 for various sizes
  IO.println "\n1. Testing ω^n = 1:"
  IO.println s!"   n=8:    {testRootPowN 8 (by decide)}"
  IO.println s!"   n=16:   {testRootPowN 16 (by decide)}"
  IO.println s!"   n=1024: {testRootPowN 1024 (by decide)}"

  -- Test 2: ω^(n/2) = -1
  IO.println "\n2. Testing ω^(n/2) = -1:"
  IO.println s!"   n=8:    {testHalfPowNegOne 8 (by decide) (by decide)}"
  IO.println s!"   n=16:   {testHalfPowNegOne 16 (by decide) (by decide)}"
  IO.println s!"   n=1024: {testHalfPowNegOne 1024 (by decide) (by decide)}"

  -- Test 3: Show actual root values
  IO.println "\n3. Primitive roots:"
  let ω8 := primitiveRoot 8 (by decide)
  let ω16 := primitiveRoot 16 (by decide)
  IO.println s!"   ω_8  = {ω8.value}"
  IO.println s!"   ω_16 = {ω16.value}"

  IO.println "\n═══════════════════════════════════════════════════════════"
  IO.println "   All tests completed"
  IO.println "═══════════════════════════════════════════════════════════"

end AmoLean.NTT
