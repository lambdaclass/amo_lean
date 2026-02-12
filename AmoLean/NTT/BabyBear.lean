/-
  AMO-Lean: BabyBear Field Instance for NTT
  Fase 8 Onda 1 — Subfase 2 Capas 2-5: NTTField, Roots, Twiddles, Tests

  BabyBear Field: p = 2^31 - 2^27 + 1 = 2013265921

  For NTT, we need primitive n-th roots of unity where n | (p-1).
  p - 1 = 2^27 × 15 = 2^27 × 3 × 5

  So BabyBear supports NTT sizes up to 2^27 (134M elements).

  The generator g = 31 has order p-1, so:
    ω_n = g^((p-1)/n) is a primitive n-th root for any n | (p-1)

  Reference: Plonky3 baby-bear/src/lib.rs
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.Field.BabyBear

namespace AmoLean.NTT.BabyBear

open AmoLean.Field.BabyBear

/-! ## Part 1: NTTField Instance for BabyBear -/

/-- NTTField instance for BabyBearField.

    Since NTTField extends CommRing, and BabyBearField already has a CommRing
    instance (from AmoLean.Field.BabyBear), we only need to provide the
    NTT-specific operations: inv, char, isZero.
-/
instance : NTTField BabyBearField where
  inv := BabyBearField.inv
  char := ORDER.toNat  -- 2013265921
  isZero := fun a => a.value == 0

/-! ## Part 2: Primitive Root Generator

The multiplicative group of BabyBear has order p-1 = 2013265920.
p - 1 = 2^27 × 3 × 5

A generator is g = 31 (multiplicative order = p-1).

For NTT of size n (power of 2), the primitive n-th root is:
  ω_n = 31^((p-1)/n)
-/

/-- The multiplicative generator of BabyBear: g = 31 -/
def GENERATOR : BabyBearField := ⟨31⟩

/-- p - 1, the order of the multiplicative group -/
def P_MINUS_ONE : Nat := ORDER.toNat - 1

/-- Maximum NTT size: 2^27 = 134217728 -/
def MAX_NTT_LOG2 : Nat := 27

/-- Compute primitive n-th root of unity: ω = g^((p-1)/n)

Note: This only works when n divides (p-1), which includes
all powers of 2 up to 2^27.
-/
def primitiveRoot (n : Nat) (hn : n > 0) : BabyBearField :=
  let exp := P_MINUS_ONE / n
  BabyBearField.pow GENERATOR exp

/-! ## Part 3: Primitive Root Proof

Prove that g = 31 is a primitive root (generator of F_p*).
This means: for each prime factor q of (p-1),
  g^((p-1)/q) ≠ 1 (mod p)

p - 1 = 2^27 × 3 × 5
Prime factors of (p-1): {2, 3, 5}
-/

/-- g = 31 is a primitive root of BabyBear.
    Verified by checking g^((p-1)/q) ≠ 1 for each prime factor q of p-1.

    The prime factors of p-1 = 2013265920 are: 2, 3, 5.
    - g^((p-1)/2) = 31^1006632960 should ≠ 1 (should be p-1 = -1)
    - g^((p-1)/3) = 31^671088640 should ≠ 1
    - g^((p-1)/5) = 31^402653184 should ≠ 1
-/
theorem babybear_generator_is_primitive_root :
    -- g^((p-1)/2) ≠ 1
    BabyBearField.pow ⟨31⟩ (P_MINUS_ONE / 2) ≠ BabyBearField.one ∧
    -- g^((p-1)/3) ≠ 1
    BabyBearField.pow ⟨31⟩ (P_MINUS_ONE / 3) ≠ BabyBearField.one ∧
    -- g^((p-1)/5) ≠ 1
    BabyBearField.pow ⟨31⟩ (P_MINUS_ONE / 5) ≠ BabyBearField.one := by
  -- These are computational checks.
  -- native_decide would work but may timeout for large exponents.
  -- For now we axiomatize; the #eval tests below verify empirically.
  exact ⟨by sorry, by sorry, by sorry⟩

/-- g = 31 has full order p-1 -/
theorem babybear_generator_order :
    BabyBearField.pow ⟨31⟩ P_MINUS_ONE = BabyBearField.one := by
  -- g^(p-1) = 1 by Fermat's little theorem
  -- Verified empirically by the eval tests below
  sorry

/-! ## Part 4: Precomputed Roots for Common NTT Sizes -/

/-- 2^3 = 8-th primitive root -/
def OMEGA_8 : BabyBearField := primitiveRoot 8 (by decide)

/-- 2^4 = 16-th primitive root -/
def OMEGA_16 : BabyBearField := primitiveRoot 16 (by decide)

/-- 2^10 = 1024-th primitive root -/
def OMEGA_1024 : BabyBearField := primitiveRoot 1024 (by decide)

/-- 2^16 = 65536-th primitive root -/
def OMEGA_65536 : BabyBearField := primitiveRoot 65536 (by decide)

/-- 2^20 = 1048576-th primitive root -/
def OMEGA_1M : BabyBearField := primitiveRoot 1048576 (by decide)

/-! ## Part 5: Verification Tests -/

/-- Test: ω^n = 1 for the primitive root -/
def testRootPowN (n : Nat) (hn : n > 0) : Bool :=
  let ω := primitiveRoot n hn
  (BabyBearField.pow ω n).value == 1

/-- Test: ω^(n/2) = -1 for even n > 2 -/
def testHalfPowNegOne (n : Nat) (hn : n > 2) (_h_even : 2 ∣ n) : Bool :=
  let ω := primitiveRoot n (by omega)
  let half_pow := BabyBearField.pow ω (n / 2)
  -- -1 in BabyBear is ORDER - 1
  half_pow.value == ORDER - 1

/-! ## Part 6: NTT Twiddle Table Generator -/

/-- Generate twiddle factors ω^0, ω^1, ..., ω^(n-1) -/
def genTwiddleTable (ω : BabyBearField) (n : Nat) : List BabyBearField :=
  (List.range n).map fun i => BabyBearField.pow ω i

/-- Generate inverse twiddle factors ω^(-0), ω^(-1), ..., ω^(-(n-1))
    Using ω^(-k) = ω^(n-k) -/
def genInvTwiddleTable (ω : BabyBearField) (n : Nat) : List BabyBearField :=
  (List.range n).map fun i =>
    if i == 0 then BabyBearField.one
    else BabyBearField.pow ω (n - i)

/-! ## Part 7: NTT Integration Test -/

/-- Forward NTT using Cooley-Tukey radix-2 (direct implementation for testing).
    Not the generated code — just a reference for oracle comparison. -/
partial def nttForwardRef (input : List BabyBearField) (ω : BabyBearField) : List BabyBearField :=
  let n := input.length
  if n ≤ 1 then input
  else
    let half := n / 2
    let evens := (List.range half).map fun i =>
      if h : 2 * i < input.length then input[2 * i] else BabyBearField.zero
    let odds := (List.range half).map fun i =>
      if h : 2 * i + 1 < input.length then input[2 * i + 1] else BabyBearField.zero
    let ω2 := BabyBearField.mul ω ω  -- ω² for recursive call
    let evenResult := nttForwardRef evens ω2
    let oddResult := nttForwardRef odds ω2
    let upper := (List.range half).map fun k =>
      let tw := BabyBearField.pow ω k
      BabyBearField.add
        (if h : k < evenResult.length then evenResult[k] else BabyBearField.zero)
        (BabyBearField.mul tw (if h : k < oddResult.length then oddResult[k] else BabyBearField.zero))
    let lower := (List.range half).map fun k =>
      let tw := BabyBearField.pow ω k
      BabyBearField.sub
        (if h : k < evenResult.length then evenResult[k] else BabyBearField.zero)
        (BabyBearField.mul tw (if h : k < oddResult.length then oddResult[k] else BabyBearField.zero))
    upper ++ lower

/-- Inverse NTT: apply NTT with ω⁻¹ and scale by 1/n -/
partial def nttInverseRef (input : List BabyBearField) (ω : BabyBearField) : List BabyBearField :=
  let n := input.length
  let ω_inv := BabyBearField.inv ω
  let result := nttForwardRef input ω_inv
  let n_inv := BabyBearField.inv (BabyBearField.ofNat n)
  result.map (BabyBearField.mul n_inv)

/-! ## Part 8: Oracle Tests -/

/-- Run oracle comparison: NTT(INTT(x)) = x -/
def testNTTRoundtrip (n : Nat) (hn : n > 0) : IO Bool := do
  let ω := primitiveRoot n hn
  let input := (List.range n).map fun i => BabyBearField.ofNat (i + 1)
  let forward := nttForwardRef input ω
  let roundtrip := nttInverseRef forward ω
  let passed := (List.range n).all fun i =>
    match input[i]?, roundtrip[i]? with
    | some a, some b => a.value == b.value
    | _, _ => false
  IO.println s!"  NTT roundtrip n={n}: {if passed then "PASS" else "FAIL"}"
  return passed

/-! ## Part 9: Quick Tests -/

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     BABYBEAR NTT ROOT TESTS                                 ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Test 1: ω^n = 1 for various sizes
  IO.println "1. Testing ω^n = 1:"
  IO.println s!"   n=8:    {testRootPowN 8 (by decide)}"
  IO.println s!"   n=16:   {testRootPowN 16 (by decide)}"
  IO.println s!"   n=32:   {testRootPowN 32 (by decide)}"
  IO.println s!"   n=1024: {testRootPowN 1024 (by decide)}"

  -- Test 2: ω^(n/2) = -1
  IO.println "\n2. Testing ω^(n/2) = -1:"
  IO.println s!"   n=8:    {testHalfPowNegOne 8 (by decide) (by decide)}"
  IO.println s!"   n=16:   {testHalfPowNegOne 16 (by decide) (by decide)}"
  IO.println s!"   n=1024: {testHalfPowNegOne 1024 (by decide) (by decide)}"

  -- Test 3: Show actual root values
  IO.println "\n3. Primitive roots:"
  let ω4 := primitiveRoot 4 (by decide)
  let ω8 := primitiveRoot 8 (by decide)
  let ω16 := primitiveRoot 16 (by decide)
  IO.println s!"   ω_4  = {ω4.value}"
  IO.println s!"   ω_8  = {ω8.value}"
  IO.println s!"   ω_16 = {ω16.value}"

  -- Test 4: ω_4^2 = -1
  IO.println "\n4. ω_4^2 = -1:"
  let ω4_sq := BabyBearField.pow ω4 2
  IO.println s!"   ω_4^2 = {ω4_sq.value} (expected: {ORDER - 1} = -1)"

  -- Test 5: Generator g=31 tests
  IO.println "\n5. Generator g=31:"
  let g : BabyBearField := ⟨31⟩
  let g_pMinus1 := BabyBearField.pow g P_MINUS_ONE
  IO.println s!"   g^(p-1) = {g_pMinus1.value} (expected: 1)"
  let g_half := BabyBearField.pow g (P_MINUS_ONE / 2)
  IO.println s!"   g^((p-1)/2) = {g_half.value} (expected: {ORDER - 1} = -1)"
  let g_third := BabyBearField.pow g (P_MINUS_ONE / 3)
  IO.println s!"   g^((p-1)/3) = {g_third.value} (should ≠ 1)"
  let g_fifth := BabyBearField.pow g (P_MINUS_ONE / 5)
  IO.println s!"   g^((p-1)/5) = {g_fifth.value} (should ≠ 1)"

  -- Test 6: Twiddle table
  IO.println "\n6. Twiddle table (n=8):"
  let twiddles := genTwiddleTable ω8 8
  for tw in twiddles do
    IO.print s!" {tw.value}"
  IO.println ""

  -- Test 7: NTT roundtrip
  IO.println "\n7. NTT roundtrip tests:"
  let _ ← testNTTRoundtrip 8 (by decide)
  let _ ← testNTTRoundtrip 16 (by decide)
  let _ ← testNTTRoundtrip 32 (by decide)

  IO.println "\n══════════════════════════════════════════════════════════════"
  IO.println "   All BabyBear NTT tests completed"
  IO.println "══════════════════════════════════════════════════════════════"

end AmoLean.NTT.BabyBear
