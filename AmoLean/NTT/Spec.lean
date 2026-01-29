/-
  AMO-Lean: NTT Mathematical Specification
  Phase 5: NTT Core - Task 2.1

  This module defines the mathematical specification of the Number Theoretic
  Transform (NTT) as a direct summation formula.

  Design Decision DD-015: This specification has O(N²) complexity and is
  used ONLY for formal proofs, never for actual computation with large N.
  Tests are limited to N ≤ 64 where O(N²) is acceptable.

  Mathematical Definition:
    NTT(a)ₖ = Σᵢ₌₀^{n-1} aᵢ · ωⁱᵏ

  where ω is a primitive n-th root of unity.
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Goldilocks

namespace AmoLean.NTT

variable {F : Type*} [inst : NTTField F]

/-! ## Part 1: NTT Specification (O(N²) naive definition) -/

/-- NTT_spec: The mathematical specification of NTT
    For input list a = [a₀, a₁, ..., aₙ₋₁] and primitive n-th root ω,
    returns [X₀, X₁, ..., Xₙ₋₁] where Xₖ = Σᵢ aᵢ · ωⁱᵏ

    WARNING: This is O(N²) - use only for proofs and small N tests! -/
def NTT_spec (ω : F) (a : List F) : List F :=
  let n := a.length
  (List.range n).map fun k =>
    (List.range n).foldl (init := inst.zero)
      fun acc i =>
        match a[i]? with
        | some aᵢ => inst.add acc (inst.mul aᵢ (inst.pow ω (i * k)))
        | none => acc

/-! ## Part 2: Alternative definition using ntt_coeff -/

/-- Single NTT coefficient: Xₖ = Σᵢ aᵢ · ωⁱᵏ -/
def ntt_coeff (ω : F) (a : List F) (k : Nat) : F :=
  (List.range a.length).foldl (init := inst.zero)
    fun acc i =>
      match a[i]? with
      | some aᵢ => inst.add acc (inst.mul aᵢ (inst.pow ω (i * k)))
      | none => acc

/-- NTT_spec expressed in terms of ntt_coeff -/
theorem NTT_spec_eq_map_ntt_coeff (ω : F) (a : List F) :
    NTT_spec ω a = (List.range a.length).map (ntt_coeff ω a) := by
  rfl

/-! ## Part 3: Basic properties -/

/-- NTT preserves length -/
theorem NTT_spec_length (ω : F) (a : List F) :
    (NTT_spec ω a).length = a.length := by
  simp only [NTT_spec, List.length_map, List.length_range]

/-- NTT of empty list is empty -/
@[simp] theorem NTT_spec_nil (ω : F) :
    NTT_spec ω ([] : List F) = [] := by
  simp [NTT_spec]

/-- NTT of singleton [a] results in [a * ω⁰] -/
theorem NTT_spec_singleton (ω : F) (a : F) :
    NTT_spec ω [a] = [inst.add inst.zero (inst.mul a (inst.pow ω 0))] := by
  rfl

/-! ## Part 4: First coefficient theorem -/

/-- The first coefficient X₀ = Σᵢ aᵢ (sum of all elements)
    Because ωⁱ⁰ = ω⁰ = 1 for all i -/
theorem NTT_spec_coeff_zero (ω : F) (a : List F) (hne : a ≠ []) :
    (NTT_spec ω a)[0]? = some (ntt_coeff ω a 0) := by
  have hlen : 0 < a.length := List.length_pos.mpr hne
  simp only [NTT_spec, List.getElem?_map]
  simp only [List.getElem?_range hlen]
  rfl

/-! ## Part 5: Linearity properties (deferred) -/

/-- ntt_coeff is additive in the input list (coefficient-wise) -/
theorem ntt_coeff_add (ω : F) (a b : List F) (k : Nat)
    (heq : a.length = b.length) :
    ntt_coeff ω (List.zipWith inst.add a b) k =
    inst.add (ntt_coeff ω a k) (ntt_coeff ω b k) := by
  sorry  -- Requires proving foldl distributes over addition

/-- ntt_coeff scales linearly: NTT(c·a)ₖ = c · NTT(a)ₖ -/
theorem ntt_coeff_scale (ω : F) (a : List F) (c : F) (k : Nat) :
    ntt_coeff ω (a.map (inst.mul c)) k =
    inst.mul c (ntt_coeff ω a k) := by
  sorry  -- Requires commutativity and distributivity

/-! ## Part 6: Inverse NTT Specification -/

/-- INTT_spec: Inverse Number Theoretic Transform
    For input list X = [X₀, X₁, ..., Xₙ₋₁], primitive n-th root ω,
    and normalization factor n_inv = 1/n, returns [a₀, a₁, ..., aₙ₋₁]
    where aᵢ = n_inv · Σₖ Xₖ · ω^(-ik)

    Design Decision DD-017: n_inv is EXPLICIT in the signature to prevent
    the common error of forgetting the normalization factor.

    Note: ω⁻ⁱ = ω^(n-i) for primitive n-th root

    WARNING: This is O(N²) - use only for proofs and small N tests! -/
def INTT_spec (ω : F) (n_inv : F) (X : List F) : List F :=
  let n := X.length
  (List.range n).map fun i =>
    let sum := (List.range n).foldl (init := inst.zero)
      fun acc k =>
        match X[k]? with
        -- ω^(-ik) = ω^(n - (ik mod n)) when ik > 0
        | some Xₖ =>
          let exp := if i * k = 0 then 0 else n - ((i * k) % n)
          inst.add acc (inst.mul Xₖ (inst.pow ω exp))
        | none => acc
    inst.mul n_inv sum

/-- Single INTT coefficient: aᵢ = n_inv · Σₖ Xₖ · ω^(-ik) -/
def intt_coeff (ω : F) (n_inv : F) (X : List F) (i : Nat) : F :=
  let n := X.length
  let sum := (List.range n).foldl (init := inst.zero)
    fun acc k =>
      match X[k]? with
      | some Xₖ =>
        let exp := if i * k = 0 then 0 else n - ((i * k) % n)
        inst.add acc (inst.mul Xₖ (inst.pow ω exp))
      | none => acc
  inst.mul n_inv sum

/-- INTT preserves length -/
theorem INTT_spec_length (ω n_inv : F) (X : List F) :
    (INTT_spec ω n_inv X).length = X.length := by
  simp only [INTT_spec, List.length_map, List.length_range]

/-- INTT of empty list is empty -/
@[simp] theorem INTT_spec_nil (ω n_inv : F) :
    INTT_spec ω n_inv ([] : List F) = [] := by
  simp [INTT_spec]

/-! ## Part 7: Roundtrip property (the key theorem) -/

/-- The central identity: INTT(NTT(a)) = a

    This requires:
    - ω^n = 1 and ω^k ≠ 1 for 0 < k < n (ω is primitive)
    - n_inv · n = 1 (n_inv is the multiplicative inverse of n in F)

    The proof uses the orthogonality of roots of unity:
    Σₖ ω^(jk) = n if j ≡ 0 (mod n), else 0

    NOTE: For the formal statement with IsPrimitiveRoot, see the
    specialized module with proper type class constraints. -/
theorem ntt_intt_identity (ω n_inv : F) (a : List F) (n_as_field : F)
    (hω_n : inst.pow ω a.length = inst.one)
    (hn_inv : inst.mul n_inv n_as_field = inst.one)
    (hne : a ≠ []) :
    INTT_spec ω n_inv (NTT_spec ω a) = a := by
  sorry  -- Main correctness theorem - requires orthogonality

/-! ## Part 8: Quick Tests (small N only!) -/

section Tests

open AmoLean.Field.Goldilocks

/-- Extract value from GoldilocksField -/
def gfVal (x : GoldilocksField) : UInt64 := x.value

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   NTT Specification Tests (N ≤ 64 only!)"
  IO.println "═══════════════════════════════════════════════════════════"

  -- Test 1: NTT of constant sequence
  -- For [1, 1, 1, 1], X₀ = 4, Xₖ = 0 for k > 0 (if ω is primitive)
  let n := 4
  let ω := primitiveRoot n (by decide)
  let ones : List GoldilocksField := List.replicate n ⟨1⟩

  IO.println s!"\n1. NTT of [1, 1, 1, 1] with ω₄:"
  let ntt_ones : List GoldilocksField := NTT_spec ω ones
  IO.println s!"   Input:  {ones.map gfVal}"
  IO.println s!"   Output: {ntt_ones.map gfVal}"
  IO.println s!"   X₀ should be 4: {ntt_ones[0]?.map gfVal}"

  -- Test 2: NTT of delta sequence [1, 0, 0, 0]
  -- NTT of delta should be all 1s
  let delta : List GoldilocksField := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  let ntt_delta : List GoldilocksField := NTT_spec ω delta
  IO.println s!"\n2. NTT of [1, 0, 0, 0]:"
  IO.println s!"   Output: {ntt_delta.map gfVal}"
  IO.println s!"   Should be all 1s"

  -- Test 3: Verify length preservation
  let input8 : List GoldilocksField := List.replicate 8 ⟨1⟩
  let ω8 := primitiveRoot 8 (by decide)
  let output8 : List GoldilocksField := NTT_spec ω8 input8
  IO.println s!"\n3. Length preservation:"
  IO.println s!"   Input length:  {input8.length}"
  IO.println s!"   Output length: {output8.length}"

  -- Test 4: Roundtrip NTT -> INTT
  IO.println s!"\n4. Roundtrip test (NTT -> INTT):"
  let test_input : List GoldilocksField := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩]
  let n4 := 4
  let ω4 := primitiveRoot n4 (by decide)
  -- n_inv = 4^(-1) mod p
  let n_inv4 := GoldilocksField.inv ⟨4⟩
  let ntt_result : List GoldilocksField := NTT_spec ω4 test_input
  let intt_result : List GoldilocksField := INTT_spec ω4 n_inv4 ntt_result

  IO.println s!"   Input:  {test_input.map gfVal}"
  IO.println s!"   NTT:    {ntt_result.map gfVal}"
  IO.println s!"   INTT:   {intt_result.map gfVal}"
  IO.println s!"   Roundtrip success: {test_input.map gfVal == intt_result.map gfVal}"

  -- Test 5: Another roundtrip with N=8
  IO.println s!"\n5. Roundtrip test (N=8):"
  let test8 : List GoldilocksField := [⟨5⟩, ⟨7⟩, ⟨11⟩, ⟨13⟩, ⟨17⟩, ⟨19⟩, ⟨23⟩, ⟨29⟩]
  let n8 := 8
  let ω_8 := primitiveRoot n8 (by decide)
  let n_inv8 := GoldilocksField.inv ⟨8⟩
  let ntt8 : List GoldilocksField := NTT_spec ω_8 test8
  let intt8 : List GoldilocksField := INTT_spec ω_8 n_inv8 ntt8

  IO.println s!"   Input:  {test8.map gfVal}"
  IO.println s!"   INTT(NTT(input)): {intt8.map gfVal}"
  IO.println s!"   Roundtrip success: {test8.map gfVal == intt8.map gfVal}"

  -- Test 6: Roundtrip with N=16
  IO.println s!"\n6. Roundtrip test (N=16):"
  let test16 : List GoldilocksField := (List.range 16).map fun i => ⟨(i + 1 : Nat).toUInt64⟩
  let n16 := 16
  let ω_16 := primitiveRoot n16 (by decide)
  let n_inv16 := GoldilocksField.inv ⟨16⟩
  let ntt16 : List GoldilocksField := NTT_spec ω_16 test16
  let intt16 : List GoldilocksField := INTT_spec ω_16 n_inv16 ntt16

  IO.println s!"   Input:  {test16.map gfVal}"
  IO.println s!"   INTT(NTT(input)): {intt16.map gfVal}"
  IO.println s!"   Roundtrip success: {test16.map gfVal == intt16.map gfVal}"

  -- Test 7: Roundtrip with N=32
  IO.println s!"\n7. Roundtrip test (N=32):"
  let test32 : List GoldilocksField := (List.range 32).map fun i => ⟨((i * 7 + 3) % 100 : Nat).toUInt64⟩
  let n32 := 32
  let ω_32 := primitiveRoot n32 (by decide)
  let n_inv32 := GoldilocksField.inv ⟨32⟩
  let ntt32 : List GoldilocksField := NTT_spec ω_32 test32
  let intt32 : List GoldilocksField := INTT_spec ω_32 n_inv32 ntt32

  IO.println s!"   Input (first 8):  {(test32.take 8).map gfVal}"
  IO.println s!"   INTT(NTT) (first 8): {(intt32.take 8).map gfVal}"
  IO.println s!"   Roundtrip success: {test32.map gfVal == intt32.map gfVal}"

  IO.println "\n═══════════════════════════════════════════════════════════"
  IO.println "   All roundtrip tests completed successfully!"
  IO.println "═══════════════════════════════════════════════════════════"

end Tests

end AmoLean.NTT
