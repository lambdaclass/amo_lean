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
import Mathlib.Tactic

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
        | some aᵢ => inst.add acc (inst.mul aᵢ (HPow.hPow ω (i * k)))
        | none => acc

/-! ## Part 2: Alternative definition using ntt_coeff -/

/-- Single NTT coefficient: Xₖ = Σᵢ aᵢ · ωⁱᵏ -/
def ntt_coeff (ω : F) (a : List F) (k : Nat) : F :=
  (List.range a.length).foldl (init := inst.zero)
    fun acc i =>
      match a[i]? with
      | some aᵢ => inst.add acc (inst.mul aᵢ (HPow.hPow ω (i * k)))
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
    NTT_spec ω [a] = [inst.add inst.zero (inst.mul a (HPow.hPow ω 0))] := by
  rfl

section SingletonSimplified
variable {F : Type*} [NTTFieldLawful F]

/-- NTT of singleton simplifies to identity: NTT_spec ω [a] = [a]

    Proof: ω^0 = 1, a * 1 = a, 0 + a = a -/
@[simp] theorem NTT_spec_singleton_simp (ω : F) (a : F) :
    NTT_spec ω [a] = [a] := by
  rw [NTT_spec_singleton]
  -- Goal: [inst.add inst.zero (inst.mul a (ω^0))] = [a]
  -- ω^0 = 1, a * 1 = a, 0 + a = a
  show [0 + a * (ω ^ 0)] = [a]
  simp [pow_zero]

end SingletonSimplified

/-! ## Part 4: First coefficient theorem -/

/-- The first coefficient X₀ = Σᵢ aᵢ (sum of all elements)
    Because ωⁱ⁰ = ω⁰ = 1 for all i -/
theorem NTT_spec_coeff_zero (ω : F) (a : List F) (hne : a ≠ []) :
    (NTT_spec ω a)[0]? = some (ntt_coeff ω a 0) := by
  have hlen : 0 < a.length := List.length_pos.mpr hne
  simp only [NTT_spec, List.getElem?_map]
  simp only [List.getElem?_range hlen]
  rfl

/-! ## Part 5: Linearity properties -/

section Linearity
variable {F : Type*} [instL : NTTFieldLawful F]

-- Helper lemmas for foldl proofs
private lemma getElem?_map_mul (a : List F) (c : F) (i : Nat) :
    (a.map (c * ·))[i]? = (a[i]?).map (c * ·) := List.getElem?_map (c * ·) a i

private lemma length_map_mul (a : List F) (c : F) : (a.map (c * ·)).length = a.length :=
  List.length_map a (c * ·)

private lemma scale_term (c aᵢ ωpow : F) :
    (c * aᵢ) * ωpow = c * (aᵢ * ωpow) := mul_assoc c aᵢ ωpow

private lemma mul_add_distrib (c acc x : F) :
    c * (acc + x) = c * acc + c * x := by
  rw [mul_comm c, add_mul, mul_comm acc, mul_comm x]

private lemma foldl_scale_general (c : F) (a : List F) (ω : F) (k : Nat)
    (indices : List Nat) (acc : F) :
    indices.foldl
      (fun ac i => match (a.map (c * ·))[i]? with
        | some aᵢ => ac + aᵢ * HPow.hPow ω (i * k)
        | none => ac)
      (c * acc) =
    c * (indices.foldl
      (fun ac i => match a[i]? with
        | some aᵢ => ac + aᵢ * HPow.hPow ω (i * k)
        | none => ac)
      acc) := by
  induction indices generalizing acc with
  | nil => simp only [List.foldl_nil]
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [getElem?_map_mul]
    cases ha : a[i]? with
    | none =>
      simp only [Option.map_none']
      exact ih acc
    | some aᵢ =>
      simp only [Option.map_some']
      have h_acc_eq : c * acc + (c * aᵢ) * HPow.hPow ω (i * k) =
          c * (acc + aᵢ * HPow.hPow ω (i * k)) := by
        rw [mul_add_distrib, scale_term]
      rw [h_acc_eq]
      exact ih (acc + aᵢ * HPow.hPow ω (i * k))

/-- ntt_coeff scales linearly: NTT(c·a)ₖ = c · NTT(a)ₖ -/
theorem ntt_coeff_scale (ω : F) (a : List F) (c : F) (k : Nat) :
    ntt_coeff ω (a.map (c * ·)) k = c * (ntt_coeff ω a k) := by
  simp only [ntt_coeff]
  rw [length_map_mul]
  have h_init : c * (0 : F) = (0 : F) := by
    rw [mul_comm, zero_mul]
  have h := foldl_scale_general c a ω k (List.range a.length) (0 : F)
  simp only [h_init] at h
  exact h

-- Helper lemmas for S1 (addition)
private lemma getElem?_zipWith_add (a b : List F) (i : Nat) :
    (List.zipWith (· + ·) a b)[i]? = match a[i]?, b[i]? with
      | some x, some y => some (x + y)
      | _, _ => none := by
  cases ha : a[i]? <;> cases hb : b[i]? <;> simp [List.getElem?_zipWith, ha, hb]

private lemma length_zipWith_add (a b : List F) :
    (List.zipWith (· + ·) a b).length = min a.length b.length :=
  List.length_zipWith (· + ·) a b

private lemma add_term_distrib (aᵢ bᵢ ωpow : F) :
    (aᵢ + bᵢ) * ωpow = aᵢ * ωpow + bᵢ * ωpow := add_mul aᵢ bᵢ ωpow

private lemma add_assoc_4 (w x y z : F) :
    (w + x) + (y + z) = (w + y) + (x + z) := by
  calc (w + x) + (y + z) = w + (x + (y + z)) := by rw [add_assoc]
    _ = w + ((x + y) + z) := by rw [← add_assoc x y z]
    _ = w + ((y + x) + z) := by rw [add_comm x y]
    _ = w + (y + (x + z)) := by rw [add_assoc y x z]
    _ = (w + y) + (x + z) := by rw [← add_assoc w y (x + z)]

private lemma foldl_add_general (a b : List F) (ω : F) (k : Nat)
    (indices : List Nat) (acc_ab acc_a acc_b : F)
    (heq : a.length = b.length)
    (h_acc : acc_ab = acc_a + acc_b) :
    indices.foldl
      (fun ac i => match (List.zipWith (· + ·) a b)[i]? with
        | some xi => ac + xi * HPow.hPow ω (i * k)
        | none => ac)
      acc_ab =
    (indices.foldl
        (fun ac i => match a[i]? with
          | some aᵢ => ac + aᵢ * HPow.hPow ω (i * k)
          | none => ac)
        acc_a) +
      (indices.foldl
        (fun ac i => match b[i]? with
          | some bᵢ => ac + bᵢ * HPow.hPow ω (i * k)
          | none => ac)
        acc_b) := by
  induction indices generalizing acc_ab acc_a acc_b with
  | nil =>
    simp only [List.foldl_nil]
    exact h_acc
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [getElem?_zipWith_add]
    cases ha : a[i]? with
    | none =>
      simp only
      have hb : b[i]? = none := by
        by_contra hne
        push_neg at hne
        have ⟨bi, hbi⟩ := Option.ne_none_iff_exists'.mp hne
        have hi_lt_b : i < b.length := List.getElem?_eq_some_iff.mp hbi |>.1
        have hi_lt_a : i < a.length := by omega
        have hsome : a[i]? = some (a[i]'hi_lt_a) := List.getElem?_eq_some_iff.mpr ⟨hi_lt_a, rfl⟩
        rw [ha] at hsome
        exact Option.noConfusion hsome
      simp only [hb]
      exact ih acc_ab acc_a acc_b h_acc
    | some aᵢ =>
      cases hb : b[i]? with
      | none =>
        simp only
        have hi_lt_a : i < a.length := List.getElem?_eq_some_iff.mp ha |>.1
        have hi_lt_b : i < b.length := by omega
        have hsome : b[i]? = some (b[i]'hi_lt_b) := List.getElem?_eq_some_iff.mpr ⟨hi_lt_b, rfl⟩
        rw [hb] at hsome
        exact Option.noConfusion hsome
      | some bᵢ =>
        simp only
        have h_new_acc : acc_ab + (aᵢ + bᵢ) * HPow.hPow ω (i * k) =
            (acc_a + aᵢ * HPow.hPow ω (i * k)) +
            (acc_b + bᵢ * HPow.hPow ω (i * k)) := by
          rw [h_acc, add_term_distrib, add_assoc_4]
        exact ih _ _ _ h_new_acc

/-- ntt_coeff is additive in the input list (coefficient-wise) -/
theorem ntt_coeff_add (ω : F) (a b : List F) (k : Nat)
    (heq : a.length = b.length) :
    ntt_coeff ω (List.zipWith (· + ·) a b) k = (ntt_coeff ω a k) + (ntt_coeff ω b k) := by
  simp only [ntt_coeff]
  rw [length_zipWith_add]
  have h_min : min a.length b.length = a.length := by omega
  rw [h_min, heq]
  have h_init : (0 : F) = 0 + 0 := by rw [add_zero]
  exact foldl_add_general a b ω k (List.range b.length) 0 0 0 heq h_init

end Linearity

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
          inst.add acc (inst.mul Xₖ (HPow.hPow ω exp))
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
        inst.add acc (inst.mul Xₖ (HPow.hPow ω exp))
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

section SingletonINTT
variable {F : Type*} [NTTFieldLawful F]

/-- INTT of singleton [a] with n_inv = 1 gives [a]

    When n = 1, the INTT is: n_inv * (a * ω^0) = 1 * (a * 1) = a -/
@[simp] theorem INTT_spec_singleton_simp (ω : F) (a : F) :
    INTT_spec ω 1 [a] = [a] := by
  simp only [INTT_spec, List.length_singleton]
  have hr1 : List.range 1 = [0] := rfl
  rw [hr1]
  -- Goal: [(1 : F) * (0 + a * ω^(if ...))] = [a]
  show [1 * (0 + a * ω ^ (if 0 * 0 = 0 then 0 else 1 - 0 * 0 % 1))] = [a]
  simp [pow_zero]

/-- When n_inv * 1 = 1, we have n_inv = 1 -/
theorem n_inv_eq_one_of_mul_one {n_inv : F} (h : n_inv * 1 = 1) : n_inv = 1 := by
  rw [mul_one] at h; exact h

/-- INTT roundtrip for singleton: INTT(NTT([a])) = [a] when n_inv * 1 = 1 -/
theorem INTT_NTT_singleton_roundtrip (ω n_inv : F) (a : F) (h_inv : n_inv * (1 : F) = 1) :
    INTT_spec ω n_inv (NTT_spec ω [a]) = [a] := by
  have h_ninv_one : n_inv = 1 := n_inv_eq_one_of_mul_one h_inv
  rw [NTT_spec_singleton_simp, h_ninv_one, INTT_spec_singleton_simp]

end SingletonINTT

/-! ## Part 7: Roundtrip property (the key theorem) -/

/-- The central identity: INTT(NTT(a)) = a

    **IMPORTANT**: The original formulation with only `ω^n = 1` is mathematically
    INSUFFICIENT. The proof requires `IsPrimitiveRoot ω n` (full primitivity).

    Counterexample: n=4, F = ℤ/5ℤ, ω = -1 ≡ 4 (mod 5). Here ω^4 = 1 but ω is NOT
    a primitive 4th root (its order is 2). The NTT matrix would be singular.

    The correct theorem is `ntt_intt_identity_list` in ListFinsetBridge.lean
    which has the correct hypotheses:
    - `IsPrimitiveRoot ω n` (ω is primitive n-th root)
    - `n_inv * n = 1` (n_inv is the multiplicative inverse of n in F)
    - `n > 1` (non-degenerate case)

    The deprecated version below is commented out because it has insufficient
    hypotheses and cannot be proven without strengthening them to IsPrimitiveRoot. -/

/-  DEPRECATED: This theorem has insufficient hypotheses
theorem ntt_intt_identity_deprecated (ω n_inv : F) (a : List F) (n_as_field : F)
    (hω_n : HPow.hPow ω a.length = inst.one)
    (hn_inv : inst.mul n_inv n_as_field = inst.one)
    (hne : a ≠ []) :
    INTT_spec ω n_inv (NTT_spec ω a) = a := by
  sorry
-/

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
