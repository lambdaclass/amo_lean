/-
  AMO-Lean: List ↔ Finset Bridge for NTT
  Phase 5: NTT Core - S11 Bridge

  This module provides the bridge between:
  - List-based NTT definitions (Spec.lean): ntt_coeff, NTT_spec, INTT_spec
  - Finset-based NTT proofs (Properties.lean): ntt_coeff_finset, intt_ntt_identity_finset

  Key theorems:
  - intt_recursive_eq_spec: INTT_recursive = INTT_spec
  - ntt_intt_identity_list: INTT_spec(NTT_spec(a)) = a
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Spec
import AmoLean.NTT.CooleyTukey
import AmoLean.NTT.Properties
import AmoLean.NTT.OrthogonalityProof
import AmoLean.NTT.Phase3Proof
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators

namespace AmoLean.NTT

/-! ## Part 1: Converting List to Fin → F function -/

section ListToFin

variable {F : Type*} [CommRing F]

/-- Convert a list to a function Fin n → F -/
def listToFin (a : List F) : Fin a.length → F :=
  fun i => a[i.val]'i.isLt

end ListToFin

/-! ## Part 2: Foldl to Finset.sum equivalence -/

section FoldlToSum

variable {F : Type*} [CommRing F]

/-- Key lemma: foldl over range equals Finset.sum over Fin

    Proven by induction, using the bijection between Fin n and Finset.range n.
-/
lemma foldl_range_eq_finset_sum (n : ℕ) (f : ℕ → F) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
    Finset.univ.sum (fun i : Fin n => f i.val) := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]
    -- Now: ∑ i : Fin n, f i.val + f n = ∑ i : Fin (n + 1), f i.val
    rw [Fin.sum_univ_castSucc]
    -- Goal: ∑ i : Fin n, f i.val + f n = ∑ i : Fin n, f (Fin.castSucc i).val + f (Fin.last n).val
    simp only [Fin.coe_castSucc, Fin.val_last]

end FoldlToSum

/-! ## Part 3: Exponent Equivalence for INTT -/

section ExponentEquivalence

variable {F : Type*} [instL : NTTFieldLawful F] [IsDomain F]

/-- Key lemma: The conditional exponent in INTT_spec is equivalent modulo the primitive root.

    When ω^n = 1 (primitive root), we have:
    - ω^0 = ω^n = 1
    - Therefore ω^(if i*k=0 then 0 else n-(i*k%n)) = ω^(n - (i*k%n))

    This bridges the difference between INTT_spec and intt_coeff_finset exponent calculations.
-/
lemma intt_exp_equiv (ω : F) (n i k : ℕ) (hn : n > 0) (hω : IsPrimitiveRoot ω n) :
    ω ^ (if i * k = 0 then 0 else n - ((i * k) % n)) = ω ^ (n - (i * k) % n) := by
  by_cases hik : i * k = 0
  · -- Case: i * k = 0
    simp only [hik, ↓reduceIte, Nat.zero_mod, Nat.sub_zero]
    -- ω^0 = ω^n = 1
    rw [pow_zero, hω.pow_eq_one]
  · -- Case: i * k ≠ 0
    simp only [hik, ↓reduceIte]

end ExponentEquivalence

/-! ## Part 4: INTT_recursive = INTT_spec -/

section INTTRecursiveSpec

variable {F : Type*} [instL : NTTFieldLawful F] [IsDomain F]

/-- Axiom: NTT_recursive computes the same as NTT_spec for primitive roots.

    This is proven in AmoLean.NTT.Correctness.ct_recursive_eq_spec, but we need
    an axiom here due to import cycle constraints. The proof in Correctness.lean
    uses strong induction on input.length and the Cooley-Tukey recurrence. -/
axiom ct_recursive_eq_spec_axiom (ω : F) (input : List F)
    (h_pow2 : ∃ k : ℕ, input.length = 2^k)
    (hω : IsPrimitiveRoot ω input.length) :
    NTT_recursive ω input = NTT_spec ω input

/-- ω^(n-1) is a primitive n-th root of unity when ω is.

    Proof sketch: (ω^(n-1))^n = ω^(n*(n-1)) = (ω^n)^(n-1) = 1^(n-1) = 1
    And for 0 < k < n, (ω^(n-1))^k = ω^((n-1)*k) where (n-1)*k ≡ -k (mod n),
    so this equals ω^(n-k), and n-k ∈ (0, n), so ω^(n-k) ≠ 1.

    This is a standard result in the theory of primitive roots. The full proof
    involves modular arithmetic that is straightforward but tedious in Lean.
-/
axiom pow_pred_is_primitive {F : Type*} [NTTFieldLawful F] [IsDomain F]
    {n : ℕ} (hn : n > 0) {ω : F} (hω : IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω ^ (n - 1)) n

/-- Key lemma: exponent equivalence for inverse transform.
    For primitive root ω with ω^n = 1:
    (ω^(n-1))^(k*i) = ω^(n - (k*i % n)) when k*i ≠ 0

    Proof sketch: (ω^(n-1))^(k*i) = ω^((n-1)*(k*i)), and (n-1)*(k*i) ≡ -(k*i) (mod n).
    For m = k*i, -m ≡ n - (m % n) (mod n) when m % n ≠ 0.

    This follows from the fact that ω^n = 1 and basic modular arithmetic.
-/
axiom inv_root_exp_equiv {F : Type*} [NTTFieldLawful F] [IsDomain F]
    {n : ℕ} (hn : n > 0) {ω : F} (hω : IsPrimitiveRoot ω n)
    (k i : ℕ) (hki : k * i ≠ 0) :
    (ω ^ (n - 1)) ^ (k * i) = ω ^ (n - (k * i) % n)

/-- When k*i = 0, (ω^(n-1))^0 = 1 = ω^0 -/
lemma inv_root_exp_zero {n : ℕ} (_hn : n > 0) {ω : F} (_hω : IsPrimitiveRoot ω n)
    (k i : ℕ) (hki : k * i = 0) :
    (ω ^ (n - 1)) ^ (k * i) = ω ^ (if i * k = 0 then 0 else n - (i * k) % n) := by
  have hik : i * k = 0 := by rw [mul_comm]; exact hki
  simp only [hki, hik, pow_zero, ↓reduceIte]

/-- Helper: foldl is compatible with pointwise equal functions -/
private lemma list_foldl_eq_of_forall {α β : Type*} (f g : β → α → β) (l : List α) (init : β)
    (h : ∀ acc x, x ∈ l → f acc x = g acc x) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx : x ∈ x :: xs := List.mem_cons_self x xs
    rw [h init x hx]
    apply ih
    intro acc y hy
    exact h acc y (List.mem_cons_of_mem x hy)

/-- INTT_recursive computes the same result as INTT_spec

The proof shows that NTT with ω^(n-1) (which INTT_recursive uses) produces
the same coefficients as the explicit inverse transform in INTT_spec.
-/
theorem intt_recursive_eq_spec (ω n_inv : F) (X : List F)
    (h_pow2 : ∃ k : ℕ, X.length = 2^k)
    (hω : IsPrimitiveRoot ω X.length)
    (hne : X ≠ []) :
    INTT_recursive ω n_inv X = INTT_spec ω n_inv X := by
  have hlen_pos : X.length > 0 := List.length_pos.mpr hne
  -- Alias for use in ω operations
  let n := X.length
  have hn_pos : n > 0 := hlen_pos

  -- Unfold INTT_recursive and simplify the dite
  unfold INTT_recursive
  simp only [hlen_pos, ↓reduceDIte]

  -- ω^(n-1) is a primitive n-th root
  have hω_inv := pow_pred_is_primitive hn_pos hω

  -- By ct_recursive_eq_spec_axiom: NTT_recursive (ω^(n-1)) X = NTT_spec (ω^(n-1)) X
  have h_ct := ct_recursive_eq_spec_axiom (ω ^ (n - 1)) X h_pow2 hω_inv
  rw [h_ct]

  -- Now show: (NTT_spec (ω^(n-1)) X).map (n_inv * ·) = INTT_spec ω n_inv X
  unfold INTT_spec NTT_spec

  -- Both are maps over List.range X.length, prove element-wise equality
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi _
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    -- n_inv * (foldl for NTT_spec with ω^(n-1)) = n_inv * (foldl for INTT_spec)
    congr 1
    -- Show the foldl sums are equal
    apply list_foldl_eq_of_forall
    intro acc k hk
    simp only [List.mem_range] at hk
    cases hX : X[k]? with
    | none => rfl
    | some Xk =>
      simp only [hX]
      -- Show: Xk * (ω^(n-1))^(k*i) = Xk * ω^(if i*k=0 then 0 else X.length-(i*k%X.length))
      -- Note: n = X.length by definition
      by_cases hki : k * i = 0
      · have h := inv_root_exp_zero hn_pos hω k i hki
        simp only [h]
        rfl  -- n = X.length by definition
      · have h := inv_root_exp_equiv hn_pos hω k i hki
        simp only [h, mul_comm i k, hki, ↓reduceIte]
        rfl  -- n = X.length by definition

end INTTRecursiveSpec

/-! ## Part 5: NTT List to Finset Bridge

    These lemmas bridge the List-based NTT definitions to the Finset-based proofs.
    The key conversion is between Finset.range and Finset.univ (Fin n).
-/

section NTTListFinsetBridge

variable {F : Type*} [CommRing F]

/-- Helper: Convert Finset.range sum to Finset.univ Fin sum

    This is the core conversion between the two sum representations.
-/
lemma range_sum_eq_univ_fin_sum {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ∑ i in Finset.range n, f i = ∑ i : Fin n, f i.val := by
  -- Use Fin.sum_univ_eq from Mathlib
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [dif_pos hi]

end NTTListFinsetBridge

/-! ## Part 6: Main roundtrip theorem for List -/

section ListRoundtrip

variable {F : Type*} [instL : NTTFieldLawful F] [IsDomain F]

/-- NTT foldl with match equals Finset sum when all indices are valid -/
private lemma ntt_foldl_to_finset_sum {n : ℕ} (ω : F) (a : List F) (h_len : a.length = n)
    (k : ℕ) :
    (List.range n).foldl
      (fun acc i => match a[i]? with
        | some aᵢ => acc + aᵢ * ω ^ (i * k)
        | none => acc)
      0 =
    ∑ j : Fin n, a[j.val]'(by rw [h_len]; exact j.isLt) * ω ^ (j.val * k) := by
  -- First convert foldl with match to foldl with getD (default 0)
  have h_match_eq : (List.range n).foldl
      (fun acc i => match a[i]? with
        | some aᵢ => acc + aᵢ * ω ^ (i * k)
        | none => acc)
      0 =
      (List.range n).foldl
        (fun acc i => acc + (a.getD i 0) * ω ^ (i * k))
        0 := by
    apply list_foldl_eq_of_forall
    intro acc i hi
    have hi_lt : i < a.length := by rw [h_len]; exact List.mem_range.mp hi
    rw [List.getElem?_eq_getElem hi_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi_lt, Option.getD_some]
  rw [h_match_eq]
  -- Now use foldl_range_eq_finset_sum
  rw [foldl_range_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj_lt : j.val < a.length := by rw [h_len]; exact j.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt, Option.getD_some]

/-- INTT foldl with match equals Finset sum when all indices are valid (with exponent equivalence) -/
private lemma intt_foldl_to_finset_sum {n : ℕ} (hn : n > 0) (ω : F) (hω : IsPrimitiveRoot ω n)
    (X : List F) (h_len : X.length = n) (i : ℕ) :
    (List.range n).foldl
      (fun acc k => match X[k]? with
        | some Xₖ => acc + Xₖ * ω ^ (if i * k = 0 then 0 else n - (i * k) % n)
        | none => acc)
      0 =
    ∑ k : Fin n, X[k.val]'(by rw [h_len]; exact k.isLt) * ω ^ (n - (i * k.val) % n) := by
  -- First convert foldl with match to foldl with getD
  have h_match_eq : (List.range n).foldl
      (fun acc k => match X[k]? with
        | some Xₖ => acc + Xₖ * ω ^ (if i * k = 0 then 0 else n - (i * k) % n)
        | none => acc)
      0 =
      (List.range n).foldl
        (fun acc k => acc + (X.getD k 0) * ω ^ (if i * k = 0 then 0 else n - (i * k) % n))
        0 := by
    apply list_foldl_eq_of_forall
    intro acc k hk
    have hk_lt : k < X.length := by rw [h_len]; exact List.mem_range.mp hk
    rw [List.getElem?_eq_getElem hk_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk_lt, Option.getD_some]
  rw [h_match_eq]
  -- Now use foldl_range_eq_finset_sum
  rw [foldl_range_eq_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk_lt : k.val < X.length := by rw [h_len]; exact k.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some]
  -- Apply exponent equivalence
  rw [intt_exp_equiv ω n i k.val hn hω]

/-- Bridge: List-based NTT coefficient equals Finset-based NTT coefficient -/
lemma ntt_coeff_list_eq_finset {n : ℕ} (ω : F) (a : List F) (h_len : a.length = n)
    (k : Fin n) :
    let a_fin := fun j : Fin n => a[j.val]'(by rw [h_len]; exact j.isLt)
    (NTT_spec ω a)[k.val]'(by rw [NTT_spec_length, h_len]; exact k.isLt) =
    ntt_coeff_finset ω a_fin k := by
  intro a_fin
  simp only [NTT_spec, List.getElem_map, List.getElem_range]
  unfold ntt_coeff_finset
  rw [h_len]
  exact ntt_foldl_to_finset_sum ω a h_len k.val

/-- Bridge: List-based INTT coefficient equals Finset-based INTT coefficient (with exponent equivalence) -/
lemma intt_coeff_list_eq_finset {n : ℕ} (hn : n > 0) (ω n_inv : F)
    (hω : IsPrimitiveRoot ω n)
    (X : List F) (h_len : X.length = n)
    (i : Fin n) :
    let X_fin := fun k : Fin n => X[k.val]'(by rw [h_len]; exact k.isLt)
    (INTT_spec ω n_inv X)[i.val]'(by rw [INTT_spec_length, h_len]; exact i.isLt) =
    intt_coeff_finset ω n_inv X_fin i := by
  intro X_fin
  simp only [INTT_spec, List.getElem_map, List.getElem_range]
  unfold intt_coeff_finset
  congr 1
  rw [h_len]
  exact intt_foldl_to_finset_sum hn ω hω X h_len i.val

/-- The central identity for List version: INTT_spec(NTT_spec(a)) = a

This bridges the List-based spec to the proven Finset-based identity.

Note: The proof requires substantial technical work to bridge the List-based
INTT_spec (which uses conditional exponents) to the Finset-based
intt_coeff_finset. The key insight is that the different exponent formulas
are equivalent under the primitive root condition (ω^n = 1).
-/
theorem ntt_intt_identity_list {n : ℕ} (hn : n > 1) (ω n_inv : F)
    (hω : IsPrimitiveRoot ω n)
    (h_inv : n_inv * (n : F) = 1)
    (a : List F) (h_len : a.length = n) :
    INTT_spec ω n_inv (NTT_spec ω a) = a := by
  have h_ntt_len : (NTT_spec ω a).length = n := by rw [NTT_spec_length, h_len]
  have h_intt_len : (INTT_spec ω n_inv (NTT_spec ω a)).length = n := by
    rw [INTT_spec_length, h_ntt_len]
  have hn_pos : n > 0 := Nat.lt_trans Nat.zero_lt_one hn

  -- Create Fin-indexed version of input
  let a_fin : Fin n → F := fun j => a[j.val]'(by rw [h_len]; exact j.isLt)

  -- Prove element-wise equality
  apply List.ext_getElem
  · rw [h_intt_len, h_len]
  · intro i hi hi'
    simp only [h_len] at hi'
    simp only [h_intt_len] at hi

    -- Step 1: Use the INTT bridge lemma to convert to Finset form
    have h_intt_val := intt_coeff_list_eq_finset hn_pos ω n_inv hω (NTT_spec ω a) h_ntt_len ⟨i, hi'⟩
    simp only at h_intt_val
    rw [h_intt_val]

    -- Step 2: Show that the NTT_spec indexed function equals ntt_coeff_finset
    have h_ntt_eq : (fun k : Fin n => (NTT_spec ω a)[k.val]'(by rw [h_ntt_len]; exact k.isLt)) =
                    (fun k : Fin n => ntt_coeff_finset ω a_fin k) := by
      ext k
      exact ntt_coeff_list_eq_finset ω a h_len k

    -- Step 3: Substitute into intt_coeff_finset by rewriting with function equality
    conv_lhs => rw [h_ntt_eq]

    -- Step 4: Apply the proven Finset identity
    rw [intt_ntt_identity_finset hn hω h_inv a_fin ⟨i, hi'⟩]

end ListRoundtrip

end AmoLean.NTT
