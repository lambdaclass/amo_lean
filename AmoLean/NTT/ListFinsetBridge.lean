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

/-- Key lemma: foldl over range equals Finset.sum over Fin -/
lemma foldl_range_eq_finset_sum (n : ℕ) (f : ℕ → F) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
    Finset.univ.sum (fun i : Fin n => f i.val) := by
  -- Standard result: accumulating sum over range = Finset.sum over Fin
  sorry -- Reindexing proof

end FoldlToSum

/-! ## Part 3: INTT_recursive = INTT_spec -/

section INTTRecursiveSpec

variable {F : Type*} [instL : NTTFieldLawful F] [IsDomain F]

/-- INTT_recursive computes the same result as INTT_spec

The proof shows that NTT with ω^(n-1) (which INTT_recursive uses) produces
the same coefficients as the explicit inverse transform in INTT_spec.
-/
theorem intt_recursive_eq_spec (ω n_inv : F) (X : List F)
    (h_pow2 : ∃ k : ℕ, X.length = 2^k)
    (hω : IsPrimitiveRoot ω X.length)
    (hne : X ≠ []) :
    INTT_recursive ω n_inv X = INTT_spec ω n_inv X := by
  -- The key insight: ω^(n-1) = ω⁻¹ for primitive roots
  -- NTT_recursive(ω^(n-1), X) computes Σ_k X_k * (ω^(n-1))^(k*i) = Σ_k X_k * ω^(-k*i)
  -- which equals Σ_k X_k * ω^(n - k*i mod n) = INTT's inner sum
  sorry -- Computational equivalence proof

end INTTRecursiveSpec

/-! ## Part 4: Main roundtrip theorem for List -/

section ListRoundtrip

variable {F : Type*} [instL : NTTFieldLawful F] [IsDomain F]

/-- The central identity for List version: INTT_spec(NTT_spec(a)) = a

This bridges the List-based spec to the proven Finset-based identity.
-/
theorem ntt_intt_identity_list {n : ℕ} (hn : n > 1) (ω n_inv : F)
    (hω : IsPrimitiveRoot ω n)
    (h_inv : n_inv * (n : F) = 1)
    (a : List F) (h_len : a.length = n) :
    INTT_spec ω n_inv (NTT_spec ω a) = a := by
  -- The proof strategy:
  -- 1. Convert list operations to Finset sums
  -- 2. Apply intt_ntt_identity_finset
  -- 3. Convert back to list

  have h_ntt_len : (NTT_spec ω a).length = n := by rw [NTT_spec_length, h_len]
  have h_intt_len : (INTT_spec ω n_inv (NTT_spec ω a)).length = n := by
    rw [INTT_spec_length, h_ntt_len]
  have hn_pos : n > 0 := Nat.lt_trans Nat.zero_lt_one hn

  -- Create Fin-indexed versions
  let a_fin : Fin n → F := fun j => a[j.val]'(by rw [h_len]; exact j.isLt)

  -- Prove element-wise equality
  apply List.ext_getElem
  · rw [h_intt_len, h_len]
  · intro i hi hi'
    simp only [h_len] at hi'
    simp only [h_intt_len] at hi

    -- Use the proven Finset roundtrip theorem
    have h_finset := intt_ntt_identity_finset hn hω h_inv a_fin ⟨i, hi'⟩

    -- The INTT_spec element equals a_fin i = a[i]
    -- This requires showing the foldl computations match the Finset sums
    sorry -- Bridge from List.foldl to Finset.sum

end ListRoundtrip

end AmoLean.NTT
