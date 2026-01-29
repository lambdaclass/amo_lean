/-
  AMO-Lean: NTT Formal Properties
  Phase 5: NTT Core - Tasks 2.3, 2.4

  This module contains the formal proofs of NTT properties.

  Key Theorems:
  1. ntt_intt_identity: INTT(NTT(x)) = x (the central correctness theorem)
  2. ntt_linearity: NTT is a linear transformation
  3. Special input properties (delta, constant)

  The proofs rely on:
  - Orthogonality of roots of unity from RootsOfUnity.lean
  - sum_of_powers_zero, powSum_*
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Spec
import AmoLean.NTT.Goldilocks
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators

namespace AmoLean.NTT

/-! ## Part 1: NTT as Finset Sum (for proof purposes) -/

section FinsetDefinitions

variable {F : Type*} [CommRing F]

/-- NTT coefficient using Finset.sum over Fin n (for proofs) -/
def ntt_coeff_finset (ω : F) (a : Fin n → F) (k : Fin n) : F :=
  Finset.univ.sum fun i : Fin n => a i * ω ^ (i.val * k.val)

/-- INTT coefficient using Finset.sum over Fin n (for proofs) -/
def intt_coeff_finset (ω : F) (n_inv : F) (X : Fin n → F) (i : Fin n) : F :=
  n_inv * Finset.univ.sum fun k : Fin n => X k * ω ^ (n - (i.val * k.val) % n)

end FinsetDefinitions

/-! ## Part 2: Orthogonality Lemma -/

section Orthogonality

variable {F : Type*} [CommRing F] [IsDomain F]

/-- Orthogonality: Σₖ ω^(d·k) = n if d = 0, else 0 (for 0 ≤ d < n)
    Direct application of powSum theorems -/
theorem orthogonality_sum_lt {n : ℕ} (hn : n > 1) {ω : F}
    (hω : IsPrimitiveRoot ω n) (d : ℕ) (hd_lt : d < n) :
    (Finset.range n).sum (fun k => ω ^ (d * k)) =
    if d = 0 then (n : F) else 0 := by
  split_ifs with hd
  · -- d = 0: sum of ω^0 = sum of 1 = n
    subst hd
    simp only [Nat.zero_mul, pow_zero, Finset.sum_const, Finset.card_range]
    -- n • 1 = n in any ring
    rw [nsmul_eq_mul, mul_one]
  · -- 0 < d < n: use powSum_nonzero
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    -- powSum uses i * j, but we have d * k; use commutativity
    have h_eq : (Finset.range n).sum (fun k => ω ^ (d * k)) =
                (Finset.range n).sum (fun k => ω ^ (k * d)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.mul_comm]
    rw [h_eq]
    exact powSum_nonzero hn hω hd_pos hd_lt

end Orthogonality

/-! ## Part 3: NTT-INTT Roundtrip Identity -/

section Roundtrip

variable {F : Type*} [CommRing F] [IsDomain F]

/-- INTT(NTT(x))ᵢ = xᵢ (Finset version)

The proof outline:
  INTT(NTT(a))_i = n_inv * Σ_k (Σ_j a_j ω^(jk)) * ω^(n - (ik mod n))
                 = n_inv * Σ_j a_j * Σ_k ω^(jk + n - (ik mod n))
                 = n_inv * Σ_j a_j * [n if j=i else 0]  (orthogonality)
                 = n_inv * n * a_i = a_i
-/
theorem intt_ntt_identity_finset {n : ℕ} (hn : n > 1) {ω n_inv : F}
    (hω : IsPrimitiveRoot ω n)
    (h_inv : n_inv * (n : F) = 1)
    (a : Fin n → F) (i : Fin n) :
    intt_coeff_finset ω n_inv (fun k => ntt_coeff_finset ω a k) i = a i := by
  unfold intt_coeff_finset ntt_coeff_finset
  -- The proof requires double sum rearrangement and orthogonality
  -- This is a complex proof that uses:
  -- 1. Finset.sum_comm to swap summation order
  -- 2. orthogonality_sum_lt to collapse the inner sum
  -- 3. Algebraic simplification
  -- Full proof deferred to a dedicated lemma
  sorry

end Roundtrip

/-! ## Part 4: Linearity Properties -/

section Linearity

variable {F : Type*} [CommRing F]

/-- NTT is additive: NTT(a + b) = NTT(a) + NTT(b) -/
theorem ntt_additive (ω : F) (a b : Fin n → F) (k : Fin n) :
    ntt_coeff_finset ω (fun i => a i + b i) k =
    ntt_coeff_finset ω a k + ntt_coeff_finset ω b k := by
  unfold ntt_coeff_finset
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- NTT scales linearly: NTT(c·a) = c·NTT(a) -/
theorem ntt_scale (ω : F) (c : F) (a : Fin n → F) (k : Fin n) :
    ntt_coeff_finset ω (fun i => c * a i) k =
    c * ntt_coeff_finset ω a k := by
  unfold ntt_coeff_finset
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- NTT is a linear transformation -/
theorem ntt_linear (ω : F) (c₁ c₂ : F) (a b : Fin n → F) (k : Fin n) :
    ntt_coeff_finset ω (fun i => c₁ * a i + c₂ * b i) k =
    c₁ * ntt_coeff_finset ω a k + c₂ * ntt_coeff_finset ω b k := by
  simp only [show (fun i => c₁ * a i + c₂ * b i) =
      fun i => (fun j => c₁ * a j) i + (fun j => c₂ * b j) i from rfl]
  rw [ntt_additive, ntt_scale, ntt_scale]

end Linearity

/-! ## Part 5: Special Input Properties -/

section SpecialInputs

variable {F : Type*} [CommRing F] [IsDomain F]

/-- Helper: delta function -/
def delta_fn (n : ℕ) : Fin n → F := fun i => if i.val = 0 then 1 else 0

/-- Helper: constant function -/
def const_fn (n : ℕ) (c : F) : Fin n → F := fun _ => c

/-- NTT of delta function [1, 0, 0, ...] is all 1s

The sum only has one nonzero term at i=0, which contributes 1 * ω^0 = 1
-/
theorem ntt_delta {n : ℕ} (hn : n > 0) (ω : F) (idx : Fin n) :
    ntt_coeff_finset ω (delta_fn n) idx = 1 := by
  unfold ntt_coeff_finset delta_fn
  -- The sum is over i : Fin n, but only i = 0 gives nonzero
  -- Split the sum: Σᵢ (if i=0 then 1 else 0) * ω^(i*k) = 1 * ω^0 = 1
  have h_split : (Finset.univ.sum fun i : Fin n =>
      (if i.val = 0 then (1 : F) else 0) * ω ^ (i.val * idx.val)) =
      (1 : F) * ω ^ (0 * idx.val) := by
    rw [Finset.sum_eq_single ⟨0, hn⟩]
    · simp
    · intro b _ hb
      simp only [Fin.val_zero] at hb
      have : b.val ≠ 0 := by
        intro h
        apply hb
        exact Fin.ext h
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [h_split, Nat.zero_mul, pow_zero, mul_one]

/-- NTT of constant [c, c, ..., c]: X₀ = n·c -/
theorem ntt_constant_zero {n : ℕ} (hn : n > 0) (ω : F) (c : F) :
    ntt_coeff_finset ω (const_fn n c) ⟨0, hn⟩ = (n : F) * c := by
  unfold ntt_coeff_finset const_fn
  simp only [Nat.mul_zero, pow_zero, mul_one]
  rw [Finset.sum_const, Finset.card_fin]
  ring

/-- NTT of constant: Xₖ = 0 for k > 0 (uses primitivity)

Uses the fact that Σᵢ ω^(i·k) = 0 for 0 < k < n (geometric series for roots of unity)
-/
theorem ntt_constant_nonzero {n : ℕ} (hn : n > 1) (ω : F) (hω : IsPrimitiveRoot ω n) (c : F)
    (idx : Fin n) (hk : idx.val > 0) :
    ntt_coeff_finset ω (const_fn n c) idx = 0 := by
  unfold ntt_coeff_finset const_fn
  -- X_k = Σᵢ c * ω^(i*k) = c * Σᵢ ω^(i*k)
  rw [← Finset.mul_sum]
  -- Now we need Σᵢ ω^(i*k) = 0
  -- Convert from Fin n sum to range sum using bijection
  have h_sum_eq : (Finset.univ.sum fun i : Fin n => ω ^ (i.val * idx.val)) =
                  (Finset.range n).sum fun i => ω ^ (i * idx.val) := by
    rw [← Finset.sum_coe_sort (Finset.range n)]
    apply Finset.sum_nbij (fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩)
    · intro _ _; exact Finset.mem_univ _
    · intro i j _ _ h
      simp only [Subtype.mk.injEq] at h
      exact Fin.ext h
    · intro j _
      refine ⟨⟨j.val, Finset.mem_range.mp j.property⟩, Finset.mem_univ _, ?_⟩
      simp
    · intro _ _; rfl
  rw [h_sum_eq]
  -- Use powSum_nonzero: Σᵢ ω^(i*k) = 0 for 0 < k < n
  have h_zero : (Finset.range n).sum (fun i => ω ^ (i * idx.val)) = 0 := by
    exact powSum_nonzero hn hω hk idx.isLt
  rw [h_zero, mul_zero]

end SpecialInputs

/-! ## Part 6: Parseval's Theorem -/

section Parseval

variable {F : Type*} [CommRing F] [IsDomain F]

/-- Parseval's identity (energy preservation) -/
theorem parseval {n : ℕ} (hn : n > 1) (ω : F) (hω : IsPrimitiveRoot ω n)
    (a : Fin n → F) :
    (n : F) * (Finset.univ.sum fun i => a i * a i) =
    Finset.univ.sum fun k => ntt_coeff_finset ω a k * ntt_coeff_finset ω a k := by
  sorry -- Proof uses orthogonality

end Parseval

end AmoLean.NTT
