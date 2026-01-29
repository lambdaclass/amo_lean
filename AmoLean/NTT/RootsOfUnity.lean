/-
  AMO-Lean: Roots of Unity for NTT
  Phase 5: NTT Core - Tasks 1.2 and 1.3

  This module provides a LIGHTWEIGHT definition of primitive roots,
  avoiding heavy Mathlib dependencies.

  Design Decision: We define our own IsPrimitiveRoot instead of using
  Mathlib's version because:
  1. Mathlib's IsPrimitiveRoot brings heavy algebraic hierarchy
  2. We only need: ω^n = 1 and ω^k ≠ 1 for 0 < k < n
  3. This keeps compile times fast (~2s vs ~2min)

  Key theorem: sum_of_powers_zero
    Σᵢ ωⁱ = 0  for any n-th primitive root ω (n > 1)
-/

import AmoLean.NTT.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

namespace AmoLean.NTT

/-! ## Part 1: Lightweight Primitive Root Definition

We define our own IsPrimitiveRoot that only requires CommMonoid,
avoiding Mathlib's heavier algebraic hierarchy.
-/

/-- A primitive n-th root of unity.

ω is a primitive n-th root if:
1. ω^n = 1
2. ω^k ≠ 1 for all 0 < k < n

This is a lightweight definition that avoids Mathlib dependencies.
-/
structure IsPrimitiveRoot {M : Type*} [Monoid M] (ω : M) (n : ℕ) : Prop where
  /-- The root raised to n equals 1 -/
  pow_eq_one : ω ^ n = 1
  /-- No smaller positive power equals 1 -/
  pow_ne_one_of_lt : ∀ k : ℕ, 0 < k → k < n → ω ^ k ≠ 1

namespace IsPrimitiveRoot

variable {M : Type*} [Monoid M] {ω : M} {n : ℕ}

/-- n must be positive for a primitive root to exist -/
theorem n_pos (h : IsPrimitiveRoot ω n) (hn : n ≠ 0) : 0 < n :=
  Nat.pos_of_ne_zero hn

/-- A primitive root is not 1 when n > 1 -/
theorem ne_one (h : IsPrimitiveRoot ω n) (hn : n > 1) : ω ≠ 1 := by
  intro heq
  have : ω ^ 1 = 1 := by simp [heq]
  exact h.pow_ne_one_of_lt 1 (by omega) hn this

/-- ω^(n*k) = 1 for any k -/
theorem pow_mul_eq_one (h : IsPrimitiveRoot ω n) (k : ℕ) : ω ^ (n * k) = 1 := by
  rw [pow_mul, h.pow_eq_one, one_pow]

/-- ω^k depends only on k mod n -/
theorem pow_eq_pow_mod (h : IsPrimitiveRoot ω n) (hn : n > 0) (k : ℕ) :
    ω ^ k = ω ^ (k % n) := by
  conv_lhs => rw [← Nat.div_add_mod k n]
  rw [pow_add, pow_mul, h.pow_eq_one, one_pow, one_mul]

end IsPrimitiveRoot

/-! ## Part 2: NTT Root Structure

Bundles a primitive root with the constraint that n is a power of 2.
-/

/-- An n-th root of unity suitable for NTT.

This bundles:
- The root value ω
- Proof that it's a primitive n-th root
- Constraint that n is a power of 2
-/
structure NTTRoot (F : Type*) [Monoid F] (n : ℕ) where
  /-- The primitive root value -/
  val : F
  /-- n is a power of 2 -/
  n_pow2 : ∃ k : ℕ, n = 2^k
  /-- n > 1 (needed for meaningful NTT) -/
  n_gt_one : n > 1
  /-- ω is a primitive n-th root of unity -/
  is_primitive : IsPrimitiveRoot val n

namespace NTTRoot

variable {F : Type*} [Monoid F] {n : ℕ}

/-- The root raised to power n equals 1 -/
theorem pow_n_eq_one (ω : NTTRoot F n) : ω.val ^ n = 1 :=
  ω.is_primitive.pow_eq_one

/-- The root raised to any power k < n is not 1 (unless k = 0) -/
theorem pow_ne_one_of_lt (ω : NTTRoot F n) {k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ω.val ^ k ≠ 1 :=
  ω.is_primitive.pow_ne_one_of_lt k hk hkn

/-- The root is not 1 -/
theorem val_ne_one (ω : NTTRoot F n) : ω.val ≠ 1 :=
  ω.is_primitive.ne_one ω.n_gt_one

end NTTRoot

/-! ## Part 3: Sum of Powers Theorem

The key theorem for NTT correctness:
  Σᵢ₌₀ⁿ⁻¹ ωⁱ = 0   when ω is a primitive n-th root and n > 1

This is used to prove:
- NTT_INTT_identity (normalization cancellation)
- Convolution theorem

The proof uses the geometric series formula:
  Σᵢ₌₀ⁿ⁻¹ ωⁱ = (1 - ωⁿ) / (1 - ω) = (1 - 1) / (1 - ω) = 0
-/

section SumOfPowers

variable {F : Type*} [CommRing F] [IsDomain F]

/-- Geometric series formula: (1 - r) * Σᵢ₌₀ⁿ⁻¹ rⁱ = 1 - r^n -/
theorem geom_sum_finset (r : F) (n : ℕ) :
    (1 - r) * (Finset.range n).sum (fun i => r ^ i) = 1 - r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- Sum of powers of primitive root is zero -/
theorem sum_of_powers_zero {ω : F} {n : ℕ} (hn : n > 1)
    (hω : IsPrimitiveRoot ω n) :
    (Finset.range n).sum (fun i => ω ^ i) = 0 := by
  -- ω ≠ 1 because n > 1
  have hω_ne_one : ω ≠ 1 := hω.ne_one hn
  -- ω^n = 1
  have hωn : ω ^ n = 1 := hω.pow_eq_one
  -- Use geometric series: (1 - ω) * sum = 1 - ω^n = 1 - 1 = 0
  have h_geom := geom_sum_finset ω n
  rw [hωn, sub_self] at h_geom
  -- Since 1 - ω ≠ 0 and F is a domain, sum = 0
  have h_factor_ne_zero : (1 : F) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω_ne_one)
  exact (mul_eq_zero.mp h_geom).resolve_left h_factor_ne_zero

/-- Corollary: sum of powers with NTTRoot -/
theorem NTTRoot.sum_powers_zero (ω : NTTRoot F n) :
    (Finset.range n).sum (fun i => ω.val ^ i) = 0 :=
  sum_of_powers_zero ω.n_gt_one ω.is_primitive

end SumOfPowers

/-! ## Part 4: Orthogonality Relations

For NTT correctness we also need:
  Σᵢ₌₀ⁿ⁻¹ ω^(i*j) = n  if j ≡ 0 (mod n)
                     = 0  otherwise
-/

section Orthogonality

variable {F : Type*} [CommRing F] [IsDomain F]

/-- Sum of ω^(i*j) for fixed j -/
def powSum (ω : F) (n j : ℕ) : F :=
  (Finset.range n).sum (fun i => ω ^ (i * j))

/-- When j ≡ 0 (mod n), the sum equals n (as field element) -/
theorem powSum_zero_mod {ω : F} {n : ℕ} (hn : n > 0) (hω : IsPrimitiveRoot ω n) :
    powSum ω n 0 = n := by
  unfold powSum
  simp only [Nat.mul_zero, pow_zero]
  simp [Finset.card_range]

/-- When 0 < j < n, the sum is 0 -/
theorem powSum_nonzero {ω : F} {n j : ℕ} (hn : n > 1) (hω : IsPrimitiveRoot ω n)
    (hj_pos : 0 < j) (hj_lt : j < n) :
    powSum ω n j = 0 := by
  unfold powSum
  -- Rewrite: ω^(i*j) = (ω^j)^i
  have h_rewrite : ∀ i, ω ^ (i * j) = (ω ^ j) ^ i := by
    intro i; rw [mul_comm, pow_mul]
  simp only [h_rewrite]
  -- ω^j ≠ 1 since 0 < j < n
  have hωj_ne_one : ω ^ j ≠ 1 := hω.pow_ne_one_of_lt j hj_pos hj_lt
  -- (ω^j)^n = ω^(j*n) = ω^(n*j) = 1
  have hωjn : (ω ^ j) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  -- Use geometric series
  have h_geom := geom_sum_finset (ω ^ j) n
  rw [hωjn, sub_self] at h_geom
  have h_factor_ne_zero : (1 : F) - ω ^ j ≠ 0 := sub_ne_zero.mpr (Ne.symm hωj_ne_one)
  exact (mul_eq_zero.mp h_geom).resolve_left h_factor_ne_zero

end Orthogonality

/-! ## Part 5: Twiddle Factor Properties

For Cooley-Tukey NTT, we need properties of twiddle factors:
- ω^(n/2) = -1
- ω^(k + n/2) = -ω^k
-/

section TwiddleFactors

variable {F : Type*} [CommRing F] [IsDomain F]

/-- ω^(n/2) squared equals 1 -/
theorem twiddle_half_squared {ω : F} {n : ℕ} (hn_even : 2 ∣ n)
    (hω : IsPrimitiveRoot ω n) :
    (ω ^ (n / 2)) ^ 2 = 1 := by
  rw [← pow_mul]
  have h : n / 2 * 2 = n := Nat.div_mul_cancel hn_even
  rw [h]
  exact hω.pow_eq_one

/-- ω^(n/2) is -1 for primitive roots with n > 2 -/
theorem twiddle_half_eq_neg_one {ω : F} {n : ℕ} (hn : n > 2) (hn_even : 2 ∣ n)
    (hω : IsPrimitiveRoot ω n) :
    ω ^ (n / 2) = -1 := by
  have h_sq := twiddle_half_squared hn_even hω
  -- ω^(n/2) is a square root of 1
  -- It can't be 1 because n/2 < n and ω is primitive
  have h_half_lt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
  have h_half_pos : 0 < n / 2 := by omega
  have h_ne_one : ω ^ (n / 2) ≠ 1 := hω.pow_ne_one_of_lt (n / 2) h_half_pos h_half_lt
  -- In a domain, x² = 1 means (x-1)(x+1) = 0
  have h_prod_zero : (ω ^ (n / 2) - 1) * (ω ^ (n / 2) + 1) = 0 := by
    have : (ω ^ (n / 2)) ^ 2 - 1 = 0 := by rw [h_sq]; ring
    calc (ω ^ (n / 2) - 1) * (ω ^ (n / 2) + 1)
        = (ω ^ (n / 2)) ^ 2 - 1 := by ring
      _ = 0 := this
  -- Since we're in a domain and x ≠ 1, we have x + 1 = 0
  rcases mul_eq_zero.mp h_prod_zero with h | h
  · exact absurd (sub_eq_zero.mp h) h_ne_one
  · -- From h : ω^(n/2) + 1 = 0, we get ω^(n/2) = -1
    have := add_eq_zero_iff_eq_neg.mp h
    exact this

/-- Key property: ω^(k + n/2) = -ω^k -/
theorem twiddle_shift {ω : F} {n k : ℕ} (hn : n > 2) (hn_even : 2 ∣ n)
    (hω : IsPrimitiveRoot ω n) :
    ω ^ (k + n / 2) = -(ω ^ k) := by
  rw [pow_add, twiddle_half_eq_neg_one hn hn_even hω]
  ring

end TwiddleFactors

/-! ## Part 6: Squared Root Properties

When n is a power of 2, ω² is a primitive (n/2)-th root.
This is essential for Cooley-Tukey recursion.
-/

section SquaredRoot

variable {F : Type*} [CommRing F] [IsDomain F]

/-- ω² is a primitive (n/2)-th root when n is even and n ≥ 4 -/
theorem squared_is_primitive {ω : F} {n : ℕ} (hn : n ≥ 4) (hn_even : 2 ∣ n)
    (hω : IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω ^ 2) (n / 2) := by
  constructor
  · -- (ω²)^(n/2) = ω^n = 1
    rw [← pow_mul]
    have h : 2 * (n / 2) = n := by
      have := Nat.div_mul_cancel hn_even
      omega
    rw [h]
    exact hω.pow_eq_one
  · -- (ω²)^k ≠ 1 for 0 < k < n/2
    intro k hk_pos hk_lt
    rw [← pow_mul]
    apply hω.pow_ne_one_of_lt
    · omega
    · have : 2 * k < 2 * (n / 2) := by omega
      have h_eq : 2 * (n / 2) = n := by
        have := Nat.div_mul_cancel hn_even
        omega
      omega

end SquaredRoot

end AmoLean.NTT
