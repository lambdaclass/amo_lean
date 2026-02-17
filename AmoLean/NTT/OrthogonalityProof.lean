/-
  AMO-Lean: Orthogonality Proof for NTT Roundtrip Identity
  Session 4: S12 Implementation

  Main theorem: ntt_orthogonality_sum
  For primitive n-th root ω:
    Σ_k ω^(jk) * ω^(n - (ik mod n)) = n if j = i, else 0

  Strategy (from QA):
  - Don't fight with Nat arithmetic and truncated subtraction
  - Use algebraic properties: ω^n = 1, so ω^(n-x) = ω^(-x) = inverse of ω^x
  - Reduce to orthogonality_sum_lt which is already proven
-/

import AmoLean.NTT.RootsOfUnity
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AmoLean.NTT

variable {F : Type*} [CommRing F] [IsDomain F]

/-! ## Part 1: Self-sum equals n

When j = i, the sum Σ_k ω^(jk) * ω^(n - (jk mod n)) = n
because each term equals 1.
-/

/-- Each term in the self-sum equals 1: ω^m * ω^(n - m%n) = 1 -/
lemma term_self_eq_one {ω : F} {n : ℕ} (hn : n > 0) (hω : IsPrimitiveRoot ω n) (m : ℕ) :
    ω ^ m * ω ^ (n - m % n) = 1 := by
  have hmod : m % n < n := Nat.mod_lt m hn
  -- ω^m = ω^(m % n) by pow_eq_pow_mod
  rw [hω.pow_eq_pow_mod hn]
  -- Now: ω^(m%n) * ω^(n - m%n) = ω^(m%n + (n - m%n)) = ω^n = 1
  rw [← pow_add]
  have h : m % n + (n - m % n) = n := Nat.add_sub_cancel' (Nat.le_of_lt hmod)
  rw [h, hω.pow_eq_one]

/-- When j = i, each term equals 1, so the sum is n -/
theorem sum_self_eq_n {ω : F} {n : ℕ} (hn : n > 1) (hω : IsPrimitiveRoot ω n) (i : Fin n) :
    (Finset.univ.sum fun k : Fin n =>
      ω ^ (i.val * k.val) * ω ^ (n - (i.val * k.val) % n)) = (n : F) := by
  have hn_pos : n > 0 := by omega
  -- Each term is 1
  have h_one : ∀ k : Fin n, ω ^ (i.val * k.val) * ω ^ (n - (i.val * k.val) % n) = 1 :=
    fun k => term_self_eq_one hn_pos hω (i.val * k.val)
  simp_rw [h_one]
  simp only [Finset.sum_const, Finset.card_fin]
  rw [nsmul_eq_mul, mul_one]

/-! ## Part 2: Different indices sum to zero

When j ≠ i, we show the sum equals 0 using orthogonality of roots of unity.
-/

/-- Helper: convert Fin n sum to range n sum -/
theorem sum_fin_eq_sum_range {n : ℕ} (f : ℕ → F) :
    (Finset.univ.sum fun k : Fin n => f k.val) = (Finset.range n).sum f := by
  rw [← Finset.sum_coe_sort (Finset.range n)]
  apply Finset.sum_nbij (fun k => ⟨k.val, Finset.mem_range.mpr k.isLt⟩)
  · intro _ _; exact Finset.mem_univ _
  · intro a b _ _ hab; exact Fin.ext (Subtype.mk.inj hab)
  · intro j _; exact ⟨⟨j.val, Finset.mem_range.mp j.property⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  · intro _ _; rfl

/-- d = (j + n - i) % n is positive when j ≠ i -/
theorem diff_mod_pos {n : ℕ} (hn : n > 0) {j i : Fin n} (h : j ≠ i) :
    0 < (j.val + n - i.val) % n := by
  have hj : j.val < n := j.isLt
  have hi : i.val < n := i.isLt
  by_cases hjge : j.val ≥ i.val
  · -- j ≥ i: (j + n - i) % n = j - i, which is > 0 since j ≠ i
    have hd : (j.val + n - i.val) % n = j.val - i.val := by
      have h1 : j.val + n - i.val = n + (j.val - i.val) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : j.val - i.val < n)]
    rw [hd]
    have hne : j.val ≠ i.val := fun heq => h (Fin.ext heq)
    omega
  · -- j < i: (j + n - i) % n = j + n - i, which is in (0, n)
    push_neg at hjge
    have hd : (j.val + n - i.val) % n = j.val + n - i.val := by
      exact Nat.mod_eq_of_lt (by omega : j.val + n - i.val < n)
    rw [hd]
    omega

/-- Key lemma: Transform the sum using algebraic properties.
    ω^(jk) * ω^(n - (ik)%n) = ω^(jk) * ω^n / ω^((ik)%n) = ω^(jk) / ω^((ik)%n)
    But in our case, we use pow_eq_pow_mod to work with exponents mod n.
-/
lemma term_eq_pow_diff_mod {ω : F} {n : ℕ} (hn : n > 0) (hω : IsPrimitiveRoot ω n)
    (j i k : ℕ) :
    ω ^ (j * k) * ω ^ (n - (i * k) % n) = ω ^ ((j * k + n - (i * k) % n) % n) := by
  have hr_lt : (i * k) % n < n := Nat.mod_lt _ hn
  have hr_le : (i * k) % n ≤ n := Nat.le_of_lt hr_lt
  have h_exp_eq : j * k + (n - (i * k) % n) = j * k + n - (i * k) % n := by omega
  rw [← pow_add, hω.pow_eq_pow_mod hn, h_exp_eq]

/-- The RHS exponent in standard form -/
lemma rhs_exp_mod {ω : F} {n : ℕ} (hn : n > 0) (hω : IsPrimitiveRoot ω n)
    (j i : ℕ) (k : ℕ) :
    ω ^ (((j + n - i) % n) * k) = ω ^ ((((j + n - i) % n) * k) % n) := by
  rw [hω.pow_eq_pow_mod hn]

/-- Exponent equality: (j*k + n - (i*k)%n) % n = (((j+n-i)%n)*k) % n

This is the core arithmetic lemma. We prove it by showing both sides
are congruent modulo n.
-/
lemma exp_mod_eq {n : ℕ} (hn : n > 0) (j i k : ℕ) (hj : j < n) (hi : i < n) :
    (j * k + n - (i * k) % n) % n = (((j + n - i) % n) * k) % n := by
  -- Set r = (i*k) % n
  set r := (i * k) % n with hr_def
  have hr_lt : r < n := Nat.mod_lt _ hn
  have hr_le : r ≤ n := Nat.le_of_lt hr_lt

  -- Set d = (j + n - i) % n
  set d := (j + n - i) % n with hd_def
  have hd_lt : d < n := Nat.mod_lt _ hn

  -- The key insight is that both expressions, when interpreted in Z/nZ,
  -- equal (j - i) * k.
  --
  -- LHS: (j*k + n - r) % n = (j*k - r) % n (adding n doesn't change mod n)
  --      since r ≡ i*k (mod n), this is ≡ j*k - i*k = (j-i)*k (mod n)
  --
  -- RHS: d*k % n where d ≡ j - i (mod n)
  --      so d*k ≡ (j-i)*k (mod n)

  by_cases hjge : j ≥ i
  · -- Case j ≥ i
    have hd_eq : d = j - i := by
      simp only [hd_def]
      have h1 : j + n - i = n + (j - i) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : j - i < n)]

    -- j*k ≥ i*k since j ≥ i
    have hjk_ge_ik : j * k ≥ i * k := Nat.mul_le_mul_right k hjge

    -- (i*k) % n ≤ i*k
    have hik_ge_r : r ≤ i * k := by rw [hr_def]; exact Nat.mod_le (i * k) n

    -- j*k ≥ r
    have hjk_ge_r : j * k ≥ r := Nat.le_trans hik_ge_r hjk_ge_ik

    -- (j*k + n - r) % n = (j*k - r + n) % n = (j*k - r) % n
    have h_lhs_step : (j * k + n - r) % n = (j * k - r) % n := by
      have h1 : j * k + n - r = j * k - r + n := by omega
      rw [h1, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

    -- (j*k - r) % n = (j*k - i*k) % n
    -- Since i*k = (i*k/n)*n + r, we have j*k - r = j*k - i*k + (i*k/n)*n
    have h_ik_eq : i * k = (i * k / n) * n + r := by
      rw [hr_def]
      have h := Nat.div_add_mod (i * k) n
      rw [Nat.mul_comm] at h
      exact h.symm

    have h_diff : j * k - r = j * k - i * k + (i * k / n) * n := by
      have h := Nat.div_add_mod (i * k) n
      have h1 : r = i * k - (i * k / n) * n := by
        rw [Nat.mul_comm] at h; omega
      calc j * k - r
          = j * k - (i * k - (i * k / n) * n) := by rw [h1]
        _ = j * k - i * k + (i * k / n) * n := by omega

    have h_lhs_mod : (j * k - r) % n = (j * k - i * k) % n := by
      rw [h_diff, Nat.add_mul_mod_self_right]

    -- (j - i) * k = j*k - i*k (holds because j ≥ i)
    have h_sub_mul : (j - i) * k = j * k - i * k := Nat.mul_sub_right_distrib j i k

    calc (j * k + n - r) % n
        = (j * k - r) % n := h_lhs_step
      _ = (j * k - i * k) % n := h_lhs_mod
      _ = ((j - i) * k) % n := by rw [← h_sub_mul]
      _ = (d * k) % n := by rw [hd_eq]

  · -- Case j < i
    push_neg at hjge

    have hd_eq : d = j + n - i := by
      simp only [hd_def]
      exact Nat.mod_eq_of_lt (by omega : j + n - i < n)

    by_cases hk : k = 0
    · -- k = 0: both sides are 0
      -- r = i * 0 % n = 0 when k = 0
      have hr_zero : r = 0 := by rw [hr_def, hk]; simp
      simp only [hk, hr_zero, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.zero_add, Nat.zero_mod, Nat.mod_self]

    have hk_pos : k > 0 := Nat.pos_of_ne_zero hk

    -- For the case j < i, we need a different approach.
    -- (j*k + n - r) and (d*k) differ by a multiple of n.

    -- d*k = (j + n - i)*k = j*k + n*k - i*k
    have h_dk : d * k = j * k + (n - i) * k := by
      rw [hd_eq]
      have h : j + n - i = j + (n - i) := by omega
      rw [h, Nat.add_mul]

    have h_nmi_k : (n - i) * k = n * k - i * k := Nat.mul_sub_right_distrib n i k

    have h_dk2 : d * k = j * k + n * k - i * k := by
      rw [h_dk, h_nmi_k]
      -- j * k + (n * k - i * k) = j * k + n * k - i * k
      -- This holds because n * k > i * k (since n > i)
      have h_nk_gt_ik : n * k > i * k := Nat.mul_lt_mul_of_pos_right (by omega : i < n) hk_pos
      omega

    -- i*k = (i*k/n)*n + r
    have h_ik_eq : i * k = (i * k / n) * n + r := by
      rw [hr_def]
      have h := Nat.div_add_mod (i * k) n
      rw [Nat.mul_comm] at h
      exact h.symm

    -- Since i < n, we have i*k < n*k, so i*k/n < k
    have hq_lt_k : i * k / n < k := by
      have h_ik_lt : i * k < n * k := Nat.mul_lt_mul_of_pos_right (by omega : i < n) hk_pos
      exact Nat.div_lt_of_lt_mul h_ik_lt

    -- d*k - (j*k + n - r) = j*k + n*k - i*k - j*k - n + r
    --                     = n*k - i*k - n + r
    --                     = n*k - n - i*k + r
    --                     = n*(k-1) - i*k + r
    -- Since i*k = q*n + r where q = i*k/n:
    -- = n*(k-1) - q*n - r + r = n*(k - 1 - q)

    -- We need to show (j*k + n - r) % n = (d*k) % n

    have h_qn_eq : (i * k / n) * n = i * k - r := by
      have h := Nat.div_add_mod (i * k) n
      -- h : i * k = n * (i * k / n) + i * k % n
      -- We want: (i * k / n) * n = i * k - r where r = i * k % n
      rw [Nat.mul_comm] at h
      -- h : i * k = (i * k / n) * n + i * k % n
      -- r = i * k % n, so i * k - r = (i * k / n) * n
      rw [hr_def]
      omega

    -- d*k = j*k + n*k - i*k
    --     = j*k + n*k - (q*n + r)
    --     = j*k + n*k - q*n - r
    --     = j*k + n*(k - q) - r   [where k > q]
    --     = j*k + n - r + n*(k - q - 1)

    have hkq : k - i * k / n ≥ 1 := by omega

    have h_expand : d * k = j * k + n - r + n * (k - 1 - i * k / n) := by
      calc d * k
          = j * k + n * k - i * k := h_dk2
        _ = j * k + n * k - ((i * k / n) * n + r) := by rw [← h_ik_eq]
        _ = j * k + n * k - (i * k / n) * n - r := by omega
        _ = j * k + (n * k - (i * k / n) * n) - r := by omega
        _ = j * k + n * (k - i * k / n) - r := by
            have h1 : n * k - (i * k / n) * n = n * (k - i * k / n) := by
              have hq_le_k : i * k / n ≤ k := Nat.le_of_lt hq_lt_k
              -- (i * k / n) * n = n * (i * k / n) by commutativity
              rw [Nat.mul_comm (i * k / n) n]
              -- Now: n * k - n * (i * k / n) = n * (k - i * k / n)
              rw [← Nat.mul_sub_left_distrib]
            rw [h1]
        _ = j * k + (n + n * (k - i * k / n - 1)) - r := by
            -- n * (k - i*k/n) = n + n * (k - i*k/n - 1) when k - i*k/n ≥ 1
            have hm_pos : k - i * k / n ≥ 1 := by omega
            have h_eq : n * (k - i * k / n) = n + n * (k - i * k / n - 1) := by
              have : n * (k - i * k / n) = n * 1 + n * (k - i * k / n - 1) := by
                rw [← Nat.mul_add n 1 (k - i * k / n - 1)]
                congr 1
                omega
              simp only [Nat.mul_one] at this
              exact this
            rw [h_eq]
        _ = j * k + n - r + n * (k - i * k / n - 1) := by omega
        _ = j * k + n - r + n * (k - 1 - i * k / n) := by
            -- k - i*k/n - 1 = k - 1 - i*k/n when k > i*k/n
            have h_eq : k - i * k / n - 1 = k - 1 - i * k / n := by omega
            rw [h_eq]

    calc (j * k + n - r) % n
        = (j * k + n - r + n * (k - 1 - i * k / n)) % n := by
            rw [Nat.mul_comm n (k - 1 - i * k / n), Nat.add_mul_mod_self_right]
      _ = (d * k) % n := by rw [← h_expand]

/-- Key algebraic lemma: the term transformation -/
lemma term_eq_pow_diff {ω : F} {n : ℕ} (hn : n > 0) (hω : IsPrimitiveRoot ω n)
    (j i k : ℕ) (hj : j < n) (hi : i < n) :
    ω ^ (j * k) * ω ^ (n - (i * k) % n) = ω ^ (((j + n - i) % n) * k) := by
  rw [term_eq_pow_diff_mod hn hω, rhs_exp_mod hn hω]
  congr 1
  exact exp_mod_eq hn j i k hj hi

/-- When j ≠ i, the orthogonality sum equals 0 -/
theorem sum_diff_eq_zero {ω : F} {n : ℕ} (hn : n > 1) (hω : IsPrimitiveRoot ω n)
    (j i : Fin n) (h : j ≠ i) :
    (Finset.univ.sum fun k : Fin n =>
      ω ^ (j.val * k.val) * ω ^ (n - (i.val * k.val) % n)) = 0 := by
  have hn_pos : n > 0 := by omega

  -- Transform each term using term_eq_pow_diff
  have h_transform : ∀ k : Fin n,
      ω ^ (j.val * k.val) * ω ^ (n - (i.val * k.val) % n) =
      ω ^ (((j.val + n - i.val) % n) * k.val) := fun k =>
    term_eq_pow_diff hn_pos hω j.val i.val k.val j.isLt i.isLt

  simp_rw [h_transform]

  -- Convert to range sum
  have h_sum_eq : (Finset.univ.sum fun k : Fin n => ω ^ (((j.val + n - i.val) % n) * k.val)) =
                  (Finset.range n).sum (fun k => ω ^ (((j.val + n - i.val) % n) * k)) := by
    exact sum_fin_eq_sum_range (fun k => ω ^ (((j.val + n - i.val) % n) * k))

  rw [h_sum_eq]

  -- Apply powSum_nonzero
  set d := (j.val + n - i.val) % n with hd_def
  have hd_pos : 0 < d := diff_mod_pos hn_pos h
  have hd_lt : d < n := Nat.mod_lt _ hn_pos

  -- Convert to powSum form (need to swap multiplication order)
  have h_eq : (Finset.range n).sum (fun k => ω ^ (d * k)) =
              (Finset.range n).sum (fun k => ω ^ (k * d)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.mul_comm]

  rw [h_eq]
  exact powSum_nonzero hn hω hd_pos hd_lt

/-! ## Part 3: Main orthogonality theorem -/

/-- Main orthogonality theorem: Σ_k ω^(jk) * ω^(n - (ik mod n)) = n if j=i, else 0 -/
theorem ntt_orthogonality_sum {ω : F} {n : ℕ} (hn : n > 1) (hω : IsPrimitiveRoot ω n)
    (j i : Fin n) :
    (Finset.univ.sum fun k : Fin n =>
      ω ^ (j.val * k.val) * ω ^ (n - (i.val * k.val) % n)) =
    if j = i then (n : F) else 0 := by
  split_ifs with h
  · -- Case j = i: sum equals n
    rw [h]
    exact sum_self_eq_n hn hω i
  · -- Case j ≠ i: sum equals 0
    exact sum_diff_eq_zero hn hω j i h

end AmoLean.NTT
