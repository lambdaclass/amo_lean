/-
  AMO-Lean: Generic NTT Correctness Proof
  N18.5 (CRITICO, GATE) — NTT Correctness Proof

  Proves that ntt_generic (Cooley-Tukey, O(n log n)) equals ntt_spec_generic
  (naive DFT, O(n²)) for power-of-2 length inputs with a primitive root.

  Key theorems:
  1. ntt_coeff_generic_eq_sum — "Golden Bridge" (foldl ↔ Finset.sum)
  2. ntt_coeff_generic_split — DFT splitting: X_k = E_k + ω^k · O_k
  3. ntt_coeff_generic_split_upper — X_{k+n/2} = E_k - ω^k · O_k
  4. ntt_generic_eq_spec — MAIN: ntt_generic ω a = ntt_spec_generic ω a
-/

import AmoLean.NTT.GenericNTT
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.ListUtils
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AmoLean.NTT.Generic

open AmoLean.NTT
open BigOperators

/-! ## Part 1: Finset.sum Shadow Definition and Golden Bridge -/

section GoldenBridge

variable {F : Type*} [Field F]

/-- Shadow specification of NTT coefficient using Finset.sum.
    Equivalent to ntt_coeff_generic but amenable to algebraic manipulation. -/
def ntt_coeff_sum_generic (ω : F) (a : List F) (k : ℕ) : F :=
  ∑ i ∈ Finset.range a.length, a.getD i 0 * ω ^ (i * k)

/-- foldl with addition over List.range equals Finset.sum. -/
private theorem list_range_foldl_eq_finset_sum_generic (n : ℕ) (f : ℕ → F) :
    (List.range n).foldl (fun acc i => acc + f i) (0 : F) =
    ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Finset.sum_range_succ, ih, add_comm]

/-- Helper: foldl with match on getElem? equals foldl with getD, for valid ranges. -/
private theorem foldl_match_eq_foldl_getD (ω : F) (a : List F) (k : ℕ) :
    ∀ n ≤ a.length, ∀ acc : F,
      (List.range n).foldl (fun ac i =>
        match a[i]? with
        | some aᵢ => ac + aᵢ * ω ^ (i * k)
        | none => ac) acc =
      (List.range n).foldl (fun ac i =>
        ac + a.getD i 0 * ω ^ (i * k)) acc := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn acc
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hn' : n < a.length := Nat.lt_of_succ_le hn
    rw [ih (le_of_lt hn') acc]
    rw [List.getElem?_eq_getElem hn', List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hn', Option.getD_some]

/-- THE GOLDEN BRIDGE: ntt_coeff_generic (foldl) = ntt_coeff_sum_generic (Finset.sum).
    After this, we never reason about foldl again. -/
theorem ntt_coeff_generic_eq_sum (ω : F) (a : List F) (k : ℕ) :
    ntt_coeff_generic ω a k = ntt_coeff_sum_generic ω a k := by
  unfold ntt_coeff_generic ntt_coeff_sum_generic
  calc (List.range a.length).foldl (fun acc i =>
        match a[i]? with
        | some aᵢ => acc + aᵢ * ω ^ (i * k)
        | none => acc) 0
      = (List.range a.length).foldl (fun ac i =>
        ac + a.getD i 0 * ω ^ (i * k)) 0 :=
        foldl_match_eq_foldl_getD ω a k a.length le_rfl 0
    _ = ∑ i ∈ Finset.range a.length, a.getD i 0 * ω ^ (i * k) :=
        list_range_foldl_eq_finset_sum_generic a.length _

end GoldenBridge

/-! ## Part 2: Finset Sum Splitting by Parity -/

section SumSplitting

variable {F : Type*} [Field F]

/-- Finset.range n splits into even and odd index sums. -/
theorem finset_sum_split_parity_generic (n : ℕ) (f : ℕ → F) :
    ∑ i ∈ Finset.range n, f i =
    ∑ m ∈ Finset.range ((n + 1) / 2), f (2 * m) +
    ∑ m ∈ Finset.range (n / 2), f (2 * m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : Even n
    · obtain ⟨k, hk⟩ := hn
      have he1 : (n + 1 + 1) / 2 = k + 1 := by omega
      have he2 : (n + 1) / 2 = k := by omega
      have he3 : n / 2 = k := by omega
      rw [he1, he2, he3, Finset.sum_range_succ]
      have : n = 2 * k := by omega
      rw [this]; ring
    · have hodd : Odd n := Nat.not_even_iff_odd.mp hn
      obtain ⟨k, hk⟩ := hodd
      have ho1 : (n + 1 + 1) / 2 = k + 1 := by omega
      have ho2 : (n + 1) / 2 = k + 1 := by omega
      have ho3 : n / 2 = k := by omega
      rw [ho1, ho2, ho3]
      have : n = 2 * k + 1 := by omega
      rw [this, Finset.sum_range_succ (f := fun x => f (2 * x + 1))]
      ring

/-- Twiddle factor for even indices: ω^(2mk) = (ω*ω)^(mk). -/
private theorem twiddle_even_generic (ω : F) (m k : ℕ) :
    ω ^ (2 * m * k) = (ω * ω) ^ (m * k) := by
  rw [← sq, ← pow_mul]; congr 1; ring

/-- Twiddle factor for odd indices: ω^((2m+1)k) = ω^k · (ω*ω)^(mk). -/
private theorem twiddle_odd_generic (ω : F) (m k : ℕ) :
    ω ^ ((2 * m + 1) * k) = ω ^ k * (ω * ω) ^ (m * k) := by
  rw [← sq, ← pow_mul]
  have h : (2 * m + 1) * k = k + 2 * (m * k) := by ring
  rw [h, pow_add, pow_mul]

/-- Sum over even indices equals ntt_coeff_sum_generic on evens list with ω*ω. -/
theorem sum_evens_eq_generic (ω : F) (a : List F) (k : ℕ) (heven : 2 ∣ a.length) :
    ∑ m ∈ Finset.range (a.length / 2), a.getD (2 * m) 0 * ω ^ (2 * m * k) =
    ntt_coeff_sum_generic (ω * ω) (evens a) k := by
  unfold ntt_coeff_sum_generic
  have hlen : (evens a).length = a.length / 2 := by
    rw [evens_length]; obtain ⟨j, hj⟩ := heven; simp only [hj]; omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro m hm
  have hm_lt : m < (evens a).length := by rw [hlen]; exact Finset.mem_range.mp hm
  have h_elem : (evens a)[m]? = a[2 * m]? := evens_get a m hm_lt
  have h_getD : (evens a).getD m 0 = a.getD (2 * m) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h_elem]
  rw [← h_getD, twiddle_even_generic]

/-- Sum over odd indices equals ω^k · ntt_coeff_sum_generic on odds list with ω*ω. -/
theorem sum_odds_eq_generic (ω : F) (a : List F) (k : ℕ) :
    ∑ m ∈ Finset.range (a.length / 2), a.getD (2 * m + 1) 0 * ω ^ ((2 * m + 1) * k) =
    ω ^ k * ntt_coeff_sum_generic (ω * ω) (odds a) k := by
  unfold ntt_coeff_sum_generic
  have hlen : (odds a).length = a.length / 2 := odds_length a
  rw [hlen, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm_lt : m < (odds a).length := by rw [hlen]; exact Finset.mem_range.mp hm
  have h_elem : (odds a)[m]? = a[2 * m + 1]? := odds_get a m hm_lt
  have h_getD : (odds a).getD m 0 = a.getD (2 * m + 1) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h_elem]
  rw [h_getD, twiddle_odd_generic]; ring

end SumSplitting

/-! ## Part 3: DFT Coefficient Splitting Theorems -/

section CoefficientSplitting

variable {F : Type*} [Field F]

/-- DFT splitting for upper half: X_k = E_k + ω^k · O_k (k < n/2). -/
theorem ntt_coeff_generic_split (ω : F) (a : List F)
    (heven : 2 ∣ a.length) (k : ℕ) (_hk : k < a.length / 2) :
    ntt_coeff_generic ω a k =
    ntt_coeff_generic (ω * ω) (evens a) k + ω ^ k * ntt_coeff_generic (ω * ω) (odds a) k := by
  rw [ntt_coeff_generic_eq_sum, ntt_coeff_generic_eq_sum, ntt_coeff_generic_eq_sum]
  -- For even-length, (n+1)/2 = n/2
  have hlen_half : (a.length + 1) / 2 = a.length / 2 := by
    obtain ⟨j, hj⟩ := heven; simp only [hj]; omega
  show ntt_coeff_sum_generic ω a k = ntt_coeff_sum_generic (ω * ω) (evens a) k +
    ω ^ k * ntt_coeff_sum_generic (ω * ω) (odds a) k
  unfold ntt_coeff_sum_generic
  rw [finset_sum_split_parity_generic a.length, hlen_half,
      sum_evens_eq_generic ω a k heven, sum_odds_eq_generic ω a k]
  rfl

/-- DFT splitting for lower half: X_{k+n/2} = E_k - ω^k · O_k.

    Uses ω^(n/2) = -1 for primitive roots. -/
theorem ntt_coeff_generic_split_upper (ω : F) (a : List F) (n : ℕ)
    (hn : n > 2) (heven : 2 ∣ n) (h_len : a.length = n)
    (hω : IsPrimitiveRoot ω n)
    (k : ℕ) (_hk : k < n / 2) :
    ntt_coeff_generic ω a (k + n / 2) =
    ntt_coeff_generic (ω * ω) (evens a) k -
    ω ^ k * ntt_coeff_generic (ω * ω) (odds a) k := by
  rw [ntt_coeff_generic_eq_sum, ntt_coeff_generic_eq_sum, ntt_coeff_generic_eq_sum]
  show ntt_coeff_sum_generic ω a (k + n / 2) =
    ntt_coeff_sum_generic (ω * ω) (evens a) k -
    ω ^ k * ntt_coeff_sum_generic (ω * ω) (odds a) k
  have heven_input : 2 ∣ a.length := by rw [h_len]; exact heven
  have hlen_half : (a.length + 1) / 2 = a.length / 2 := by
    obtain ⟨j, hj⟩ := heven_input; simp only [hj]; omega
  have h_half_neg : ω ^ (n / 2) = -1 := twiddle_half_eq_neg_one hn heven hω
  -- Rewrite LHS using sum splitting
  have h_lhs : ntt_coeff_sum_generic ω a (k + n / 2) =
      ∑ m ∈ Finset.range (a.length / 2), a.getD (2 * m) 0 * ω ^ (2 * m * (k + n / 2)) +
      ∑ m ∈ Finset.range (a.length / 2), a.getD (2 * m + 1) 0 * ω ^ ((2 * m + 1) * (k + n / 2)) := by
    unfold ntt_coeff_sum_generic
    rw [finset_sum_split_parity_generic a.length, hlen_half]
  -- Even-index terms: ω^(2m*(k+n/2)) = ω^(2mk) since ω^(mn) = 1
  have h_even_sum : ∑ m ∈ Finset.range (a.length / 2),
      a.getD (2 * m) 0 * ω ^ (2 * m * (k + n / 2)) =
    ntt_coeff_sum_generic (ω * ω) (evens a) k := by
    rw [← sum_evens_eq_generic ω a k heven_input]
    apply Finset.sum_congr rfl
    intro m _
    congr 1
    have h_cancel : 2 * m * (k + n / 2) = 2 * m * k + n * m := by
      have := Nat.div_mul_cancel heven; nlinarith
    rw [h_cancel, pow_add, hω.pow_mul_eq_one m, mul_one]
  -- Odd-index terms: ω^((2m+1)*(k+n/2)) = -ω^((2m+1)*k)
  have h_odd_sum : ∑ m ∈ Finset.range (a.length / 2),
      a.getD (2 * m + 1) 0 * ω ^ ((2 * m + 1) * (k + n / 2)) =
    -(ω ^ k * ntt_coeff_sum_generic (ω * ω) (odds a) k) := by
    -- First show each term picks up a factor of -1
    have h_termwise : ∀ m ∈ Finset.range (a.length / 2),
        a.getD (2 * m + 1) 0 * ω ^ ((2 * m + 1) * (k + n / 2)) =
        -(a.getD (2 * m + 1) 0 * ω ^ ((2 * m + 1) * k)) := by
      intro m _
      have h1 : (2 * m + 1) * (k + n / 2) = (2 * m + 1) * k + ((2 * m + 1) * (n / 2)) := by ring
      rw [h1, pow_add]
      have h2 : (2 * m + 1) * (n / 2) = n * m + n / 2 := by
        have := Nat.div_mul_cancel heven; nlinarith
      rw [h2, pow_add, hω.pow_mul_eq_one m, one_mul, h_half_neg]
      ring
    rw [Finset.sum_congr rfl h_termwise, Finset.sum_neg_distrib,
        sum_odds_eq_generic ω a k]
  rw [h_lhs, h_even_sum, h_odd_sum]
  ring

/-- ntt_spec_generic at index k equals ntt_coeff_generic at k. -/
theorem ntt_spec_generic_getElem_eq (ω : F) (a : List F) (k : ℕ) (hk : k < a.length) :
    (ntt_spec_generic ω a)[k]? = some (ntt_coeff_generic ω a k) := by
  simp only [ntt_spec_generic, ntt_coeff_generic]
  rw [List.getElem?_map, List.getElem?_range hk]
  rfl

end CoefficientSplitting

/-! ## Part 4: Main Correctness Theorem -/

section MainTheorem

variable {F : Type*} [Field F]

/-- ntt_generic on singleton equals ntt_spec_generic on singleton. -/
private theorem ntt_generic_eq_spec_singleton (ω : F) (x : F) :
    ntt_generic ω [x] = ntt_spec_generic ω [x] := by
  simp only [ntt_generic, ntt_spec_generic, List.length_singleton]
  have hr1 : List.range 1 = [0] := by decide
  rw [hr1]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
             List.getElem?_cons_zero, Nat.zero_mul, pow_zero, mul_one, zero_add]

/-- Helper: accessing ntt_spec_generic at a valid index via getD. -/
private theorem spec_getElem_getD (ω : F) (a : List F) (k : ℕ) (hk : k < a.length) :
    (ntt_spec_generic ω a)[k]?.getD 0 = ntt_coeff_generic ω a k := by
  rw [ntt_spec_generic_getElem_eq ω a k hk]
  simp only [Option.getD_some]

/-- ω^2 = ω * ω (helper for converting squared_is_primitive results). -/
private theorem sq_eq_mul_self (ω : F) : ω ^ 2 = ω * ω := sq ω

/-- Primitive root of order 2 satisfies ω = -1. -/
private theorem primitive_root_two_eq_neg_one {ω : F} (hω : IsPrimitiveRoot ω 2) :
    ω = -1 := by
  have h_sq : ω ^ 2 = 1 := hω.pow_eq_one
  have h_ne : ω ≠ 1 := hω.ne_one (by omega)
  have h_prod : (ω - 1) * (ω + 1) = 0 := by
    have : ω ^ 2 - 1 = 0 := by rw [h_sq]; ring
    calc (ω - 1) * (ω + 1) = ω ^ 2 - 1 := by ring
      _ = 0 := this
  rcases mul_eq_zero.mp h_prod with h | h
  · exact absurd (sub_eq_zero.mp h) h_ne
  · exact add_eq_zero_iff_eq_neg.mp h

/-- n=2 edge case for lower butterfly:
    ntt_coeff_generic ω a 1 = E_0 - ω^0 * O_0 when a.length = 2, ω primitive 2nd root. -/
private theorem ntt_coeff_generic_n2_lower (ω : F) (a : List F)
    (hω : IsPrimitiveRoot ω 2) (hlen : a.length = 2) :
    ntt_coeff_generic ω a 1 =
    ntt_coeff_generic (ω * ω) (evens a) 0 -
    ω ^ 0 * ntt_coeff_generic (ω * ω) (odds a) 0 := by
  have h_neg1 : ω = -1 := primitive_root_two_eq_neg_one hω
  have h_sq1 : ω * ω = 1 := by rw [h_neg1]; ring
  rw [ntt_coeff_generic_eq_sum, ntt_coeff_generic_eq_sum, ntt_coeff_generic_eq_sum]
  show ntt_coeff_sum_generic ω a 1 =
    ntt_coeff_sum_generic (ω * ω) (evens a) 0 -
    ω ^ 0 * ntt_coeff_sum_generic (ω * ω) (odds a) 0
  unfold ntt_coeff_sum_generic
  have hevlen : (evens a).length = 1 := by
    rw [evens_length]; omega
  have hodlen : (odds a).length = 1 := by rw [odds_length, hlen]
  rw [hlen, hevlen, hodlen, h_sq1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
             mul_one, one_pow]
  -- getD for evens/odds
  have hev_getD : (evens a).getD 0 0 = a.getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [evens_get a 0 (by rw [hevlen]; omega)]
  have hod_getD : (odds a).getD 0 0 = a.getD 1 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [odds_get a 0 (by rw [hodlen]; omega)]
  rw [hev_getD, hod_getD, h_neg1]
  ring

/-- THE MAIN THEOREM: ntt_generic (Cooley-Tukey) equals ntt_spec_generic (naive DFT).

    Proved by strong induction on the exponent in 2^exp = a.length.

    Requires:
    - a.length is a power of 2
    - ω is a primitive a.length-th root of unity -/
theorem ntt_generic_eq_spec (ω : F) (a : List F)
    (h_pow2 : ∃ k : ℕ, a.length = 2 ^ k)
    (hω : IsPrimitiveRoot ω a.length) :
    ntt_generic ω a = ntt_spec_generic ω a := by
  obtain ⟨exp, hexp⟩ := h_pow2
  cases exp with
  | zero =>
    have h_len : a.length = 1 := by simp [hexp]
    match h : a with
    | [] => simp at h_len
    | [x] => exact ntt_generic_eq_spec_singleton ω x
    | _ :: _ :: _ => simp at h_len
  | succ exp' =>
    have h_len_ge2 : a.length ≥ 2 := by
      rw [hexp, Nat.pow_succ]
      have : 2 ^ exp' ≥ 1 := Nat.one_le_pow exp' 2 (by norm_num)
      omega
    have h_even : 2 ∣ a.length := by
      rw [hexp, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
    have h_evens_len : (evens a).length = 2 ^ exp' := by
      rw [evens_length, hexp, Nat.pow_succ]; omega
    have h_odds_len : (odds a).length = 2 ^ exp' := by
      rw [odds_length, hexp, Nat.pow_succ]; omega
    have h_evens_pow2 : ∃ k', (evens a).length = 2 ^ k' := ⟨exp', h_evens_len⟩
    have h_odds_pow2 : ∃ k', (odds a).length = 2 ^ k' := ⟨exp', h_odds_len⟩
    -- ω*ω is primitive root for subproblems
    have hω_sq : IsPrimitiveRoot (ω * ω) (evens a).length := by
      cases exp' with
      | zero =>
        have h_input_len : a.length = 2 := by simp [hexp]
        have h_omega_sq : ω * ω = 1 := by
          have := hω.pow_eq_one; rw [h_input_len] at this; simpa [sq] using this
        rw [h_evens_len, h_omega_sq]
        exact ⟨by ring, fun d hd _ => by omega⟩
      | succ e =>
        have hn_ge4 : a.length ≥ 4 := by
          simp only [hexp, Nat.pow_succ]
          have : 2 * 2 ^ (e + 1) = 2 * 2 * 2 ^ e := by ring
          omega
        have hsq := squared_is_primitive (n := a.length) hn_ge4 h_even hω
        -- hsq : IsPrimitiveRoot (ω ^ 2) (a.length / 2)
        have h_half : a.length / 2 = 2 ^ (e + 1) := by
          rw [hexp, Nat.pow_succ]; omega
        rw [h_evens_len]
        rw [h_half] at hsq
        rwa [sq_eq_mul_self] at hsq
    have hω_sq_odds : IsPrimitiveRoot (ω * ω) (odds a).length := by
      rw [h_odds_len, ← h_evens_len]; exact hω_sq
    -- Inductive hypotheses
    have ih_evens : ntt_generic (ω * ω) (evens a) = ntt_spec_generic (ω * ω) (evens a) :=
      ntt_generic_eq_spec (ω * ω) (evens a) h_evens_pow2 hω_sq
    have ih_odds : ntt_generic (ω * ω) (odds a) = ntt_spec_generic (ω * ω) (odds a) :=
      ntt_generic_eq_spec (ω * ω) (odds a) h_odds_pow2 hω_sq_odds
    -- Unfold and prove element-wise
    rw [ntt_generic_unfold ω a h_len_ge2]
    apply List.ext_getElem?
    intro k
    let n := a.length
    let half := n / 2
    have h_half_half : half + half = n := by
      have := Nat.mul_div_cancel' h_even; omega
    simp only [ih_evens, ih_odds]
    by_cases hk_lt_half : k < half
    · -- Case 1: k < half (upper butterfly)
      rw [List.getElem?_append_left
        (by simp [List.length_map, List.length_range]; exact hk_lt_half)]
      rw [List.getElem?_map, List.getElem?_range hk_lt_half]
      simp only [Option.map_some]
      have hk_lt_n : k < n := by omega
      rw [ntt_spec_generic_getElem_eq ω a k hk_lt_n]
      congr 1
      rw [spec_getElem_getD (ω * ω) (evens a) k (by rw [h_evens_len]; omega)]
      rw [spec_getElem_getD (ω * ω) (odds a) k (by rw [h_odds_len]; omega)]
      exact (ntt_coeff_generic_split ω a h_even k hk_lt_half).symm
    · -- k ≥ half
      push_neg at hk_lt_half
      by_cases hk_lt_n : k < n
      · -- Case 2: half ≤ k < n (lower butterfly)
        rw [List.getElem?_append_right
          (by simp [List.length_map, List.length_range]; exact hk_lt_half)]
        simp only [List.length_map, List.length_range]
        have hk_sub_lt : k - half < half := by omega
        rw [List.getElem?_map, List.getElem?_range hk_sub_lt]
        simp only [Option.map_some]
        set j := k - half with hj_def
        have hj_lt : j < n / 2 := hk_sub_lt
        rw [spec_getElem_getD (ω * ω) (evens a) j (by rw [h_evens_len]; omega)]
        rw [spec_getElem_getD (ω * ω) (odds a) j (by rw [h_odds_len]; omega)]
        rw [ntt_spec_generic_getElem_eq ω a k hk_lt_n]
        congr 1
        -- k = j + n/2
        have hk_eq : k = j + n / 2 := by omega
        rw [hk_eq]
        cases exp' with
        | zero =>
          -- n = 2, half = 1, j = 0
          have hn2 : n = 2 := by omega
          have hj0 : j = 0 := by omega
          rw [hj0]
          have halen : a.length = 2 := hn2
          have hω2 : IsPrimitiveRoot ω 2 := by rwa [← halen]
          show ntt_coeff_generic (ω * ω) (evens a) 0 -
               ω ^ 0 * ntt_coeff_generic (ω * ω) (odds a) 0 =
               ntt_coeff_generic ω a (0 + n / 2)
          rw [hn2]
          exact (ntt_coeff_generic_n2_lower ω a hω2 halen).symm
        | succ e =>
          have hn_gt2 : n > 2 := by
            have h2e : 2 ^ (e + 1) ≥ 2 := by
              have : 2 ^ e ≥ 1 := Nat.one_le_pow e 2 (by norm_num)
              calc 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ, mul_comm]
                _ ≥ 2 * 1 := by omega
                _ = 2 := by ring
            show a.length > 2
            rw [hexp]; rw [Nat.pow_succ]; rw [mul_comm]
            omega
          exact (ntt_coeff_generic_split_upper ω a n hn_gt2 h_even rfl hω j
            (show j < n / 2 from hk_sub_lt)).symm
      · -- Case 3: k ≥ n (out of bounds)
        push_neg at hk_lt_n
        rw [List.getElem?_append_right
          (by simp [List.length_map, List.length_range]; omega)]
        simp only [List.length_map, List.length_range]
        rw [List.getElem?_eq_none
          (by simp [List.length_map, List.length_range]; omega)]
        rw [List.getElem?_eq_none]
        simp only [ntt_spec_generic, List.length_map, List.length_range]
        exact hk_lt_n
termination_by a.length
decreasing_by
  all_goals
    simp only [h_evens_len, h_odds_len, hexp, Nat.pow_succ]
    omega

end MainTheorem

/-! ## Part 5: Smoke Tests -/

section Tests

/-- ntt_generic = ntt_spec_generic for [1, 0] with ω = -1. -/
example : ntt_generic (-1 : ℚ) [1, 0] = ntt_spec_generic (-1 : ℚ) [1, 0] := by
  native_decide

/-- ntt_generic = ntt_spec_generic for [1, 1] with ω = -1. -/
example : ntt_generic (-1 : ℚ) [1, 1] = ntt_spec_generic (-1 : ℚ) [1, 1] := by
  native_decide

end Tests

end AmoLean.NTT.Generic
