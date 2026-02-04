/-
  AMO-Lean: NTT Correctness Proofs
  Phase 5: NTT Core - Task 3.2

  This module proves that NTT_recursive computes the same result as NTT_spec.
  This is the central correctness theorem for the Cooley-Tukey implementation.

  Main Theorem:
    ct_recursive_eq_spec: NTT_recursive ω input = NTT_spec ω input

  Proof Strategy:
  1. Show base case (N=1): Both return the single element
  2. Show inductive case: The butterfly combination produces correct coefficients
  3. Use the Cooley-Tukey recurrence relation to link recursive and spec definitions
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Spec
import AmoLean.NTT.CooleyTukey
import AmoLean.NTT.Goldilocks
import AmoLean.NTT.Properties
import AmoLean.NTT.Phase3Proof
import AmoLean.NTT.ListFinsetBridge

namespace AmoLean.NTT

/-! ## Part 1: Base Case -/

section BaseCase

-- Use only NTTFieldLawful to avoid instance diamond with NTTField
variable {F : Type*} [NTTFieldLawful F]

/-- Base case: NTT_recursive of a single element is just that element -/
theorem ntt_recursive_singleton (ω : F) (x : F) :
    NTT_recursive ω [x] = [x] := by
  unfold NTT_recursive
  simp only [List.length_singleton, ↓reduceDIte, decide_true]

/-- Base case equality: Both NTT implementations agree on singletons

    The proof uses: ω^0 = 1, x * 1 = x, 0 + x = x
-/
theorem ntt_eq_singleton (ω : F) (x : F) :
    NTT_recursive ω [x] = NTT_spec ω [x] := by
  rw [ntt_recursive_singleton]
  rw [NTT_spec_singleton]
  -- Goal: [x] = [Add.add 0 (Mul.mul x (ω^0))]
  congr 1
  -- ω^0 = 1 from Mathlib's pow_zero
  rw [pow_zero]
  -- Goal: x = Add.add 0 (Mul.mul x 1)
  -- Add.add and Mul.mul are just + and * in notation
  show x = 0 + x * 1
  ring

end BaseCase

/-! ## Part 2: Cooley-Tukey Recurrence

These lemmas connect Phase3Proof results to the NTT_spec list formulation.
-/

section CTRecurrence

variable {F : Type*} [NTTFieldLawful F] [IsDomain F]

/-- The Cooley-Tukey recurrence: X_k = E_k + ω^k · O_k for k < n/2

    Uses Phase3Proof.NTT_spec_upper_half_eq
-/
theorem cooley_tukey_upper_half {n : ℕ} (hn : n > 0) (hn_even : 2 ∣ n)
    (ω : F) (hω : IsPrimitiveRoot ω n)
    (input : List F) (h_len : input.length = n)
    (E O : List F) (hE : E = NTT_spec (ω * ω) (evens input))
    (hO : O = NTT_spec (ω * ω) (odds input))
    (k : ℕ) (hk : k < n / 2) :
    (NTT_spec ω input)[k]? =
    some ((E[k]?.getD 0) + (ω ^ k) * (O[k]?.getD 0)) := by
  -- Direct from Phase3Proof.NTT_spec_upper_half_eq
  have hk' : k < input.length / 2 := by rw [h_len]; exact hk
  have heven' : 2 ∣ input.length := by rw [h_len]; exact hn_even
  have h := Phase3Proof.NTT_spec_upper_half_eq ω input heven' k hk'
  -- Connect ntt_coeff to list access
  have hevens_len : (evens input).length = input.length / 2 :=
    Phase3Proof.evens_length_even input heven'
  have hodds_len : (odds input).length = input.length / 2 := odds_length input
  have hE_get : (NTT_spec (ω * ω) (evens input))[k]? = some (ntt_coeff (ω * ω) (evens input) k) := by
    apply Phase3Proof.ntt_spec_getElem_eq_coeff
    rw [hevens_len]; exact hk'
  have hO_get : (NTT_spec (ω * ω) (odds input))[k]? = some (ntt_coeff (ω * ω) (odds input) k) := by
    apply Phase3Proof.ntt_spec_getElem_eq_coeff
    rw [hodds_len]; exact hk'
  -- Rewrite using h, then substitute E and O
  rw [h, hE, hO, hE_get, hO_get]
  simp only [Option.getD_some]
  -- Add.add and + are the same
  rfl

/-- The Cooley-Tukey recurrence for lower half: X_{k+n/2} = E_k - ω^k · O_k

    Uses Phase3Proof.ntt_coeff_lower_half_split
-/
theorem cooley_tukey_lower_half {n : ℕ} (hn : n > 2) (hn_even : 2 ∣ n)
    (ω : F) (hω : IsPrimitiveRoot ω n)
    (input : List F) (h_len : input.length = n)
    (E O : List F) (hE : E = NTT_spec (ω * ω) (evens input))
    (hO : O = NTT_spec (ω * ω) (odds input))
    (k : ℕ) (hk : k < n / 2) :
    (NTT_spec ω input)[k + n/2]? =
    some ((E[k]?.getD 0) - (ω ^ k) * (O[k]?.getD 0)) := by
  -- Use Phase3Proof.ntt_coeff_lower_half_split
  have h_coeff := Phase3Proof.ntt_coeff_lower_half_split ω input n hn hn_even h_len hω k hk
  -- Connect to NTT_spec
  have h_idx : k + n / 2 < input.length := by
    rw [h_len]
    -- n / 2 + n / 2 = n for even n
    have h2 : n / 2 + n / 2 = n := by
      have := Nat.mul_div_cancel' hn_even  -- 2 * (n/2) = n
      omega
    omega
  have h_spec : (NTT_spec ω input)[k + n/2]? = some (ntt_coeff ω input (k + n / 2)) :=
    Phase3Proof.ntt_spec_getElem_eq_coeff ω input (k + n / 2) h_idx
  rw [h_spec, h_coeff, hE, hO]
  -- Connect ntt_coeff to list access
  have heven' : 2 ∣ input.length := by rw [h_len]; exact hn_even
  have hk' : k < input.length / 2 := by rw [h_len]; exact hk
  have hevens_len : (evens input).length = input.length / 2 :=
    Phase3Proof.evens_length_even input heven'
  have hodds_len : (odds input).length = input.length / 2 := odds_length input
  have hE_get : (NTT_spec (ω * ω) (evens input))[k]? = some (ntt_coeff (ω * ω) (evens input) k) := by
    apply Phase3Proof.ntt_spec_getElem_eq_coeff
    rw [hevens_len]; exact hk'
  have hO_get : (NTT_spec (ω * ω) (odds input))[k]? = some (ntt_coeff (ω * ω) (odds input) k) := by
    apply Phase3Proof.ntt_spec_getElem_eq_coeff
    rw [hodds_len]; exact hk'
  simp only [hE_get, hO_get, Option.getD_some]

end CTRecurrence

/-! ## Part 3: Main Correctness Theorem -/

section MainTheorem

variable {F : Type*} [NTTFieldLawful F] [IsDomain F]

/-- Helper: The recursive NTT produces a list of the correct length
    Note: This only holds for power-of-2 lengths; see NTT_recursive_length in CooleyTukey.lean -/
theorem ntt_recursive_length_eq (ω : F) (input : List F)
    (hpow2 : ∃ k : ℕ, input.length = 2^k) :
    (NTT_recursive ω input).length = input.length :=
  NTT_recursive_length ω input hpow2

/-- The central correctness theorem: NTT_recursive computes NTT_spec

    This theorem establishes that our O(n log n) Cooley-Tukey implementation
    produces identical results to the O(n²) specification.

    Requires:
    - input.length is a power of 2
    - ω is a primitive input.length-th root of unity
-/
theorem ct_recursive_eq_spec (ω : F) (input : List F)
    (h_pow2 : ∃ k : ℕ, input.length = 2^k)
    (hω : IsPrimitiveRoot ω input.length) :
    NTT_recursive ω input = NTT_spec ω input := by
  -- We prove by strong induction on input.length
  -- The key insight: if input.length = 2^k, then evens/odds have length 2^(k-1)
  obtain ⟨exp, hexp⟩ := h_pow2

  -- Base case: exp = 0 means length = 1
  cases exp with
  | zero =>
    -- input.length = 1, so input is a singleton
    have h_len : input.length = 1 := by simp [hexp]
    match h : input with
    | [] => simp at h_len
    | [x] => exact ntt_eq_singleton ω x
    | _ :: _ :: _ => simp at h_len

  | succ exp' =>
    -- input.length = 2^(exp'+1) ≥ 2
    have h_len_ge2 : input.length ≥ 2 := by
      rw [hexp, Nat.pow_succ]
      have h2e : 2^exp' ≥ 1 := Nat.one_le_pow exp' 2 (by norm_num)
      omega

    have h_even : 2 ∣ input.length := by
      rw [hexp, Nat.pow_succ]
      exact Nat.dvd_mul_left 2 _

    -- The sublists have length 2^exp' < 2^(exp'+1) = input.length
    have h_evens_len : (evens input).length = 2^exp' := by
      rw [Phase3Proof.evens_length_even input h_even, hexp, Nat.pow_succ]
      simp [Nat.mul_div_cancel_left]

    have h_odds_len : (odds input).length = 2^exp' := by
      rw [odds_length, hexp, Nat.pow_succ]
      simp [Nat.mul_div_cancel_left]

    have h_evens_pow2 : ∃ k', (evens input).length = 2^k' := ⟨exp', h_evens_len⟩
    have h_odds_pow2 : ∃ k', (odds input).length = 2^k' := ⟨exp', h_odds_len⟩

    -- Prove ω² is primitive root for the subproblems
    have hω_sq : IsPrimitiveRoot (ω * ω) (evens input).length := by
      cases exp' with
      | zero =>
        -- exp' = 0, so evens.length = 1, input.length = 2
        have h_input_len : input.length = 2 := by simp [hexp]
        have h_omega_sq : ω * ω = 1 := by
          have := hω.pow_eq_one
          rw [h_input_len] at this
          simpa [sq] using this
        rw [h_evens_len, h_omega_sq]
        -- Goal: IsPrimitiveRoot 1 1
        exact ⟨by ring, fun d hd _ => by omega⟩
      | succ e =>
        -- exp' ≥ 1, so evens.length ≥ 2, input.length ≥ 4
        have hn_ge4 : input.length ≥ 4 := by
          simp only [hexp, Nat.pow_succ]
          have : 2 * 2^(e + 1) = 2 * 2 * 2^e := by ring
          omega
        have hsq := squared_is_primitive (n := input.length) hn_ge4 h_even hω
        -- hsq : IsPrimitiveRoot (ω^2) (input.length / 2)
        -- We need: IsPrimitiveRoot (ω*ω) (evens input).length
        have h_half : (evens input).length = input.length / 2 :=
          Phase3Proof.evens_length_even input h_even
        rw [h_half, ← sq]
        exact hsq

    have hω_sq_odds : IsPrimitiveRoot (ω * ω) (odds input).length := by
      rw [h_odds_len, ← h_evens_len]; exact hω_sq

    -- Apply recursive calls (termination guaranteed by NTT_recursive's termination proof)
    have ih_evens : NTT_recursive (ω * ω) (evens input) = NTT_spec (ω * ω) (evens input) :=
      ct_recursive_eq_spec (ω * ω) (evens input) h_evens_pow2 hω_sq

    have ih_odds : NTT_recursive (ω * ω) (odds input) = NTT_spec (ω * ω) (odds input) :=
      ct_recursive_eq_spec (ω * ω) (odds input) h_odds_pow2 hω_sq_odds

    -- Use the unfolding lemma and prove equality element-wise
    rw [NTT_recursive_unfold ω input h_len_ge2]

    -- Now prove equality using List.ext_getElem?
    apply List.ext_getElem?
    intro k

    let n := input.length
    let half := n / 2

    have h_half_half : half + half = n := by
      have := Nat.mul_div_cancel' h_even
      omega

    -- Rewrite using IH
    simp only [ih_evens, ih_odds]

    -- Case split on k
    by_cases hk_lt_half : k < half
    · -- Case 1: k < half (upper part)
      rw [List.getElem?_append_left (by simp [List.length_map, List.length_range]; exact hk_lt_half)]
      rw [List.getElem?_map, List.getElem?_range hk_lt_half]
      simp only [Option.map_some']
      -- Use cooley_tukey_upper_half
      have hn_pos : n > 0 := by omega
      have hk' : k < n / 2 := hk_lt_half
      let E := NTT_spec (ω * ω) (evens input)
      let O := NTT_spec (ω * ω) (odds input)
      rw [cooley_tukey_upper_half hn_pos h_even ω hω input rfl E O rfl rfl k hk']
    · -- k ≥ half
      push_neg at hk_lt_half
      by_cases hk_lt_n : k < n
      · -- Case 2: half ≤ k < n (lower part)
        rw [List.getElem?_append_right (by simp [List.length_map, List.length_range]; exact hk_lt_half)]
        simp only [List.length_map, List.length_range]
        have hk_sub_lt : k - half < half := by omega
        rw [List.getElem?_map, List.getElem?_range hk_sub_lt]
        simp only [Option.map_some']
        -- Use cooley_tukey_lower_half (need n > 2)
        let j := k - half
        have hj : j < n / 2 := hk_sub_lt
        have hj_add : j + n / 2 = k := by omega
        let E := NTT_spec (ω * ω) (evens input)
        let O := NTT_spec (ω * ω) (odds input)
        -- Case split: exp' = 0 (n = 2) vs exp' > 0 (n > 2)
        -- Need to show: some (E[k - half].getD 0 - ω^(k-half) * O[k - half].getD 0) = (NTT_spec ω input)[k]?
        -- Use j = k - half
        have hj_eq : k - half = j := rfl
        rw [hj_eq]
        -- Goal: some (E[j].getD 0 - ω^j * O[j].getD 0) = (NTT_spec ω input)[k]?
        -- Rewrite k = j + half
        have hk_eq : k = j + half := by omega
        rw [hk_eq]
        -- Goal: some (E[j].getD 0 - ω^j * O[j].getD 0) = (NTT_spec ω input)[j + half]?
        -- Since half = n / 2:
        -- Goal: some (E[j].getD 0 - ω^j * O[j].getD 0) = (NTT_spec ω input)[j + n/2]?
        cases exp' with
        | zero =>
          -- n = 2, so half = 1, j = 0
          -- For n=2: (NTT_spec ω input)[1] = E[0] - O[0] = input[0] - input[1]
          -- Since ω is primitive 2nd root: ω = -1, ω² = 1
          have hn2 : n = 2 := by omega
          have hhalf1 : half = 1 := by omega
          have hj0 : j = 0 := by omega
          have h_input_len : input.length = 2 := by omega
          have heven' : 2 ∣ input.length := ⟨1, by omega⟩
          rw [hj0, hhalf1]
          simp only [pow_zero, one_mul, Nat.add_zero]
          -- Match on input to extract its two elements
          match h_input : input with
          | [] => simp at h_input_len
          | [_] => simp at h_input_len
          | a :: b :: rest =>
            -- rest must be empty for length = 2
            have h_rest : rest = [] := by
              simp only [List.length_cons] at h_input_len
              cases rest with
              | nil => rfl
              | cons _ _ => simp at h_input_len
            simp only [h_rest] at h_input ⊢
            -- Now input = [a, b], evens = [a], odds = [b]
            have h_evens : evens [a, b] = [a] := by simp [evens]
            have h_odds : odds [a, b] = [b] := by simp [odds]
            simp only [h_evens, h_odds]
            -- For ω² = 1, NTT_spec 1 [x] = [x * 1] = [x]
            have hω2 : IsPrimitiveRoot ω 2 := by
              have : (a :: b :: rest).length = 2 := h_input_len
              simp only [this, h_input] at hω ⊢
              exact hω
            have h_omega_sq : ω * ω = 1 := by
              have h := Phase3Proof.primitive_root_two_sq hω2
              rw [sq] at h
              exact h
            have h_neg1 : ω = -1 := Phase3Proof.primitive_root_two_eq_neg_one hω2
            -- NTT_spec 1 [x] = [x] (since 0 + x * 1^0 = x)
            have hE : NTT_spec (ω * ω) [a] = [a] := by
              rw [h_omega_sq, NTT_spec_singleton]
              congr 1
              show (0 : F) + a * ((1 : F) ^ 0) = a
              ring
            have hO : NTT_spec (ω * ω) [b] = [b] := by
              rw [h_omega_sq, NTT_spec_singleton]
              congr 1
              show (0 : F) + b * ((1 : F) ^ 0) = b
              ring
            simp only [hE, hO]
            -- Goal: some ([a][0]?.getD 0 - [b][0]?.getD 0) = (NTT_spec ω [a, b])[1]?
            simp only [List.getElem?_cons_zero, Option.getD_some]
            -- Now: some (a - b) = (NTT_spec ω [a, b])[1]?
            -- Compute NTT_spec ω [a, b]
            have h_spec1 : (NTT_spec ω [a, b])[1]? = some (ntt_coeff ω [a, b] 1) := by
              apply Phase3Proof.ntt_spec_getElem_eq_coeff
              simp
            rw [h_spec1]
            congr 1
            -- ntt_coeff ω [a, b] 1 = a * ω^0 + b * ω^1 = a + b * (-1) = a - b
            -- ntt_coeff uses foldl, so we expand it manually for n=2
            unfold ntt_coeff
            simp only [List.length_cons, List.length_nil]
            -- Show List.range 2 = [0, 1]
            have hr2 : List.range 2 = [0, 1] := by native_decide
            rw [hr2]
            simp only [List.foldl_cons, List.foldl_nil]
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil]
            rw [h_neg1]
            simp only [Nat.zero_mul, Nat.one_mul, pow_zero, pow_one, mul_one]
            -- Goal: a - b = Add.add (Add.add 0 (Mul.mul a 1)) (Mul.mul b (-1))
            -- = (0 + a * 1) + b * (-1) = a + b * (-1) = a - b
            show a - b = (0 + a * 1) + b * (-1)
            ring
        | succ e =>
          -- exp' ≥ 1, so n ≥ 4 > 2
          -- hexp now says: input.length = 2^((e+1)+1) = 2^(e+2)
          have h_n_val : n = 2^(e + 2) := by simp only [hexp, Nat.pow_succ, Nat.pow_add]; omega
          have h2_ge : 2^(e+2) ≥ 4 := by
            have he1 : 2^e ≥ 1 := Nat.one_le_pow e 2 (by norm_num)
            have : 2^(e+2) = 2^e * 4 := by simp only [Nat.pow_succ, Nat.pow_add]; omega
            omega
          have hn_gt2 : n > 2 := by omega
          have h_lower := cooley_tukey_lower_half hn_gt2 h_even ω hω input rfl E O rfl rfl j hj
          -- h_lower : (NTT_spec ω input)[j + n / 2]? = some (E[j]?.getD 0 - ω ^ j * O[j]?.getD 0)
          -- Goal: some (E[j]?.getD 0 - ω^j * O[j]?.getD 0) = (NTT_spec ω input)[j + half]?
          -- Since half = n / 2, just use h_lower
          rw [h_lower]
      · -- Case 3: k ≥ n
        push_neg at hk_lt_n
        rw [List.getElem?_append_right (by simp [List.length_map, List.length_range]; omega)]
        simp only [List.length_map, List.length_range]
        rw [List.getElem?_eq_none (by simp [List.length_map, List.length_range]; omega)]
        rw [List.getElem?_eq_none]
        simp only [NTT_spec, List.length_map, List.length_range]
        exact hk_lt_n
termination_by input.length
decreasing_by
  all_goals
    simp_wf
    -- evens/odds have length = input.length / 2 < input.length for input.length ≥ 2
    simp only [h_evens_len, h_odds_len, hexp, Nat.pow_succ]
    omega

/-- Corollary: NTT roundtrip works for recursive version -/
theorem ntt_intt_recursive_roundtrip (ω n_inv : F) (input : List F)
    (h_pow2 : ∃ k : ℕ, input.length = 2^k)
    (hω : IsPrimitiveRoot ω input.length)
    (h_inv : n_inv * (input.length : F) = 1) :
    INTT_recursive ω n_inv (NTT_recursive ω input) = input := by
  -- By correctness, NTT_recursive = NTT_spec
  have h_ntt := ct_recursive_eq_spec ω input h_pow2 hω
  rw [h_ntt]
  -- INTT_recursive = INTT_spec (from ListFinsetBridge)
  by_cases hne : input = []
  · -- Empty input case
    subst hne
    simp only [NTT_spec_nil, INTT_recursive, List.length_nil]
    -- 0 > 0 is false, so the if returns []
    simp
  · -- Non-empty input
    have h_intt_eq := intt_recursive_eq_spec ω n_inv (NTT_spec ω input)
        (by rw [NTT_spec_length]; exact h_pow2)
        (by rw [NTT_spec_length]; exact hω)
        (by intro h; have := congrArg List.length h; simp [NTT_spec_length] at this; exact hne this)
    rw [h_intt_eq]
    -- Now use INTT_spec(NTT_spec(input)) = input
    -- This requires n > 1 for the Finset roundtrip theorem
    obtain ⟨exp, hexp⟩ := h_pow2
    cases exp with
    | zero =>
      -- n = 1, degenerate case: single element [x]
      -- For n=1, NTT_spec ω [x] = [x] and INTT_spec ω 1 [x] = [x]
      have h_len : input.length = 1 := by simp [hexp]
      match h : input with
      | [] => simp at h_len
      | [x] =>
        -- h_inv : n_inv * ↑[x].length = 1, and [x].length = 1
        have h_inv' : n_inv * (1 : F) = 1 := by
          simp only [List.length_singleton, Nat.cast_one] at h_inv
          exact h_inv
        exact INTT_NTT_singleton_roundtrip ω n_inv x h_inv'
      | _ :: _ :: _ => simp at h_len
    | succ e =>
      -- n = 2^(e+1) ≥ 2, so n > 1
      have hn_gt1 : input.length > 1 := by
        rw [hexp]
        have : 2^(e+1) ≥ 2 := by
          have h2e : 2^e ≥ 1 := Nat.one_le_pow e 2 (by norm_num)
          simp only [Nat.pow_succ]; omega
        omega
      -- Use the List roundtrip theorem from ListFinsetBridge
      exact ntt_intt_identity_list hn_gt1 ω n_inv hω h_inv input rfl

end MainTheorem

/-! ## Part 4: Testing Consistency -/

section TestConsistency

open AmoLean.Field.Goldilocks

/-- Compile-time verification for small sizes -/
example : NTT_recursive (primitiveRoot 4 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] =
          NTT_spec (primitiveRoot 4 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] := by
  native_decide

example : NTT_recursive (primitiveRoot 8 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩] =
          NTT_spec (primitiveRoot 8 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩] := by
  native_decide

end TestConsistency

end AmoLean.NTT
