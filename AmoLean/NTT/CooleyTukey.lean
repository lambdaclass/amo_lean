/-
  AMO-Lean: Cooley-Tukey Recursive NTT
  Phase 5: NTT Core - Layer 2

  This module implements the recursive Cooley-Tukey FFT algorithm
  for Number Theoretic Transform.

  Complexity: O(N log N)

  The algorithm:
    NTT(a) for |a| = n:
    1. If n = 1, return a
    2. Split a into evens and odds
    3. Recursively compute NTT(evens) and NTT(odds) with ω²
    4. Combine using butterfly: Xₖ = Eₖ + ωᵏ·Oₖ, Xₖ₊ₙ/₂ = Eₖ - ωᵏ·Oₖ
-/

import AmoLean.NTT.Field
import AmoLean.NTT.ListUtils
import AmoLean.NTT.Goldilocks
import AmoLean.NTT.Spec

namespace AmoLean.NTT

variable {F : Type*} [inst : NTTField F]

/-! ## Part 1: Cooley-Tukey Recursive NTT

    Note: The butterfly operation is defined in Butterfly.lean.
    Here we use inline butterfly logic to avoid import cycles.
-/

/-- Cooley-Tukey NTT: O(N log N) recursive algorithm

    Preconditions:
    - n = |a| must be a power of 2
    - ω must be a primitive n-th root of unity

    The recursion:
    - Base case: n=1 → return [a₀]
    - Recursive: split into evens/odds, recurse with ω², combine with butterfly -/
def NTT_recursive (ω : F) (a : List F) : List F :=
  match h : a with
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    let n := a.length
    let half := n / 2

    -- Split into even and odd indices
    let a_even := evens a
    let a_odd := odds a

    -- ω² is primitive (n/2)-th root (using standard * operator)
    let ω_squared := ω * ω

    -- Recursive calls (termination: evens/odds reduce list size)
    let E := NTT_recursive ω_squared a_even
    let O := NTT_recursive ω_squared a_odd

    -- Combine using butterfly operations (using standard operators)
    let upper := (List.range half).map fun k =>
      let twiddle := ω ^ k
      let ek := E[k]?.getD 0
      let ok := O[k]?.getD 0
      ek + twiddle * ok

    let lower := (List.range half).map fun k =>
      let twiddle := ω ^ k
      let ek := E[k]?.getD 0
      let ok := O[k]?.getD 0
      ek - twiddle * ok

    upper ++ lower
termination_by a.length
decreasing_by
  all_goals
    -- a = x :: y :: xs, so a.length = xs.length + 2
    -- evens a = x :: evens xs, so (evens a).length = 1 + (evens xs).length
    -- odds a = y :: odds xs, so (odds a).length = 1 + (odds xs).length
    simp only [h, evens, odds, List.length_cons]
    have he : (evens xs).length = (xs.length + 1) / 2 := evens_length xs
    have ho : (odds xs).length = xs.length / 2 := odds_length xs
    omega

/-! ## Part 3: Inverse NTT (Cooley-Tukey) -/

/-- Inverse NTT using Cooley-Tukey

    INTT(X) = (1/n) * NTT(X) with ω⁻¹

    For primitive root ω, we have ω⁻¹ = ω^(n-1) -/
def INTT_recursive (ω : F) (n_inv : F) (X : List F) : List F :=
  let n := X.length
  if h : n > 0 then
    -- ω⁻¹ = ω^(n-1) for primitive n-th root (using standard ^ operator)
    let ω_inv := ω ^ (n - 1)
    let result := NTT_recursive ω_inv X
    -- Multiply each element by n⁻¹ (using standard * operator)
    result.map (n_inv * ·)
  else
    []

/-! ## Part 4: Length Theorem -/

/-- NTT_recursive preserves length for power-of-2 sized lists

    Note: This property ONLY holds for power-of-2 lengths. For other lengths,
    the recursive splitting causes data loss. -/
theorem NTT_recursive_length (ω : F) (a : List F)
    (hpow2 : ∃ k : ℕ, a.length = 2^k) :
    (NTT_recursive ω a).length = a.length := by
  -- Match on the list structure
  match a with
  | [] =>
    -- Base case: [] → []
    simp only [NTT_recursive]
  | [x] =>
    -- Base case: [x] → [x] (2^0 = 1)
    simp only [NTT_recursive, List.length_singleton]
  | x :: y :: xs =>
    -- Recursive case
    simp only [NTT_recursive]
    -- After unfolding, we have upper ++ lower where each has length n/2
    simp only [List.length_append, List.length_map, List.length_range]
    -- For power-of-2 n ≥ 2, n is even so n/2 + n/2 = n
    obtain ⟨k, hk⟩ := hpow2
    have hn : (x :: y :: xs).length ≥ 2 := by simp
    -- 2^k ≥ 2 implies k ≥ 1, so 2^k is even
    have hk_ge : k ≥ 1 := by
      cases k with
      | zero =>
        -- 2^0 = 1, but length ≥ 2
        simp only [List.length_cons] at hk
        omega
      | succ k' => omega
    have heven : 2 ∣ (x :: y :: xs).length := by
      rw [hk]
      -- 2 divides 2^k for k ≥ 1
      cases k with
      | zero => omega -- contradiction: k ≥ 1 but k = 0
      | succ k' =>
        -- 2^(k'+1) = 2^k' * 2, and 2 | (m * 2)
        rw [Nat.pow_succ]
        exact Nat.dvd_mul_left 2 _
    -- n/2 + n/2 = n for even n
    obtain ⟨m, hm⟩ := heven
    simp only [hm]
    omega

/-! ## Part 5: Unfolding Lemma for Correctness Proof -/

/-- Unfolding lemma: NTT_recursive on a list of length ≥ 2 equals upper ++ lower

    This lemma exposes the structure of NTT_recursive without let bindings,
    making it suitable for use in the correctness proof.
-/
theorem NTT_recursive_unfold (ω : F) (a : List F) (ha : a.length ≥ 2) :
    NTT_recursive ω a =
    let half := a.length / 2
    let E := NTT_recursive (ω * ω) (evens a)
    let O := NTT_recursive (ω * ω) (odds a)
    let upper := (List.range half).map fun k =>
      E[k]?.getD 0 + ω ^ k * O[k]?.getD 0
    let lower := (List.range half).map fun k =>
      E[k]?.getD 0 - ω ^ k * O[k]?.getD 0
    upper ++ lower := by
  -- a has length ≥ 2, so it matches x :: y :: xs
  match h : a with
  | [] => simp at ha
  | [_] => simp at ha
  | x :: y :: xs =>
    -- Unfold NTT_recursive for the x :: y :: xs case
    simp only [NTT_recursive, h]
    -- The structure matches directly (simp already closes the goal)

/-- Element access for NTT_recursive upper half (k < n/2) -/
theorem NTT_recursive_getElem_upper (ω : F) (a : List F) (ha : a.length ≥ 2) (k : ℕ)
    (hk : k < a.length / 2) :
    (NTT_recursive ω a)[k]? =
    some ((NTT_recursive (ω * ω) (evens a))[k]?.getD 0 +
          ω ^ k * (NTT_recursive (ω * ω) (odds a))[k]?.getD 0) := by
  rw [NTT_recursive_unfold ω a ha]
  simp only []
  rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; exact hk)]
  rw [List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some']

/-- Element access for NTT_recursive lower half (n/2 ≤ k < n) -/
theorem NTT_recursive_getElem_lower (ω : F) (a : List F) (ha : a.length ≥ 2)
    (heven : 2 ∣ a.length) (k : ℕ) (hk_ge : k ≥ a.length / 2) (hk_lt : k < a.length) :
    (NTT_recursive ω a)[k]? =
    some ((NTT_recursive (ω * ω) (evens a))[k - a.length / 2]?.getD 0 -
          ω ^ (k - a.length / 2) * (NTT_recursive (ω * ω) (odds a))[k - a.length / 2]?.getD 0) := by
  rw [NTT_recursive_unfold ω a ha]
  simp only []
  have h_upper_len : ((List.range (a.length / 2)).map fun k =>
      (NTT_recursive (ω * ω) (evens a))[k]?.getD 0 +
      ω ^ k * (NTT_recursive (ω * ω) (odds a))[k]?.getD 0).length = a.length / 2 := by
    simp only [List.length_map, List.length_range]
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; exact hk_ge)]
  simp only [List.length_map, List.length_range]
  have hk_sub : k - a.length / 2 < a.length / 2 := by
    have h2 := Nat.mul_div_cancel' heven
    omega
  rw [List.getElem?_map, List.getElem?_range hk_sub]
  simp only [Option.map_some']

/-- NTT_recursive returns none for indices ≥ length -/
theorem NTT_recursive_getElem_none (ω : F) (a : List F) (k : ℕ)
    (hpow2 : ∃ e : ℕ, a.length = 2^e) (hk : k ≥ a.length) :
    (NTT_recursive ω a)[k]? = none := by
  rw [List.getElem?_eq_none]
  rw [NTT_recursive_length ω a hpow2]
  exact hk

/-! ## Part 6: Quick Tests -/

section Tests

open AmoLean.Field.Goldilocks

/-- Helper to extract values -/
def gfVal' (x : GoldilocksField) : UInt64 := x.value

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   Cooley-Tukey NTT Tests"
  IO.println "═══════════════════════════════════════════════════════════"

  -- Test 1: Basic N=4
  IO.println "\n1. NTT_recursive vs NTT_spec (N=4):"
  let n := 4
  let ω := primitiveRoot n (by decide)
  let input : List GoldilocksField := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩]

  let spec_result : List GoldilocksField := NTT_spec ω input
  let rec_result : List GoldilocksField := NTT_recursive ω input

  IO.println s!"   Input:       {input.map gfVal'}"
  IO.println s!"   NTT_spec:    {spec_result.map gfVal'}"
  IO.println s!"   NTT_recursive: {rec_result.map gfVal'}"
  IO.println s!"   Match: {spec_result.map gfVal' == rec_result.map gfVal'}"

  -- Test 2: N=8
  IO.println "\n2. NTT_recursive vs NTT_spec (N=8):"
  let n8 := 8
  let ω8 := primitiveRoot n8 (by decide)
  let input8 : List GoldilocksField := (List.range 8).map fun i => ⟨(i + 1).toUInt64⟩

  let spec8 : List GoldilocksField := NTT_spec ω8 input8
  let rec8 : List GoldilocksField := NTT_recursive ω8 input8

  IO.println s!"   Input:       {input8.map gfVal'}"
  IO.println s!"   NTT_spec:    {spec8.map gfVal'}"
  IO.println s!"   NTT_recursive: {rec8.map gfVal'}"
  IO.println s!"   Match: {spec8.map gfVal' == rec8.map gfVal'}"

  -- Test 3: Roundtrip
  IO.println "\n3. Roundtrip INTT_recursive(NTT_recursive(x)) = x (N=8):"
  let n_inv8 := GoldilocksField.inv ⟨8⟩
  let roundtrip8 : List GoldilocksField := INTT_recursive ω8 n_inv8 rec8

  IO.println s!"   Input:    {input8.map gfVal'}"
  IO.println s!"   Roundtrip: {roundtrip8.map gfVal'}"
  IO.println s!"   Match: {input8.map gfVal' == roundtrip8.map gfVal'}"

  -- Test 4: N=16
  IO.println "\n4. NTT_recursive vs NTT_spec (N=16):"
  let n16 := 16
  let ω16 := primitiveRoot n16 (by decide)
  let input16 : List GoldilocksField := (List.range 16).map fun i => ⟨(i + 1).toUInt64⟩

  let spec16 : List GoldilocksField := NTT_spec ω16 input16
  let rec16 : List GoldilocksField := NTT_recursive ω16 input16

  IO.println s!"   Match: {spec16.map gfVal' == rec16.map gfVal'}"

  IO.println "\n═══════════════════════════════════════════════════════════"

end Tests

end AmoLean.NTT
