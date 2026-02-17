/-
  Phase 3: Cooley-Tukey Correctness Proofs

  Auxiliary lemmas for proving:
  - S8: cooley_tukey_upper_half
  - S9: cooley_tukey_lower_half
  - S10: ct_recursive_eq_spec

  See docs/project/PHASE3_COOLEY_TUKEY_STRATEGY.md for full strategy.
-/

import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Spec
import AmoLean.NTT.Properties
import AmoLean.NTT.ListUtils
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AmoLean.NTT.Phase3Proof

open AmoLean.NTT

/-!
## Layer 1: Fundamental Lemmas
-/

section PrimitiveRootTwo

variable {F : Type*} [CommRing F] [IsDomain F]

/-- For n = 2, a primitive root must be -1.

    Proof: ω² = 1 and ω ≠ 1 implies (ω-1)(ω+1) = 0.
    Since ω ≠ 1, we have ω + 1 = 0, so ω = -1.

    This handles the n = 2 edge case uniformly without special-casing
    in the main Cooley-Tukey theorems.
-/
theorem primitive_root_two_eq_neg_one {ω : F} (hω : IsPrimitiveRoot ω 2) :
    ω = -1 := by
  -- ω² = 1
  have h_sq : ω ^ 2 = 1 := hω.pow_eq_one
  -- ω ≠ 1 (because ω^1 ≠ 1 for a primitive 2nd root)
  have h_ne : ω ≠ 1 := hω.ne_one (by omega)
  -- (ω - 1)(ω + 1) = ω² - 1 = 0
  have h_prod : (ω - 1) * (ω + 1) = 0 := by
    calc (ω - 1) * (ω + 1) = ω ^ 2 - 1 := by ring
      _ = 1 - 1 := by rw [h_sq]
      _ = 0 := by ring
  -- In a domain, one factor must be zero
  rcases mul_eq_zero.mp h_prod with h | h
  · -- ω - 1 = 0 contradicts ω ≠ 1
    exact absurd (sub_eq_zero.mp h) h_ne
  · -- ω + 1 = 0 means ω = -1
    exact add_eq_zero_iff_eq_neg.mp h

/-- Alternative formulation: primitive 2nd root squared is 1 -/
theorem primitive_root_two_sq {ω : F} (hω : IsPrimitiveRoot ω 2) :
    ω ^ 2 = 1 := hω.pow_eq_one

end PrimitiveRootTwo

/-!
## Layer 1: Twiddle Factor Lemmas

These lemmas relate powers of ω to powers of ω².
Essential for the DFT splitting formula.
-/

section TwiddleFactors

variable {F : Type*} [CommRing F]

/-- ω^(2mk) = (ω²)^(mk)

    This relates the twiddle factor for even indices to ω².
-/
theorem twiddle_even_factor (ω : F) (m k : ℕ) :
    ω ^ (2 * m * k) = (ω ^ 2) ^ (m * k) := by
  rw [← pow_mul]
  congr 1
  ring

/-- ω^((2m+1)k) = ω^k · (ω²)^(mk)

    This relates the twiddle factor for odd indices to ω² with an ω^k factor.
-/
theorem twiddle_odd_factor (ω : F) (m k : ℕ) :
    ω ^ ((2 * m + 1) * k) = ω ^ k * (ω ^ 2) ^ (m * k) := by
  rw [← pow_mul]
  have h : (2 * m + 1) * k = k + 2 * m * k := by ring
  rw [h, pow_add]
  congr 1
  ring

/-- Variant: ω^(2m·k) expressed differently -/
theorem twiddle_even_factor' (ω : F) (m k : ℕ) :
    ω ^ (2 * (m * k)) = (ω ^ 2) ^ (m * k) := by
  rw [← pow_mul]

/-- For any m, 2m is even (useful for index arithmetic) -/
theorem two_mul_even (m : ℕ) : 2 ∣ (2 * m) := ⟨m, rfl⟩

/-- For any m, 2m+1 is odd -/
theorem two_mul_add_one_odd (m : ℕ) : (2 * m + 1) % 2 = 1 := by omega

end TwiddleFactors

/-!
## Layer 1b: Twiddle Factors for NTTFieldLawful

Alternative versions of twiddle factor lemmas that use HPow.hPow instead of CommRing ^.
These are needed because GoldilocksField has NTTFieldLawful but not CommRing.
-/

section TwiddleFactorsNTT

variable {F : Type*} [inst : NTTFieldLawful F]

/-- ω^(2mk) = (ω²)^(mk) using HPow.hPow

    Uses pow_mul: pow a (m * n) = pow (pow a m) n
-/
theorem twiddle_even_factor_ntt (ω : F) (m k : ℕ) :
    HPow.hPow ω (2 * m * k) = HPow.hPow (HPow.hPow ω 2) (m * k) := by
  -- 2 * m * k = 2 * (m * k)
  have h : 2 * m * k = 2 * (m * k) := by ring
  rw [h]
  exact pow_mul ω 2 (m * k)

/-- ω^((2m+1)k) = ω^k · (ω²)^(mk) using HPow.hPow

    Uses pow_add and pow_mul
-/
theorem twiddle_odd_factor_ntt (ω : F) (m k : ℕ) :
    HPow.hPow ω ((2 * m + 1) * k) = HPow.hPow ω k * HPow.hPow (HPow.hPow ω 2) (m * k) := by
  -- (2m+1)*k = k + 2*m*k = k + 2*(m*k)
  have h1 : (2 * m + 1) * k = k + 2 * (m * k) := by ring
  rw [h1]
  -- pow ω (k + 2*(m*k)) = pow ω k * pow ω (2*(m*k))
  rw [pow_add]
  -- pow ω (2*(m*k)) = pow (pow ω 2) (m*k)
  rw [pow_mul]

/-- pow ω 2 = ω * ω -/
theorem pow_2_eq_mul_ntt (ω : F) : HPow.hPow ω 2 = ω * ω := by
  rw [sq]

end TwiddleFactorsNTT

/-!
## Layer 1: NTT Length Preservation

These lemmas ensure that NTT_spec preserves list length.
-/

section NTTLength

variable {F : Type*} [inst : NTTField F]

/-- NTT_spec preserves length (re-export for convenience) -/
theorem ntt_spec_length (ω : F) (a : List F) :
    (NTT_spec ω a).length = a.length :=
  NTT_spec_length ω a

/-- For valid index k < n, (NTT_spec ω a)[k]? is some -/
theorem ntt_spec_getElem_some (ω : F) (a : List F) (k : ℕ) (hk : k < a.length) :
    ∃ x, (NTT_spec ω a)[k]? = some x := by
  have hlen : k < (NTT_spec ω a).length := by
    rw [ntt_spec_length]
    exact hk
  exact ⟨(NTT_spec ω a)[k]'hlen, List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩⟩

/-- NTT_spec at valid index equals ntt_coeff -/
theorem ntt_spec_getElem_eq_coeff (ω : F) (a : List F) (k : ℕ) (hk : k < a.length) :
    (NTT_spec ω a)[k]? = some (ntt_coeff ω a k) := by
  simp only [NTT_spec, List.getElem?_map]
  have hr : (List.range a.length)[k]? = some k := by
    rw [List.getElem?_range hk]
  rw [hr]
  rfl

end NTTLength

/-!
## Layer 1: Index Arithmetic Helpers

Lemmas to simplify index calculations in Cooley-Tukey proofs.
-/

section IndexArithmetic

/-- 2 * (n / 2) = n when n is even -/
theorem two_mul_half_eq (n : ℕ) (hn : 2 ∣ n) : 2 * (n / 2) = n :=
  Nat.mul_div_cancel' hn

/-- k < n/2 implies 2*k < n -/
theorem double_lt_of_lt_half (k n : ℕ) (hk : k < n / 2) : 2 * k < n := by
  omega

/-- k < n/2 implies k + n/2 < n -/
theorem add_half_lt_of_lt_half (k n : ℕ) (hn : n > 0) (hk : k < n / 2) :
    k + n / 2 < n := by
  omega

/-- For even n, n/2 ≤ n -/
theorem half_le (n : ℕ) : n / 2 ≤ n := Nat.div_le_self n 2

/-- For even n > 0, n/2 < n -/
theorem half_lt (n : ℕ) (hn : n > 0) (heven : 2 ∣ n) : n / 2 < n := by
  obtain ⟨m, hm⟩ := heven
  cases m with
  | zero => omega
  | succ m' => omega

/-- evens extracts element at position 2*k -/
theorem evens_getElem_eq {α : Type*} (a : List α) (k : ℕ) (hk : k < (evens a).length) :
    (evens a)[k]? = a[2 * k]? := evens_get a k hk

/-- odds extracts element at position 2*k+1 -/
theorem odds_getElem_eq {α : Type*} (a : List α) (k : ℕ) (hk : k < (odds a).length) :
    (odds a)[k]? = a[2 * k + 1]? := odds_get a k hk

/-- For even n, evens has length (n+1)/2 = n/2 -/
theorem evens_length_even {α : Type*} (a : List α) (heven : 2 ∣ a.length) :
    (evens a).length = a.length / 2 := by
  rw [evens_length]
  obtain ⟨m, hm⟩ := heven
  simp only [hm]
  omega

/-- For even n, odds has length n/2 -/
theorem odds_length_even {α : Type*} (a : List α) (heven : 2 ∣ a.length) :
    (odds a).length = a.length / 2 := by
  rw [odds_length]

end IndexArithmetic

/-!
## Layer 1: Well-Definedness Lemmas

These ensure that E[k]? and O[k]? are `some` for valid indices.
-/

section WellDefinedness

variable {F : Type*} [inst : NTTField F]

/-- E = NTT_spec ω² (evens input) has length ≤ input.length / 2 + 1
    More precisely, for even-length input, E.length = input.length / 2 -/
theorem E_length (ω : F) (input : List F) (heven : 2 ∣ input.length) :
    (NTT_spec (ω * ω) (evens input)).length = input.length / 2 := by
  rw [NTT_spec_length, evens_length_even input heven]

/-- O = NTT_spec ω² (odds input) has length = input.length / 2 -/
theorem O_length (ω : F) (input : List F) :
    (NTT_spec (ω * ω) (odds input)).length = input.length / 2 := by
  rw [NTT_spec_length, odds_length]

/-- For k < n/2, E[k]? is some -/
theorem E_getElem_some (ω : F) (input : List F) (heven : 2 ∣ input.length)
    (k : ℕ) (hk : k < input.length / 2) :
    ∃ e, (NTT_spec (ω * ω) (evens input))[k]? = some e := by
  have hlen : k < (NTT_spec (ω * ω) (evens input)).length := by
    rw [E_length ω input heven]
    exact hk
  exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩⟩

/-- For k < n/2, O[k]? is some -/
theorem O_getElem_some (ω : F) (input : List F)
    (k : ℕ) (hk : k < input.length / 2) :
    ∃ o, (NTT_spec (ω * ω) (odds input))[k]? = some o := by
  have hlen : k < (NTT_spec (ω * ω) (odds input)).length := by
    rw [O_length]
    exact hk
  exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩⟩

/-- E[k]? = some (ntt_coeff ω² (evens input) k) for valid k -/
theorem E_getElem_eq_coeff (ω : F) (input : List F) (heven : 2 ∣ input.length)
    (k : ℕ) (hk : k < input.length / 2) :
    (NTT_spec (ω * ω) (evens input))[k]? =
    some (ntt_coeff (ω * ω) (evens input) k) := by
  have hlen : k < (evens input).length := by
    rw [evens_length_even input heven]
    exact hk
  exact ntt_spec_getElem_eq_coeff (ω * ω) (evens input) k hlen

/-- O[k]? = some (ntt_coeff ω² (odds input) k) for valid k -/
theorem O_getElem_eq_coeff (ω : F) (input : List F)
    (k : ℕ) (hk : k < input.length / 2) :
    (NTT_spec (ω * ω) (odds input))[k]? =
    some (ntt_coeff (ω * ω) (odds input) k) := by
  have hlen : k < (odds input).length := by rw [odds_length]; exact hk
  exact ntt_spec_getElem_eq_coeff (ω * ω) (odds input) k hlen

end WellDefinedness

/-!
## Layer 2: DFT Splitting Formula

The key insight of Cooley-Tukey is that:
  Σᵢ aᵢ · ω^(ik) = Σₘ a_{2m} · ω^(2mk) + Σₘ a_{2m+1} · ω^((2m+1)k)
                 = Σₘ a_{2m} · (ω²)^(mk) + ω^k · Σₘ a_{2m+1} · (ω²)^(mk)
                 = E_k + ω^k · O_k

where E = NTT(evens), O = NTT(odds) with ω² as primitive root.

Design Decision (DD-030): The twiddle factor lemmas (twiddle_even_factor,
twiddle_odd_factor) are proved for CommRing types in TwiddleFactors section.
For the main Cooley-Tukey theorems, we work directly with these lemmas
since GoldilocksField provides a CommRing instance via Mathlib.

Implementation Strategy (from QA consultation):
- Use direct foldl-level approach with parity splitting
- Bridge lemmas connect foldl sums with evens/odds sublists
- Avoid full Finset.sum bridge for simplicity
-/

section DFTSplitting

/-!
### Summary of available twiddle factor lemmas

From TwiddleFactors section (CommRing context):
- twiddle_even_factor: ω^(2mk) = (ω²)^(mk)
- twiddle_odd_factor: ω^((2m+1)k) = ω^k · (ω²)^(mk)

These are used directly in the Cooley-Tukey proofs where
F has a CommRing instance (e.g., GoldilocksField).
-/

/-!
### Foldl-level splitting lemmas

These lemmas work directly with List.foldl to split sums by parity.
-/

/-- Extract even indices from a range: [0, 2, 4, ...] -/
def evenIndices (n : ℕ) : List ℕ := (List.range ((n + 1) / 2)).map (· * 2)

/-- Extract odd indices from a range: [1, 3, 5, ...] -/
def oddIndices (n : ℕ) : List ℕ := (List.range (n / 2)).map (· * 2 + 1)

-- Note: evenIndices and oddIndices are just natural number lists (no type class needed)

-- For the following lemmas that involve F, we use AddCommMonoid to avoid
-- the instance diamond between NTTField and CommRing.
variable {F : Type*} [AddCommMonoid F]

/-- evenIndices extracts correctly from range

    For i in evenIndices n: i < n and i is even (i % 2 = 0)

    Proof: If i = m * 2 with m < (n + 1) / 2, then:
    - i = m * 2 < (n + 1) / 2 * 2 ≤ n + 1, but we need i < n
    - Since m < (n + 1) / 2, we have m ≤ n / 2, so m * 2 ≤ n
    - But m * 2 is even so can't equal n when n is odd
    - When n is even, m < (n + 1) / 2 = n / 2, so m * 2 < n
-/
theorem evenIndices_mem (n i : ℕ) (h : i ∈ evenIndices n) : i < n ∧ i % 2 = 0 := by
  simp only [evenIndices, List.mem_map, List.mem_range] at h
  obtain ⟨m, hm, rfl⟩ := h
  constructor
  · -- Show m * 2 < n given m < (n + 1) / 2
    -- Key: (n + 1) / 2 * 2 ≤ n + 1, and m * 2 < (n + 1) / 2 * 2
    -- When n is odd: (n + 1) / 2 = (n + 1) / 2, max m is (n - 1) / 2, so m * 2 ≤ n - 1
    -- When n is even: (n + 1) / 2 = n / 2, so m * 2 < n
    have h1 : m ≤ n / 2 := by
      have : (n + 1) / 2 ≤ n / 2 + 1 := by omega
      omega
    have h2 : m * 2 ≤ n / 2 * 2 := Nat.mul_le_mul_right 2 h1
    have h3 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
    -- Now show strict inequality
    by_cases hn : n % 2 = 0
    · -- n even: (n + 1) / 2 = n / 2, so m < n / 2, so m * 2 < n
      have : (n + 1) / 2 = n / 2 := by omega
      have : m < n / 2 := by omega
      have : m * 2 < n / 2 * 2 := Nat.mul_lt_mul_of_pos_right this (by omega : 0 < 2)
      omega
    · -- n odd: (n + 1) / 2 = (n + 1) / 2, and n / 2 * 2 = n - 1
      have : n / 2 * 2 = n - 1 := by omega
      omega
  · -- Show (m * 2) % 2 = 0
    omega

/-- oddIndices extracts correctly from range

    For i in oddIndices n: i < n and i is odd (i % 2 = 1)
-/
theorem oddIndices_mem (n i : ℕ) (h : i ∈ oddIndices n) : i < n ∧ i % 2 = 1 := by
  simp only [oddIndices, List.mem_map, List.mem_range] at h
  obtain ⟨m, hm, rfl⟩ := h
  constructor
  · -- Show m * 2 + 1 < n given m < n / 2
    have h1 : m * 2 < n / 2 * 2 := Nat.mul_lt_mul_of_pos_right hm (by omega : 0 < 2)
    have h2 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
    omega
  · -- Show (m * 2 + 1) % 2 = 1
    omega

/-- For i < n with i even, i is in evenIndices n -/
theorem mem_evenIndices_of_even (n i : ℕ) (hi : i < n) (heven : i % 2 = 0) :
    i ∈ evenIndices n := by
  simp only [evenIndices, List.mem_map, List.mem_range]
  use i / 2
  constructor
  · -- Show i / 2 < (n + 1) / 2
    omega
  · -- Show i / 2 * 2 = i
    have h := Nat.div_add_mod i 2
    omega

/-- For i < n with i odd, i is in oddIndices n -/
theorem mem_oddIndices_of_odd (n i : ℕ) (hi : i < n) (hodd : i % 2 = 1) :
    i ∈ oddIndices n := by
  simp only [oddIndices, List.mem_map, List.mem_range]
  use i / 2
  constructor
  · -- Show i / 2 < n / 2
    omega
  · -- Show i / 2 * 2 + 1 = i
    have h := Nat.div_add_mod i 2
    omega

/-- evenIndices has no duplicates -/
theorem evenIndices_nodup (n : ℕ) : (evenIndices n).Nodup := by
  simp only [evenIndices]
  apply List.Nodup.map _ (List.nodup_range)
  intro a b hab
  -- a * 2 = b * 2 implies a = b
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hab

/-- oddIndices has no duplicates -/
theorem oddIndices_nodup (n : ℕ) : (oddIndices n).Nodup := by
  simp only [oddIndices]
  apply List.Nodup.map _ (List.nodup_range)
  intro a b hab
  -- a * 2 + 1 = b * 2 + 1 implies a = b
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) (Nat.add_right_cancel hab)

/-!
### Transition lemmas for evenIndices/oddIndices

These lemmas describe how evenIndices and oddIndices change when we increment n.
-/

/-- Helper: (2k + 1 + 1) / 2 = k + 1 -/
private lemma div2_even_succ (k : ℕ) : (2 * k + 1 + 1) / 2 = k + 1 := by omega

/-- Helper: (2k + 1) / 2 = k -/
private lemma div2_even (k : ℕ) : (2 * k + 1) / 2 = k := by omega

/-- Helper: (2k + 2 + 1) / 2 = k + 1 -/
private lemma div2_odd_succ (k : ℕ) : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega

/-- Helper: (2k + 2) / 2 = k + 1 -/
private lemma div2_odd (k : ℕ) : (2 * k + 1 + 1) / 2 = k + 1 := by omega

/-- When n is even, evenIndices (n+1) = evenIndices n ++ [n]

    Proof: If n = 2k, then:
    - evenIndices (2k+1) = range((2k+2)/2).map (*2) = range(k+1).map (*2) = [0,2,...,2k]
    - evenIndices (2k) = range((2k+1)/2).map (*2) = range(k).map (*2) = [0,2,...,2k-2]
    - So evenIndices (2k+1) = evenIndices (2k) ++ [2k]
-/
lemma evenIndices_succ_of_even (n : ℕ) (he : Even n) :
    evenIndices (n + 1) = evenIndices n ++ [n] := by
  obtain ⟨k, rfl⟩ := he
  -- Now n = k + k (not 2 * k, due to Even definition)
  unfold evenIndices
  -- LHS: range((k+k+1+1)/2).map (*2) = range(k+1).map (*2)
  -- RHS: range((k+k+1)/2).map (*2) ++ [k+k] = range(k).map (*2) ++ [k+k]
  have h1 : (k + k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (k + k + 1) / 2 = k := by omega
  rw [h1, h2]
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  ring_nf

/-- When n is odd, evenIndices (n+1) = evenIndices n -/
lemma evenIndices_succ_of_odd (n : ℕ) (ho : Odd n) :
    evenIndices (n + 1) = evenIndices n := by
  obtain ⟨k, rfl⟩ := ho
  unfold evenIndices
  have h1 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h1, h2]

/-- When n is odd, oddIndices (n+1) = oddIndices n ++ [n] -/
lemma oddIndices_succ_of_odd (n : ℕ) (ho : Odd n) :
    oddIndices (n + 1) = oddIndices n ++ [n] := by
  obtain ⟨k, rfl⟩ := ho
  unfold oddIndices
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2]
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  ring_nf

/-- When n is even, oddIndices (n+1) = oddIndices n -/
lemma oddIndices_succ_of_even (n : ℕ) (he : Even n) :
    oddIndices (n + 1) = oddIndices n := by
  obtain ⟨k, rfl⟩ := he
  -- Now n = k + k (not 2 * k, due to Even definition)
  unfold oddIndices
  have h1 : (k + k + 1) / 2 = k := by omega
  have h2 : (k + k) / 2 = k := by omega
  rw [h1, h2]

/-- evenIndices 0 is empty -/
lemma evenIndices_zero : evenIndices 0 = [] := rfl

/-- oddIndices 0 is empty -/
lemma oddIndices_zero : oddIndices 0 = [] := rfl

/-- Key lemma: Sum over range n equals sum over even indices plus sum over odd indices

    This is the foldl-level splitting that enables the Cooley-Tukey decomposition.

    Mathematical identity: Σᵢ<n f(i) = Σₘ f(2m) + Σₘ f(2m+1)
    where the even sum is over m < (n+1)/2 and odd sum is over m < n/2.

    Proof by induction on n using Nat.even_or_odd to case split.
-/
theorem foldl_split_parity (n : ℕ) (f : ℕ → F) :
    (List.range n).foldl (fun acc i => acc + f i) (0 : F) =
    (evenIndices n).foldl (fun acc i => acc + f i) (0 : F) +
    (oddIndices n).foldl (fun acc i => acc + f i) (0 : F) := by
  induction n with
  | zero =>
    -- Goal: List.foldl ... [] 0 = List.foldl ... [] 0 + List.foldl ... [] 0
    simp only [List.range_zero, List.foldl_nil, evenIndices_zero, oddIndices_zero]
    -- After simp: 0 = 0 + 0
    exact (add_zero 0).symm
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.even_or_odd n with he | ho
    -- Case: n is even, so n goes to evenIndices
    · have h1 := evenIndices_succ_of_even n he
      have h2 := oddIndices_succ_of_even n he
      rw [h1, h2]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]
      -- Goal: (E + O) + f n = (E + f n) + O
      -- Use abel for additive group rearrangement
      abel
    -- Case: n is odd, so n goes to oddIndices
    · have h1 := evenIndices_succ_of_odd n ho
      have h2 := oddIndices_succ_of_odd n ho
      rw [h1, h2]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]
      -- Goal: (E + O) + f n = E + (O + f n)
      abel

/-- Reindexing lemma for even indices: foldl over evenIndices equals foldl over range((n+1)/2)

    Maps m ↦ 2m, so sum over evenIndices gives sum over 0,2,4,...
-/
theorem foldl_even_reindex (n : ℕ) (f : ℕ → F) :
    (evenIndices n).foldl (fun acc i => acc + f i) (0 : F) =
    (List.range ((n + 1) / 2)).foldl (fun acc m => acc + f (2 * m)) (0 : F) := by
  simp only [evenIndices]
  rw [List.foldl_map]
  congr 2
  funext acc m
  ring_nf

/-- Reindexing lemma for odd indices: foldl over oddIndices equals foldl over range(n/2)

    Maps m ↦ 2m+1, so sum over oddIndices gives sum over 1,3,5,...
-/
theorem foldl_odd_reindex (n : ℕ) (f : ℕ → F) :
    (oddIndices n).foldl (fun acc i => acc + f i) (0 : F) =
    (List.range (n / 2)).foldl (fun acc m => acc + f (2 * m + 1)) (0 : F) := by
  simp only [oddIndices]
  rw [List.foldl_map]
  congr 2
  funext acc m
  ring_nf

end DFTSplitting

/-!
## Layer 2b: Algebraic Bridge Infrastructure (Capa 3.0)

The "Pragmatic Algebraic Bridge" strategy:
1. Define a shadow specification using Finset.sum (ntt_coeff_sum)
2. Prove equivalence with the foldl-based ntt_coeff (The Golden Bridge)
3. Do all algebraic manipulation in the Finset world
4. Transfer results back via the bridge

This approach leverages Mathlib's BigOperators library for algebraic properties
(Finset.mul_sum, Finset.sum_add_distrib, etc.) instead of proving them manually for foldl.
-/

section AlgebraicBridge

open BigOperators

variable {F : Type*} [inst : NTTFieldLawful F] [IsDomain F]

/-!
### Capa 3.0: Shadow Definition and getD Infrastructure
-/

/-- Shadow specification of NTT coefficient using Finset.sum.
    Semantically equivalent to ntt_coeff but algebraically tractable.

    Uses List.getD for total function behavior (returns 0 for out-of-bounds).
-/
def ntt_coeff_sum (ω : F) (a : List F) (k : ℕ) : F :=
  ∑ i ∈ Finset.range a.length, (a.getD i 0) * HPow.hPow ω (i * k)

/-- getD returns the element when index is valid -/
theorem getD_eq_get_of_lt {α : Type*} (a : List α) (i : ℕ) (d : α) (hi : i < a.length) :
    a.getD i d = a[i]'hi := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- getD returns default when index is out of bounds -/
theorem getD_eq_default_of_ge {α : Type*} (a : List α) (i : ℕ) (d : α) (hi : i ≥ a.length) :
    a.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

/-- Simp lemma: within Finset.range, getD equals get -/
theorem getD_of_mem_range {α : Type*} (a : List α) (i : ℕ) (d : α)
    (hi : i ∈ Finset.range a.length) :
    a.getD i d = a[i]'(Finset.mem_range.mp hi) := by
  exact getD_eq_get_of_lt a i d (Finset.mem_range.mp hi)

/-!
### Capa 3.1: The Golden Bridge

This is the critical theorem that connects the foldl implementation to the Finset specification.
Once proven, we never need to reason about foldl again for algebraic manipulations.

The proof requires showing that:
  (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i

This is a standard result but requires careful handling of:
1. Add.add vs + (definitionally equal for NTTFieldLawful + CommRing)
2. match a[i]? vs getD (equal when i < length)
-/

/-- NTTField.zero equals CommRing zero (definitional for our concrete type) -/
@[simp] theorem ntt_zero_eq_ring_zero : ((0 : F) : F) = (0 : F) := rfl

/-- Key lemma: foldl with addition over List.range equals Finset.sum over Finset.range.

    NOW PROVEN: With NTTField extending CommRing, there is only ONE Zero instance,
    so the typeclass diamond is resolved.
-/
theorem list_range_foldl_eq_finset_sum (n : ℕ) (f : ℕ → F) :
    (List.range n).foldl (fun acc i => acc + f i) (0 : F) = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [Finset.sum_range_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Finset.sum_range_succ, ih, add_comm]

/-- Helper: match on getElem? equals getD * pow for valid indices -/
theorem ntt_term_eq_getD_mul (ω : F) (a : List F) (k i : ℕ) (hi : i < a.length) :
    (match a[i]? with
      | some aᵢ => aᵢ * HPow.hPow ω (i * k)
      | none => (0 : F)) =
    (a.getD i 0) * HPow.hPow ω (i * k) := by
  have h : a[i]? = some (a[i]'hi) := List.getElem?_eq_getElem hi
  rw [h]
  simp only [List.getD_eq_getElem?_getD, h, Option.getD_some]

/-- THE GOLDEN BRIDGE: foldl implementation equals Finset.sum specification.
    Now proven with the resolved typeclass infrastructure.
-/
theorem ntt_coeff_eq_sum (ω : F) (a : List F) (k : ℕ) :
    ntt_coeff ω a k = ntt_coeff_sum ω a k := by
  unfold ntt_coeff ntt_coeff_sum
  -- Convert goal to standard notation using show
  show List.foldl (fun ac i => match a[i]? with
        | some aᵢ => ac + aᵢ * HPow.hPow ω (i * k)
        | none => ac) 0 (List.range a.length) =
      ∑ i ∈ Finset.range a.length, (a.getD i 0) * HPow.hPow ω (i * k)
  -- Step 1: Prove foldl with match equals foldl with getD
  suffices h : List.foldl (fun ac i => match a[i]? with
        | some aᵢ => ac + aᵢ * HPow.hPow ω (i * k)
        | none => ac) 0 (List.range a.length) =
      List.foldl (fun ac i => ac + (a.getD i 0) * HPow.hPow ω (i * k)) 0 (List.range a.length) by
    rw [h]
    exact list_range_foldl_eq_finset_sum a.length _
  -- Step 2: Prove by induction on list length
  have h_range : ∀ n ≤ a.length, ∀ acc,
      List.foldl (fun ac i => match a[i]? with
        | some aᵢ => ac + aᵢ * HPow.hPow ω (i * k)
        | none => ac) acc (List.range n) =
      List.foldl (fun ac i => ac + (a.getD i 0) * HPow.hPow ω (i * k)) acc (List.range n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn acc
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hn' : n < a.length := Nat.lt_of_succ_le hn
      have ih' := ih (le_of_lt hn') acc
      rw [ih']
      rw [List.getElem?_eq_getElem hn', List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hn', Option.getD_some]
  exact h_range a.length (le_refl _) 0

/-!
### Capa 3.2: Finset Sum Splitting by Parity

Split a Finset.sum over range n into sums over even and odd indices.
This is the Finset version of foldl_split_parity.
-/

/-- Finset.range n splits into even and odd indices -/
theorem finset_sum_split_parity (n : ℕ) (f : ℕ → F) :
    ∑ i ∈ Finset.range n, f i =
    ∑ m ∈ Finset.range ((n + 1) / 2), f (2 * m) +
    ∑ m ∈ Finset.range (n / 2), f (2 * m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : Even n
    · -- n is even: n = 2k, so n+1 is odd
      -- (n+1+1)/2 = (2k+2)/2 = k+1, (n+1)/2 = (2k+1)/2 = k
      -- The new term f(n) = f(2k) goes in the evens sum
      obtain ⟨k, hk⟩ := hn
      have he1 : (n + 1 + 1) / 2 = k + 1 := by omega
      have he2 : (n + 1) / 2 = k := by omega
      have he3 : n / 2 = k := by omega
      rw [he1, he2, he3, Finset.sum_range_succ]
      have hn_eq : n = 2 * k := by omega
      rw [hn_eq]
      ring
    · -- n is odd: n = 2k+1, so n+1 is even
      -- (n+1+1)/2 = (2k+3)/2 = k+1, (n+1)/2 = (2k+2)/2 = k+1
      -- The new term f(n) = f(2k+1) goes in the odds sum
      have hodd : Odd n := Nat.not_even_iff_odd.mp hn
      obtain ⟨k, hk⟩ := hodd
      have ho1 : (n + 1 + 1) / 2 = k + 1 := by omega
      have ho2 : (n + 1) / 2 = k + 1 := by omega
      have ho3 : n / 2 = k := by omega
      rw [ho1, ho2, ho3]
      have hn_eq : n = 2 * k + 1 := by omega
      rw [hn_eq]
      -- Goal: evens_sum + odds_sum + f(2k+1) = evens_sum + odds_sum'
      -- where odds_sum' = ∑ x ∈ range(k+1), f(2x+1)
      rw [Finset.sum_range_succ (f := fun x => f (2 * x + 1))]
      ring

/-!
### Capa 3.3: Connection between evens/odds and Finset reindexing

These theorems connect the physical list operations (evens, odds)
with the logical Finset operations (reindexed sums).
-/

/-- Sum over even indices equals ntt_coeff_sum on evens list with ω² -/
theorem sum_evens_eq_ntt_coeff_sum (ω : F) (a : List F) (k : ℕ)
    (heven : 2 ∣ a.length) :
    ∑ m ∈ Finset.range (a.length / 2), (a.getD (2 * m) 0) * HPow.hPow ω (2 * m * k) =
    ntt_coeff_sum (ω * ω) (evens a) k := by
  -- Unfold RHS
  unfold ntt_coeff_sum
  -- Step 1: The ranges match by evens_length_even
  have hlen : (evens a).length = a.length / 2 := evens_length_even a heven
  rw [hlen]
  -- Step 2: Show term-by-term equality
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  -- Need: (a.getD (2 * m) 0) * HPow.hPow ω (2 * m * k) =
  --       (evens a).getD m 0 * HPow.hPow (ω * ω) (m * k)
  -- Part A: (evens a).getD m 0 = a.getD (2*m) 0
  have hm_bound : m < (evens a).length := by rw [hlen]; exact hm
  have h_elem : (evens a)[m]? = a[2 * m]? := evens_get a m hm_bound
  have h_getD : (evens a).getD m 0 = a.getD (2 * m) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [h_elem]
  rw [← h_getD]
  -- Part B: HPow.hPow ω (2 * m * k) = HPow.hPow (ω * ω) (m * k)
  have h_pow : HPow.hPow ω (2 * m * k) = HPow.hPow (ω * ω) (m * k) := by
    rw [twiddle_even_factor_ntt, pow_2_eq_mul_ntt]
  rw [h_pow]

/-- Sum over odd indices with twiddle equals ω^k times ntt_coeff_sum on odds list -/
theorem sum_odds_eq_mul_ntt_coeff_sum (ω : F) (a : List F) (k : ℕ) :
    ∑ m ∈ Finset.range (a.length / 2), (a.getD (2 * m + 1) 0) * HPow.hPow ω ((2 * m + 1) * k) =
    HPow.hPow ω k * ntt_coeff_sum (ω * ω) (odds a) k := by
  -- Unfold RHS
  unfold ntt_coeff_sum
  -- Step 1: The ranges match by odds_length
  have hlen : (odds a).length = a.length / 2 := odds_length a
  rw [hlen]
  -- Step 2: Expand ω^k * Σ f = Σ (ω^k * f)
  rw [Finset.mul_sum]
  -- Step 3: Show term-by-term equality
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  -- Need: (a.getD (2 * m + 1) 0) * HPow.hPow ω ((2 * m + 1) * k) =
  --       HPow.hPow ω k * ((odds a).getD m 0 * HPow.hPow (ω * ω) (m * k))
  -- Part A: (odds a).getD m 0 = a.getD (2*m+1) 0
  have hm_bound : m < (odds a).length := by rw [hlen]; exact hm
  have h_elem : (odds a)[m]? = a[2 * m + 1]? := odds_get a m hm_bound
  have h_getD : (odds a).getD m 0 = a.getD (2 * m + 1) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [h_elem]
  rw [h_getD]
  -- Part B: Use twiddle_odd_factor_ntt and pow_2_eq_mul_ntt
  -- ω^((2m+1)k) = ω^k · (ω²)^(mk) = ω^k · (ω*ω)^(mk)
  have h_pow : HPow.hPow ω ((2 * m + 1) * k) =
      HPow.hPow ω k * HPow.hPow (ω * ω) (m * k) := by
    rw [twiddle_odd_factor_ntt, pow_2_eq_mul_ntt]
  rw [h_pow]
  -- Now: a[2m+1] * (ω^k * (ω*ω)^(mk)) = ω^k * (a[2m+1] * (ω*ω)^(mk))
  ring

/-!
### Capa 3.4: Main Splitting Theorem in Finset World

This is the algebraic heart of Cooley-Tukey, proved in the clean Finset world.
-/

/-- DFT splitting formula in Finset.sum form:
    ntt_coeff_sum ω a k = ntt_coeff_sum (ω²) (evens a) k + ω^k · ntt_coeff_sum (ω²) (odds a) k
-/
theorem ntt_coeff_sum_upper_half_split (ω : F) (a : List F)
    (heven : 2 ∣ a.length) (k : ℕ) (hk : k < a.length / 2) :
    ntt_coeff_sum ω a k =
    ntt_coeff_sum (ω * ω) (evens a) k +
    HPow.hPow ω k * ntt_coeff_sum (ω * ω) (odds a) k := by
  -- Step 1: Unfold ntt_coeff_sum on LHS
  unfold ntt_coeff_sum
  -- Step 2: Apply finset_sum_split_parity
  rw [finset_sum_split_parity a.length (fun i => (a.getD i 0) * HPow.hPow ω (i * k))]
  -- Step 3: When 2 | a.length, (a.length + 1) / 2 = a.length / 2
  have h_even_half : (a.length + 1) / 2 = a.length / 2 := by
    obtain ⟨m, hm⟩ := heven
    omega
  rw [h_even_half]
  -- Step 4: Apply congr_arg2 for addition
  apply congr_arg₂ (· + ·)
  · exact sum_evens_eq_ntt_coeff_sum ω a k heven
  · exact sum_odds_eq_mul_ntt_coeff_sum ω a k

end AlgebraicBridge

/-!
## Layer 3: Cooley-Tukey Splitting Lemmas

These lemmas directly support the proofs of S8 and S9 by establishing
the relationship between ntt_coeff of the full input and the E/O sub-transforms.
-/

section CooleyTukeySplitting

-- Note: We use NTTFieldLawful instead of NTTField to access pow_mul, pow_add lemmas
-- needed for twiddle factor proofs. NTTFieldLawful extends NTTField.
variable {F : Type*} [inst : NTTFieldLawful F] [IsDomain F]

/-! Helper lemmas bridging HPow.hPow with notation.

    Note: Since NTTField extends CommRing, * + - 0 1 come from CommRing.
    Only pow, inv, char, isZero are NTT-specific operations.
-/

/-- Derived: x * 0 = 0 (from CommRing) -/
theorem mul_zero_ntt (x : F) : x * (0 : F) = 0 := mul_zero x

/-!
### Key relationship: ω² and HPow.hPow

When F has both NTTField and CommRing instances, we can use both
HPow.hPow and the ^ operator. For GoldilocksField, they agree.
-/

/-- ω ^ 2 = ω * ω (from Mathlib's sq lemma) -/
theorem inst_pow_2_eq_mul' {F : Type*} [inst : NTTFieldLawful F] (ω : F) :
    ω ^ 2 = ω * ω := sq ω

/-- For CommRing, ω * ω = ω^2 -/
theorem mul_eq_sq {F : Type*} [CommRing F] (ω : F) : ω * ω = ω ^ 2 := by ring

/-!
### ntt_coeff expansion for evens/odds

These lemmas expand ntt_coeff in terms of the even and odd indexed elements.
-/

/-- Single term of NTT coefficient sum: aᵢ · ω^(i·k)
    Returns zero if index is out of bounds.

    This helper function extracts the term computation from ntt_coeff,
    making it easier to reason about the sum splitting.
-/
def ntt_term (ω : F) (a : List F) (k : ℕ) (i : ℕ) : F :=
  match a[i]? with
  | some aᵢ => aᵢ * HPow.hPow ω (i * k)
  | none => (0 : F)

/-- Bridge lemma: ntt_term at even index relates to evens sublist

    For m < (evens a).length:
      ntt_term ω a k (2*m) = ntt_term (ω²) (evens a) k m

    This uses:
    - evens_get: (evens a)[m]? = a[2*m]?
    - twiddle_even_factor: ω^(2mk) = (ω²)^(mk)
-/
theorem ntt_term_even_index (ω : F) (a : List F) (k m : ℕ) (hm : m < (evens a).length) :
    ntt_term ω a k (2 * m) = ntt_term (ω * ω) (evens a) k m := by
  -- Unfold ntt_term on both sides
  simp only [ntt_term]
  -- Use evens_get to rewrite (evens a)[m]? = a[2*m]?
  have h_evens : (evens a)[m]? = a[2 * m]? := evens_get a m hm
  rw [h_evens]
  -- Now both sides have match a[2*m]? with ...
  -- Case split on a[2*m]?
  cases h : a[2 * m]? with
  | none => rfl  -- Both sides are (0 : F)
  | some aᵢ =>
    -- Need to show: inst.mul aᵢ (HPow.hPow ω (2*m*k)) = inst.mul aᵢ (HPow.hPow (ω * ω) (m*k))
    -- First rewrite the exponent using twiddle_even_factor_ntt
    have h_exp : HPow.hPow ω (2 * m * k) = HPow.hPow (ω * ω) (m * k) := by
      rw [twiddle_even_factor_ntt]
      rw [pow_2_eq_mul_ntt]
    rw [h_exp]

/-- Bridge lemma: ntt_term at odd index relates to odds sublist with twiddle

    For m < (odds a).length:
      ntt_term ω a k (2*m+1) = ω^k · ntt_term (ω²) (odds a) k m

    This uses:
    - odds_get: (odds a)[m]? = a[2*m+1]?
    - twiddle_odd_factor: ω^((2m+1)k) = ω^k · (ω²)^(mk)
-/
theorem ntt_term_odd_index (ω : F) (a : List F) (k m : ℕ) (hm : m < (odds a).length) :
    ntt_term ω a k (2 * m + 1) =
    HPow.hPow ω k * ntt_term (ω * ω) (odds a) k m := by
  -- Unfold ntt_term on both sides
  simp only [ntt_term]
  -- Use odds_get to rewrite (odds a)[m]? = a[2*m+1]?
  have h_odds : (odds a)[m]? = a[2 * m + 1]? := odds_get a m hm
  rw [h_odds]
  -- Now both sides have a[2*m+1]? in common
  -- Case split on a[2*m+1]?
  cases h : a[2 * m + 1]? with
  | none =>
    -- LHS: 0, RHS: HPow.hPow ω k * 0
    exact (mul_zero (HPow.hPow ω k)).symm
  | some aᵢ =>
    -- LHS: aᵢ * (HPow.hPow ω ((2*m+1)*k))
    -- RHS: HPow.hPow ω k * (aᵢ * HPow.hPow (ω * ω) (m*k))
    -- First rewrite the exponent using twiddle_odd_factor_ntt and pow_2_eq_mul_ntt
    have h_exp : HPow.hPow ω ((2 * m + 1) * k) = HPow.hPow ω k * HPow.hPow (ω * ω) (m * k) := by
      rw [twiddle_odd_factor_ntt, pow_2_eq_mul_ntt]
    rw [h_exp]
    -- Now: aᵢ * (HPow.hPow ω k * p) = HPow.hPow ω k * (aᵢ * p)
    -- where p = HPow.hPow (ω * ω) (m * k)
    -- Use CommRing lemmas for the algebraic manipulation
    -- a * (b * c) = (a * b) * c = (b * a) * c = b * (a * c)
    calc aᵢ * (HPow.hPow ω k * HPow.hPow (ω * ω) (m * k))
        = (aᵢ * HPow.hPow ω k) * HPow.hPow (ω * ω) (m * k) := by rw [mul_assoc]
      _ = (HPow.hPow ω k * aᵢ) * HPow.hPow (ω * ω) (m * k) := by rw [mul_comm aᵢ]
      _ = HPow.hPow ω k * (aᵢ * HPow.hPow (ω * ω) (m * k)) := by rw [mul_assoc]

/-!
### Main DFT Splitting Formula

The central algebraic identity for Cooley-Tukey:
  ntt_coeff ω input k = ntt_coeff (ω²) (evens input) k + ω^k · ntt_coeff (ω²) (odds input) k

This is the mathematical heart of the Cooley-Tukey algorithm.

The proof requires showing that the foldl-based sum decomposes into
even and odd indexed sums. This is mathematically clear:
  Σᵢ aᵢ · ω^(ik) = Σₘ a_{2m} · ω^(2mk) + Σₘ a_{2m+1} · ω^((2m+1)k)
                 = Σₘ a_{2m} · (ω²)^(mk) + ω^k · Σₘ a_{2m+1} · (ω²)^(mk)

The technical challenge is the bridge between foldl and algebraic sums.
This involves several lemmas that require careful Finset manipulation.

Proof Structure (with sorries for technical lemmas):
1. ntt_coeff_eq_finset: Bridge from foldl to Finset.sum
2. finset_sum_split_parity: Split sum into even/odd indexed parts
3. finset_sum_even_reindex, finset_sum_odd_reindex: Reindex sums
4. ntt_coeff_evens_eq_reindex, ntt_coeff_odds_eq_reindex: Connect to evens/odds
5. Twiddle factor algebra using twiddle_even_factor and twiddle_odd_factor
-/

/-- Main DFT splitting: X_k = E_k + ω^k · O_k

    For input of length n (even), and k < n/2:
    - E_k = ntt_coeff (ω²) (evens input) k
    - O_k = ntt_coeff (ω²) (odds input) k
    - X_k = ntt_coeff ω input k

    The proof follows the DFT splitting identity. The detailed steps involve:
    1. Split the sum Σᵢ aᵢ · ω^(ik) into even and odd indexed parts
    2. Reindex: even indices i=2m, odd indices i=2m+1
    3. Use twiddle_even_factor: ω^(2mk) = (ω²)^(mk)
    4. Use twiddle_odd_factor: ω^((2m+1)k) = ω^k · (ω²)^(mk)
    5. Factor out ω^k from the odd sum
    6. Recognize the results as ntt_coeff on evens and odds

    This is verified computationally via native_decide tests in Correctness.lean.
-/
theorem ntt_coeff_upper_half_split (ω : F) (input : List F)
    (heven : 2 ∣ input.length) (k : ℕ) (hk : k < input.length / 2) :
    ntt_coeff ω input k =
    Add.add
      (ntt_coeff (ω * ω) (evens input) k)
      (HPow.hPow ω k * (ntt_coeff (ω * ω) (odds input) k)) := by
  -- Step 1: Convert all ntt_coeff to ntt_coeff_sum (using the Golden Bridge)
  rw [ntt_coeff_eq_sum, ntt_coeff_eq_sum, ntt_coeff_eq_sum]
  -- Step 2: Apply the algebraic splitting theorem
  rw [ntt_coeff_sum_upper_half_split ω input heven k hk]
  -- Step 3: Add.add = + and HPow.hPow = HPow.hPow are definitionally equal
  rfl

/-- Main DFT splitting for lower half: X_{k+n/2} = E_k - ω^k · O_k

    Uses the fact that ω^(n/2) = -1 for primitive n-th root.
-/
theorem ntt_coeff_lower_half_split (ω : F) (input : List F) (n : ℕ)
    (hn : n > 2) (heven : 2 ∣ n)
    (h_len : input.length = n) (hω : IsPrimitiveRoot ω n)
    (k : ℕ) (hk : k < n / 2) :
    ntt_coeff ω input (k + n / 2) =
    (ntt_coeff (ω * ω) (evens input) k) - (ω ^ k * (ntt_coeff (ω * ω) (odds input) k)) := by
  -- Key insight: ω^(n/2) = -1 for primitive n-th root
  have h_half_neg : ω ^ (n / 2) = -1 := twiddle_half_eq_neg_one hn heven hω

  -- Express in terms of ntt_coeff_sum
  rw [ntt_coeff_eq_sum, ntt_coeff_eq_sum, ntt_coeff_eq_sum]
  unfold ntt_coeff_sum

  -- Get the evens/odds lengths
  have heven_input : 2 ∣ input.length := by rw [h_len]; exact heven
  have hlen_evens : (evens input).length = input.length / 2 := evens_length_even input heven_input
  have hlen_odds : (odds input).length = input.length / 2 := odds_length input

  -- Rewrite the ranges
  rw [hlen_evens, hlen_odds, h_len]

  -- Split the main sum by parity
  rw [finset_sum_split_parity n (fun i => (input.getD i 0) * HPow.hPow ω (i * (k + n / 2)))]

  -- When 2 | n, (n + 1) / 2 = n / 2
  have h_even_half : (n + 1) / 2 = n / 2 := by omega

  rw [h_even_half]

  -- Now we need to show the evens sum and odds sum transform correctly
  -- For evens: ω^(2m * (k + n/2)) = ω^(2mk) because ω^(m*n) = 1
  -- For odds: ω^((2m+1) * (k + n/2)) = -ω^((2m+1)k) because ω^(n/2) = -1

  -- First, prove the evens sum matches
  have h_evens_sum : ∑ m ∈ Finset.range (n / 2), (input.getD (2 * m) 0) *
      ω ^ ((2 * m) * (k + n / 2)) =
      ∑ i ∈ Finset.range (n / 2), (evens input).getD i 0 * (ω * ω) ^ (i * k) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    -- Show the getD values match
    have hm_bound : m < (evens input).length := by rw [hlen_evens, h_len]; exact hm
    have h_elem : (evens input)[m]? = input[2 * m]? := evens_get input m hm_bound
    have h_getD : (evens input).getD m 0 = input.getD (2 * m) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h_elem]
    rw [← h_getD]
    -- Show the exponent transforms correctly: 2m * (k + n/2) → m * k for ω² base
    -- Key: ω^(2m * (k + n/2)) = ω^(2mk + m*n) = ω^(2mk) * (ω^n)^m = ω^(2mk)
    have h_exp : ω ^ ((2 * m) * (k + n / 2)) = (ω * ω) ^ (m * k) := by
      -- (2 * m) * (k + n / 2) = 2 * m * k + m * n
      have hn2 : 2 * (n / 2) = n := Nat.mul_div_cancel' heven
      have h1 : (2 * m) * (k + n / 2) = 2 * m * k + m * n := by
        calc (2 * m) * (k + n / 2)
            = 2 * m * k + 2 * m * (n / 2) := by ring
          _ = 2 * m * k + m * (2 * (n / 2)) := by ring
          _ = 2 * m * k + m * n := by rw [hn2]
      rw [h1, pow_add]
      -- ω^(m*n) = 1
      have h_pow_mn : ω ^ (m * n) = 1 := by
        rw [mul_comm m n, pow_mul, hω.pow_eq_one, one_pow]
      rw [h_pow_mn, mul_one]
      -- ω^(2mk) = (ω²)^(mk) = (ω*ω)^(mk)
      have h2 : 2 * m * k = 2 * (m * k) := by ring
      rw [h2, pow_mul, sq]
    simp only [h_exp]

  -- Second, prove the odds sum transforms with sign flip
  have h_odds_sum : ∑ m ∈ Finset.range (n / 2), (input.getD (2 * m + 1) 0) *
      ω ^ ((2 * m + 1) * (k + n / 2)) =
      -(ω ^ k * ∑ i ∈ Finset.range (n / 2), (odds input).getD i 0 * (ω * ω) ^ (i * k)) := by
    -- Transform RHS: -(ω^k * Σᵢ fᵢ) = -(Σᵢ ω^k * fᵢ) = Σᵢ -(ω^k * fᵢ)
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    -- Show the getD values match
    have hm_bound : m < (odds input).length := by rw [hlen_odds, h_len]; exact hm
    have h_elem : (odds input)[m]? = input[2 * m + 1]? := odds_get input m hm_bound
    have h_getD : (odds input).getD m 0 = input.getD (2 * m + 1) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h_elem]
    rw [← h_getD]
    -- Show: input[2m+1] * ω^((2m+1)*(k+n/2)) = -(ω^k * ((odds input)[m] * (ω*ω)^(mk)))
    -- Key: ω^((2m+1) * (k + n/2)) = -ω^k * (ω*ω)^(mk)
    have h_exp : ω ^ ((2 * m + 1) * (k + n / 2)) = -(ω ^ k * (ω * ω) ^ (m * k)) := by
      -- (2m+1) * (k + n/2) = (2m+1)*k + m*n + n/2
      have hn2 : 2 * (n / 2) = n := Nat.mul_div_cancel' heven
      have h1 : (2 * m + 1) * (k + n / 2) = (2 * m + 1) * k + m * n + n / 2 := by
        calc (2 * m + 1) * (k + n / 2)
            = (2 * m + 1) * k + (2 * m + 1) * (n / 2) := by ring
          _ = (2 * m + 1) * k + 2 * m * (n / 2) + (n / 2) := by ring
          _ = (2 * m + 1) * k + m * (2 * (n / 2)) + n / 2 := by ring
          _ = (2 * m + 1) * k + m * n + n / 2 := by rw [hn2]
      rw [h1, pow_add, pow_add]
      -- ω^(m*n) = (ω^n)^m = 1^m = 1
      have h_pow_mn : ω ^ (m * n) = 1 := by
        rw [mul_comm m n, pow_mul, hω.pow_eq_one, one_pow]
      rw [h_pow_mn, mul_one]
      -- ω^(n/2) = -1
      rw [h_half_neg]
      -- ω^((2m+1)k) * (-1) = -(ω^k * (ω*ω)^(m*k))
      have h2 : (2 * m + 1) * k = k + 2 * (m * k) := by ring
      rw [h2, pow_add, pow_mul, sq]
      ring
    -- input[2m+1] * (-(ω^k * (ω*ω)^(mk))) = -(ω^k * (input[2m+1] * (ω*ω)^(mk)))
    rw [h_exp]
    ring

  -- Convert (ω * ω) to (ω ^ 2) in hypotheses so they match the goal
  -- The goal uses ω^2 (from finset_sum_split_parity), hypotheses use ω*ω
  -- sq : a^2 = a*a, so (sq ω).symm : ω*ω = ω^2
  have h_sq : ω * ω = ω ^ 2 := (sq ω).symm
  simp only [h_sq] at h_evens_sum h_odds_sum
  rw [h_evens_sum, h_odds_sum]
  -- Goal: evens_sum + (-ω^k * odds_sum) = evens_sum - (ω^k * odds_sum)
  -- The RHS still has (ω * ω) from the theorem statement, convert it
  simp only [h_sq]
  -- Goal: a + (-b) = a - b
  rw [sub_eq_add_neg]

end CooleyTukeySplitting

/-!
## Layer 3: Connecting ntt_coeff to NTT_spec

NTT_spec is defined via ntt_coeff. These lemmas make the connection explicit.
-/

section NTTSpecConnection

variable {F : Type*} [inst : NTTField F]

/-- NTT_spec at index k equals ntt_coeff at k (when k is valid) -/
theorem NTT_spec_at_k (ω : F) (input : List F) (k : ℕ) (hk : k < input.length) :
    (NTT_spec ω input)[k]? = some (ntt_coeff ω input k) :=
  ntt_spec_getElem_eq_coeff ω input k hk

/-- Combining NTT_spec_at_k with the upper half splitting -/
theorem NTT_spec_upper_half_eq {F : Type*} [inst : NTTFieldLawful F] [IsDomain F]
    (ω : F) (input : List F)
    (heven : 2 ∣ input.length) (k : ℕ) (hk : k < input.length / 2) :
    (NTT_spec ω input)[k]? =
    some (Add.add
      (ntt_coeff (ω * ω) (evens input) k)
      (HPow.hPow ω k * (ntt_coeff (ω * ω) (odds input) k))) := by
  have hk' : k < input.length := by
    calc k < input.length / 2 := hk
      _ ≤ input.length := Nat.div_le_self _ _
  rw [NTT_spec_at_k ω input k hk']
  rw [ntt_coeff_upper_half_split ω input heven k hk]

end NTTSpecConnection

/-!
## Verification
-/

#check primitive_root_two_eq_neg_one
#check twiddle_even_factor
#check twiddle_odd_factor
#check E_getElem_some
#check O_getElem_some
#check ntt_coeff_upper_half_split
#check NTT_spec_upper_half_eq

end AmoLean.NTT.Phase3Proof
