/-
  AMO-Lean: List Utilities for NTT
  Phase 5: NTT Core - Tasks 2.0a, 2.0b, 2.0c

  This module provides helper functions for Cooley-Tukey NTT:
  - evens: Extract elements at even indices
  - odds: Extract elements at odd indices
  - interleave: Combine two lists alternating elements

  Design Decision DD-016: These functions have preservation theorems
  that guarantee no elements are lost or duplicated, preventing
  index errors in the recursive NTT algorithm.

  Key theorems:
  - evens_odds_length: l.evens.length + l.odds.length = l.length
  - interleave_evens_odds: interleave l.evens l.odds = l
-/

namespace AmoLean.NTT

/-! ## Part 1: evens - Extract elements at even indices (0, 2, 4, ...) -/

/-- Extract elements at even indices: [a₀, a₁, a₂, a₃, ...] → [a₀, a₂, ...] -/
def evens : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evens xs

/-- Length of evens is (n + 1) / 2 -/
theorem evens_length (l : List α) :
    (evens l).length = (l.length + 1) / 2 := by
  induction l using evens.induct with
  | case1 => simp [evens]
  | case2 x => simp [evens]
  | case3 x y xs ih =>
    simp only [evens, List.length_cons]
    rw [ih]
    omega

/-! ## Part 2: odds - Extract elements at odd indices (1, 3, 5, ...) -/

/-- Extract elements at odd indices: [a₀, a₁, a₂, a₃, ...] → [a₁, a₃, ...] -/
def odds : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: odds xs

/-- Length of odds is n / 2 -/
theorem odds_length (l : List α) :
    (odds l).length = l.length / 2 := by
  induction l using odds.induct with
  | case1 => simp [odds]
  | case2 x => simp [odds]
  | case3 x y xs ih =>
    simp only [odds, List.length_cons]
    rw [ih]
    omega

/-! ## Part 3: Length preservation theorem -/

/-- evens.length + odds.length = original length -/
theorem evens_odds_length (l : List α) :
    (evens l).length + (odds l).length = l.length := by
  rw [evens_length, odds_length]
  omega

/-! ## Part 4: interleave - Combine two lists alternating elements -/

/-- Interleave two lists: [a, b, c], [x, y, z] → [a, x, b, y, c, z]
    If lists have different lengths, remaining elements are appended. -/
def interleave : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: interleave xs ys

/-- Length of interleave is sum of lengths -/
theorem interleave_length (xs ys : List α) :
    (interleave xs ys).length = xs.length + ys.length := by
  induction xs, ys using interleave.induct with
  | case1 ys => simp [interleave]
  | case2 xs => simp [interleave]
  | case3 x xs y ys ih =>
    simp only [interleave, List.length_cons]
    rw [ih]
    omega

/-! ## Part 5: Roundtrip theorem - The key correctness property -/

/-- Interleaving evens and odds reconstructs the original list -/
theorem interleave_evens_odds (l : List α) :
    interleave (evens l) (odds l) = l := by
  induction l using evens.induct with
  | case1 => simp [evens, odds, interleave]
  | case2 x => simp [evens, odds, interleave]
  | case3 x y xs ih =>
    simp only [evens, odds, interleave]
    rw [ih]

/-! ## Part 6: Additional properties for NTT -/

/-- evens of empty list is empty -/
@[simp] theorem evens_nil : evens ([] : List α) = [] := rfl

/-- odds of empty list is empty -/
@[simp] theorem odds_nil : odds ([] : List α) = [] := rfl

/-- evens of singleton is singleton -/
@[simp] theorem evens_singleton (x : α) : evens [x] = [x] := rfl

/-- odds of singleton is empty -/
@[simp] theorem odds_singleton (x : α) : odds [x] = [] := rfl

/-- interleave with empty right is identity -/
@[simp] theorem interleave_nil_right (xs : List α) :
    interleave xs [] = xs := by
  cases xs <;> simp [interleave]

/-- interleave with empty left is identity -/
@[simp] theorem interleave_nil_left (ys : List α) :
    interleave [] ys = ys := by
  simp [interleave]

/-! ## Part 7: Properties for power-of-2 lengths (NTT specific) -/

/-- For even-length lists, evens and odds have equal length -/
theorem evens_odds_eq_length_of_even (l : List α) (h : 2 ∣ l.length) :
    (evens l).length = (odds l).length := by
  rw [evens_length, odds_length]
  obtain ⟨k, hk⟩ := h
  simp only [hk]
  omega

/-- For power-of-2 length ≥ 2, evens and odds each have length n/2 -/
theorem evens_length_pow2 (l : List α) (k : Nat) (hk : k ≥ 1)
    (hl : l.length = 2^k) :
    (evens l).length = 2^(k-1) := by
  rw [evens_length, hl]
  have h2k : 2^k = 2 * 2^(k-1) := by
    cases k with
    | zero => omega
    | succ n => simp [Nat.pow_succ, Nat.mul_comm]
  omega

/-- For power-of-2 length ≥ 2, odds has length n/2 -/
theorem odds_length_pow2 (l : List α) (k : Nat) (hk : k ≥ 1)
    (hl : l.length = 2^k) :
    (odds l).length = 2^(k-1) := by
  rw [odds_length, hl]
  have h2k : 2^k = 2 * 2^(k-1) := by
    cases k with
    | zero => omega
    | succ n => simp [Nat.pow_succ, Nat.mul_comm]
  omega

/-! ## Part 8: Get elements (for specification) -/

/-- Get element at index from evens corresponds to element at 2*i in original -/
theorem evens_get (l : List α) (i : Nat) (hi : i < (evens l).length) :
    (evens l)[i]? = l[2*i]? := by
  induction l using evens.induct generalizing i with
  | case1 => simp [evens] at hi
  | case2 x =>
    simp only [evens, List.length_singleton] at hi ⊢
    match i with
    | 0 => rfl
    | n + 1 => omega
  | case3 x y xs ih =>
    match i with
    | 0 => simp [evens]
    | j + 1 =>
      simp only [evens] at hi ⊢
      have hj : j < (evens xs).length := by
        simp only [List.length_cons] at hi
        omega
      -- Goal: (x :: evens xs)[j + 1]? = (x :: y :: xs)[2 * (j + 1)]?
      -- Use that 2*(j+1) = 2*j + 2
      have hidx : 2 * (j + 1) = 2 * j + 2 := by omega
      simp only [hidx, List.getElem?_cons_succ, ih j hj]

/-- Get element at index from odds corresponds to element at 2*i+1 in original -/
theorem odds_get (l : List α) (i : Nat) (hi : i < (odds l).length) :
    (odds l)[i]? = l[2*i + 1]? := by
  induction l using odds.induct generalizing i with
  | case1 => simp [odds] at hi
  | case2 x => simp [odds] at hi
  | case3 x y xs ih =>
    match i with
    | 0 => simp [odds]
    | j + 1 =>
      simp only [odds] at hi ⊢
      have hj : j < (odds xs).length := by
        simp only [List.length_cons] at hi
        omega
      -- Goal: (y :: odds xs)[j + 1]? = (x :: y :: xs)[2 * (j + 1) + 1]?
      -- Use that 2*(j+1) + 1 = 2*j + 3
      have hidx : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
      simp only [hidx, List.getElem?_cons_succ, ih j hj]

/-! ## Part 9: Quick Tests -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   List Utilities Tests"
  IO.println "═══════════════════════════════════════════════════════════"

  let test1 := [0, 1, 2, 3, 4, 5, 6, 7]
  IO.println s!"\nOriginal: {test1}"
  IO.println s!"evens:    {evens test1}"
  IO.println s!"odds:     {odds test1}"
  IO.println s!"interleave(evens, odds): {interleave (evens test1) (odds test1)}"

  let roundtrip := interleave (evens test1) (odds test1) == test1
  IO.println s!"\nRoundtrip test: {roundtrip}"

  -- Test with odd length
  let test2 := [0, 1, 2, 3, 4]
  IO.println s!"\nOriginal (odd length): {test2}"
  IO.println s!"evens:    {evens test2}"
  IO.println s!"odds:     {odds test2}"
  IO.println s!"interleave(evens, odds): {interleave (evens test2) (odds test2)}"

  let roundtrip2 := interleave (evens test2) (odds test2) == test2
  IO.println s!"Roundtrip test: {roundtrip2}"

  IO.println "\n═══════════════════════════════════════════════════════════"

end AmoLean.NTT
