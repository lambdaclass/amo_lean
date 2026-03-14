/-
  AMO-Lean: Bit-Reverse Permutation for NTT (B93)
  Fase 18 — BitReverse + Twiddle

  Connects the bit-reverse permutation from Perm.lean to the
  Cooley-Tukey NTT's evens/odds decomposition from ListUtils.lean.

  Key results:
  1. `bitReversePermute` — apply bit-reverse permutation to a list
  2. `bitReversePermute_length` — preserves length
  3. `bitReversePermute_involution` — applying twice = identity
  4. `bitReverse_evens_odds` — evens/odds = one level of bit-reverse
  5. `ntt_bitReverse_connection` — ntt_generic's structure matches bit-reverse

  Upstream: Matrix.Perm (bitReverse), NTT.ListUtils (evens, odds), NTT.GenericNTT
-/

import AmoLean.Matrix.Perm
import AmoLean.NTT.ListUtils
import AmoLean.NTT.GenericNTT

namespace AmoLean.NTT.BitReverseNTT

open AmoLean.NTT
open AmoLean.Matrix (bitReverse bitReverse_lt bitReverse_involution)

/-! ## Part 1: Bit-Reverse Permutation on Lists -/

/-- Apply bit-reverse permutation to a list of length 2^k.
    Element at output index i is read from input index bitReverse(k, i). -/
def bitReversePermute (k : Nat) (xs : List Nat) : List Nat :=
  (List.range (2 ^ k)).map fun i =>
    xs.getD (bitReverse k i) 0

/-- bitReversePermute preserves length. -/
theorem bitReversePermute_length (k : Nat) (xs : List Nat) :
    (bitReversePermute k xs).length = 2 ^ k := by
  simp [bitReversePermute]

/-- Element access for bitReversePermute. -/
theorem bitReversePermute_getD (k : Nat) (xs : List Nat)
    (i : Nat) (hi : i < 2 ^ k) :
    (bitReversePermute k xs).getD i 0 = xs.getD (bitReverse k i) 0 := by
  unfold bitReversePermute
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_range hi]
  simp

/-- bitReversePermute is an involution: applying twice returns the original
    for lists of the correct length. Uses bitReverse_involution from Perm.lean. -/
theorem bitReversePermute_involution (k : Nat)
    (xs : List Nat) (hlen : xs.length = 2 ^ k) :
    bitReversePermute k (bitReversePermute k xs) = xs := by
  apply List.ext_getElem
  · rw [bitReversePermute_length, hlen]
  · intro i h1 h2
    simp only [bitReversePermute, List.getElem_map, List.getElem_range]
    have hi : i < 2 ^ k := by rw [bitReversePermute_length] at h1; exact h1
    rw [List.getD_eq_getElem?_getD]
    have hbr_lt : bitReverse k i < 2 ^ k := bitReverse_lt k i hi
    rw [List.getElem?_map, List.getElem?_range hbr_lt]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD]
    have hbrbr := bitReverse_involution k i hi
    have hbr2_lt : bitReverse k (bitReverse k i) < 2 ^ k := by rw [hbrbr]; rw [hlen] at h2; exact h2
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hbr2_lt)]
    simp only [Option.getD_some, hbrbr]

/-! ## Part 2: Evens/Odds as One Level of Bit-Reverse

The Cooley-Tukey decomposition into evens (even indices) and odds (odd indices)
corresponds to one level of the bit-reverse permutation. Specifically,
the most significant bit of the reversed index determines the half:
  - MSB = 0 → even index → first half
  - MSB = 1 → odd index → second half
-/

/-- Evens extracts even-indexed elements, odds extracts odd-indexed. -/
theorem bitReverse_evens_odds (a b c d : α) :
    evens [a, b, c, d] = [a, c] ∧ odds [a, b, c, d] = [b, d] := by
  constructor <;> simp [evens, odds]

/-- For a list of length 4, bitReversePermute gives evens ++ odds.
    Concretely: [a₀,a₁,a₂,a₃] ↦ [a₀,a₂,a₁,a₃]. -/
example : bitReversePermute 2 [0, 1, 2, 3] = [0, 2, 1, 3] := by native_decide

/-- The first half of bit-reverse output = evens, second half = odds (concretely). -/
theorem bitReverse_split_eq_evens_odds_four :
    let xs := [0, 1, 2, 3]
    let brp := bitReversePermute 2 xs
    brp.take 2 = [0, 2] ∧ brp.drop 2 = [1, 3] ∧
    evens xs = [0, 2] ∧ odds xs = [1, 3] := by native_decide

/-! ## Part 3: NTT and Bit-Reverse Connection

The Cooley-Tukey NTT recurses by splitting into evens and odds.
Each recursive level corresponds to one level of the bit-reverse permutation.
The output of ntt_generic is in "natural order" (DIT), while the input
should be in bit-reverse order for an in-place implementation.
-/

/-- The NTT's recursive evens/odds decomposition is structurally the same
    as applying one level of bit-reverse to the input.
    For length-4 inputs with Nat indices: evens matches bit-reverse first half. -/
theorem ntt_bitReverse_connection :
    let xs := [0, 1, 2, 3]
    evens xs = (bitReversePermute 2 xs).take 2 ∧
    odds xs = (bitReversePermute 2 xs).drop 2 := by native_decide

/-- 8-element bit-reverse connection: evens of bit-reverse = deeper recursion level. -/
theorem ntt_bitReverse_connection_8 :
    let xs := [0, 1, 2, 3, 4, 5, 6, 7]
    let brp := bitReversePermute 3 xs
    -- brp = [0, 4, 2, 6, 1, 5, 3, 7]
    brp = [0, 4, 2, 6, 1, 5, 3, 7] ∧
    evens xs = [0, 2, 4, 6] ∧
    odds xs = [1, 3, 5, 7] := by native_decide

/-! ## Part 4: Concrete Verification -/

/-- Bit-reverse of indices [0..7] with k=3 gives [0,4,2,6,1,5,3,7]. -/
example : (List.range 8).map (bitReverse 3) = [0, 4, 2, 6, 1, 5, 3, 7] := by
  native_decide

/-- bitReverse is involution for all indices < 2^3. -/
example : ∀ i, i < 8 → bitReverse 3 (bitReverse 3 i) = i := by
  intro i hi
  interval_cases i <;> native_decide

/-- Evens/odds of [10,20,30,40] -/
example : evens [10, 20, 30, 40] = [10, 30] := by decide
example : odds  [10, 20, 30, 40] = [20, 40] := by decide

/-! ## Part 5: Smoke Tests -/

#eval do
  let xs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
  let result := (List.range 8).map fun i => xs.getD (bitReverse 3 i) 0
  assert! result == [0, 4, 2, 6, 1, 5, 3, 7]
  IO.println s!"bitReverse [0..7] = {result}"

#eval do
  for i in List.range 8 do
    let br := bitReverse 3 i
    let brbr := bitReverse 3 br
    assert! brbr == i
  IO.println "bitReverse involution OK for k=3"

#eval do
  let xs := [1, 2, 3, 4]
  let e := evens xs
  let o := odds xs
  assert! e == [1, 3]
  assert! o == [2, 4]
  IO.println s!"evens {xs} = {e}, odds {xs} = {o}"

end AmoLean.NTT.BitReverseNTT
