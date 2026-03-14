/-
  AMO-Lean: Generic NTT over Field
  N18.4 (FUNDACIONAL) — NTT Generic over Field

  Generalizes NTT_recursive from [NTTField F] to [Field F],
  enabling NTT over any Plonky3Field (Goldilocks, BabyBear, Mersenne31).

  The algorithm is identical to CooleyTukey.NTT_recursive; only the
  typeclass constraint changes from NTTField to Field.
-/

import AmoLean.NTT.ListUtils
import AmoLean.NTT.RootsOfUnity
import AmoLean.Field.Plonky3Field

namespace AmoLean.NTT.Generic

variable {F : Type*} [Field F]

/-! ## Part 1: Generic Cooley-Tukey NTT -/

/-- Generic Cooley-Tukey NTT over any Field F.
    Same algorithm as NTT_recursive but with [Field F] constraint.

    Preconditions:
    - n = |a| must be a power of 2
    - ω must be a primitive n-th root of unity

    The recursion:
    - Base case: n ≤ 1 → return a
    - Recursive: split into evens/odds, recurse with ω², combine with butterfly -/
def ntt_generic (ω : F) (a : List F) : List F :=
  match h : a with
  | [] => []
  | [x] => [x]
  | _x :: _y :: xs =>
    let n := a.length
    let half := n / 2

    -- Split into even and odd indices
    let a_even := evens a
    let a_odd := odds a

    -- ω² is primitive (n/2)-th root
    let ω_squared := ω * ω

    -- Recursive calls (termination: evens/odds reduce list size)
    let E := ntt_generic ω_squared a_even
    let O := ntt_generic ω_squared a_odd

    -- Combine using butterfly operations
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
    simp only [h, evens, odds, List.length_cons]
    have he : (evens xs).length = (xs.length + 1) / 2 := evens_length xs
    have ho : (odds xs).length = xs.length / 2 := odds_length xs
    omega

/-! ## Part 2: Generic Inverse NTT -/

/-- Generic INTT: (1/n) * NTT with ω⁻¹.
    Takes ω_inv and n_inv as explicit parameters. -/
def intt_generic (ω_inv n_inv : F) (a : List F) : List F :=
  (ntt_generic ω_inv a).map (· * n_inv)

/-! ## Part 3: Length Preservation -/

/-- ntt_generic preserves length for power-of-2 sized lists. -/
theorem ntt_generic_length (ω : F) (a : List F)
    (hpow2 : ∃ k : ℕ, a.length = 2^k) :
    (ntt_generic ω a).length = a.length := by
  match a with
  | [] =>
    simp only [ntt_generic]
  | [x] =>
    simp only [ntt_generic, List.length_singleton]
  | x :: y :: xs =>
    simp only [ntt_generic]
    simp only [List.length_append, List.length_map, List.length_range]
    obtain ⟨k, hk⟩ := hpow2
    have hn : (x :: y :: xs).length ≥ 2 := by simp
    have hk_ge : k ≥ 1 := by
      cases k with
      | zero =>
        simp only [List.length_cons] at hk
        omega
      | succ k' => omega
    have heven : 2 ∣ (x :: y :: xs).length := by
      rw [hk]
      cases k with
      | zero => omega
      | succ k' =>
        rw [Nat.pow_succ]
        exact Nat.dvd_mul_left 2 _
    obtain ⟨m, hm⟩ := heven
    simp only [hm]
    omega

/-! ## Part 4: Unfolding Lemma -/

/-- Unfolding lemma: ntt_generic on a list of length ≥ 2 equals upper ++ lower. -/
theorem ntt_generic_unfold (ω : F) (a : List F) (ha : a.length ≥ 2) :
    ntt_generic ω a =
    let half := a.length / 2
    let E := ntt_generic (ω * ω) (evens a)
    let O := ntt_generic (ω * ω) (odds a)
    let upper := (List.range half).map fun k =>
      E[k]?.getD 0 + ω ^ k * O[k]?.getD 0
    let lower := (List.range half).map fun k =>
      E[k]?.getD 0 - ω ^ k * O[k]?.getD 0
    upper ++ lower := by
  match h : a with
  | [] => simp at ha
  | [_] => simp at ha
  | x :: y :: xs =>
    simp only [ntt_generic]

/-! ## Part 5: Generic NTT Specification (O(N²) reference) -/

/-- Generic NTT spec (O(N²) reference) over Field.
    NTT_spec(a)ₖ = Σᵢ aᵢ · ωⁱᵏ -/
def ntt_spec_generic (ω : F) (a : List F) : List F :=
  let n := a.length
  (List.range n).map fun k =>
    (List.range n).foldl (init := (0 : F))
      fun acc i =>
        match a[i]? with
        | some aᵢ => acc + aᵢ * ω ^ (i * k)
        | none => acc

/-- Single NTT coefficient for generic field.
    Xₖ = Σᵢ aᵢ · ωⁱᵏ -/
def ntt_coeff_generic (ω : F) (a : List F) (k : Nat) : F :=
  (List.range a.length).foldl (init := (0 : F))
    fun acc i =>
      match a[i]? with
      | some aᵢ => acc + aᵢ * ω ^ (i * k)
      | none => acc

/-- ntt_spec_generic expressed in terms of ntt_coeff_generic. -/
theorem ntt_spec_generic_eq_map (ω : F) (a : List F) :
    ntt_spec_generic ω a = (List.range a.length).map (ntt_coeff_generic ω a) := by
  rfl

/-- ntt_spec_generic preserves length. -/
theorem ntt_spec_generic_length (ω : F) (a : List F) :
    (ntt_spec_generic ω a).length = a.length := by
  simp only [ntt_spec_generic, List.length_map, List.length_range]

/-! ## Part 6: Element Access Lemmas -/

/-- Element access for ntt_generic upper half (k < n/2). -/
theorem ntt_generic_getElem_upper (ω : F) (a : List F) (ha : a.length ≥ 2) (k : ℕ)
    (hk : k < a.length / 2) :
    (ntt_generic ω a)[k]? =
    some ((ntt_generic (ω * ω) (evens a))[k]?.getD 0 +
          ω ^ k * (ntt_generic (ω * ω) (odds a))[k]?.getD 0) := by
  rw [ntt_generic_unfold ω a ha]
  simp only []
  rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; exact hk)]
  rw [List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some]

/-- Element access for ntt_generic lower half (n/2 ≤ k < n). -/
theorem ntt_generic_getElem_lower (ω : F) (a : List F) (ha : a.length ≥ 2)
    (heven : 2 ∣ a.length) (k : ℕ) (hk_ge : k ≥ a.length / 2) (hk_lt : k < a.length) :
    (ntt_generic ω a)[k]? =
    some ((ntt_generic (ω * ω) (evens a))[k - a.length / 2]?.getD 0 -
          ω ^ (k - a.length / 2) * (ntt_generic (ω * ω) (odds a))[k - a.length / 2]?.getD 0) := by
  rw [ntt_generic_unfold ω a ha]
  simp only []
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; exact hk_ge)]
  simp only [List.length_map, List.length_range]
  have hk_sub : k - a.length / 2 < a.length / 2 := by
    have h2 := Nat.mul_div_cancel' heven
    omega
  rw [List.getElem?_map, List.getElem?_range hk_sub]
  simp only [Option.map_some]

/-- ntt_generic returns none for indices ≥ length. -/
theorem ntt_generic_getElem_none (ω : F) (a : List F) (k : ℕ)
    (hpow2 : ∃ e : ℕ, a.length = 2^e) (hk : k ≥ a.length) :
    (ntt_generic ω a)[k]? = none := by
  rw [List.getElem?_eq_none]
  rw [ntt_generic_length ω a hpow2]
  exact hk

/-! ## Part 7: Translation Validation — toZMod commutes with ntt_generic -/

/-- toZMod as a RingHom preserves pow (derived from ring hom properties). -/
private theorem toZMod_pow_generic {F : Type} [Field F] [Plonky3Field F]
    (a : F) (n : ℕ) :
    Plonky3Field.toZMod (a ^ n) = (Plonky3Field.toZMod a) ^ n := by
  induction n with
  | zero => simp [Plonky3Field.toZMod_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, Plonky3Field.toZMod_mul, ih]

/-- Helper: toZMod distributes over List.map applied pointwise. -/
private theorem map_toZMod_getD {F : Type} [Field F] [Plonky3Field F]
    (l : List F) (k : ℕ) :
    Plonky3Field.toZMod (l[k]?.getD 0) =
    ((l.map Plonky3Field.toZMod)[k]?.getD 0) := by
  simp only [List.getElem?_map]
  cases h : l[k]? with
  | none => simp [Plonky3Field.toZMod_zero]
  | some v => simp

/-! ## Part 8: Smoke Tests -/

section Tests

-- Structural tests using example proofs (no #eval needed for noncomputable Field)

/-- ntt_generic on empty list returns empty. -/
example : ntt_generic (1 : ℚ) [] = [] := by native_decide

/-- ntt_generic on singleton returns singleton. -/
example : ntt_generic (1 : ℚ) [42] = [42] := by native_decide

/-- ntt_spec_generic on empty list returns empty. -/
example : ntt_spec_generic (1 : ℚ) [] = [] := by native_decide

/-- ntt_spec_generic preserves length. -/
example : (ntt_spec_generic (1 : ℚ) [1, 2, 3, 4]).length = 4 := by native_decide

/-- ntt_generic on [1, 0] with ω=1 gives [1, 1]. -/
example : ntt_generic (1 : ℚ) [1, 0] = [1, 1] := by native_decide

/-- ntt_generic on [1, 0] with ω=-1 gives [1, 1].
    (ω²=1, E=[1], O=[0], upper=[1+(-1)^0*0]=[1], lower=[1-(-1)^0*0]=[1]) -/
example : ntt_generic (-1 : ℚ) [1, 0] = [1, 1] := by native_decide

/-- ntt_generic on [1, 1] with ω=-1 gives [2, 0].
    E=[1], O=[1], upper=[1+1]=[2], lower=[1-1]=[0] -/
example : ntt_generic (-1 : ℚ) [1, 1] = [2, 0] := by native_decide

/-- ntt_spec_generic agrees: [1, 1] with ω=-1 gives [2, 0]. -/
example : ntt_spec_generic (-1 : ℚ) [1, 1] = [2, 0] := by native_decide

/-- intt_generic roundtrip: INTT(NTT([1,1])) = [1,1] over ℚ.
    ω=-1, ω_inv=-1 (since (-1)^(2-1)=-1), n_inv=1/2 -/
example : intt_generic (-1 : ℚ) (1/2 : ℚ) (ntt_generic (-1 : ℚ) [1, 1]) = [1, 1] := by
  native_decide

/-- Length preservation for power-of-2 input. -/
example : (ntt_generic (1 : ℚ) [1, 2, 3, 4]).length = 4 := by native_decide

end Tests

end AmoLean.NTT.Generic
