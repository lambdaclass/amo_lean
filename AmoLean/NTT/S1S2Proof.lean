/-
  Proof development for S1 and S2: ntt_coeff_add and ntt_coeff_scale
-/

import AmoLean.NTT.Field
import Mathlib.Tactic

namespace AmoLean.NTT.S1S2Proof

variable {F : Type*} [inst : NTTFieldLawful F]

/-!
## S2: ntt_coeff_scale

Goal: ntt_coeff ω (a.map (inst.mul c)) k = inst.mul c (ntt_coeff ω a k)

Strategy: Use a generalized induction showing that for any accumulator `acc`:
  foldl_scaled (c*acc) indices = c * foldl acc indices
-/

-- Key insight: (a.map f)[i]? = (a[i]?).map f
omit inst in
lemma getElem?_map' (a : List F) (f : F → F) (i : Nat) :
    (a.map f)[i]? = (a[i]?).map f := List.getElem?_map f a i

-- Key insight: (a.map f).length = a.length
omit inst in
lemma length_map' (a : List F) (f : F → F) : (a.map f).length = a.length :=
  List.length_map a f

-- For the scaled term: (c * aᵢ) * ωⁱᵏ = c * (aᵢ * ωⁱᵏ)
lemma scale_term (c aᵢ ωpow : F) :
    (c * aᵢ) * ωpow = c * (aᵢ * ωpow) := by
  rw [NTTFieldLawful.mul_assoc]

-- Key: c * (acc + x) = c*acc + c*x (left distributivity)
lemma mul_add_distrib (c acc x : F) :
    c * (acc + x) = c * acc + c * x := by
  rw [NTTFieldLawful.mul_comm c, NTTFieldLawful.add_mul, NTTFieldLawful.mul_comm acc, NTTFieldLawful.mul_comm x]

/-!
## Generalized foldl lemma for S2

The key insight is to prove a stronger statement:
For any accumulator acc, the scaled foldl starting from (c*acc) equals
c times the foldl starting from acc.
-/

/-- Generalized foldl scale lemma with arbitrary accumulator -/
lemma foldl_scale_general (c : F) (a : List F) (ω : F) (k : Nat)
    (indices : List Nat) (acc : F) :
    indices.foldl
      (fun ac i => match (a.map (c * ·))[i]? with
        | some aᵢ => ac + aᵢ * NTTField.pow ω (i * k)
        | none => ac)
      (c * acc) =
    c * (indices.foldl
      (fun ac i => match a[i]? with
        | some aᵢ => ac + aᵢ * NTTField.pow ω (i * k)
        | none => ac)
      acc) := by
  induction indices generalizing acc with
  | nil => simp only [List.foldl_nil]
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [getElem?_map']
    cases ha : a[i]? with
    | none =>
      simp only [Option.map_none']
      exact ih acc
    | some aᵢ =>
      simp only [Option.map_some']
      -- LHS accumulator: c*acc + (c*aᵢ)*ω^(ik)
      -- RHS accumulator: acc + aᵢ*ω^(ik)
      -- Need: c*(acc + aᵢ*ω^(ik)) = c*acc + (c*aᵢ)*ω^(ik)
      have h_acc_eq : c * acc + (c * aᵢ) * NTTField.pow ω (i * k) =
          c * (acc + aᵢ * NTTField.pow ω (i * k)) := by
        rw [mul_add_distrib, scale_term]
      rw [h_acc_eq]
      exact ih (acc + aᵢ * NTTField.pow ω (i * k))

/-- S2 main theorem: scaling distributes through ntt_coeff -/
theorem ntt_coeff_scale_proof (ω : F) (a : List F) (c : F) (k : Nat) :
    (List.range (a.map (c * ·)).length).foldl (init := (0 : F))
      (fun acc i => match (a.map (c * ·))[i]? with
        | some aᵢ => acc + aᵢ * NTTField.pow ω (i * k)
        | none => acc) =
    c * ((List.range a.length).foldl (init := (0 : F))
      (fun acc i => match a[i]? with
        | some aᵢ => acc + aᵢ * NTTField.pow ω (i * k)
        | none => acc)) := by
  rw [length_map']
  -- Need to show: foldl_scaled zero = c * foldl zero
  -- Use generalized lemma with acc = zero, noting c * zero = zero
  have h_init : c * (0 : F) = 0 := by
    rw [NTTFieldLawful.mul_comm, NTTFieldLawful.zero_mul]
  conv_lhs => rw [← h_init]
  exact foldl_scale_general c a ω k (List.range a.length) 0

/-!
## S1: ntt_coeff_add

Goal: ntt_coeff ω (List.zipWith inst.add a b) k = inst.add (ntt_coeff ω a k) (ntt_coeff ω b k)

This is more complex because zipWith involves two lists.
Strategy: Show that for matching indices, (a[i] + b[i]) * ω^(ik) = a[i]*ω^(ik) + b[i]*ω^(ik)
-/

-- Key insight: (List.zipWith f a b)[i]? behavior
omit inst in
lemma getElem?_zipWith' (f : F → F → F) (a b : List F) (i : Nat) :
    (List.zipWith f a b)[i]? = match a[i]?, b[i]? with
      | some x, some y => some (f x y)
      | _, _ => none := by
  cases ha : a[i]? <;> cases hb : b[i]? <;> simp [List.getElem?_zipWith, ha, hb]

-- Length of zipWith
omit inst in
lemma length_zipWith' (f : F → F → F) (a b : List F) :
    (List.zipWith f a b).length = min a.length b.length :=
  List.length_zipWith f a b

-- Right distributivity: (aᵢ + bᵢ) * ω^(ik) = aᵢ*ω^(ik) + bᵢ*ω^(ik)
lemma add_term_distrib (aᵢ bᵢ ωpow : F) :
    (aᵢ + bᵢ) * ωpow = aᵢ * ωpow + bᵢ * ωpow := by
  rw [NTTFieldLawful.add_mul]

-- Associativity of addition: (w + x) + (y + z) = (w + y) + (x + z)
lemma add_assoc_4 (w x y z : F) :
    (w + x) + (y + z) = (w + y) + (x + z) := by
  calc (w + x) + (y + z) = w + (x + (y + z)) := by rw [NTTFieldLawful.add_assoc]
    _ = w + ((x + y) + z) := by rw [← NTTFieldLawful.add_assoc x y z]
    _ = w + ((y + x) + z) := by rw [NTTFieldLawful.add_comm x y]
    _ = w + (y + (x + z)) := by rw [NTTFieldLawful.add_assoc y x z]
    _ = (w + y) + (x + z) := by rw [← NTTFieldLawful.add_assoc w y (x + z)]

/-- Generalized foldl add lemma: accumulating in parallel -/
lemma foldl_add_general (a b : List F) (ω : F) (k : Nat)
    (indices : List Nat) (acc_ab acc_a acc_b : F)
    (heq : a.length = b.length)
    (h_acc : acc_ab = acc_a + acc_b) :
    indices.foldl
      (fun ac i => match (List.zipWith (· + ·) a b)[i]? with
        | some xi => ac + xi * NTTField.pow ω (i * k)
        | none => ac)
      acc_ab =
    (indices.foldl
        (fun ac i => match a[i]? with
          | some aᵢ => ac + aᵢ * NTTField.pow ω (i * k)
          | none => ac)
        acc_a) +
      (indices.foldl
        (fun ac i => match b[i]? with
          | some bᵢ => ac + bᵢ * NTTField.pow ω (i * k)
          | none => ac)
        acc_b) := by
  induction indices generalizing acc_ab acc_a acc_b with
  | nil =>
    simp only [List.foldl_nil]
    exact h_acc
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [getElem?_zipWith']
    -- Case split on whether both a[i]? and b[i]? are some
    cases ha : a[i]? with
    | none =>
      simp only
      -- Since a.length = b.length, if a[i]? = none then b[i]? = none too
      have hb : b[i]? = none := by
        by_contra hne
        push_neg at hne
        have ⟨bi, hbi⟩ := Option.ne_none_iff_exists'.mp hne
        have hi_lt_b : i < b.length := List.getElem?_eq_some_iff.mp hbi |>.1
        have hi_lt_a : i < a.length := by omega
        have hsome : a[i]? = some (a[i]'hi_lt_a) := List.getElem?_eq_some_iff.mpr ⟨hi_lt_a, rfl⟩
        rw [ha] at hsome
        exact Option.noConfusion hsome
      simp only [hb]
      exact ih acc_ab acc_a acc_b h_acc
    | some aᵢ =>
      cases hb : b[i]? with
      | none =>
        -- If a[i]? = some but b[i]? = none with heq, contradiction
        simp only
        have hi_lt_a : i < a.length := List.getElem?_eq_some_iff.mp ha |>.1
        have hi_lt_b : i < b.length := by omega
        have hsome : b[i]? = some (b[i]'hi_lt_b) := List.getElem?_eq_some_iff.mpr ⟨hi_lt_b, rfl⟩
        rw [hb] at hsome
        exact Option.noConfusion hsome
      | some bᵢ =>
        simp only
        -- Both a[i]? = some aᵢ and b[i]? = some bᵢ
        have h_new_acc : acc_ab + (aᵢ + bᵢ) * NTTField.pow ω (i * k) =
            (acc_a + aᵢ * NTTField.pow ω (i * k)) +
            (acc_b + bᵢ * NTTField.pow ω (i * k)) := by
          rw [h_acc, add_term_distrib, add_assoc_4]
        exact ih _ _ _ h_new_acc

/-- S1 main theorem: addition distributes through ntt_coeff -/
theorem ntt_coeff_add_proof (ω : F) (a b : List F) (k : Nat)
    (heq : a.length = b.length) :
    (List.range (List.zipWith (· + ·) a b).length).foldl (init := (0 : F))
      (fun acc i => match (List.zipWith (· + ·) a b)[i]? with
        | some xi => acc + xi * NTTField.pow ω (i * k)
        | none => acc) =
    ((List.range a.length).foldl (init := (0 : F))
        (fun acc i => match a[i]? with
          | some aᵢ => acc + aᵢ * NTTField.pow ω (i * k)
          | none => acc)) +
      ((List.range b.length).foldl (init := (0 : F))
        (fun acc i => match b[i]? with
          | some bᵢ => acc + bᵢ * NTTField.pow ω (i * k)
          | none => acc)) := by
  rw [length_zipWith']
  -- min a.length b.length = a.length = b.length when heq
  have h_min : min a.length b.length = a.length := by omega
  rw [h_min, heq]
  -- Now use the generalized lemma with zero accumulators
  have h_init : (0 : F) = 0 + 0 := by
    rw [NTTFieldLawful.add_zero]
  exact foldl_add_general a b ω k (List.range b.length) 0 0 0 heq h_init

end AmoLean.NTT.S1S2Proof
