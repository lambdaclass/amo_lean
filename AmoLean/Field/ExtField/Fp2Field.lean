/-
  AMO-Lean: Fp2 Field Instance
  N18.2 (CRITICO) — Field instance for Fp2 F W when W is a non-square

  Key construction:
  - IsNonSquare W: typeclass expressing that W has no square root in F
  - norm_ne_zero: if W is a non-square and a ≠ 0 in Fp2, then norm(a) ≠ 0
  - Fp2.inv': inverse via (c0/N, -c1/N) where N = c0² - W*c1²
  - Field instance: mul_inv_cancel proved via norm_ne_zero

  Plonky3Field for Fp2: The current Plonky3Field typeclass requires an injective
  map to ZMod p, but Fp2 has p² elements. A proper instance needs either
  ZMod(p²) target or a generalized typeclass. Deferred to a future phase.

  0 sorry, 0 axioms.
-/

import AmoLean.Field.ExtField.Fp2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Classical

namespace AmoLean.Field.ExtField

open Fp2

/-! ## Part 1: IsNonSquare Typeclass -/

/-- W is a non-square in F: no element x satisfies x * x = W.
    This is the condition under which F[u]/(u² - W) is a field. -/
class IsNonSquare {F : Type*} [Field F] (W : F) : Prop where
  not_square : ∀ x : F, x * x ≠ W

/-! ## Part 2: Norm Properties -/

variable {F : Type*} [Field F] {W : F}

/-- The norm of an Fp2 element is nonzero for nonzero elements when W is a non-square.

    Proof by contradiction:
    - If norm(a) = 0, then c0² = W * c1².
    - Case c1 ≠ 0: then W = (c0/c1)², contradicting IsNonSquare.
    - Case c1 = 0: then c0² = 0, so c0 = 0, hence a = 0, contradiction. -/
theorem Fp2.norm_ne_zero [IsNonSquare W] (a : Fp2 F W) (ha : a ≠ 0) :
    Fp2.norm a ≠ 0 := by
  intro hnorm
  -- hnorm : norm a = 0, i.e., a.c0 * a.c0 - W * (a.c1 * a.c1) = 0
  have heq : a.c0 * a.c0 = W * (a.c1 * a.c1) := by
    have hdef : Fp2.norm a = a.c0 * a.c0 - W * (a.c1 * a.c1) := rfl
    rw [hdef] at hnorm
    exact sub_eq_zero.mp hnorm
  by_cases hc1 : a.c1 = 0
  · -- c1 = 0 ⟹ c0² = 0 ⟹ c0 = 0 ⟹ a = 0, contradiction
    rw [hc1, mul_zero, mul_zero] at heq
    have hc0 : a.c0 = 0 := mul_self_eq_zero.mp heq
    exact ha (Fp2.ext hc0 hc1)
  · -- c1 ≠ 0 ⟹ W = (c0/c1)², contradicting IsNonSquare
    have hW : a.c0 / a.c1 * (a.c0 / a.c1) = W := by
      field_simp
      simp only [sq]
      rw [heq]
      ring
    exact IsNonSquare.not_square (a.c0 / a.c1) hW

/-! ## Part 3: Inverse -/

/-- Fp2 inverse: (c0, c1)⁻¹ = (c0/N, -c1/N) where N = norm(a) = c0² - W*c1².
    Returns 0 for the zero element. -/
noncomputable def Fp2.inv' [IsNonSquare W] (a : Fp2 F W) : Fp2 F W :=
  if a = 0 then 0
  else
    let n := Fp2.norm a
    ⟨a.c0 / n, -a.c1 / n⟩

/-- Fp2 division: a / b = a * b⁻¹. -/
noncomputable def Fp2.div' [IsNonSquare W] (a b : Fp2 F W) : Fp2 F W :=
  a * Fp2.inv' b

/-! ## Part 4: exists_pair_ne -/

/-- Fp2 has at least two distinct elements: 0 ≠ 1. -/
theorem Fp2.zero_ne_one : (0 : Fp2 F W) ≠ 1 := by
  intro h
  have := congr_arg Fp2.c0 h
  simp at this

/-! ## Part 5: mul_inv_cancel -/

/-- a * a⁻¹ = 1 for nonzero a in Fp2. -/
theorem Fp2.mul_inv_cancel' [IsNonSquare W] (a : Fp2 F W) (ha : a ≠ 0) :
    a * Fp2.inv' a = 1 := by
  have hn_ne : Fp2.norm a ≠ 0 := Fp2.norm_ne_zero a ha
  unfold Fp2.inv'
  rw [if_neg ha]
  ext
  · -- c0: a.c0 * (a.c0 / N) + W * (a.c1 * (-a.c1 / N)) = 1
    simp only [mul_c0, one_c0]
    have hnorm_def : Fp2.norm a = a.c0 * a.c0 - W * (a.c1 * a.c1) := rfl
    field_simp
    simp only [sq]
    rw [hnorm_def]
    ring
  · -- c1: a.c0 * (-a.c1 / N) + a.c1 * (a.c0 / N) = 0
    simp only [mul_c1, one_c1]
    field_simp
    ring

/-! ## Part 6: inv_zero -/

/-- inv(0) = 0 in Fp2. -/
theorem Fp2.inv_zero' [IsNonSquare W] :
    Fp2.inv' (0 : Fp2 F W) = 0 := by
  unfold Fp2.inv'
  rw [if_pos rfl]

/-! ## Part 7: Field Instance -/

/-- Field instance for Fp2 F W when W is a non-square in F.
    Noncomputable because inv involves division in F. -/
noncomputable instance Fp2.instField [IsNonSquare W] : Field (Fp2 F W) where
  exists_pair_ne := ⟨0, 1, Fp2.zero_ne_one⟩
  inv := Fp2.inv'
  mul_inv_cancel := fun a ha => Fp2.mul_inv_cancel' a ha
  inv_zero := Fp2.inv_zero'
  div := Fp2.div'
  div_eq_mul_inv := fun _ _ => rfl
  zpow := fun n a =>
    if n ≥ 0
    then Fp2.npow n.toNat a
    else Fp2.inv' (Fp2.npow (-n).toNat a)
  zpow_zero' := fun _ => by
    simp only [ge_iff_le, le_refl, ↓reduceIte, Int.toNat_zero, Fp2.npow]
    rfl
  zpow_succ' := fun n a => by
    simp only [ge_iff_le]
    rw [if_pos (Int.natCast_nonneg n.succ)]
    rw [if_pos (Int.natCast_nonneg n)]
    simp only [Int.toNat_natCast]
    show Fp2.npow (n + 1) a = Fp2.npow n a * a
    simp only [Fp2.npow, Fp2.mul]
    ext <;> simp <;> ring
  zpow_neg' := fun n a => by
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
    rw [if_pos (Int.natCast_nonneg (n + 1))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]
    rfl
  nnratCast := fun q => Fp2.div' (q.num : Fp2 F W) (q.den : Fp2 F W)
  nnratCast_def := fun _ => rfl
  nnqsmul := fun q a => Fp2.div' (q.num : Fp2 F W) (q.den : Fp2 F W) * a
  nnqsmul_def := fun _ _ => rfl
  ratCast := fun q => Fp2.div' (q.num : Fp2 F W) (q.den : Fp2 F W)
  ratCast_def := fun _ => rfl
  qsmul := fun q a => Fp2.div' (q.num : Fp2 F W) (q.den : Fp2 F W) * a
  qsmul_def := fun _ _ => rfl

/-! ## Part 8: Non-Vacuity Examples -/

section NonVacuity

/-- -1 is a non-square in Rat (no rational x satisfies x² = -1). -/
instance : IsNonSquare ((-1 : Rat)) where
  not_square := by
    intro x habs
    have h1 : x * x ≥ 0 := mul_self_nonneg x
    have h2 : x * x = -1 := habs
    linarith

/-- Non-vacuity: Field instance exists for Fp2 Rat (-1) (Gaussian rationals). -/
noncomputable example : Field (Fp2 Rat (-1)) := inferInstance

/-- Non-vacuity: (1 + i) has a well-defined inverse in Q[i]. -/
noncomputable example : (⟨1, 1⟩ : Fp2 Rat (-1)) * Fp2.inv' (⟨1, 1⟩ : Fp2 Rat (-1)) = 1 :=
  Fp2.mul_inv_cancel' ⟨1, 1⟩ (by intro h; have := congr_arg Fp2.c1 h; simp at this)

/-- Non-vacuity: norm(1 + i) = 1 - (-1)*1 = 2. -/
example : Fp2.norm (⟨1, 1⟩ : Fp2 Rat (-1)) = 2 := by
  simp [Fp2.norm]; ring

/-- Non-vacuity: norm_ne_zero holds concretely. -/
example : Fp2.norm (⟨1, 1⟩ : Fp2 Rat (-1)) ≠ 0 := by
  simp [Fp2.norm]; norm_num

end NonVacuity

end AmoLean.Field.ExtField
