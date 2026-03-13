/-
  AMO-Lean: Plonky3Field Typeclass
  Fase 17 Nodo 6 — N17.6: Unifying Typeclass for Plonky3-Verified Fields

  Defines a typeclass that captures the common structure shared by all
  Plonky3 prime fields: Mersenne31, BabyBear, and Goldilocks.

  Each field carries:
  - A prime characteristic `char`
  - A ring homomorphism `toZMod : F → ZMod char` that is injective
  - Proofs that toZMod preserves +, *, 0, 1

  This allows writing generic lemmas once and instantiating for any
  Plonky3-verified field.

  Design: parameterized over representation type F (not bounded to 32-bit),
  so extension fields (e.g., BabyBear^4) can also be instances in the future.
  Uses `[Field F]` as a prerequisite rather than `extends Field F` to avoid
  diamond issues with existing instances.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

import AmoLean.Field.Mersenne31
import AmoLean.Field.BabyBear
import AmoLean.Field.Goldilocks

/-! ## Part 1: Plonky3Field Typeclass -/

/-- A field verified to match a Plonky3 implementation.

    Parameterized over the field type `F`.
    Requires `Field F` as a prerequisite (avoids diamond with existing instances).
    Carries the characteristic, `toZMod` homomorphism, and injectivity proof.

    Extension-field-ready: `char` is `Nat` (not bounded to 32-bit).

    The `toZMod` map is an injective ring homomorphism `F → ZMod char`,
    which proves that `F ≅ ZMod char` as rings. All algebraic properties
    of `F` can then be transferred from `ZMod char`. -/
class Plonky3Field (F : Type) [Field F] where
  /-- The prime characteristic -/
  char : Nat
  /-- Proof that `char` is prime -/
  char_prime : Nat.Prime char
  /-- Ring homomorphism to `ZMod char` -/
  toZMod : F → ZMod char
  /-- `toZMod` is injective (field is isomorphic to `ZMod char`) -/
  toZMod_injective : Function.Injective toZMod
  /-- `toZMod` preserves addition -/
  toZMod_add : ∀ a b : F, toZMod (a + b) = toZMod a + toZMod b
  /-- `toZMod` preserves multiplication -/
  toZMod_mul : ∀ a b : F, toZMod (a * b) = toZMod a * toZMod b
  /-- `toZMod` preserves zero -/
  toZMod_zero : toZMod 0 = 0
  /-- `toZMod` preserves one -/
  toZMod_one : toZMod 1 = 1

namespace Plonky3Field

variable {F : Type} [Field F] [Plonky3Field F]

/-! ## Part 2: Derived Fact Instance -/

/-- `Fact (Nat.Prime (Plonky3Field.char F))` for Mathlib interop. -/
instance charPrimeFact : Fact (Nat.Prime (Plonky3Field.char F)) :=
  ⟨Plonky3Field.char_prime⟩

/-! ## Part 3: Generic Lemmas -/

/-- Generic: any Plonky3Field addition is correct in `ZMod`. -/
theorem add_correct (a b : F) :
    Plonky3Field.toZMod (a + b) = Plonky3Field.toZMod a + Plonky3Field.toZMod b :=
  Plonky3Field.toZMod_add a b

/-- Generic: any Plonky3Field multiplication is correct in `ZMod`. -/
theorem mul_correct (a b : F) :
    Plonky3Field.toZMod (a * b) = Plonky3Field.toZMod a * Plonky3Field.toZMod b :=
  Plonky3Field.toZMod_mul a b

/-- Generic: `toZMod` preserves negation. -/
theorem toZMod_neg (a : F) :
    Plonky3Field.toZMod (-a) = -Plonky3Field.toZMod a := by
  have h : Plonky3Field.toZMod a + Plonky3Field.toZMod (-a) = 0 := by
    rw [← Plonky3Field.toZMod_add, add_neg_cancel, Plonky3Field.toZMod_zero]
  exact eq_neg_of_add_eq_zero_right h

/-- Generic: `toZMod` preserves subtraction. -/
theorem toZMod_sub (a b : F) :
    Plonky3Field.toZMod (a - b) = Plonky3Field.toZMod a - Plonky3Field.toZMod b := by
  rw [sub_eq_add_neg, Plonky3Field.toZMod_add, toZMod_neg, ← sub_eq_add_neg]

/-- Generic: two elements are equal iff their `toZMod` images are equal. -/
theorem eq_iff_toZMod_eq (a b : F) :
    a = b ↔ Plonky3Field.toZMod a = Plonky3Field.toZMod b :=
  ⟨fun h => congrArg _ h, fun h => Plonky3Field.toZMod_injective h⟩

/-- Generic: `toZMod` is a `RingHom`. -/
noncomputable def toZModRingHom : F →+* ZMod (Plonky3Field.char F) where
  toFun := Plonky3Field.toZMod
  map_one' := Plonky3Field.toZMod_one
  map_mul' := Plonky3Field.toZMod_mul
  map_zero' := Plonky3Field.toZMod_zero
  map_add' := Plonky3Field.toZMod_add

end Plonky3Field

/-! ## Part 4: Instances for Plonky3 Fields -/

/-! ### Mersenne31Field Instance -/

noncomputable instance : Plonky3Field AmoLean.Field.Mersenne31.Mersenne31Field where
  char := AmoLean.Field.Mersenne31.ORDER_NAT
  char_prime := AmoLean.Field.Mersenne31.mersenne31_prime_is_prime
  toZMod := AmoLean.Field.Mersenne31.toZMod
  toZMod_injective := AmoLean.Field.Mersenne31.toZMod_injective
  toZMod_add := AmoLean.Field.Mersenne31.toZMod_add
  toZMod_mul := AmoLean.Field.Mersenne31.toZMod_mul
  toZMod_zero := AmoLean.Field.Mersenne31.toZMod_zero
  toZMod_one := AmoLean.Field.Mersenne31.toZMod_one

/-! ### BabyBearField Instance -/

noncomputable instance : Plonky3Field AmoLean.Field.BabyBear.BabyBearField where
  char := AmoLean.Field.BabyBear.ORDER_NAT
  char_prime := AmoLean.Field.BabyBear.babybear_prime_is_prime
  toZMod := AmoLean.Field.BabyBear.toZMod
  toZMod_injective := AmoLean.Field.BabyBear.toZMod_injective
  toZMod_add := AmoLean.Field.BabyBear.toZMod_add
  toZMod_mul := AmoLean.Field.BabyBear.toZMod_mul
  toZMod_zero := AmoLean.Field.BabyBear.toZMod_zero
  toZMod_one := AmoLean.Field.BabyBear.toZMod_one

/-! ### GoldilocksField Instance -/

noncomputable instance : Plonky3Field AmoLean.Field.Goldilocks.GoldilocksField where
  char := AmoLean.Field.Goldilocks.ORDER_NAT
  char_prime := AmoLean.Field.Goldilocks.goldilocks_prime_is_prime
  toZMod := AmoLean.Field.Goldilocks.toZMod
  toZMod_injective := AmoLean.Field.Goldilocks.toZMod_injective
  toZMod_add := AmoLean.Field.Goldilocks.toZMod_add
  toZMod_mul := AmoLean.Field.Goldilocks.toZMod_mul
  toZMod_zero := AmoLean.Field.Goldilocks.toZMod_zero
  toZMod_one := AmoLean.Field.Goldilocks.toZMod_one

/-! ## Part 5: Non-Vacuity Examples -/

/-- Non-vacuity: Mersenne31Field is a Plonky3Field. -/
noncomputable example : Plonky3Field AmoLean.Field.Mersenne31.Mersenne31Field := inferInstance

/-- Non-vacuity: BabyBearField is a Plonky3Field. -/
noncomputable example : Plonky3Field AmoLean.Field.BabyBear.BabyBearField := inferInstance

/-- Non-vacuity: GoldilocksField is a Plonky3Field. -/
noncomputable example : Plonky3Field AmoLean.Field.Goldilocks.GoldilocksField := inferInstance

/-! ## Part 6: Generic Theorems Using the Typeclass -/

section GenericTheorems

variable {F : Type} [Field F] [Plonky3Field F]

/-- In any Plonky3Field, `toZMod (a * b + c) = toZMod a * toZMod b + toZMod c`. -/
theorem plonky3_muladd_correct (a b c : F) :
    Plonky3Field.toZMod (a * b + c) =
    Plonky3Field.toZMod a * Plonky3Field.toZMod b + Plonky3Field.toZMod c := by
  rw [Plonky3Field.toZMod_add, Plonky3Field.toZMod_mul]

/-- In any Plonky3Field, `toZMod (a * a) = toZMod a * toZMod a`. -/
theorem plonky3_sq_correct (a : F) :
    Plonky3Field.toZMod (a * a) = Plonky3Field.toZMod a * Plonky3Field.toZMod a := by
  rw [Plonky3Field.toZMod_mul]

/-- In any Plonky3Field, distinct elements map to distinct ZMod values. -/
theorem plonky3_distinct (a b : F) (h : a ≠ b) :
    Plonky3Field.toZMod a ≠ Plonky3Field.toZMod b :=
  fun heq => h (Plonky3Field.toZMod_injective heq)

end GenericTheorems
