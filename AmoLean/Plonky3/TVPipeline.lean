/-
  AMO-Lean: Plonky3 Translation Validation Pipeline — Capstone
  Fase 17 Nodo 9 — N17.9: TV Pipeline Integration

  Composes all Fase 17 results into end-to-end translation validation
  theorems for the Plonky3 proving system. For any Plonky3Field F:

    1. Field arithmetic (add, mul) preserves ZMod semantics  [Plonky3Field]
    2. NTT butterfly (DIT, DIF) preserves ZMod semantics     [ButterflyTV]
    3. FRI fold step preserves ZMod semantics                 [FoldTV]

  Each concrete field (Mersenne31, BabyBear, Goldilocks) additionally has
  refinement theorems showing Plonky3's specific implementations match the
  abstract field operations.

  Theorems: 7 definitions/theorems + 5 non-vacuity examples
  LOC: ~200, 0 sorry, 0 new axioms
-/

import AmoLean.Field.Plonky3Field
import AmoLean.Field.Plonky3.Mersenne31TV
import AmoLean.Field.Plonky3.BabyBearTV
import AmoLean.Field.Plonky3.GoldilocksTV
import AmoLean.NTT.Plonky3.ButterflyTV
import AmoLean.FRI.Plonky3.FoldTV

namespace AmoLean.Plonky3.TVPipeline

open Plonky3Field
open AmoLean.NTT.Plonky3.ButterflyTV
open AmoLean.FRI.Plonky3.FoldTV

/-! ## Part 1: TV Result Structure

A `Plonky3TVResult F` bundles the three layers of translation validation
for a Plonky3 field: field arithmetic, NTT butterfly, and FRI fold. -/

/-- Complete translation validation result for a Plonky3 proving system field.
    Captures correctness of field ops, NTT butterfly, and FRI fold in ZMod. -/
structure Plonky3TVResult (F : Type) [Field F] [Plonky3Field F] where
  /-- Field addition preserves ZMod semantics -/
  add_hom : ∀ a b : F,
    toZMod (a + b) = toZMod a + toZMod b
  /-- Field multiplication preserves ZMod semantics -/
  mul_hom : ∀ a b : F,
    toZMod (a * b) = toZMod a * toZMod b
  /-- DIT butterfly preserves ZMod semantics (both outputs) -/
  dit_correct : ∀ a b tw : F,
    toZMod (dit_butterfly a b tw).1 =
      toZMod a + toZMod tw * toZMod b ∧
    toZMod (dit_butterfly a b tw).2 =
      toZMod a - toZMod tw * toZMod b
  /-- DIF butterfly preserves ZMod semantics (both outputs) -/
  dif_correct : ∀ a b tw : F,
    toZMod (dif_butterfly a b tw).1 =
      toZMod a + toZMod b ∧
    toZMod (dif_butterfly a b tw).2 =
      (toZMod a - toZMod b) * toZMod tw
  /-- FRI fold step preserves ZMod semantics -/
  fold_correct : ∀ lo hi beta coeff two_inv : F,
    toZMod (fold_step lo hi beta coeff two_inv) =
    (toZMod lo + toZMod hi) * toZMod two_inv +
    toZMod beta * ((toZMod lo - toZMod hi) * toZMod two_inv) * toZMod coeff

/-! ## Part 2: Generic Construction

The master theorem: for ANY Plonky3Field, the TV pipeline holds.
This follows directly from the ring homomorphism properties of toZMod. -/

/-- For any Plonky3Field, the full translation validation pipeline holds.
    Composes Plonky3Field (ring hom), ButterflyTV, and FoldTV. -/
noncomputable def plonky3_tv_complete (F : Type) [Field F] [Plonky3Field F] :
    Plonky3TVResult F where
  add_hom := Plonky3Field.add_correct
  mul_hom := Plonky3Field.mul_correct
  dit_correct := dit_butterfly_correct
  dif_correct := dif_butterfly_correct
  fold_correct := fold_step_correct

/-! ## Part 3: Field-Specific Instantiations

Each Plonky3 field gets a concrete TVResult via the generic construction. -/

/-- Mersenne31 (p = 2^31 - 1) translation validation. -/
noncomputable def mersenne31_tv :
    Plonky3TVResult AmoLean.Field.Mersenne31.Mersenne31Field :=
  plonky3_tv_complete _

/-- BabyBear (p = 2^31 - 2^27 + 1) translation validation. -/
noncomputable def babybear_tv :
    Plonky3TVResult AmoLean.Field.BabyBear.BabyBearField :=
  plonky3_tv_complete _

/-- Goldilocks (p = 2^64 - 2^32 + 1) translation validation. -/
noncomputable def goldilocks_tv :
    Plonky3TVResult AmoLean.Field.Goldilocks.GoldilocksField :=
  plonky3_tv_complete _

/-! ## Part 4: Derived Theorems

Useful consequences that compose multiple layers of the TV pipeline. -/

/-- NTT-FRI composition: a DIT butterfly followed by a fold step preserves
    ZMod semantics end-to-end. This is the core of the Plonky3 prover:
    NTT transforms the evaluation domain, then FRI folds it. -/
theorem ntt_fri_composition {F : Type} [Field F] [Plonky3Field F]
    (a b tw beta coeff two_inv : F) :
    let bfly := dit_butterfly a b tw
    toZMod (fold_step bfly.1 bfly.2 beta coeff two_inv) =
    (toZMod bfly.1 + toZMod bfly.2) * toZMod two_inv +
    toZMod beta * ((toZMod bfly.1 - toZMod bfly.2) * toZMod two_inv) *
      toZMod coeff :=
  fold_step_correct _ _ _ _ _

/-- The TV result is unique: any two constructions agree (they are
    propositionally equal since all fields are Prop-valued). -/
theorem tv_result_unique {F : Type} [Field F] [Plonky3Field F]
    (r₁ r₂ : Plonky3TVResult F) :
    r₁.add_hom = r₂.add_hom ∧
    r₁.mul_hom = r₂.mul_hom := by
  exact ⟨funext fun a => funext fun b => rfl, funext fun a => funext fun b => rfl⟩

/-- Butterfly + field correctness: DIT output sum equals 2*a in ZMod. -/
theorem dit_sum_in_zmod {F : Type} [Field F] [Plonky3Field F]
    (a b tw : F) :
    toZMod (dit_butterfly a b tw).1 + toZMod (dit_butterfly a b tw).2 =
    toZMod a + toZMod a := by
  rw [dit_butterfly_fst_correct, dit_butterfly_snd_correct]
  ring

/-! ## Part 5: Non-Vacuity Examples -/

section NonVacuity

/-- Non-vacuity: mersenne31_tv is constructible and its add_hom holds. -/
noncomputable example :
    mersenne31_tv.add_hom
      (1 : AmoLean.Field.Mersenne31.Mersenne31Field) 2 =
    Plonky3Field.toZMod_add 1 2 := rfl

/-- Non-vacuity: babybear_tv fold_correct instantiates with concrete values. -/
noncomputable example :
    babybear_tv.fold_correct
      (1 : AmoLean.Field.BabyBear.BabyBearField) 2 3 4 5 =
    fold_step_correct
      (1 : AmoLean.Field.BabyBear.BabyBearField) 2 3 4 5 := rfl

/-- Non-vacuity: goldilocks_tv dit_correct instantiates with concrete values. -/
noncomputable example :
    goldilocks_tv.dit_correct
      (1 : AmoLean.Field.Goldilocks.GoldilocksField) 2 3 =
    dit_butterfly_correct
      (1 : AmoLean.Field.Goldilocks.GoldilocksField) 2 3 := rfl

/-- Non-vacuity: plonky3_tv_complete produces a valid result for each field. -/
noncomputable example :
    Plonky3TVResult AmoLean.Field.Mersenne31.Mersenne31Field :=
  plonky3_tv_complete _
noncomputable example :
    Plonky3TVResult AmoLean.Field.BabyBear.BabyBearField :=
  plonky3_tv_complete _
noncomputable example :
    Plonky3TVResult AmoLean.Field.Goldilocks.GoldilocksField :=
  plonky3_tv_complete _

/-- Non-vacuity: ntt_fri_composition is satisfiable over Mersenne31. -/
noncomputable example :
    let bfly := dit_butterfly (1 : AmoLean.Field.Mersenne31.Mersenne31Field) 2 3
    Plonky3Field.toZMod (fold_step bfly.1 bfly.2 4 5 6) =
    (Plonky3Field.toZMod bfly.1 + Plonky3Field.toZMod bfly.2) *
      Plonky3Field.toZMod (6 : AmoLean.Field.Mersenne31.Mersenne31Field) +
    Plonky3Field.toZMod (4 : AmoLean.Field.Mersenne31.Mersenne31Field) *
      ((Plonky3Field.toZMod bfly.1 - Plonky3Field.toZMod bfly.2) *
        Plonky3Field.toZMod (6 : AmoLean.Field.Mersenne31.Mersenne31Field)) *
      Plonky3Field.toZMod (5 : AmoLean.Field.Mersenne31.Mersenne31Field) :=
  ntt_fri_composition 1 2 3 4 5 6

end NonVacuity

/-! ## Part 6: Summary

### Theorem inventory (N17.9)

| Theorem                  | Statement                                      |
|--------------------------|-------------------------------------------------|
| `plonky3_tv_complete`    | Generic TV result for any Plonky3Field          |
| `mersenne31_tv`          | Concrete TV for Mersenne31 (p = 2^31 - 1)      |
| `babybear_tv`            | Concrete TV for BabyBear (p = 2^31 - 2^27 + 1) |
| `goldilocks_tv`          | Concrete TV for Goldilocks (p = 2^64 - 2^32 + 1)|
| `ntt_fri_composition`    | DIT butterfly + FRI fold preserves ZMod         |
| `tv_result_unique`       | Two TV results agree on add/mul hom             |
| `dit_sum_in_zmod`        | Butterfly output sum = 2a in ZMod               |

### Axiom audit

All theorems rely only on:
- Lean 4 kernel axioms (propext, Quot.sound, Classical.choice)
- Mathlib axioms (standard)
- NO project-specific axioms

Verify with:
  #print axioms plonky3_tv_complete
  #print axioms ntt_fri_composition
-/

#print axioms plonky3_tv_complete
#print axioms mersenne31_tv
#print axioms babybear_tv
#print axioms goldilocks_tv
#print axioms ntt_fri_composition
#print axioms dit_sum_in_zmod

end AmoLean.Plonky3.TVPipeline
