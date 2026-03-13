/-
  AMO-Lean: Butterfly Translation Validation for Plonky3 Fields
  Fase 17 Nodo 7 — N17.7: NTT Butterfly Translation Validation

  Proves that NTT butterfly operations over any Plonky3Field preserve
  ZMod semantics. The key insight is that `toZMod` is a ring homomorphism,
  so both DIT and DIF butterfly outputs map correctly through `toZMod`.

  The butterfly is the atomic building block of Cooley-Tukey NTT:
  - DIT (decimation in time):  (a, b) → (a + tw·b, a - tw·b)
  - DIF (decimation in freq):  (a, b) → (a + b, (a - b)·tw)

  Since `toZMod` preserves +, -, *, the butterfly outputs in the concrete
  field F map to the same butterfly outputs in ZMod char. This is the
  translation validation step that ensures Plonky3's NTT implementation
  computes the mathematically correct transform.

  Theorems: 8 (all proven, 0 sorry, 0 axioms)
  LOC: ~200
-/

import AmoLean.Field.Plonky3Field

namespace AmoLean.NTT.Plonky3.ButterflyTV

/-! ## Part 1: Butterfly Definitions over Field F -/

variable {F : Type} [Field F]

/-- DIT butterfly (decimation in time): the standard Cooley-Tukey butterfly.
    Given inputs a (even) and b (odd) with twiddle factor tw:
    - First output:  a + tw * b
    - Second output: a - tw * b -/
def dit_butterfly (a b tw : F) : F × F :=
  (a + tw * b, a - tw * b)

/-- DIF butterfly (decimation in frequency): the inverse NTT direction.
    Given inputs a and b with twiddle factor tw:
    - First output:  a + b
    - Second output: (a - b) * tw -/
def dif_butterfly (a b tw : F) : F × F :=
  (a + b, (a - b) * tw)

/-! ## Part 2: DIT Butterfly Translation Validation -/

section DIT_TV

variable [Plonky3Field F]

/-- DIT butterfly first output preserves ZMod semantics.
    toZMod (a + tw * b) = toZMod a + toZMod tw * toZMod b -/
theorem dit_butterfly_fst_correct (a b tw : F) :
    Plonky3Field.toZMod (dit_butterfly a b tw).1 =
      Plonky3Field.toZMod a + Plonky3Field.toZMod tw * Plonky3Field.toZMod b := by
  simp only [dit_butterfly, Plonky3Field.toZMod_add, Plonky3Field.toZMod_mul]

/-- DIT butterfly second output preserves ZMod semantics.
    toZMod (a - tw * b) = toZMod a - toZMod tw * toZMod b -/
theorem dit_butterfly_snd_correct (a b tw : F) :
    Plonky3Field.toZMod (dit_butterfly a b tw).2 =
      Plonky3Field.toZMod a - Plonky3Field.toZMod tw * Plonky3Field.toZMod b := by
  simp only [dit_butterfly, Plonky3Field.toZMod_sub, Plonky3Field.toZMod_mul]

/-- DIT butterfly preserves ZMod semantics (both outputs). -/
theorem dit_butterfly_correct (a b tw : F) :
    Plonky3Field.toZMod (dit_butterfly a b tw).1 =
      Plonky3Field.toZMod a + Plonky3Field.toZMod tw * Plonky3Field.toZMod b ∧
    Plonky3Field.toZMod (dit_butterfly a b tw).2 =
      Plonky3Field.toZMod a - Plonky3Field.toZMod tw * Plonky3Field.toZMod b :=
  ⟨dit_butterfly_fst_correct a b tw, dit_butterfly_snd_correct a b tw⟩

end DIT_TV

/-! ## Part 3: DIF Butterfly Translation Validation -/

section DIF_TV

variable [Plonky3Field F]

/-- DIF butterfly first output preserves ZMod semantics.
    toZMod (a + b) = toZMod a + toZMod b -/
theorem dif_butterfly_fst_correct (a b tw : F) :
    Plonky3Field.toZMod (dif_butterfly a b tw).1 =
      Plonky3Field.toZMod a + Plonky3Field.toZMod b := by
  simp only [dif_butterfly, Plonky3Field.toZMod_add]

/-- DIF butterfly second output preserves ZMod semantics.
    toZMod ((a - b) * tw) = (toZMod a - toZMod b) * toZMod tw -/
theorem dif_butterfly_snd_correct (a b tw : F) :
    Plonky3Field.toZMod (dif_butterfly a b tw).2 =
      (Plonky3Field.toZMod a - Plonky3Field.toZMod b) * Plonky3Field.toZMod tw := by
  simp only [dif_butterfly, Plonky3Field.toZMod_mul, Plonky3Field.toZMod_sub]

/-- DIF butterfly preserves ZMod semantics (both outputs). -/
theorem dif_butterfly_correct (a b tw : F) :
    Plonky3Field.toZMod (dif_butterfly a b tw).1 =
      Plonky3Field.toZMod a + Plonky3Field.toZMod b ∧
    Plonky3Field.toZMod (dif_butterfly a b tw).2 =
      (Plonky3Field.toZMod a - Plonky3Field.toZMod b) * Plonky3Field.toZMod tw :=
  ⟨dif_butterfly_fst_correct a b tw, dif_butterfly_snd_correct a b tw⟩

end DIF_TV

/-! ## Part 4: Algebraic Properties -/

section Algebraic

/-- DIT butterfly sum: first + second = 2 * a.
    (a + tw*b) + (a - tw*b) = a + a -/
theorem dit_butterfly_sum (a b tw : F) :
    (dit_butterfly a b tw).1 + (dit_butterfly a b tw).2 = a + a := by
  simp only [dit_butterfly]; ring

/-- DIF butterfly composes with DIT to recover scaled inputs.
    dif_butterfly applied after dit_butterfly gives (a + a, (b + b) * tw * tw⁻¹). -/
theorem butterfly_roundtrip (a b tw : F) :
    dif_butterfly (dit_butterfly a b tw).1 (dit_butterfly a b tw).2 tw⁻¹ =
      (a + a, (b + b) * tw * tw⁻¹) := by
  ext <;> simp only [dit_butterfly, dif_butterfly] <;> ring

/-- Simplified butterfly roundtrip: with tw ≠ 0, we recover (2a, 2b). -/
theorem butterfly_roundtrip_cancel (a b tw : F) (htw : tw ≠ 0) :
    dif_butterfly (dit_butterfly a b tw).1 (dit_butterfly a b tw).2 tw⁻¹ =
      (a + a, b + b) := by
  ext <;> simp only [dit_butterfly, dif_butterfly]
  · ring
  · field_simp; ring

end Algebraic

/-! ## Part 5: Non-Vacuity Examples -/

section NonVacuity

open AmoLean.Field.Mersenne31

/-- Non-vacuity: dit_butterfly computes over Mersenne31Field. -/
noncomputable example : Mersenne31Field × Mersenne31Field :=
  dit_butterfly (1 : Mersenne31Field) (2 : Mersenne31Field) (3 : Mersenne31Field)

/-- Non-vacuity: dif_butterfly computes over Mersenne31Field. -/
noncomputable example : Mersenne31Field × Mersenne31Field :=
  dif_butterfly (1 : Mersenne31Field) (2 : Mersenne31Field) (3 : Mersenne31Field)

/-- Non-vacuity: dit_butterfly_correct is satisfiable over Mersenne31Field.
    Instantiates the theorem with concrete values. -/
noncomputable example :
    Plonky3Field.toZMod (dit_butterfly (1 : Mersenne31Field) 2 3).1 =
      Plonky3Field.toZMod 1 + Plonky3Field.toZMod 3 * Plonky3Field.toZMod 2 ∧
    Plonky3Field.toZMod (dit_butterfly (1 : Mersenne31Field) 2 3).2 =
      Plonky3Field.toZMod 1 - Plonky3Field.toZMod 3 * Plonky3Field.toZMod 2 :=
  dit_butterfly_correct 1 2 3

/-- Non-vacuity: dif_butterfly_correct is satisfiable over Mersenne31Field. -/
noncomputable example :
    Plonky3Field.toZMod (dif_butterfly (1 : Mersenne31Field) 2 3).1 =
      Plonky3Field.toZMod 1 + Plonky3Field.toZMod 2 ∧
    Plonky3Field.toZMod (dif_butterfly (1 : Mersenne31Field) 2 3).2 =
      (Plonky3Field.toZMod 1 - Plonky3Field.toZMod 2) * Plonky3Field.toZMod 3 :=
  dif_butterfly_correct 1 2 3

/-- Non-vacuity: butterfly_roundtrip_cancel with concrete tw ≠ 0. -/
noncomputable example :
    dif_butterfly
      (dit_butterfly (1 : Mersenne31Field) 2 3).1
      (dit_butterfly (1 : Mersenne31Field) 2 3).2
      (3 : Mersenne31Field)⁻¹ = (1 + 1, 2 + 2) :=
  butterfly_roundtrip_cancel 1 2 3 (by decide)

end NonVacuity

/-! ## Part 6: Smoke Tests

  Since `dit_butterfly`/`dif_butterfly` use the noncomputable `Field` instance,
  we compute butterfly values directly using computable Mersenne31Field ops. -/

section SmokeTests

open AmoLean.Field.Mersenne31

-- Smoke test: DIT butterfly via raw Mersenne31 arithmetic
-- DIT(a=7, b=11, tw=5): (7 + 5*11, 7 - 5*11) = (62, p-48)
#eval do
  let a : Mersenne31Field := ⟨7, by native_decide⟩
  let b : Mersenne31Field := ⟨11, by native_decide⟩
  let tw : Mersenne31Field := ⟨5, by native_decide⟩
  let t := Mersenne31Field.mul tw b
  let x := Mersenne31Field.add a t
  let y := Mersenne31Field.sub a t
  IO.println s!"DIT butterfly: ({x}, {y})"

-- Smoke test: DIF butterfly via raw Mersenne31 arithmetic
-- DIF(a=7, b=11, tw=5): (7+11, (7-11)*5) = (18, (p-4)*5)
#eval do
  let a : Mersenne31Field := ⟨7, by native_decide⟩
  let b : Mersenne31Field := ⟨11, by native_decide⟩
  let tw : Mersenne31Field := ⟨5, by native_decide⟩
  let x := Mersenne31Field.add a b
  let y := Mersenne31Field.mul (Mersenne31Field.sub a b) tw
  IO.println s!"DIF butterfly: ({x}, {y})"

-- Smoke test: DIT with twiddle = 1 gives (a+b, a-b)
#eval do
  let a : Mersenne31Field := ⟨100, by native_decide⟩
  let b : Mersenne31Field := ⟨42, by native_decide⟩
  let one : Mersenne31Field := ⟨1, by native_decide⟩
  let t := Mersenne31Field.mul one b
  let x := Mersenne31Field.add a t
  let y := Mersenne31Field.sub a t
  IO.println s!"DIT tw=1: ({x}, {y})"
  -- Expected: (142, 58)

end SmokeTests

end AmoLean.NTT.Plonky3.ButterflyTV
