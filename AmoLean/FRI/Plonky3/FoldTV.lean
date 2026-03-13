/-
  AMO-Lean: FRI Fold Translation Validation for Plonky3Fields
  N17.8 (PARALELO) — Fase 17

  Proves that FRI fold operations over any `Plonky3Field` compose
  with the existing `FoldBridge` to give end-to-end correctness.

  The FRI fold formula (Plonky3 convention) is:
    result[i] = halve(lo + hi) + beta * halve(lo - hi) * inv_power[i]
  where lo = evals[2*i], hi = evals[2*i+1], halve(x) = x * 2⁻¹.

  Key theorem chain:
  1. `foldStep_toZMod`: toZMod commutes with fold (ring homomorphism)
  2. `foldStep_matches_foldPolynomial`: fold of coset pair = polynomial fold
  3. `foldStep_end_to_end`: composition of (1) and (2) for full TV

  Architecture:
  - Upstream: Plonky3Field (N17.6), FoldBridge (N13.4), FieldBridge (N12.2)
  - Downstream: FRI pipeline integration for Plonky3 fields
-/

import AmoLean.Field.Plonky3Field
import AmoLean.FRI.Verified.FoldBridge

open Plonky3Field AmoLean.FRI.Verified Polynomial

namespace AmoLean.FRI.Plonky3.FoldTV

section Generic
variable {F : Type} [Field F] [inst : Plonky3Field F]

/-- Bridge lemma: `toZModRingHom` applied to a value equals `toZMod`. -/
private theorem toZModRingHom_eq (a : F) :
    (toZModRingHom (F := F)) a = Plonky3Field.toZMod a := rfl

/-! ## Part 1: FRI Fold Step Definition -/

/-- Single FRI fold step: the Plonky3 formula.
    result = halve(lo + hi) + beta * halve(lo - hi) * coeff
    where halve(x) = x * 2⁻¹, lo = evals[2i], hi = evals[2i+1],
    and coeff = inv_power[i] (the twiddle factor).

    This captures the exact computation performed by Plonky3's
    `fold_row` function at a single index. -/
def foldStep (lo hi beta coeff : F) : F :=
  (lo + hi) * (2 : F)⁻¹ + beta * ((lo - hi) * (2 : F)⁻¹) * coeff

/-! ## Part 2: Translation Validation — foldStep preserves toZMod -/

/-- toZMod commutes with foldStep. Follows directly from toZMod being
    an injective ring homomorphism (preserves +, *, -, ⁻¹).

    This is the core TV theorem at the single-step level: computing
    foldStep in the representation type F and then projecting to ZMod
    gives the same result as projecting first and computing in ZMod. -/
theorem foldStep_toZMod (lo hi beta coeff : F) :
    Plonky3Field.toZMod (foldStep lo hi beta coeff) =
    foldStep (Plonky3Field.toZMod lo) (Plonky3Field.toZMod hi)
             (Plonky3Field.toZMod beta) (Plonky3Field.toZMod coeff) := by
  unfold foldStep
  change (toZModRingHom (F := F)) _ = _
  simp only [map_add, map_mul, map_sub, map_inv₀, map_ofNat, toZModRingHom_eq]

/-! ## Part 3: FRI Fold Row -/

/-- FRI fold row: applies foldStep to each pair of evaluations.
    For index i: fold(evals[2i], evals[2i+1], beta, invPowers[i]).
    Matches the Plonky3 `fold_row` operation over an evaluation array. -/
noncomputable def foldRow (n : Nat) (evals : Fin (2 * n) → F) (beta : F)
    (invPowers : Fin n → F) : Fin n → F :=
  fun i => foldStep (evals ⟨2 * i.val, by omega⟩)
                    (evals ⟨2 * i.val + 1, by omega⟩)
                    beta (invPowers i)

/-- foldRow preserves ZMod semantics pointwise. Each output element
    in F maps to the corresponding ZMod fold result. -/
theorem foldRow_toZMod (n : Nat) (evals : Fin (2 * n) → F) (beta : F)
    (invPowers : Fin n → F) (i : Fin n) :
    Plonky3Field.toZMod (foldRow n evals beta invPowers i) =
    foldRow n (Plonky3Field.toZMod ∘ evals) (Plonky3Field.toZMod beta)
             (Plonky3Field.toZMod ∘ invPowers) i := by
  simp only [foldRow, Function.comp]
  exact foldStep_toZMod _ _ _ _

/-! ## Part 4: Characteristic Lemmas -/

/-- (2 : ZMod p) is nonzero when p > 2. All Plonky3 primes satisfy this
    (Mersenne31 = 2^31-1, BabyBear = 2^31-2^27+1, Goldilocks = 2^64-2^32+1). -/
theorem two_ne_zero_zmod (h : inst.char > 2) :
    (2 : ZMod inst.char) ≠ 0 := by
  have : ((2 : ℕ) : ZMod inst.char) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  exact_mod_cast this

/-- (2 : F) is nonzero when char F > 2. Derived from `two_ne_zero_zmod`
    via the injectivity of toZMod. -/
theorem two_ne_zero (h : inst.char > 2) : (2 : F) ≠ 0 := by
  intro h2
  have heq := congrArg Plonky3Field.toZMod h2
  rw [show Plonky3Field.toZMod (2 : F) = ((2 : ℕ) : ZMod inst.char) from
    map_ofNat (toZModRingHom (F := F)) 2, Plonky3Field.toZMod_zero] at heq
  exact absurd (Nat.le_of_dvd (by norm_num)
    ((ZMod.natCast_eq_zero_iff 2 _).mp heq)) (by omega)

/-! ## Part 5: Algebraic Properties of foldStep -/

omit inst in
/-- foldStep with unit twiddle factor (coeff = 1). -/
theorem foldStep_unit_twiddle (lo hi beta : F) :
    foldStep lo hi beta 1 =
    (lo + hi) * (2 : F)⁻¹ + beta * ((lo - hi) * (2 : F)⁻¹) := by
  unfold foldStep; ring

omit inst in
/-- foldStep with zero challenge (beta = 0) extracts the average. -/
theorem foldStep_beta_zero (lo hi coeff : F) :
    foldStep lo hi 0 coeff = (lo + hi) * (2 : F)⁻¹ := by
  unfold foldStep; ring

omit inst in
/-- foldStep is symmetric in lo, hi when beta = 0. -/
theorem foldStep_zero_symmetric (lo hi coeff : F) :
    foldStep lo hi 0 coeff = foldStep hi lo 0 coeff := by
  unfold foldStep; ring

omit inst in
/-- When lo = hi, the difference term vanishes. -/
theorem foldStep_lo_eq_hi (a beta coeff : F) :
    foldStep a a beta coeff = (a + a) * (2 : F)⁻¹ := by
  unfold foldStep; ring

omit inst in
/-- Algebraic connection: foldStep applied to raw evaluations P(x), P(-x)
    yields the decomposed even/odd fold result.

    When lo = pEven + x * pOdd and hi = pEven - x * pOdd:
    foldStep(lo, hi, alpha, x⁻¹) = pEven + alpha * pOdd -/
theorem foldStep_eq_abstract_fold (pEvenVal pOddVal x alpha : F)
    (hx : x ≠ 0) (_h2 : (2 : F) ≠ 0) :
    let lo := pEvenVal + x * pOddVal
    let hi := pEvenVal - x * pOddVal
    foldStep lo hi alpha x⁻¹ = pEvenVal + alpha * pOddVal := by
  simp only [foldStep]; field_simp; ring

/-! ## Part 6: Connection to foldPolynomial (Polynomial Bridge) -/

omit inst in
/-- Core algebraic bridge: when inputs come from polynomial evaluation at
    a coset pair {x, -x}, foldStep recovers the fold polynomial evaluation.

    P(x) = pEven(x^2) + x * pOdd(x^2)
    P(-x) = pEven(x^2) - x * pOdd(x^2)

    foldStep(P(x), P(-x), alpha, x⁻¹)
      = (P(x)+P(-x))/2 + alpha * (P(x)-P(-x))/(2x)
      = pEven(x^2) + alpha * pOdd(x^2)
      = foldPolynomial(pEven, pOdd, alpha).eval(x^2)

    This connects the Plonky3 fold formula directly to the verified
    polynomial fold from FieldBridge.lean. -/
theorem foldStep_matches_foldPolynomial (pEven pOdd : Polynomial F)
    (x alpha : F) (hx : x ≠ 0) (_h2 : (2 : F) ≠ 0) :
    let lo := pEven.eval (x * x) + x * pOdd.eval (x * x)
    let hi := pEven.eval (x * x) - x * pOdd.eval (x * x)
    foldStep lo hi alpha x⁻¹ = (foldPolynomial pEven pOdd alpha).eval (x * x) := by
  simp only [foldStep, foldPolynomial, eval_add, eval_mul, eval_C]
  field_simp; ring

/-! ## Part 7: End-to-End Composition -/

/-- End-to-end translation validation: the Plonky3 fold step, performed
    over any Plonky3Field F, when projected to ZMod via toZMod, yields
    the fold polynomial evaluation in ZMod.

    This composes three facts:
    1. toZMod commutes with fold (ring homomorphism)
    2. Inputs encode polynomial evaluations (coset structure hypotheses)
    3. Fold of coset pair = foldPolynomial.eval (algebraic identity)

    Hypotheses hlo, hhi, hcoeff encode the Plonky3 FRI domain structure:
    - hlo: lo is the evaluation at a domain point x
    - hhi: hi is the evaluation at the conjugate -x
    - hcoeff: the twiddle factor is x⁻¹

    Conclusion: the result maps to foldPolynomial.eval on the squared domain. -/
theorem foldStep_end_to_end (lo hi alpha coeff : F)
    (pEven pOdd : Polynomial (ZMod inst.char))
    (x : F) (hx : x ≠ 0) (hchar : inst.char > 2)
    (hlo : Plonky3Field.toZMod lo =
           pEven.eval (Plonky3Field.toZMod x * Plonky3Field.toZMod x) +
           Plonky3Field.toZMod x *
             pOdd.eval (Plonky3Field.toZMod x * Plonky3Field.toZMod x))
    (hhi : Plonky3Field.toZMod hi =
           pEven.eval (Plonky3Field.toZMod x * Plonky3Field.toZMod x) -
           Plonky3Field.toZMod x *
             pOdd.eval (Plonky3Field.toZMod x * Plonky3Field.toZMod x))
    (hcoeff : Plonky3Field.toZMod coeff = (Plonky3Field.toZMod x)⁻¹) :
    Plonky3Field.toZMod (foldStep lo hi alpha coeff) =
    (foldPolynomial pEven pOdd (Plonky3Field.toZMod alpha)).eval
      (Plonky3Field.toZMod x * Plonky3Field.toZMod x) := by
  -- Step 1: Push toZMod through the ring operations
  change (toZModRingHom (F := F)) _ = _
  unfold foldStep
  simp only [map_add, map_mul, map_sub, map_inv₀, map_ofNat, toZModRingHom_eq]
  -- Step 2: Substitute the polynomial interpretation
  rw [hlo, hhi, hcoeff]
  -- Step 3: Reduce to algebraic identity in ZMod
  unfold foldPolynomial
  simp [eval_add, eval_mul, eval_C]
  have hxz : Plonky3Field.toZMod x ≠ 0 :=
    fun h => hx (Plonky3Field.toZMod_injective
      (by rw [h, Plonky3Field.toZMod_zero]))
  have h2z := two_ne_zero_zmod hchar
  field_simp; ring

/-- Full fold row end-to-end: projecting foldRow output through toZMod
    gives the same result as performing the fold in ZMod.

    This is the row-level TV theorem, lifting foldStep_toZMod
    to arrays of evaluations. -/
theorem foldRow_end_to_end (n : Nat) (evals : Fin (2 * n) → F) (beta : F)
    (invPowers : Fin n → F) :
    ∀ i : Fin n,
      Plonky3Field.toZMod (foldRow n evals beta invPowers i) =
      foldRow n (Plonky3Field.toZMod ∘ evals) (Plonky3Field.toZMod beta)
               (Plonky3Field.toZMod ∘ invPowers) i :=
  fun i => foldRow_toZMod n evals beta invPowers i

end Generic

/-! ## Part 8: Smoke Tests and Non-Vacuity Examples -/

section SmokeTests

open AmoLean.Field.Mersenne31

private def m31 (n : Nat) : Mersenne31Field := Mersenne31Field.ofNat n

/-- Local foldStep for Mersenne31 computability (the generic version
    uses Field F which is noncomputable for Mersenne31). -/
private def foldStepM31 (lo hi beta coeff : Mersenne31Field) : Mersenne31Field :=
  (lo + hi) * (2 : Mersenne31Field)⁻¹ +
    beta * ((lo - hi) * (2 : Mersenne31Field)⁻¹) * coeff

-- Smoke test: foldStep(5, 3, 2, 7) = 18 in Mersenne31.
-- halve(5+3) = 4, halve(5-3) = 1, result = 4 + 2*1*7 = 18
#eval
  let result := foldStepM31 (m31 5) (m31 3) (m31 2) (m31 7)
  Mersenne31Field.toNat result  -- 18

-- Smoke test: foldStep with beta=0 extracts the average. halve(10+6) = 8
#eval
  let result := foldStepM31 (m31 10) (m31 6) (m31 0) (m31 99)
  Mersenne31Field.toNat result  -- 8

-- Smoke test: foldStep with coeff=0 ignores the difference term. halve(10+6) = 8
#eval
  let result := foldStepM31 (m31 10) (m31 6) (m31 3) (m31 0)
  Mersenne31Field.toNat result  -- 8

-- Smoke test: lo = hi means difference vanishes. halve(7+7) = 7
#eval
  let result := foldStepM31 (m31 7) (m31 7) (m31 5) (m31 3)
  Mersenne31Field.toNat result  -- 7

end SmokeTests

section NonVacuity

/-- Non-vacuity: Mersenne31 has char > 2 (required by foldStep_end_to_end). -/
noncomputable example :
    (Plonky3Field.char AmoLean.Field.Mersenne31.Mersenne31Field) > 2 := by
  show AmoLean.Field.Mersenne31.ORDER_NAT > 2; native_decide

/-- Non-vacuity: BabyBear has char > 2. -/
noncomputable example :
    (Plonky3Field.char AmoLean.Field.BabyBear.BabyBearField) > 2 := by
  show AmoLean.Field.BabyBear.ORDER_NAT > 2; native_decide

/-- Non-vacuity: Goldilocks has char > 2. -/
noncomputable example :
    (Plonky3Field.char AmoLean.Field.Goldilocks.GoldilocksField) > 2 := by
  show AmoLean.Field.Goldilocks.ORDER_NAT > 2; native_decide

/-- Non-vacuity: foldStep_toZMod instantiates for Mersenne31. -/
noncomputable example (lo hi beta coeff : AmoLean.Field.Mersenne31.Mersenne31Field) :
    Plonky3Field.toZMod (foldStep lo hi beta coeff) =
    foldStep (Plonky3Field.toZMod lo) (Plonky3Field.toZMod hi)
             (Plonky3Field.toZMod beta) (Plonky3Field.toZMod coeff) :=
  foldStep_toZMod lo hi beta coeff

/-- Non-vacuity: two_ne_zero instantiates for Mersenne31. -/
noncomputable example : (2 : AmoLean.Field.Mersenne31.Mersenne31Field) ≠ 0 := by
  apply two_ne_zero
  show AmoLean.Field.Mersenne31.ORDER_NAT > 2; native_decide

end NonVacuity

/-! ## Part 9: Module Summary

FoldTV provides:

1. `foldStep`: Plonky3 FRI fold formula (halve + twiddle)
2. `foldStep_toZMod`: TV at single-step level (ring homomorphism)
3. `foldRow` / `foldRow_toZMod`: TV at row level
4. `two_ne_zero_zmod` / `two_ne_zero`: char > 2 utility lemmas
5. `foldStep_unit_twiddle` / `_beta_zero` / `_zero_symmetric` / `_lo_eq_hi`:
   algebraic properties
6. `foldStep_eq_abstract_fold`: algebraic connection to even/odd decomposition
7. `foldStep_matches_foldPolynomial`: bridge to verified polynomial fold
8. `foldStep_end_to_end`: full TV composition
   (Plonky3 fold -> ZMod -> polynomial fold)
9. `foldRow_end_to_end`: row-level TV composition

Upstream:
- Plonky3Field.lean (N17.6): toZMod ring homomorphism
- FoldBridge.lean (N13.4): foldSpec, foldBridge_equivalence
- FieldBridge.lean (N12.2): EvenOddDecomp, foldPolynomial, evalOnDomain
- FoldSoundness.lean (N12.4): fold_eval_at_point, fold_preserves_consistency

Downstream:
- FRI pipeline integration for Plonky3 fields (N17.9+)
-/

end AmoLean.FRI.Plonky3.FoldTV
