/-
  AMO-Lean: BabyBear Plonky3 Montgomery Refinement
  Fase 17 Nodo 4 — N17.4 (CRITICO)

  Instantiates the generic Montgomery theory (Montgomery.lean) for BabyBear
  and proves that Plonky3's MontyField31 operations are correct.

  BabyBear prime: p = 2^31 - 2^27 + 1 = 2013265921
  Montgomery radix: R = 2^32 = 4294967296

  Reference: Plonky3 monty-31 crate
  - monty_reduce: utils.rs lines 105-125
  - MontyField31 mul: monty-31/src/lib.rs

  Key Plonky3 constants:
  - MONTY_MU = p⁻¹ mod R = 2281701377
  - MU_NEG  = R - MONTY_MU = 2013265919
  - Property: (MU_NEG * p + 1) % R = 0
-/

import AmoLean.Field.Montgomery
import AmoLean.Field.BabyBear

namespace AmoLean.Field.Plonky3.BabyBear

open AmoLean.Field.Montgomery
open AmoLean.Field.BabyBear

/-! ## Part 1: BabyBear Montgomery Configuration -/

/-- Montgomery configuration for BabyBear (p = 2013265921).

    Plonky3's MontyField31<BabyBearParameters> uses:
    - PRIME = 2013265921
    - MONTY_MU = 2281701377 (= p⁻¹ mod 2^32)
    - Our MU_NEG = 2^32 - MONTY_MU = 2013265919 -/
def bbMontyConfig : MontyConfig where
  p := 2013265921
  p_prime := by native_decide
  p_lt_half_R := by native_decide
  MU_NEG := 2013265919
  mu_neg_lt_R := by native_decide
  mu_neg_spec := by native_decide

/-! ## Part 2: Constant Verification -/

/-- Plonky3's MONTY_MU matches our derived MU. -/
theorem bb_monty_mu_eq : bbMontyConfig.MU = 2281701377 := by native_decide

/-- BabyBear prime matches the expected value. -/
theorem bb_p_eq : bbMontyConfig.p = 2013265921 := rfl

/-- BabyBear prime matches ORDER_NAT from BabyBear.lean. -/
theorem bb_p_eq_order_nat : bbMontyConfig.p = ORDER_NAT := by native_decide

/-- MU_NEG is exactly R - MONTY_MU. -/
theorem bb_mu_neg_eq : bbMontyConfig.MU_NEG = 2013265919 := rfl

/-- The fundamental Montgomery identity: MU * p ≡ 1 (mod R). -/
theorem bb_mu_spec : (bbMontyConfig.MU * bbMontyConfig.p) % R = 1 :=
  MontyConfig.mu_spec bbMontyConfig

/-! ## Part 3: Montgomery Reduction for BabyBear -/

/-- monty_reduce for BabyBear produces a value < p. -/
theorem bb_monty_reduce_lt_p (x : Nat) (hx : x < R * bbMontyConfig.p) :
    monty_reduce bbMontyConfig x < bbMontyConfig.p :=
  monty_reduce_lt_p bbMontyConfig x hx

/-- Core Montgomery correctness for BabyBear:
    R * monty_reduce(x) ≡ x (mod p) for any x.
    This says monty_reduce computes x * R⁻¹ mod p. -/
theorem bb_monty_reduce_spec (x : Nat) :
    (R * monty_reduce bbMontyConfig x) % bbMontyConfig.p = x % bbMontyConfig.p :=
  monty_reduce_spec bbMontyConfig x

/-! ## Part 4: BabyBear Montgomery Arithmetic -/

/-- BabyBear Montgomery multiplication: monty_reduce(a_M * b_M). -/
def bb_monty_mul (a_M b_M : Nat) : Nat :=
  monty_mul bbMontyConfig a_M b_M

/-- BabyBear to Montgomery form: a ↦ (a * R) % p. -/
def bb_to_monty (a : Nat) : Nat :=
  to_monty bbMontyConfig a

/-- BabyBear from Montgomery form: a_M ↦ monty_reduce(a_M). -/
def bb_from_monty (a_M : Nat) : Nat :=
  from_monty bbMontyConfig a_M

/-! ## Part 5: Correctness Theorems -/

/-- Montgomery multiplication satisfies:
    R * monty_mul(a_M, b_M) ≡ a_M * b_M (mod p). -/
theorem bb_monty_mul_spec (a_M b_M : Nat) :
    (R * bb_monty_mul a_M b_M) % bbMontyConfig.p = (a_M * b_M) % bbMontyConfig.p :=
  monty_mul_spec bbMontyConfig a_M b_M

/-- Montgomery multiplication is in [0, p) for canonical inputs. -/
theorem bb_monty_mul_lt_p (a_M b_M : Nat) (ha : a_M < bbMontyConfig.p) (hb : b_M < bbMontyConfig.p) :
    bb_monty_mul a_M b_M < bbMontyConfig.p :=
  monty_mul_lt_p bbMontyConfig a_M b_M (mul_lt_R_mul_p bbMontyConfig a_M b_M ha hb)

/-- to_monty produces a value < p. -/
theorem bb_to_monty_lt_p (a : Nat) : bb_to_monty a < bbMontyConfig.p :=
  to_monty_lt_p bbMontyConfig a

/-- Round-trip: R * from_monty(to_monty(a)) ≡ a * R (mod p).
    This ensures the Montgomery form is consistent. -/
theorem bb_roundtrip (a : Nat) :
    (R * bb_from_monty (bb_to_monty a)) % bbMontyConfig.p = (a * R) % bbMontyConfig.p :=
  R_mul_from_to_monty bbMontyConfig a

/-- Chained Montgomery multiplications compose correctly for BabyBear:
    R² * monty_mul(monty_mul(a_M, b_M), c_M) ≡ a_M * b_M * c_M (mod p). -/
theorem bb_monty_mul_chain (a_M b_M c_M : Nat) :
    (R * R * monty_mul bbMontyConfig (monty_mul bbMontyConfig a_M b_M) c_M) % bbMontyConfig.p
    = (a_M * b_M * c_M) % bbMontyConfig.p :=
  monty_mul_chain bbMontyConfig a_M b_M c_M

/-! ## Part 6: Full Roundtrip — from_monty(monty_mul(to_monty(a), to_monty(b))) computes (a * b) mod p

  The key bridge theorem connecting Montgomery representation to standard arithmetic.
  For canonical values a, b:
    from_monty(monty_mul(to_monty(a), to_monty(b))) = (a * b) % p

  Proof sketch:
    1. to_monty(a) = (a * R) % p, to_monty(b) = (b * R) % p
    2. monty_mul = monty_reduce(to_monty(a) * to_monty(b))
    3. R * monty_mul ≡ to_monty(a) * to_monty(b) ≡ a*R * b*R ≡ a*b*R² (mod p)
    4. from_monty = monty_reduce(monty_mul)
    5. R * from_monty ≡ monty_mul ≡ a*b*R² / R ≡ a*b*R (mod p)
    6. R² * from_monty ≡ a*b*R² (mod p)
    7. Since gcd(R, p) = 1, cancel R² to get from_monty ≡ a*b (mod p)
    8. Both sides < p, so equality holds.
-/

/-- gcd(R, p) = 1 for BabyBear (p is odd, R = 2^32). -/
theorem bb_R_coprime_p : Nat.Coprime R bbMontyConfig.p := by native_decide

/-- p.gcd R = 1 (symmetric form needed for ModEq.cancel_left_of_coprime). -/
theorem bb_p_gcd_R : bbMontyConfig.p.gcd R = 1 := by native_decide

/-- p.gcd (R * R) = 1. -/
theorem bb_p_gcd_R2 : bbMontyConfig.p.gcd (R * R) = 1 := by native_decide

/-- R * R * from_monty(monty_mul(to_monty(a), to_monty(b))) ≡ a * b * R * R (mod p).
    This follows from chaining two Montgomery reductions. -/
theorem bb_full_chain_R2 (a b : Nat) :
    (R * R * from_monty bbMontyConfig (monty_mul bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b))) % bbMontyConfig.p
    = (a * b * R * R) % bbMontyConfig.p := by
  -- Unfold from_monty to monty_reduce
  unfold from_monty
  set result := monty_mul bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b) with hresult_def
  -- Step 1: R * monty_reduce(result) ≡ result (mod p)
  have h_reduce := monty_reduce_spec bbMontyConfig result
  -- Step 2: R * result ≡ to_monty(a) * to_monty(b) (mod p)
  have h_mul := monty_mul_spec bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b)
  -- Chain via Nat.ModEq:
  -- R * R * monty_reduce(result)
  -- = R * (R * monty_reduce(result))     [associativity]
  -- ≡ R * result                         [h_reduce: R * reduce ≡ result]
  -- ≡ to_monty(a) * to_monty(b)          [h_mul]
  -- ≡ a * b * R * R                      [to_monty defn]
  have step1 : (R * (R * monty_reduce bbMontyConfig result)) % bbMontyConfig.p
      = (R * result) % bbMontyConfig.p := by
    rw [Nat.mul_mod R, h_reduce, ← Nat.mul_mod]
  have step2 : (R * result) % bbMontyConfig.p
      = (to_monty bbMontyConfig a * to_monty bbMontyConfig b) % bbMontyConfig.p := h_mul
  have step3 : (to_monty bbMontyConfig a * to_monty bbMontyConfig b) % bbMontyConfig.p
      = (a * R * (b * R)) % bbMontyConfig.p := by
    unfold to_monty
    rw [Nat.mul_mod ((a * R) % bbMontyConfig.p), Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.mul_mod]
    rw [Nat.mul_mod (a * R) ((b * R) % bbMontyConfig.p), Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.mul_mod]
  have step4 : (a * R * (b * R)) % bbMontyConfig.p = (a * b * R * R) % bbMontyConfig.p := by
    ring_nf
  rw [Nat.mul_assoc R R]
  rw [step1, step2, step3, step4]

/-- The full roundtrip theorem: from_monty(monty_mul(to_monty(a), to_monty(b))) = (a * b) % p.

    This is the capstone: Plonky3's Montgomery multiplication pipeline produces
    exactly the same result as standard modular multiplication in BabyBearField. -/
theorem bb_monty_roundtrip (a b : Nat) :
    from_monty bbMontyConfig (monty_mul bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b))
    = (a * b) % bbMontyConfig.p := by
  -- Both sides are < p
  have hlhs : from_monty bbMontyConfig (monty_mul bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b)) < bbMontyConfig.p := by
    unfold from_monty
    apply monty_reduce_lt_p
    -- monty_mul(to_monty(a), to_monty(b)) < R * p
    unfold monty_mul
    have hmr : monty_reduce bbMontyConfig (to_monty bbMontyConfig a * to_monty bbMontyConfig b) < bbMontyConfig.p := by
      apply monty_reduce_lt_p
      exact mul_lt_R_mul_p bbMontyConfig _ _ (to_monty_lt_p bbMontyConfig a) (to_monty_lt_p bbMontyConfig b)
    calc monty_reduce bbMontyConfig (to_monty bbMontyConfig a * to_monty bbMontyConfig b)
        < bbMontyConfig.p := hmr
      _ ≤ 1 * bbMontyConfig.p := by omega
      _ ≤ R * bbMontyConfig.p := by apply Nat.mul_le_mul_right; decide
  have hrhs : (a * b) % bbMontyConfig.p < bbMontyConfig.p := Nat.mod_lt _ (by decide)
  -- Both sides satisfy R * R * x ≡ a * b * R * R (mod p) and are < p
  have hR2_lhs := bb_full_chain_R2 a b
  have hR2_rhs : (R * R * ((a * b) % bbMontyConfig.p)) % bbMontyConfig.p = (a * b * R * R) % bbMontyConfig.p := by
    rw [Nat.mul_mod (R * R), Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.mul_mod]
    ring_nf
  -- R * R * lhs ≡ R * R * rhs (mod p) [both equal a * b * R * R mod p]
  have hmod_eq : (R * R * from_monty bbMontyConfig (monty_mul bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b))) % bbMontyConfig.p
    = (R * R * ((a * b) % bbMontyConfig.p)) % bbMontyConfig.p := by
    rw [hR2_lhs, hR2_rhs]
  -- Cancel R * R using Nat.ModEq.cancel_left_of_coprime
  -- hmod_eq says: R*R*lhs ≡ R*R*rhs [MOD p]
  -- cancel_left_of_coprime needs: p.gcd(R*R) = 1
  have hcancel : Nat.ModEq bbMontyConfig.p
    (from_monty bbMontyConfig (monty_mul bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b)))
    ((a * b) % bbMontyConfig.p) :=
    Nat.ModEq.cancel_left_of_coprime bb_p_gcd_R2 hmod_eq
  -- hcancel : lhs ≡ rhs [MOD p], i.e., lhs % p = rhs % p
  -- Since both < p, they are equal
  exact Nat.ModEq.eq_of_lt_of_lt hcancel hlhs hrhs

/-! ## Part 7: Bridge to BabyBearField -/

/-- Plonky3 Montgomery multiplication on BabyBearField values produces
    the same Nat-level result as standard BabyBear multiplication.

    This bridges the Montgomery representation used by Plonky3 with the
    direct modular arithmetic in BabyBearField. -/
theorem bb_monty_mul_matches_field (a b : BabyBearField) :
    from_monty bbMontyConfig
      (monty_mul bbMontyConfig
        (to_monty bbMontyConfig a.value.toNat)
        (to_monty bbMontyConfig b.value.toNat))
    = (a.value.toNat * b.value.toNat) % bbMontyConfig.p := by
  exact bb_monty_roundtrip a.value.toNat b.value.toNat

/-- Strengthened bridge: the Montgomery result matches BabyBearField.mul's value.
    Uses mul_val_eq to connect BabyBearField's internal representation. -/
theorem bb_monty_matches_mul_val (a b : BabyBearField) :
    from_monty bbMontyConfig
      (monty_mul bbMontyConfig
        (to_monty bbMontyConfig a.value.toNat)
        (to_monty bbMontyConfig b.value.toNat))
    = (a * b).value.toNat := by
  rw [bb_monty_roundtrip, bb_p_eq_order_nat]
  -- Goal: (a.value.toNat * b.value.toNat) % ORDER_NAT = (a * b).value.toNat
  have h := mul_val_eq a b
  -- h : (a * b).value.toNat % ORDER_NAT = (a.value.toNat * b.value.toNat) % ORDER_NAT
  have hcan : (a * b).value.toNat < ORDER_NAT := babybear_canonical (a * b)
  rw [← h, Nat.mod_eq_of_lt hcan]

/-! ## Part 8: Non-vacuity Examples -/

/-- Non-vacuity: bbMontyConfig is well-formed and monty_reduce produces < p. -/
example : monty_reduce bbMontyConfig 42 < bbMontyConfig.p := by native_decide

/-- Non-vacuity: Montgomery roundtrip for 42 * 17 = 714. -/
example : from_monty bbMontyConfig
    (monty_mul bbMontyConfig
      (to_monty bbMontyConfig 42)
      (to_monty bbMontyConfig 17)) = 714 := by native_decide

/-- Non-vacuity: Montgomery roundtrip for 0 * anything = 0. -/
example : from_monty bbMontyConfig
    (monty_mul bbMontyConfig
      (to_monty bbMontyConfig 0)
      (to_monty bbMontyConfig 999)) = 0 := by native_decide

/-- Non-vacuity: Montgomery roundtrip for large values near p. -/
example : from_monty bbMontyConfig
    (monty_mul bbMontyConfig
      (to_monty bbMontyConfig 2013265920)  -- p - 1
      (to_monty bbMontyConfig 2013265920)) -- p - 1
    = 1 := by native_decide

/-- Non-vacuity: bb_monty_mul_lt_p with concrete inputs. -/
example : bb_monty_mul (to_monty bbMontyConfig 100) (to_monty bbMontyConfig 200)
    < bbMontyConfig.p := by native_decide

/-- Non-vacuity: full bridge theorem is satisfiable. -/
example : ∃ a b : Nat,
    from_monty bbMontyConfig
      (monty_mul bbMontyConfig
        (to_monty bbMontyConfig a) (to_monty bbMontyConfig b))
    = (a * b) % bbMontyConfig.p :=
  ⟨42, 17, bb_monty_roundtrip 42 17⟩

/-! ## Part 9: #eval Smoke Tests -/

-- Smoke test 1: Montgomery roundtrip for small values
#eval do
  let p := bbMontyConfig.p
  let pairs := #[(42, 17), (0, 999), (1, 1), (100, 200), (12345, 67890)]
  for (a, b) in pairs do
    let expected := (a * b) % p
    let result := from_monty bbMontyConfig
      (monty_mul bbMontyConfig (to_monty bbMontyConfig a) (to_monty bbMontyConfig b))
    assert! result == expected
    IO.println s!"  {a} * {b} mod p: expected={expected}, got={result} ✓"
  IO.println s!"All small value tests passed."

-- Smoke test 2: Edge cases (0, 1, p-1)
#eval do
  let p := bbMontyConfig.p
  -- 0 * x = 0
  let r0 := from_monty bbMontyConfig
    (monty_mul bbMontyConfig (to_monty bbMontyConfig 0) (to_monty bbMontyConfig 42))
  assert! r0 == 0
  -- 1 * x = x
  let r1 := from_monty bbMontyConfig
    (monty_mul bbMontyConfig (to_monty bbMontyConfig 1) (to_monty bbMontyConfig 42))
  assert! r1 == 42
  -- (p-1) * (p-1) = 1
  let r2 := from_monty bbMontyConfig
    (monty_mul bbMontyConfig (to_monty bbMontyConfig (p-1)) (to_monty bbMontyConfig (p-1)))
  assert! r2 == 1
  IO.println s!"Edge case tests passed: 0*42={r0}, 1*42={r1}, (p-1)²={r2}"

-- Smoke test 3: Verify MONTY_MU matches Plonky3
#eval do
  let mu := bbMontyConfig.MU
  assert! mu == 2281701377
  assert! (mu * bbMontyConfig.p) % R == 1
  IO.println s!"MONTY_MU = {mu}, verified (MU * p) % R = 1 ✓"

-- Smoke test 4: Chained multiplications (a * b * c)
#eval do
  let p := bbMontyConfig.p
  let a := 42
  let b := 17
  let c := 99
  let expected := (a * b * c) % p
  let a_M := to_monty bbMontyConfig a
  let b_M := to_monty bbMontyConfig b
  let c_M := to_monty bbMontyConfig c
  let ab_M := monty_mul bbMontyConfig a_M b_M
  let abc_M := monty_mul bbMontyConfig ab_M c_M
  let result := from_monty bbMontyConfig abc_M
  assert! result == expected
  IO.println s!"{a} * {b} * {c} mod p: expected={expected}, got={result} ✓"

-- Smoke test 5: Compare with BabyBearField operations
#eval do
  let a : BabyBearField := ⟨42, by native_decide⟩
  let b : BabyBearField := ⟨17, by native_decide⟩
  let field_result := (a * b).value.toNat
  let monty_result := from_monty bbMontyConfig
    (monty_mul bbMontyConfig
      (to_monty bbMontyConfig a.value.toNat)
      (to_monty bbMontyConfig b.value.toNat))
  assert! field_result == monty_result
  IO.println s!"BabyBearField mul vs Montgomery: field={field_result}, monty={monty_result} ✓"

end AmoLean.Field.Plonky3.BabyBear
