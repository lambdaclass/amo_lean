/-
  AmoLean.Field.Montgomery — Generic Montgomery Multiplication (N17.3)

  Formalizes Montgomery reduction for 31-bit prime fields with R = 2^32,
  matching Plonky3's monty_reduce algorithm (monty-31/src/utils.rs:105-125).

  All arithmetic is modeled at the Nat level (no UInt32/UInt64).
  Core identity: R * monty_reduce(x) ≡ x (mod p) for x < R * p.
-/
import Mathlib.Data.ZMod.Basic

namespace AmoLean.Field.Montgomery

/-! ## Constants -/

/-- R = 2^32, the Montgomery radix for 31-bit fields. -/
abbrev R : Nat := 2 ^ 32

/-! ## Configuration -/

/-- Montgomery configuration for a 31-bit prime field.

  Uses the "negative inverse" convention: (MU_NEG * p + 1) % R = 0.
  This enables the addition-based REDC that avoids Nat underflow.

  Relation to Plonky3: Plonky3 uses MU = p⁻¹ mod R (subtraction variant).
  Our MU_NEG = R - MU. Both compute the same result. -/
structure MontyConfig where
  /-- The prime modulus -/
  p : Nat
  /-- Primality proof -/
  p_prime : Nat.Prime p
  /-- The prime fits in 31 bits -/
  p_lt_half_R : p < R / 2
  /-- Negative Montgomery parameter: (-p⁻¹) mod R -/
  MU_NEG : Nat
  /-- MU_NEG is in range -/
  mu_neg_lt_R : MU_NEG < R
  /-- Key property: (MU_NEG * p + 1) % R = 0 -/
  mu_neg_spec : (MU_NEG * p + 1) % R = 0

namespace MontyConfig

variable (cfg : MontyConfig)

theorem p_pos : 0 < cfg.p := cfg.p_prime.pos
theorem p_gt_one : 1 < cfg.p := cfg.p_prime.one_lt
theorem p_lt_R : cfg.p < R := by have := cfg.p_lt_half_R; omega

/-- The positive Montgomery parameter MU = R - MU_NEG.
    Satisfies (MU * p) % R = 1. This is Plonky3's MONTY_MU. -/
def MU : Nat := R - cfg.MU_NEG

/-- MU * p ≡ 1 (mod R). -/
theorem mu_spec : (cfg.MU * cfg.p) % R = 1 := by
  unfold MU
  have hle : cfg.MU_NEG ≤ R := Nat.le_of_lt cfg.mu_neg_lt_R
  rw [Nat.sub_mul]
  have hdvd : R ∣ (cfg.MU_NEG * cfg.p + 1) := Nat.dvd_of_mod_eq_zero cfg.mu_neg_spec
  obtain ⟨k, hk⟩ := hdvd
  have hk_pos : 0 < k := by
    rcases k with _ | k'
    · simp at hk  -- R * 0 = 0 ≠ MU_NEG * p + 1
    · omega
  have hmup_le : cfg.MU_NEG * cfg.p ≤ R * cfg.p := Nat.mul_le_mul_right _ hle
  have hk_le : k ≤ cfg.p := by
    by_contra hk_gt; push_neg at hk_gt
    have h1 : R * k ≥ R * (cfg.p + 1) := Nat.mul_le_mul_left _ hk_gt
    -- R * k = MU_NEG * p + 1 ≤ R * p + 1 (from hmup_le)
    -- But R * k ≥ R * (p + 1) = R * p + R
    -- So R * p + 1 ≥ R * p + R, contradicting R ≥ 2
    have h2 : R * k ≤ R * cfg.p + 1 := by omega
    have h3 : R * (cfg.p + 1) = R * cfg.p + R := Nat.mul_succ R cfg.p
    have hR : R ≥ 2 := by decide
    omega
  -- MU_NEG * p = R * k - 1 (from hk, since MU_NEG * p + 1 = R * k)
  have hmup_eq : cfg.MU_NEG * cfg.p = R * k - 1 := by omega
  -- R * p - (R * k - 1) = R * (p - k) + 1
  have hRk_le : R * k ≤ R * cfg.p := Nat.mul_le_mul_left _ hk_le
  have hval : R * cfg.p - (R * k - 1) = R * (cfg.p - k) + 1 := by
    have hRsub : R * cfg.p - R * k = R * (cfg.p - k) := (Nat.mul_sub R cfg.p k).symm
    -- R * p - (R * k - 1) = R * p - R * k + 1 = R * (p - k) + 1
    -- since R * k ≥ 1 (k ≥ 1, R ≥ 1)
    have hRk_ge_1 : R * k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by omega)
    omega
  rw [hmup_eq, hval, Nat.add_comm (R * (cfg.p - k)) 1]
  rw [Nat.add_mul_mod_self_left]; decide

end MontyConfig

/-! ## Montgomery Reduction (Addition Variant)

  The textbook REDC addition variant, avoiding Nat underflow:
  1. m = (x * MU_NEG) % R
  2. s = x + m * p              — always ≥ 0, divisible by R
  3. q = s / R                  — in range [0, 2p)
  4. if q ≥ p then q - p else q — normalize to [0, p) -/

/-- Montgomery reduction: given x < R * p, compute the unique q ∈ [0, p)
    such that R * q ≡ x (mod p). -/
def monty_reduce (cfg : MontyConfig) (x : Nat) : Nat :=
  let m := (x * cfg.MU_NEG) % R
  let s := x + m * cfg.p
  let q := s / R
  if q ≥ cfg.p then q - cfg.p else q

/-! ## Plonky3 Subtraction Variant -/

/-- Plonky3-style Montgomery reduction using subtraction.
    Uses MU = p⁻¹ mod R and computes x - t*p (with underflow correction). -/
def monty_reduce_plonky3 (cfg : MontyConfig) (x : Nat) : Nat :=
  let t := (x * cfg.MU) % R
  let u := t * cfg.p
  if x ≥ u then
    let q := (x - u) / R
    if q ≥ cfg.p then q - cfg.p else q
  else
    cfg.p - (u - x) / R

/-! ## Core Algebraic Lemmas -/

/-- The sum s = x + m*p is divisible by R, where m = (x * MU_NEG) % R. -/
theorem sum_dvd_R (cfg : MontyConfig) (x : Nat) :
    R ∣ (x + (x * cfg.MU_NEG) % R * cfg.p) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  -- Step 1: ((x * MU_NEG) % R * p) % R = (x * MU_NEG * p) % R
  have h1 : ((x * cfg.MU_NEG) % R * cfg.p) % R = (x * cfg.MU_NEG * cfg.p) % R :=
    Nat.mod_mul_mod _ _ _
  -- Step 2: (x + m*p) % R = (x + x*MU_NEG*p) % R
  rw [Nat.add_mod, h1, ← Nat.add_mod]
  -- Step 3: factor out x
  have hfactor : x + x * cfg.MU_NEG * cfg.p = x * (1 + cfg.MU_NEG * cfg.p) := by
    rw [Nat.mul_add x 1, Nat.mul_one, Nat.mul_assoc]
  rw [hfactor]
  -- Step 4: use Nat.mul_mod + mu_neg_spec to get 0
  rw [Nat.mul_mod]
  have hmod : (1 + cfg.MU_NEG * cfg.p) % R = 0 := by
    rw [Nat.add_comm]; exact cfg.mu_neg_spec
  rw [hmod, Nat.mul_zero, Nat.zero_mod]

/-! ## Range Analysis -/

/-- When x < R * p, the sum s = x + m*p < 2 * R * p. -/
theorem sum_lt_two_R_p (cfg : MontyConfig) (x : Nat) (hx : x < R * cfg.p) :
    x + (x * cfg.MU_NEG) % R * cfg.p < 2 * R * cfg.p := by
  have hm : (x * cfg.MU_NEG) % R < R := Nat.mod_lt _ (by decide)
  have hmp : (x * cfg.MU_NEG) % R * cfg.p < R * cfg.p := (Nat.mul_lt_mul_right cfg.p_pos).mpr hm
  -- x < R*p and m*p < R*p, so x + m*p < 2*(R*p) = 2*R*p
  have hassoc : 2 * R * cfg.p = 2 * (R * cfg.p) := Nat.mul_assoc 2 R cfg.p
  omega

/-- The quotient q = s / R < 2 * p when x < R * p. -/
theorem quot_lt_two_p (cfg : MontyConfig) (x : Nat) (hx : x < R * cfg.p) :
    (x + (x * cfg.MU_NEG) % R * cfg.p) / R < 2 * cfg.p := by
  have hs := sum_lt_two_R_p cfg x hx
  rw [show 2 * R * cfg.p = R * (2 * cfg.p) from by
    rw [Nat.mul_assoc, Nat.mul_comm R (2 * cfg.p), Nat.mul_assoc,
        Nat.mul_comm R cfg.p]] at hs
  exact Nat.div_lt_of_lt_mul hs

/-- monty_reduce produces a value less than p. -/
theorem monty_reduce_lt_p (cfg : MontyConfig) (x : Nat) (hx : x < R * cfg.p) :
    monty_reduce cfg x < cfg.p := by
  unfold monty_reduce; simp only
  set q := (x + (x * cfg.MU_NEG) % R * cfg.p) / R
  have hq : q < 2 * cfg.p := quot_lt_two_p cfg x hx
  split <;> omega

/-! ## Core Correctness -/

/-- s = R * (s / R) since R divides s. -/
theorem sum_eq_R_mul_quot (cfg : MontyConfig) (x : Nat) :
    x + (x * cfg.MU_NEG) % R * cfg.p = R * ((x + (x * cfg.MU_NEG) % R * cfg.p) / R) := by
  exact Nat.eq_mul_of_div_eq_right (sum_dvd_R cfg x) rfl

/-- Key: R * q ≡ x (mod p), where q = s / R, since s ≡ x (mod p) and s = R * q. -/
theorem R_mul_quot_mod_p (cfg : MontyConfig) (x : Nat) :
    (R * ((x + (x * cfg.MU_NEG) % R * cfg.p) / R)) % cfg.p = x % cfg.p := by
  rw [← sum_eq_R_mul_quot]
  exact Nat.add_mul_mod_self_right x _ cfg.p

/-- The core Montgomery correctness theorem:
    R * monty_reduce(x) ≡ x (mod p) for x < R * p.

    This says monty_reduce computes x * R⁻¹ mod p. -/
theorem monty_reduce_spec (cfg : MontyConfig) (x : Nat) :
    (R * monty_reduce cfg x) % cfg.p = x % cfg.p := by
  unfold monty_reduce; simp only
  set q := (x + (x * cfg.MU_NEG) % R * cfg.p) / R with hq_def
  have hRq := R_mul_quot_mod_p cfg x
  split
  case isTrue hge =>
    -- q ≥ p: result = q - p
    -- R * (q - p) = R * q - R * p by Nat.mul_sub
    rw [Nat.mul_sub R q cfg.p]
    -- (R * q - R * p) % p = (R * q) % p
    -- Rewrite R * p = p * R for Nat.sub_mul_mod
    rw [show R * cfg.p = cfg.p * R from Nat.mul_comm R cfg.p]
    rw [Nat.sub_mul_mod (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left R hge)]
    exact hRq
  case isFalse _ =>
    exact hRq

/-! ## Montgomery Operations -/

/-- Convert to Montgomery form: a_M = (a * R) mod p. -/
def to_monty (cfg : MontyConfig) (a : Nat) : Nat := (a * R) % cfg.p

/-- Convert from Montgomery form using monty_reduce. -/
def from_monty (cfg : MontyConfig) (a_M : Nat) : Nat := monty_reduce cfg a_M

/-- Montgomery multiplication: monty_reduce(a_M * b_M).
    If a_M, b_M represent a, b in Montgomery form, the result represents a*b. -/
def monty_mul (cfg : MontyConfig) (a_M b_M : Nat) : Nat :=
  monty_reduce cfg (a_M * b_M)

/-! ## Montgomery Multiplication Correctness -/

/-- monty_reduce satisfies R * monty_reduce(a_M * b_M) ≡ a_M * b_M (mod p). -/
theorem monty_mul_spec (cfg : MontyConfig) (a_M b_M : Nat) :
    (R * monty_mul cfg a_M b_M) % cfg.p = (a_M * b_M) % cfg.p :=
  monty_reduce_spec cfg (a_M * b_M)

/-- Montgomery product is in [0, p). -/
theorem monty_mul_lt_p (cfg : MontyConfig) (a_M b_M : Nat)
    (hab : a_M * b_M < R * cfg.p) :
    monty_mul cfg a_M b_M < cfg.p :=
  monty_reduce_lt_p cfg (a_M * b_M) hab

/-- When a_M < p and b_M < p, and p < R/2, the product a_M * b_M < R * p.
    This ensures monty_mul is always safe for canonical inputs. -/
theorem mul_lt_R_mul_p (cfg : MontyConfig) (a_M b_M : Nat)
    (ha : a_M < cfg.p) (hb : b_M < cfg.p) :
    a_M * b_M < R * cfg.p := by
  have hp : cfg.p < R / 2 := cfg.p_lt_half_R
  have hp_pos := cfg.p_pos
  -- a_M * b_M < p * p < (R/2) * p ≤ R * p
  have h1 : a_M * b_M < cfg.p * cfg.p := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) hp_pos
  have h2 : cfg.p * cfg.p < (R / 2) * cfg.p := (Nat.mul_lt_mul_right hp_pos).mpr hp
  have h3 : R / 2 ≤ R := Nat.div_le_self _ _
  have h4 : (R / 2) * cfg.p ≤ R * cfg.p := Nat.mul_le_mul_right _ h3
  omega

/-- to_monty produces a value less than p. -/
theorem to_monty_lt_p (cfg : MontyConfig) (a : Nat) :
    to_monty cfg a < cfg.p := Nat.mod_lt _ cfg.p_pos

/-- Applying monty_reduce twice gives the same as multiplying by R⁻² mod p.
    Specifically: R * from_monty(to_monty(a)) ≡ to_monty(a) ≡ a * R (mod p). -/
theorem R_mul_from_to_monty (cfg : MontyConfig) (a : Nat) :
    (R * from_monty cfg (to_monty cfg a)) % cfg.p = (a * R) % cfg.p := by
  unfold from_monty
  rw [monty_reduce_spec cfg _]
  unfold to_monty
  exact Nat.mod_mod_of_dvd _ (dvd_refl _)

/-- to_monty input is always < R * p (since to_monty(a) < p < R * p). -/
theorem to_monty_lt_R_mul_p (cfg : MontyConfig) (a : Nat) :
    to_monty cfg a < R * cfg.p := by
  have : to_monty cfg a < cfg.p := to_monty_lt_p cfg a
  calc to_monty cfg a < cfg.p := this
    _ ≤ 1 * cfg.p := by omega
    _ ≤ R * cfg.p := by apply Nat.mul_le_mul_right; decide

/-! ## Compositional Properties -/

/-- Chained Montgomery multiplications compose correctly.
    R² * monty_mul(a_M, b_M) ≡ R * a_M * b_M ≡ a_M * R * b_M (mod p).
    This ensures the Montgomery form is preserved through chains of operations. -/
theorem monty_mul_chain (cfg : MontyConfig) (a_M b_M c_M : Nat) :
    (R * R * monty_mul cfg (monty_mul cfg a_M b_M) c_M) % cfg.p
    = (a_M * b_M * c_M) % cfg.p := by
  -- First multiplication: R * monty_mul(a_M, b_M) ≡ a_M * b_M (mod p)
  have h1 := monty_mul_spec cfg a_M b_M
  -- Second multiplication: R * monty_mul(ab_M, c_M) ≡ ab_M * c_M (mod p)
  have h2 := monty_mul_spec cfg (monty_mul cfg a_M b_M) c_M
  -- Combine: R * R * result ≡ R * (ab_M * c_M) ≡ (R * ab_M) * c_M ≡ (a_M * b_M) * c_M
  -- R * R * result = R * (R * result)
  rw [Nat.mul_assoc R R]
  -- R * (R * result) % p = R * (ab_M * c_M) % p  [by h2]
  rw [Nat.mul_mod R, h2, ← Nat.mul_mod]
  -- Goal: R * (ab_M * c_M) % p = a_M * b_M * c_M % p
  -- R * (ab_M * c_M) = (R * ab_M) * c_M
  rw [← Nat.mul_assoc R (monty_mul cfg a_M b_M) c_M]
  -- (R * ab_M) * c_M % p, use h1 on the R * ab_M part
  rw [Nat.mul_mod (R * monty_mul cfg a_M b_M) c_M, h1, ← Nat.mul_mod]

/-! ## Equivalence of Addition and Subtraction Variants -/

-- The proof that monty_reduce = monty_reduce_plonky3 requires showing both
-- satisfy R * result ≡ x (mod p) with result < p, so they must be equal.
-- This is deferred to N17.4 (BabyBear instantiation) where we can also
-- verify with concrete computations.

/-! ## Smoke Tests -/

-- BabyBear: p = 2013265921
-- Plonky3 MU = 2281701377 (p⁻¹ mod 2^32)
-- MU_NEG = 2^32 - 2281701377 = 2013265919

-- Verify mu_neg_spec: (MU_NEG * p + 1) % R = 0
#eval (2013265919 * 2013265921 + 1) % (2 ^ 32)  -- expect 0

-- Verify mu_spec: (MU * p) % R = 1
#eval (2281701377 * 2013265921) % (2 ^ 32)  -- expect 1

-- Smoke test: monty_reduce on concrete BabyBear value
#eval do
  let p := 2013265921
  let mu_neg := 2013265919
  let r := 2 ^ 32
  let x : Nat := 42
  let m := (x * mu_neg) % r
  let s := x + m * p
  let q := s / r
  let result := if q ≥ p then q - p else q
  -- R * result % p should equal x % p = 42
  return (result, (r * result) % p, x % p)

-- Smoke test: roundtrip to_monty / from_monty
#eval do
  let p := 2013265921
  let mu_neg := 2013265919
  let r := 2 ^ 32
  let a := 12345
  -- to_monty
  let a_M := (a * r) % p
  -- from_monty = monty_reduce(a_M)
  let m := (a_M * mu_neg) % r
  let s := a_M + m * p
  let q := s / r
  let result := if q ≥ p then q - p else q
  -- R * result % p should equal a_M % p = a * R % p
  -- result should reconstruct a (after one more reduction or direct check)
  return (a, a_M, result, (r * result) % p, a_M % p)

end AmoLean.Field.Montgomery
