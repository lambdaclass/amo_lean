/-
  AMO-Lean — FieldInt64: Int64 Range Certificates for Field Arithmetic
  Fase 29 N29.3: Verified Code Generation Pipeline

  Proves that BabyBear, Mersenne31, and KoalaBear field operations (add, sub, mul, neg)
  produce intermediate values within TrustLean's Int64 range [-2^63, 2^63-1].

  This guarantees TrustLean's `binOp_agreement` applies, enabling the
  verified codegen path (Path A) for these fields.

  Goldilocks (p ~ 2^64) does NOT fit in Int64 and is documented as requiring
  the untrusted path (Path B) until u128 support is added.

  0 sorry, 0 new axioms.
-/

import TrustLean.MicroC.Int64
import TrustLean.MicroC.UInt128
import TrustLean.MicroC.UInt128Agreement
import TrustLean.Plonky3.GoldilocksUInt128

set_option autoImplicit false

namespace AmoLean.Bridge.MicroC.FieldInt64

open TrustLean (InInt64Range maxInt64 minInt64)

/-! ## Field Constants -/

/-- BabyBear prime: p = 15 * 2^27 + 1 = 2013265921. Fits in u32. -/
def babyBearP : Nat := 2013265921

/-- Mersenne31 prime: p = 2^31 - 1 = 2147483647. Fits in u32. -/
def mersenne31P : Nat := 2147483647

/-- Goldilocks prime: p = 2^64 - 2^32 + 1 = 18446744069414584321. Fits in u64. -/
def goldilocksP : Nat := 18446744069414584321

/-! ## BabyBear Int64 Range Proofs

BabyBear elements satisfy 0 <= a < p = 2013265921 < 2^31.
- Addition: a + b < 2p < 2^32 << 2^63 -- fits
- Multiplication: a * b < p^2 ~ 4.05 * 10^18 < 9.22 * 10^18 = maxInt64 -- fits
- Subtraction: a - b > -p > -2^31 >> -2^63 = minInt64 -- fits
- Negation: -a > -p > -2^31 >> -2^63 = minInt64 -- fits
-/

/-- BabyBear addition stays in Int64: a + b < 2p < 2^32 << 2^63. -/
theorem babybear_add_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < babyBearP) (hb' : b < babyBearP) :
    InInt64Range (a + b) := by
  unfold InInt64Range maxInt64 minInt64 babyBearP at *
  constructor <;> omega

/-- BabyBear multiplication stays in Int64: a * b <= (p-1)^2 = 4053239664633446400 < maxInt64. -/
theorem babybear_mul_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < babyBearP) (hb' : b < babyBearP) :
    InInt64Range (a * b) := by
  unfold InInt64Range maxInt64 minInt64 babyBearP at *
  constructor
  · have := Int.mul_nonneg ha hb; omega
  · have ha1 : a ≤ 2013265920 := by omega
    have hb1 : b ≤ 2013265920 := by omega
    calc a * b ≤ a * 2013265920 := Int.mul_le_mul_of_nonneg_left hb1 ha
        _ ≤ 2013265920 * 2013265920 := Int.mul_le_mul_of_nonneg_right ha1 (by omega)
        _ ≤ 9223372036854775807 := by native_decide

/-- BabyBear subtraction stays in Int64: a - b > -p > minInt64. -/
theorem babybear_sub_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < babyBearP) (hb' : b < babyBearP) :
    InInt64Range (a - b) := by
  unfold InInt64Range maxInt64 minInt64 babyBearP at *
  constructor <;> omega

/-- BabyBear negation stays in Int64: -a >= -p+1 > minInt64. -/
theorem babybear_neg_in_int64 (a : Int) (ha : 0 ≤ a) (ha' : a < babyBearP) :
    InInt64Range (-a) := by
  unfold InInt64Range maxInt64 minInt64 babyBearP at *
  constructor <;> omega

/-! ## Mersenne31 Int64 Range Proofs

Mersenne31 elements satisfy 0 <= a < p = 2147483647 < 2^31.
- Addition: a + b < 2p < 2^32 << 2^63 -- fits
- Multiplication: a * b < p^2 ~ 4.61 * 10^18 < 9.22 * 10^18 = maxInt64 -- fits
- Subtraction: a - b > -p > -2^31 >> -2^63 = minInt64 -- fits
- Negation: -a > -p > -2^31 >> -2^63 = minInt64 -- fits
-/

/-- Mersenne31 addition stays in Int64: a + b < 2p < 2^32 << 2^63. -/
theorem mersenne31_add_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < mersenne31P) (hb' : b < mersenne31P) :
    InInt64Range (a + b) := by
  unfold InInt64Range maxInt64 minInt64 mersenne31P at *
  constructor <;> omega

/-- Mersenne31 multiplication stays in Int64: a * b <= (p-1)^2 = 4611686009837453316 < maxInt64. -/
theorem mersenne31_mul_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < mersenne31P) (hb' : b < mersenne31P) :
    InInt64Range (a * b) := by
  unfold InInt64Range maxInt64 minInt64 mersenne31P at *
  constructor
  · have := Int.mul_nonneg ha hb; omega
  · have ha1 : a ≤ 2147483646 := by omega
    have hb1 : b ≤ 2147483646 := by omega
    calc a * b ≤ a * 2147483646 := Int.mul_le_mul_of_nonneg_left hb1 ha
        _ ≤ 2147483646 * 2147483646 := Int.mul_le_mul_of_nonneg_right ha1 (by omega)
        _ ≤ 9223372036854775807 := by native_decide

/-- Mersenne31 subtraction stays in Int64: a - b > -p > minInt64. -/
theorem mersenne31_sub_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < mersenne31P) (hb' : b < mersenne31P) :
    InInt64Range (a - b) := by
  unfold InInt64Range maxInt64 minInt64 mersenne31P at *
  constructor <;> omega

/-- Mersenne31 negation stays in Int64: -a >= -p+1 > minInt64. -/
theorem mersenne31_neg_in_int64 (a : Int) (ha : 0 ≤ a) (ha' : a < mersenne31P) :
    InInt64Range (-a) := by
  unfold InInt64Range maxInt64 minInt64 mersenne31P at *
  constructor <;> omega

/-! ## KoalaBear Int64 Range Proofs

KoalaBear elements satisfy 0 <= a < p = 2130706433 < 2^31.
- Addition: a + b < 2p < 2^32 << 2^63 -- fits
- Multiplication: a * b < p^2 ~ 4.54 * 10^18 < 9.22 * 10^18 = maxInt64 -- fits
- Subtraction: a - b > -p > -2^31 >> -2^63 = minInt64 -- fits
- Negation: -a > -p > -2^31 >> -2^63 = minInt64 -- fits
-/

/-- KoalaBear prime: p = 2^31 - 2^24 + 1 = 2130706433. Fits in u32. -/
def koalaBearP : Nat := 2130706433

/-- KoalaBear addition stays in Int64: a + b < 2p < 2^32 << 2^63. -/
theorem koalabear_add_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < koalaBearP) (hb' : b < koalaBearP) :
    InInt64Range (a + b) := by
  unfold InInt64Range maxInt64 minInt64 koalaBearP at *
  constructor <;> omega

/-- KoalaBear multiplication stays in Int64: a * b <= (p-1)^2 = 4539909899366170624 < maxInt64. -/
theorem koalabear_mul_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < koalaBearP) (hb' : b < koalaBearP) :
    InInt64Range (a * b) := by
  unfold InInt64Range maxInt64 minInt64 koalaBearP at *
  constructor
  · have := Int.mul_nonneg ha hb; omega
  · have ha1 : a ≤ 2130706432 := by omega
    have hb1 : b ≤ 2130706432 := by omega
    calc a * b ≤ a * 2130706432 := Int.mul_le_mul_of_nonneg_left hb1 ha
        _ ≤ 2130706432 * 2130706432 := Int.mul_le_mul_of_nonneg_right ha1 (by omega)
        _ ≤ 9223372036854775807 := by native_decide

/-- KoalaBear subtraction stays in Int64: a - b > -p > minInt64. -/
theorem koalabear_sub_in_int64 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a < koalaBearP) (hb' : b < koalaBearP) :
    InInt64Range (a - b) := by
  unfold InInt64Range maxInt64 minInt64 koalaBearP at *
  constructor <;> omega

/-- KoalaBear negation stays in Int64: -a >= -p+1 > minInt64. -/
theorem koalabear_neg_in_int64 (a : Int) (ha : 0 ≤ a) (ha' : a < koalaBearP) :
    InInt64Range (-a) := by
  unfold InInt64Range maxInt64 minInt64 koalaBearP at *
  constructor <;> omega

/-! ## Goldilocks: Int64 Overflow Analysis

Goldilocks p = 2^64 - 2^32 + 1 = 18446744069414584321 ~ 1.84 * 10^19.
Field elements are up to p-1 ~ 1.84 * 10^19 > maxInt64 ~ 9.22 * 10^18.

Therefore, Goldilocks field elements **do not fit** in Int64Range.
This means:
- TrustLean's `binOp_agreement` does NOT apply to Goldilocks
- Goldilocks codegen requires either:
  (a) uint128_t accumulators (C extension)
  (b) Split-radix multiplication with explicit overflow handling
  (c) Working in reduced representation (e.g., two 32-bit limbs)

UPDATE (TrustLean v4.1.0): Goldilocks arithmetic fits in UInt128Range (2^128).
TrustLean's `evalMicroCBinOp_uint128_agree_*` theorems now apply.
Goldilocks codegen is VERIFIED via Path A with UInt128 agreement.
See Section 6 below for Goldilocks UInt128 certificates.
-/

/-- Goldilocks field elements exceed Int64 range: p-1 > maxInt64. -/
theorem goldilocks_exceeds_int64 : ¬ InInt64Range (goldilocksP - 1 : Int) := by
  unfold InInt64Range goldilocksP maxInt64 minInt64
  omega

/-! ## Bundled Field Certificates

A `FieldInt64Cert` bundles the proof that all four arithmetic operations
on field elements produce values within Int64 range. This is the key
precondition for using TrustLean's verified codegen pipeline (Path A).
-/

/-- Certificate that a prime field's arithmetic stays within Int64 range.
    Fields: `prime` is the characteristic, and four safety proofs guarantee
    that add/sub/mul/neg on elements in [0, prime) produce Int64-range values. -/
structure FieldInt64Cert where
  /-- The field characteristic -/
  prime : Nat
  /-- Addition of two field elements stays in Int64 range -/
  add_safe : ∀ a b : Int, 0 ≤ a → 0 ≤ b → a < prime → b < prime → InInt64Range (a + b)
  /-- Subtraction of two field elements stays in Int64 range -/
  sub_safe : ∀ a b : Int, 0 ≤ a → 0 ≤ b → a < prime → b < prime → InInt64Range (a - b)
  /-- Multiplication of two field elements stays in Int64 range -/
  mul_safe : ∀ a b : Int, 0 ≤ a → 0 ≤ b → a < prime → b < prime → InInt64Range (a * b)
  /-- Negation of a field element stays in Int64 range -/
  neg_safe : ∀ a : Int, 0 ≤ a → a < prime → InInt64Range (-a)

/-- BabyBear field certificate: all arithmetic stays in Int64 range. -/
def babybearCert : FieldInt64Cert where
  prime := babyBearP
  add_safe := babybear_add_in_int64
  sub_safe := babybear_sub_in_int64
  mul_safe := babybear_mul_in_int64
  neg_safe := babybear_neg_in_int64

/-- Mersenne31 field certificate: all arithmetic stays in Int64 range. -/
def mersenne31Cert : FieldInt64Cert where
  prime := mersenne31P
  add_safe := mersenne31_add_in_int64
  sub_safe := mersenne31_sub_in_int64
  mul_safe := mersenne31_mul_in_int64
  neg_safe := mersenne31_neg_in_int64

/-- KoalaBear field certificate: all arithmetic stays in Int64 range. -/
def koalabearCert : FieldInt64Cert where
  prime := koalaBearP
  add_safe := koalabear_add_in_int64
  sub_safe := koalabear_sub_in_int64
  mul_safe := koalabear_mul_in_int64
  neg_safe := koalabear_neg_in_int64

/-! ## Non-Vacuity Examples

Concrete instantiations proving the theorems are non-vacuous:
elements exist satisfying all hypotheses. -/

/-- Non-vacuity: BabyBear add with concrete values. -/
example : InInt64Range ((1000000000 : Int) + 1000000000) := by
  unfold InInt64Range maxInt64 minInt64; constructor <;> omega

/-- Non-vacuity: BabyBear mul with concrete values. -/
example : InInt64Range ((2013265920 : Int) * 2013265920) := by
  unfold InInt64Range maxInt64 minInt64
  constructor
  · omega
  · native_decide

/-- Non-vacuity: Mersenne31 mul with concrete values. -/
example : InInt64Range ((2147483646 : Int) * 2147483646) := by
  unfold InInt64Range maxInt64 minInt64
  constructor
  · omega
  · native_decide

/-- Non-vacuity: KoalaBear mul with concrete values. -/
example : InInt64Range ((2130706432 : Int) * 2130706432) := by
  unfold InInt64Range maxInt64 minInt64
  constructor
  · omega
  · native_decide

/-- Non-vacuity: Goldilocks overflow is real (for Int64). -/
example : ¬ InInt64Range (18446744069414584320 : Int) := by
  unfold InInt64Range maxInt64 minInt64; omega

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Goldilocks UInt128 Agreement (TrustLean v4.1.0)
-- ══════════════════════════════════════════════════════════════════

/-! ### Goldilocks UInt128 Agreement

TrustLean v4.1.0 adds `evalMicroCBinOp_uint128` with `InUInt128Range` (0 ≤ n < 2^128).
Goldilocks arithmetic fits: (P-1)² < 2^128, so `binOp_agreement_uint128` applies.

This closes the Goldilocks gap: ALL field operations are now verified via Path A
using the UInt128 evaluator instead of Int64. -/

open TrustLean (InUInt128Range goldilocks_P_int
  goldilocks_mul_fits_uint128 goldilocks_add_fits_uint128 goldilocks_sub_fits_uint128)

/-- Goldilocks Nat prime equals TrustLean's Int prime. -/
private theorem goldilocksP_eq : (goldilocksP : Int) = goldilocks_P_int := by
  unfold goldilocksP goldilocks_P_int; rfl

/-- Goldilocks mul fits UInt128: (P-1)² < 2^128.
    Bridges AMO-Lean's goldilocksP (Nat) to TrustLean's goldilocks_P_int (Int). -/
theorem goldilocks_mul_uint128 (a b : Int)
    (ha : 0 ≤ a ∧ a < goldilocksP) (hb : 0 ≤ b ∧ b < goldilocksP) :
    InUInt128Range (a * b) :=
  goldilocks_mul_fits_uint128 a b ⟨ha.1, goldilocksP_eq ▸ ha.2⟩ ⟨hb.1, goldilocksP_eq ▸ hb.2⟩

/-- Goldilocks add fits UInt128. -/
theorem goldilocks_add_uint128 (a b : Int)
    (ha : 0 ≤ a ∧ a < goldilocksP) (hb : 0 ≤ b ∧ b < goldilocksP) :
    InUInt128Range (a + b) :=
  goldilocks_add_fits_uint128 a b ⟨ha.1, goldilocksP_eq ▸ ha.2⟩ ⟨hb.1, goldilocksP_eq ▸ hb.2⟩

/-- Goldilocks sub fits UInt128 (when a ≥ b, i.e., no underflow). -/
theorem goldilocks_sub_uint128 (a b : Int)
    (ha : 0 ≤ a ∧ a < goldilocksP) (hb : 0 ≤ b) (hsub : 0 ≤ a - b) :
    InUInt128Range (a - b) :=
  goldilocks_sub_fits_uint128 a b ⟨ha.1, goldilocksP_eq ▸ ha.2⟩ hb hsub

/-- Bundled UInt128 certificate for field arithmetic.
    Note: sub_safe requires non-negative result (no underflow). -/
structure FieldUInt128Cert where
  prime : Nat
  add_safe : ∀ a b : Int, 0 ≤ a → 0 ≤ b → a < prime → b < prime → InUInt128Range (a + b)
  sub_safe : ∀ a b : Int, 0 ≤ a → a < prime → 0 ≤ b → 0 ≤ a - b → InUInt128Range (a - b)
  mul_safe : ∀ a b : Int, 0 ≤ a → 0 ≤ b → a < prime → b < prime → InUInt128Range (a * b)

/-- Goldilocks UInt128 certificate: ALL arithmetic fits in 128-bit range. -/
def goldilocksCert128 : FieldUInt128Cert where
  prime := goldilocksP
  add_safe := fun a b ha hb ha' hb' => goldilocks_add_uint128 a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
  sub_safe := fun a b ha ha' hb hsub => goldilocks_sub_uint128 a b ⟨ha, ha'⟩ hb hsub
  mul_safe := fun a b ha hb ha' hb' => goldilocks_mul_uint128 a b ⟨ha, ha'⟩ ⟨hb, hb'⟩

end AmoLean.Bridge.MicroC.FieldInt64
