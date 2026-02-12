/-
  AMO-Lean: BabyBear Field Implementation
  Fase 8 Onda 1 — Subfase 2: BabyBear Field for Risc0/SP1 Ecosystem

  BabyBear Field: F_p where p = 2^31 - 2^27 + 1 = 2013265921

  This field is used by Risc0/SP1 (Plonky3) for efficient ZK proofs.
  The special structure allows fast modular reduction using
  the identity: 2^31 ≡ 2^27 - 1 (mod p)

  p - 1 = 2^27 × 15 = 2^27 × 3 × 5
  So BabyBear supports NTT sizes up to 2^27 (134M elements).
  Generator g = 31 (multiplicative order = p-1).

  Reference: Plonky3 baby-bear crate (Polygon)

  === VERIFICATION STRATEGY ===
  Same as Goldilocks: prove algebraic properties via isomorphism to ZMod p:
  1. Define toZMod : BabyBearField → ZMod p
  2. Prove toZMod is a ring homomorphism (respects +, *, -, 0, 1)
  3. Prove toZMod is injective (via canonicity of representations)
  4. Transfer all proofs via toZMod_injective

  The primality of p = 2013265921 CAN be verified by native_decide
  (unlike Goldilocks which is too large).
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.FieldTheory.Finite.Basic
import Batteries.Data.UInt

namespace AmoLean.Field.BabyBear

/-! ## Part 1: Field Constants -/

/-- BabyBear prime: p = 2^31 - 2^27 + 1 = 2013265921 -/
def ORDER : UInt32 := 2013265921

/-- Order as Nat for ZMod usage -/
def ORDER_NAT : Nat := ORDER.toNat

/-- BabyBear prime is prime.
    Unlike Goldilocks, this IS small enough for native_decide. -/
theorem babybear_prime_is_prime : Nat.Prime ORDER_NAT := by native_decide

instance : Fact (Nat.Prime ORDER_NAT) := ⟨babybear_prime_is_prime⟩

/-- ORDER_NAT is positive (follows from primality) -/
theorem order_nat_pos : 0 < ORDER_NAT := Nat.Prime.pos babybear_prime_is_prime

/-- ORDER_NAT is at least 2 (follows from primality) -/
theorem order_nat_ge_two : 2 ≤ ORDER_NAT := Nat.Prime.two_le babybear_prime_is_prime

/-- ORDER.toNat equals ORDER_NAT -/
@[simp]
theorem order_toNat_eq : ORDER.toNat = ORDER_NAT := rfl

/-- ORDER.toNat < 2^32 (UInt32.size) -/
theorem order_lt_size : ORDER.toNat < UInt32.size := by native_decide

/-- Key reduction constant: 2^27 - 1 = 134217727
    Since 2^31 ≡ 2^27 - 1 (mod p), this is used in fast reduction. -/
def REDUCE_CONST : UInt32 := 134217727

/-- Low 31 bits mask -/
def LOW_31_MASK : UInt32 := 0x7FFFFFFF

/-! ## Part 2: BabyBear Field Type -/

/-- BabyBear field element.
    Invariant enforced at type level: value < ORDER -/
structure BabyBearField where
  value : UInt32
  h_lt : value.toNat < ORDER.toNat

instance : DecidableEq BabyBearField := fun a b =>
  if h : a.value = b.value then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro hab; exact h (congrArg BabyBearField.value hab))

instance : Repr BabyBearField where
  reprPrec a n := reprPrec a.value n

instance : Hashable BabyBearField where
  hash a := hash a.value

instance : Inhabited BabyBearField := ⟨⟨0, by native_decide⟩⟩

namespace BabyBearField

/-- For any BabyBearField element, value.toNat < 2^32 -/
theorem val_lt_size (a : BabyBearField) : a.value.toNat < UInt32.size := a.value.val.isLt

/-- Extensionality theorem -/
@[ext]
theorem ext {a b : BabyBearField} (h : a.value = b.value) : a = b := by
  cases a; cases b; simp_all

/-! ## Part 3: Constructors -/

/-- Create a field element from UInt32, reducing if necessary -/
def ofUInt32 (n : UInt32) : BabyBearField :=
  if h : n < ORDER then ⟨n, h⟩
  else ⟨(n.toNat % ORDER.toNat).toUInt32, by
    have hord_pos : 0 < ORDER.toNat := order_nat_pos
    have hord_lt : ORDER.toNat < UInt32.size := by native_decide
    have hlt : n.toNat % ORDER.toNat < ORDER.toNat := Nat.mod_lt _ hord_pos
    simp only [Nat.toUInt32, UInt32.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n.toNat % ORDER.toNat < UInt32.size)]
    exact hlt⟩

/-- Create a field element from Nat -/
def ofNat (n : Nat) : BabyBearField :=
  let reduced := n % ORDER.toNat
  ofUInt32 reduced.toUInt32

/-- Zero element -/
def zero : BabyBearField := ⟨0, by native_decide⟩

/-- One element -/
def one : BabyBearField := ⟨1, by native_decide⟩

/-! ## Part 4: Core Arithmetic Operations -/

/-- Addition: (a + b) mod p
    Uses Nat arithmetic to avoid UInt32 overflow. -/
def add (a b : BabyBearField) : BabyBearField :=
  let sum := a.value.toNat + b.value.toNat
  let reduced := if sum >= ORDER.toNat then sum - ORDER.toNat else sum
  ⟨reduced.toUInt32, by
    have ha := a.h_lt; have hb := b.h_lt
    have hord_lt : ORDER.toNat < UInt32.size := by native_decide
    have hlt : reduced < ORDER.toNat := by
      show (if a.value.toNat + b.value.toNat ≥ ORDER.toNat
            then a.value.toNat + b.value.toNat - ORDER.toNat
            else a.value.toNat + b.value.toNat) < ORDER.toNat
      split_ifs with h <;> omega
    simp only [Nat.toUInt32, UInt32.toNat_ofNat, Nat.mod_eq_of_lt (by omega : reduced < UInt32.size)]
    exact hlt⟩

/-- Subtraction: (a - b) mod p -/
def sub (a b : BabyBearField) : BabyBearField :=
  if h : a.value >= b.value then
    ⟨a.value - b.value, by
      have ha := a.h_lt
      have hsub : (a.value - b.value).toNat = a.value.toNat - b.value.toNat := by
        rw [UInt32.toNat_sub_of_le]; exact h
      rw [hsub]; omega⟩
  else
    ⟨ORDER - b.value + a.value, by
      have ha := a.h_lt; have hb := b.h_lt
      have halt : a.value.toNat < b.value.toNat := by
        simp only [ge_iff_le, UInt32.le_iff_toNat_le, not_le] at h; exact h
      have hb_le_ord : b.value ≤ ORDER := by
        simp only [UInt32.le_iff_toNat_le]; omega
      have hsub1 : (ORDER - b.value).toNat = ORDER.toNat - b.value.toNat := by
        rw [UInt32.toNat_sub_of_le]; exact hb_le_ord
      have hsum_lt : ORDER.toNat - b.value.toNat + a.value.toNat < UInt32.size := by
        have : ORDER.toNat < UInt32.size := by native_decide
        omega
      have hadd : (ORDER - b.value + a.value).toNat =
                  (ORDER - b.value).toNat + a.value.toNat := by
        simp only [UInt32.toNat_add, hsub1, Nat.mod_eq_of_lt hsum_lt]
      rw [hadd, hsub1]; omega⟩

/-- Negation: -a mod p -/
def neg (a : BabyBearField) : BabyBearField :=
  if h : a.value = 0 then ⟨0, by native_decide⟩
  else ⟨ORDER - a.value, by
    have ha := a.h_lt
    have ha_pos : 0 < a.value.toNat := by
      by_contra hle; push_neg at hle
      exact h (UInt32.ext (Nat.eq_zero_of_le_zero hle))
    have hsub : (ORDER - a.value).toNat = ORDER.toNat - a.value.toNat := by
      rw [UInt32.toNat_sub_of_le]; simp only [UInt32.le_iff_toNat_le]; omega
    rw [hsub]; omega⟩

/-- BabyBear modular reduction for multiplication.

    For z = a * b (product of two values < p, so z < p² < 2^62):

    We compute z mod p using Nat arithmetic for correctness.
    A future optimization can use the BabyBear identity:
      2^31 ≡ 2^27 - 1 (mod p)
    to split z into z_hi (bits ≥ 31) and z_lo (bits 0..30):
      z ≡ z_lo + z_hi * (2^27 - 1) (mod p)
    with possible further reduction steps.

    For now, we use the simple % reduction which is correct by definition. -/
def reduceMul (product : Nat) : BabyBearField :=
  ⟨(product % ORDER.toNat).toUInt32, by
    have hord_pos : 0 < ORDER.toNat := order_nat_pos
    have hord_lt : ORDER.toNat < UInt32.size := by native_decide
    have hlt : product % ORDER.toNat < ORDER.toNat := Nat.mod_lt _ hord_pos
    simp only [Nat.toUInt32, UInt32.toNat_ofNat, Nat.mod_eq_of_lt (by omega : product % ORDER.toNat < UInt32.size)]
    exact hlt⟩

/-- Multiplication: (a * b) mod p -/
def mul (a b : BabyBearField) : BabyBearField :=
  let product := a.value.toNat * b.value.toNat
  reduceMul product

/-- Squaring: a^2 mod p -/
def square (a : BabyBearField) : BabyBearField :=
  mul a a

/-- Exponentiation: base^exp mod p using binary method -/
def pow (base : BabyBearField) (exp : Nat) : BabyBearField :=
  match exp with
  | 0 => one
  | 1 => base
  | n + 2 =>
    let halfExp := (n + 2) / 2
    let halfPow := pow base halfExp
    let squared := square halfPow
    if (n + 2) % 2 == 0 then squared
    else mul squared base
termination_by exp

/-- Multiplicative inverse: a^(-1) mod p using Fermat's little theorem
    a^(-1) ≡ a^(p-2) (mod p) -/
def inv (a : BabyBearField) : BabyBearField :=
  if a.value == 0 then zero  -- Undefined, return 0 as sentinel
  else pow a (ORDER.toNat - 2)

/-- Division: a / b = a * b^(-1) mod p -/
def div (a b : BabyBearField) : BabyBearField :=
  mul a (inv b)

/-! ## S-Box for Poseidon2

For BabyBear: p-1 = 2^27 × 3 × 5
  - gcd(5, p-1) = 5 ≠ 1  →  x^5 is NOT invertible
  - gcd(7, p-1) = 1       →  x^7 IS invertible (SECURE)
-/

/-- S-Box exponent for BabyBear (MUST be 7, not 5) -/
def SBOX_EXPONENT : Nat := 7

/-- S-Box: x^7 (for Poseidon2 on BabyBear) -/
def sbox (x : BabyBearField) : BabyBearField :=
  let x2 := square x      -- x^2
  let x4 := square x2     -- x^4
  let x6 := mul x4 x2     -- x^6
  mul x6 x                -- x^7

end BabyBearField

/-! ## Part 5: Instances -/

instance : Add BabyBearField := ⟨BabyBearField.add⟩
instance : Sub BabyBearField := ⟨BabyBearField.sub⟩
instance : Neg BabyBearField := ⟨BabyBearField.neg⟩
instance : Mul BabyBearField := ⟨BabyBearField.mul⟩
instance : Div BabyBearField := ⟨BabyBearField.div⟩

instance : OfNat BabyBearField n where
  ofNat := BabyBearField.ofNat n

instance : Zero BabyBearField where
  zero := BabyBearField.zero

instance : ToString BabyBearField where
  toString f := toString f.value

namespace BabyBearField

/-! ## Part 6: Field Properties -/

/-- Field element is valid if value < ORDER -/
def isValid (a : BabyBearField) : Prop := a.value < ORDER

/-- The order of the field -/
def order : Nat := ORDER.toNat

/-! ## Part 7: Conversion Utilities -/

/-- Convert to UInt32 (for FFI/testing) -/
def toUInt32 (a : BabyBearField) : UInt32 := a.value

/-- Convert to Nat -/
def toNat (a : BabyBearField) : Nat := a.value.toNat

end BabyBearField

/-! ## Part 8: Constants -/

/-- p - 1: Maximum valid field element -/
def P_MINUS_1 : BabyBearField := ⟨ORDER - 1, by native_decide⟩

/-- p - 2: Used for inverse calculation -/
def P_MINUS_2 : BabyBearField := ⟨ORDER - 2, by native_decide⟩

/-! ## Part 9: ZMod Isomorphism Infrastructure

Same strategy as Goldilocks: GoldilocksField ≃+* ZMod ORDER_NAT.
-/

/-- Conversion from BabyBearField to ZMod ORDER_NAT -/
def toZMod (x : BabyBearField) : ZMod ORDER_NAT :=
  (x.value.toNat : ZMod ORDER_NAT)

/-- Conversion from ZMod ORDER_NAT back to BabyBearField -/
def ofZMod (z : ZMod ORDER_NAT) : BabyBearField :=
  ⟨(ZMod.val z).toUInt32, by
    have hval : ZMod.val z < ORDER_NAT := ZMod.val_lt z
    have hlt_size : ZMod.val z < UInt32.size := by
      have : ORDER_NAT < UInt32.size := by native_decide
      omega
    simp only [Nat.toUInt32, UInt32.toNat_ofNat, Nat.mod_eq_of_lt hlt_size]
    exact hval⟩

/-! ### Canonicity -/

/-- A BabyBearField element is canonical if value < ORDER -/
def BabyBearField.isCanonical (a : BabyBearField) : Prop := a.value < ORDER

/-- All BabyBearField values are canonical.
    Now a trivial consequence of the h_lt proof field. -/
theorem babybear_canonical (a : BabyBearField) : a.isCanonical := a.h_lt

/-! ### val_eq Lemmas -/

/-- Addition produces the modular sum at the Nat level. -/
theorem add_val_eq (a b : BabyBearField) :
    (a + b).value.toNat = (a.value.toNat + b.value.toNat) % ORDER_NAT := by
  simp only [HAdd.hAdd, Add.add, BabyBearField.add, ORDER_NAT]
  have ha : a.value.toNat < ORDER.toNat := babybear_canonical a
  have hb : b.value.toNat < ORDER.toNat := babybear_canonical b
  have hsum_eq : a.value.toNat.add b.value.toNat = a.value.toNat + b.value.toNat := rfl
  split_ifs with h
  · -- Case: sum >= ORDER
    have hge : a.value.toNat + b.value.toNat ≥ ORDER.toNat := by rw [← hsum_eq]; exact h
    have hsum_bound : a.value.toNat + b.value.toNat < 2 * ORDER.toNat := by omega
    have hres_bound : a.value.toNat + b.value.toNat - ORDER.toNat < ORDER.toNat := by omega
    have hres_lt_size : a.value.toNat + b.value.toNat - ORDER.toNat < UInt32.size := by
      have : ORDER.toNat < UInt32.size := by native_decide
      omega
    simp only [Nat.toUInt32, UInt32.toNat_ofNat, hsum_eq, Nat.mod_eq_of_lt hres_lt_size]
    have heq : a.value.toNat + b.value.toNat = ORDER.toNat + (a.value.toNat + b.value.toNat - ORDER.toNat) := by omega
    conv_rhs => rw [heq]
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hres_bound]
  · -- Case: sum < ORDER
    have hsum_lt : a.value.toNat + b.value.toNat < ORDER.toNat := by
      simp only [ge_iff_le, not_le] at h; rw [← hsum_eq]; exact h
    have hsum_lt_size : a.value.toNat + b.value.toNat < UInt32.size := by
      have : ORDER.toNat < UInt32.size := by native_decide
      omega
    simp only [Nat.toUInt32, UInt32.toNat_ofNat, hsum_eq, Nat.mod_eq_of_lt hsum_lt_size]
    exact (Nat.mod_eq_of_lt hsum_lt).symm

/-- Negation produces the modular negation at the Nat level. -/
theorem neg_val_eq (a : BabyBearField) :
    (-a).value.toNat = (ORDER_NAT - a.value.toNat % ORDER_NAT) % ORDER_NAT := by
  simp only [Neg.neg, BabyBearField.neg, ORDER_NAT]
  have ha : a.value.toNat < ORDER.toNat := babybear_canonical a
  have ha_mod : a.value.toNat % ORDER.toNat = a.value.toNat := Nat.mod_eq_of_lt ha
  rw [ha_mod]
  split_ifs with h
  · simp only [h, UInt32.toNat_zero, Nat.sub_zero, Nat.mod_self]
  · have ha_pos : 0 < a.value.toNat := by
      by_contra hcon
      push_neg at hcon
      have : a.value.toNat = 0 := Nat.eq_zero_of_le_zero hcon
      exact h (UInt32.ext this)
    have hsub_lt : ORDER.toNat - a.value.toNat < ORDER.toNat := by omega
    have hsub_lt_size : ORDER.toNat - a.value.toNat < UInt32.size := by
      have : ORDER.toNat < UInt32.size := by native_decide
      omega
    have hresult : (ORDER - a.value).toNat = ORDER.toNat - a.value.toNat := by
      rw [UInt32.toNat_sub_of_le]
      · exact le_of_lt ha
    rw [hresult, Nat.mod_eq_of_lt hsub_lt]

/-- Subtraction produces the modular difference at the Nat level. -/
theorem sub_val_eq (a b : BabyBearField) :
    (a - b).value.toNat = (a.value.toNat + ORDER_NAT - b.value.toNat) % ORDER_NAT := by
  simp only [HSub.hSub, Sub.sub, BabyBearField.sub, ORDER_NAT]
  have ha : a.value.toNat < ORDER.toNat := babybear_canonical a
  have hb : b.value.toNat < ORDER.toNat := babybear_canonical b
  split_ifs with h
  · have hge : b.value ≤ a.value := h
    have hsub : (a.value.sub b.value).toNat = a.value.toNat - b.value.toNat :=
      UInt32.toNat_sub_of_le a.value b.value hge
    simp only [hsub]
    have hge_nat : b.value.toNat ≤ a.value.toNat := by
      simp only [UInt32.le_iff_toNat_le] at hge; exact hge
    have hdiff_lt : a.value.toNat - b.value.toNat < ORDER.toNat := by omega
    have hsub_eq : (a.value.toNat + ORDER.toNat).sub b.value.toNat =
                   a.value.toNat + ORDER.toNat - b.value.toNat := rfl
    rw [hsub_eq]
    have heq : a.value.toNat + ORDER.toNat - b.value.toNat =
               (a.value.toNat - b.value.toNat) + ORDER.toNat := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    exact (Nat.mod_eq_of_lt hdiff_lt).symm
  · have hlt : a.value.toNat < b.value.toNat := by
      simp only [UInt32.le_iff_toNat_le, ge_iff_le, not_le] at h; exact h
    have hb_le : b.value ≤ ORDER := by
      simp only [UInt32.le_iff_toNat_le]; exact le_of_lt hb
    have hsub1 : (ORDER.sub b.value).toNat = ORDER.toNat - b.value.toNat :=
      UInt32.toNat_sub_of_le ORDER b.value hb_le
    have hsum_bound : ORDER.toNat - b.value.toNat + a.value.toNat < UInt32.size := by
      have horder_lt : ORDER.toNat < UInt32.size := by native_decide
      omega
    have hadd : (ORDER.sub b.value + a.value).toNat =
                (ORDER.sub b.value).toNat + a.value.toNat := by
      rw [UInt32.toNat_add, hsub1]
      exact Nat.mod_eq_of_lt hsum_bound
    simp only [hadd, hsub1]
    have hsub_eq : (a.value.toNat + ORDER.toNat).sub b.value.toNat =
                   a.value.toNat + ORDER.toNat - b.value.toNat := rfl
    rw [hsub_eq]
    have hres : ORDER.toNat - b.value.toNat + a.value.toNat =
                a.value.toNat + ORDER.toNat - b.value.toNat := by omega
    rw [hres]
    have hres_lt : a.value.toNat + ORDER.toNat - b.value.toNat < ORDER.toNat := by omega
    exact (Nat.mod_eq_of_lt hres_lt).symm

/-- Multiplication produces the modular product at the Nat level. -/
theorem mul_val_eq (a b : BabyBearField) :
    (a * b).value.toNat % ORDER_NAT = (a.value.toNat * b.value.toNat) % ORDER_NAT := by
  simp only [HMul.hMul, Mul.mul, BabyBearField.mul, BabyBearField.reduceMul, ORDER_NAT]
  -- reduceMul computes (product % ORDER).toUInt32
  -- Need: ((a * b % ORDER).toUInt32).toNat % ORDER = (a * b) % ORDER
  have ha : a.value.toNat < ORDER.toNat := babybear_canonical a
  have hb : b.value.toNat < ORDER.toNat := babybear_canonical b
  have hord_pos : 0 < ORDER.toNat := order_nat_pos
  -- product % ORDER < ORDER < 2^32
  have hmod_lt : a.value.toNat * b.value.toNat % ORDER.toNat < ORDER.toNat :=
    Nat.mod_lt _ hord_pos
  have hmod_lt_size : a.value.toNat * b.value.toNat % ORDER.toNat < UInt32.size := by
    have : ORDER.toNat < UInt32.size := by native_decide
    omega
  simp only [Nat.toUInt32, UInt32.toNat_ofNat]
  -- Goal uses Nat.mul (dot notation); normalize to * for rw
  simp only [Nat.mul_def]
  -- Goal: (a*b % ORDER) % 2^32 % ORDER = (a*b) % ORDER
  -- Since a*b % ORDER < ORDER < 2^32, the % 2^32 is identity
  have hmod_lt_2_32 : a.value.toNat * b.value.toNat % ORDER.toNat < 2 ^ 32 := by
    have : ORDER.toNat < 2 ^ 32 := by native_decide
    have := Nat.mod_lt (a.value.toNat * b.value.toNat) hord_pos
    omega
  rw [Nat.mod_eq_of_lt hmod_lt_2_32]
  -- Goal: (a*b % ORDER) % ORDER = (a*b) % ORDER
  exact Nat.mod_mod_of_dvd _ (dvd_refl ORDER.toNat)

/-! ### toZMod Homomorphism Properties -/

@[simp]
theorem toZMod_zero : toZMod (0 : BabyBearField) = 0 := by
  simp only [toZMod, Zero.zero, BabyBearField.zero]
  rfl

@[simp]
theorem toZMod_one : toZMod (1 : BabyBearField) = 1 := by
  simp only [toZMod, One.one, BabyBearField.one]
  rfl

@[simp]
theorem toZMod_add (a b : BabyBearField) :
    toZMod (a + b) = toZMod a + toZMod b := by
  apply ZMod.val_injective
  simp only [toZMod]
  have hab : (a + b).value.toNat < ORDER_NAT := babybear_canonical (a + b)
  have ha : a.value.toNat < ORDER_NAT := babybear_canonical a
  have hb : b.value.toNat < ORDER_NAT := babybear_canonical b
  rw [ZMod.val_cast_of_lt hab]
  rw [ZMod.val_add]
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb]
  exact add_val_eq a b

@[simp]
theorem toZMod_neg (a : BabyBearField) :
    toZMod (-a) = -toZMod a := by
  apply ZMod.val_injective
  simp only [toZMod]
  have ha : a.value.toNat < ORDER_NAT := babybear_canonical a
  have hnega : (-a).value.toNat < ORDER_NAT := babybear_canonical (-a)
  rw [ZMod.val_cast_of_lt hnega]
  rw [ZMod.neg_val']
  rw [ZMod.val_cast_of_lt ha]
  rw [neg_val_eq]
  have ha_mod : a.value.toNat % ORDER_NAT = a.value.toNat := Nat.mod_eq_of_lt ha
  rw [ha_mod]

@[simp]
theorem toZMod_mul (a b : BabyBearField) :
    toZMod (a * b) = toZMod a * toZMod b := by
  simp only [toZMod]
  rw [← Nat.cast_mul]
  rw [ZMod.natCast_eq_natCast_iff]
  exact mul_val_eq a b

@[simp]
theorem toZMod_sub (a b : BabyBearField) :
    toZMod (a - b) = toZMod a - toZMod b := by
  apply ZMod.val_injective
  simp only [toZMod]
  have ha : a.value.toNat < ORDER_NAT := babybear_canonical a
  have hb : b.value.toNat < ORDER_NAT := babybear_canonical b
  have hsub : (a - b).value.toNat < ORDER_NAT := babybear_canonical (a - b)
  rw [ZMod.val_cast_of_lt hsub]
  rw [sub_eq_add_neg]
  rw [ZMod.val_add, ZMod.neg_val']
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb]
  rw [sub_val_eq]
  have hp : ORDER_NAT > 0 := order_nat_pos
  conv_rhs =>
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have heq : a.value.toNat + ORDER_NAT - b.value.toNat = a.value.toNat + (ORDER_NAT - b.value.toNat) := by
    have hle : b.value.toNat ≤ ORDER_NAT := le_of_lt hb
    omega
  rw [heq]

/-- toZMod is injective. -/
theorem toZMod_injective : Function.Injective toZMod := by
  intro a b hab
  simp only [toZMod] at hab
  have ha : a.value.toNat < ORDER_NAT := babybear_canonical a
  have hb : b.value.toNat < ORDER_NAT := babybear_canonical b
  have ha_val : (a.value.toNat : ZMod ORDER_NAT).val = a.value.toNat := ZMod.val_cast_of_lt ha
  have hb_val : (b.value.toNat : ZMod ORDER_NAT).val = b.value.toNat := ZMod.val_cast_of_lt hb
  have hval : (a.value.toNat : ZMod ORDER_NAT).val = (b.value.toNat : ZMod ORDER_NAT).val := by
    rw [hab]
  rw [ha_val, hb_val] at hval
  have hval_eq : a.value = b.value := UInt32.ext hval
  exact BabyBearField.ext hval_eq

@[simp]
theorem toZMod_ofNat (n : Nat) :
    toZMod (BabyBearField.ofNat n) = (n : ZMod ORDER_NAT) := by
  simp only [toZMod, BabyBearField.ofNat, BabyBearField.ofUInt32, ORDER_NAT]
  have hlt : n % ORDER.toNat < ORDER.toNat := Nat.mod_lt n order_nat_pos
  have hlt_size : n % ORDER.toNat < UInt32.size := by
    have : ORDER.toNat < UInt32.size := by native_decide
    omega
  have htoUInt32 : (n % ORDER.toNat).toUInt32.toNat = n % ORDER.toNat := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat, Nat.mod_eq_of_lt hlt_size]
  have hcond : (n % ORDER.toNat).toUInt32 < ORDER := by
    simp only [UInt32.lt_iff_toNat_lt, htoUInt32]
    exact hlt
  simp only [dif_pos hcond, htoUInt32]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq n ORDER.toNat

/-- Bridge: BabyBearField.mul equals * (for simp unification). -/
private theorem mul_def (a b : BabyBearField) : BabyBearField.mul a b = a * b := rfl

/-- toZMod respects square (helper for toZMod_pow). -/
private theorem toZMod_square (a : BabyBearField) :
    toZMod (BabyBearField.square a) = (toZMod a) * (toZMod a) :=
  toZMod_mul a a

/-- toZMod respects pow.
    Proved by strong induction matching the binary exponentiation structure
    of BabyBearField.pow. Each branch reduces to toZMod_mul and toZMod_one. -/
@[simp]
theorem toZMod_pow (a : BabyBearField) (n : Nat) :
    toZMod (BabyBearField.pow a n) = (toZMod a) ^ n := by
  induction n using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 =>
      simp only [BabyBearField.pow, pow_zero]
      exact toZMod_one
    | 1 => simp [BabyBearField.pow, pow_one]
    | n + 2 =>
      have h_lt : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih _ h_lt
      simp only [BabyBearField.pow]
      split
      · next heven =>
        have hmod : (n + 2) % 2 = 0 := eq_of_beq heven
        simp only [BabyBearField.square, mul_def, toZMod_mul, hrec, ← pow_add]
        congr 1; omega
      · next hodd =>
        have hmod : (n + 2) % 2 ≠ 0 := by intro h; exact hodd (by simp [h])
        simp only [BabyBearField.square, mul_def, toZMod_mul, hrec, ← pow_add, ← pow_succ]
        congr 1; omega

/-- toZMod respects inv.
    For a = 0: inv 0 = 0 and 0⁻¹ = 0 in ZMod.
    For a ≠ 0: inv a = a^(p-2) and a^(p-2) = a⁻¹ by Fermat's Little Theorem
    (ZMod.pow_card_sub_one_eq_one). -/
@[simp]
theorem toZMod_inv (a : BabyBearField) :
    toZMod (BabyBearField.inv a) = (toZMod a)⁻¹ := by
  simp only [BabyBearField.inv]
  split
  · next hzero =>
    have htza : toZMod a = 0 := by
      have hv : a.value = 0 := eq_of_beq hzero
      show (a.value.toNat : ZMod ORDER_NAT) = 0
      rw [hv]; simp
    rw [htza, inv_zero]; exact toZMod_zero
  · next hnonzero =>
    rw [toZMod_pow, order_toNat_eq]
    have hne : toZMod a ≠ 0 := by
      intro heq; apply hnonzero
      have := toZMod_injective (heq.trans toZMod_zero.symm)
      subst this; native_decide
    have hfermat : (toZMod a) ^ (ORDER_NAT - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hne
    have h1 : (toZMod a) ^ (ORDER_NAT - 2) * toZMod a = 1 := by
      rw [← pow_succ, show ORDER_NAT - 2 + 1 = ORDER_NAT - 1 from by
        have := order_nat_ge_two; omega]
      exact hfermat
    exact mul_right_cancel₀ hne (h1.trans (inv_mul_cancel₀ hne).symm)

/-! ## Part 10: Algebraic Instances via toZMod -/

instance : One BabyBearField where
  one := BabyBearField.one

instance : Pow BabyBearField ℕ where
  pow := BabyBearField.pow

instance : NatCast BabyBearField where
  natCast n := BabyBearField.ofNat n

instance : IntCast BabyBearField where
  intCast n := if n ≥ 0 then BabyBearField.ofNat n.toNat
               else BabyBearField.neg (BabyBearField.ofNat (-n).toNat)

instance : Inv BabyBearField where
  inv := BabyBearField.inv

/-- CommRing instance for BabyBearField.
    All laws follow from the toZMod homomorphism to ZMod p. -/
instance : CommRing BabyBearField where
  add_assoc := fun a b c => by
    apply toZMod_injective
    simp only [toZMod_add]
    ring
  zero_add := fun a => by
    show BabyBearField.add BabyBearField.zero a = a
    simp only [BabyBearField.add, BabyBearField.zero]
    simp only [UInt32.toNat_zero, Nat.zero_add]
    have ha : a.value.toNat < ORDER.toNat := babybear_canonical a
    have hcond : ¬(a.value.toNat ≥ ORDER.toNat) := not_le.mpr ha
    simp only [hcond, ↓reduceIte]
    ext
    simp only [Nat.toUInt32]
    have hlt : a.value.toNat < UInt32.size := a.value.val.isLt
    rw [UInt32.ofNat_toNat]
  add_zero := fun a => by
    show BabyBearField.add a BabyBearField.zero = a
    simp only [BabyBearField.add, BabyBearField.zero]
    simp only [UInt32.toNat_zero, Nat.add_zero]
    have ha : a.value.toNat < ORDER.toNat := babybear_canonical a
    have hcond : ¬(a.value.toNat ≥ ORDER.toNat) := not_le.mpr ha
    simp only [hcond, ↓reduceIte]
    ext
    simp only [Nat.toUInt32]
    have hlt : a.value.toNat < UInt32.size := a.value.val.isLt
    rw [UInt32.ofNat_toNat]
  add_comm := fun a b => by
    show BabyBearField.add a b = BabyBearField.add b a
    simp only [BabyBearField.add]
    have hcomm : a.value.toNat + b.value.toNat = b.value.toNat + a.value.toNat := Nat.add_comm _ _
    simp only [hcomm]
  neg := BabyBearField.neg
  neg_add_cancel := fun a => by
    apply toZMod_injective
    have hneg : toZMod a.neg = -toZMod a := toZMod_neg a
    simp only [toZMod_add, toZMod_zero]
    rw [hneg]
    ring
  nsmul := fun n a => BabyBearField.mul (BabyBearField.ofNat n) a
  nsmul_zero := fun a => by
    show BabyBearField.ofNat 0 * a = 0
    apply toZMod_injective
    rw [toZMod_mul, toZMod_ofNat, Nat.cast_zero, zero_mul, toZMod_zero]
  nsmul_succ := fun n a => by
    show (BabyBearField.ofNat (n + 1)).mul a = (BabyBearField.ofNat n).mul a + a
    apply toZMod_injective
    have hmul1 : toZMod ((BabyBearField.ofNat (n + 1)).mul a) =
                 toZMod (BabyBearField.ofNat (n + 1)) * toZMod a := toZMod_mul _ _
    have hmul2 : toZMod ((BabyBearField.ofNat n).mul a) =
                 toZMod (BabyBearField.ofNat n) * toZMod a := toZMod_mul _ _
    rw [hmul1, toZMod_add, hmul2, toZMod_ofNat, toZMod_ofNat]
    push_cast
    ring
  zsmul := fun n a => if n ≥ 0
                      then BabyBearField.mul (BabyBearField.ofNat n.toNat) a
                      else BabyBearField.neg (BabyBearField.mul (BabyBearField.ofNat (-n).toNat) a)
  zsmul_zero' := fun a => by
    simp only [ge_iff_le, le_refl, ↓reduceIte, Int.toNat_zero]
    show BabyBearField.ofNat 0 * a = 0
    apply toZMod_injective
    rw [toZMod_mul, toZMod_ofNat, Nat.cast_zero, zero_mul, toZMod_zero]
  zsmul_succ' := fun n a => by
    simp only [ge_iff_le]
    rw [if_pos (Int.natCast_nonneg n.succ)]
    rw [if_pos (Int.natCast_nonneg n)]
    simp only [Int.toNat_natCast]
    change BabyBearField.ofNat n.succ * a = BabyBearField.ofNat n * a + a
    apply toZMod_injective
    rw [toZMod_mul, toZMod_add, toZMod_mul, toZMod_ofNat, toZMod_ofNat]
    have h : ((n.succ : ℕ) : ZMod ORDER_NAT) = (n : ZMod ORDER_NAT) + 1 := by
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [h, add_mul, one_mul]
  zsmul_neg' := fun n a => by
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
    rw [if_pos (Int.natCast_nonneg (n + 1))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]
    rfl
  sub := BabyBearField.sub
  sub_eq_add_neg := fun a b => by
    apply toZMod_injective
    have hneg : toZMod b.neg = -toZMod b := toZMod_neg b
    simp only [toZMod_sub, toZMod_add]
    rw [hneg]
    ring
  mul_assoc := fun a b c => by
    apply toZMod_injective
    simp only [toZMod_mul]
    ring
  one_mul := fun a => by
    show BabyBearField.mul BabyBearField.one a = a
    simp only [BabyBearField.mul, BabyBearField.one, BabyBearField.reduceMul]
    have h1 : (1 : UInt32).toNat = 1 := rfl
    simp only [h1, Nat.one_mul]
    have ha : a.value.toNat < ORDER_NAT := babybear_canonical a
    have hmod : a.value.toNat % ORDER.toNat = a.value.toNat := Nat.mod_eq_of_lt ha
    have hmod_lt_2_32 : a.value.toNat % ORDER.toNat < 2 ^ 32 := by
      have hord_lt : ORDER.toNat < 2 ^ 32 := by native_decide
      have hord_pos : 0 < ORDER.toNat := by rw [order_toNat_eq]; exact order_nat_pos
      have hml := Nat.mod_lt a.value.toNat hord_pos
      omega
    ext
    simp only [Nat.toUInt32, UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hmod_lt_2_32, hmod]
  mul_one := fun a => by
    show BabyBearField.mul a BabyBearField.one = a
    simp only [BabyBearField.mul, BabyBearField.one, BabyBearField.reduceMul]
    have h1 : (1 : UInt32).toNat = 1 := rfl
    simp only [h1, Nat.mul_one]
    have ha : a.value.toNat < ORDER_NAT := babybear_canonical a
    have hmod : a.value.toNat % ORDER.toNat = a.value.toNat := Nat.mod_eq_of_lt ha
    have hmod_lt_2_32 : a.value.toNat % ORDER.toNat < 2 ^ 32 := by
      have hord_lt : ORDER.toNat < 2 ^ 32 := by native_decide
      have hord_pos : 0 < ORDER.toNat := by rw [order_toNat_eq]; exact order_nat_pos
      have hml := Nat.mod_lt a.value.toNat hord_pos
      omega
    ext
    simp only [Nat.toUInt32, UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hmod_lt_2_32, hmod]
  mul_comm := fun a b => by
    show BabyBearField.mul a b = BabyBearField.mul b a
    simp only [BabyBearField.mul, BabyBearField.reduceMul]
    have hcomm : a.value.toNat * b.value.toNat = b.value.toNat * a.value.toNat := Nat.mul_comm _ _
    simp only [hcomm]
  left_distrib := fun a b c => by
    apply toZMod_injective
    simp only [toZMod_mul, toZMod_add]
    ring
  right_distrib := fun a b c => by
    apply toZMod_injective
    simp only [toZMod_mul, toZMod_add]
    ring
  zero_mul := fun a => by
    apply toZMod_injective
    rw [toZMod_mul, toZMod_zero, zero_mul]
  mul_zero := fun a => by
    apply toZMod_injective
    rw [toZMod_mul, toZMod_zero, mul_zero]
  natCast := fun n => BabyBearField.ofNat n
  natCast_zero := by rfl
  natCast_succ := fun n => by
    show BabyBearField.ofNat (n + 1) = BabyBearField.ofNat n + 1
    apply toZMod_injective
    rw [toZMod_ofNat, toZMod_add, toZMod_ofNat, toZMod_one]
    push_cast
    ring
  intCast := fun n => if n ≥ 0 then BabyBearField.ofNat n.toNat
                      else BabyBearField.neg (BabyBearField.ofNat (-n).toNat)
  intCast_negSucc := fun n => by
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]
    rfl
  intCast_ofNat := fun n => by
    simp only [ge_iff_le, Int.ofNat_nonneg, ↓reduceIte, Int.toNat_natCast]
    rfl
  npow := fun n a => BabyBearField.pow a n
  npow_zero := fun a => by
    show BabyBearField.pow a 0 = 1
    simp only [BabyBearField.pow]
    rfl
  npow_succ := fun n a => by
    apply toZMod_injective
    rw [toZMod_mul, toZMod_pow, toZMod_pow]
    rw [pow_succ]

/-- Field instance for BabyBearField via ZMod isomorphism. -/
instance : Field BabyBearField where
  exists_pair_ne := ⟨0, 1, by decide⟩
  inv := BabyBearField.inv
  mul_inv_cancel := fun a ha => by
    show a * a.inv = 1
    apply toZMod_injective
    have hmul : toZMod (a * a.inv) = toZMod a * toZMod a.inv :=
      toZMod_mul a a.inv
    have hinv : toZMod a.inv = (toZMod a)⁻¹ := toZMod_inv a
    rw [hmul, hinv, toZMod_one]
    have hne : toZMod a ≠ 0 := by
      intro heq
      apply ha
      apply toZMod_injective
      rw [heq, toZMod_zero]
    exact mul_inv_cancel₀ hne
  inv_zero := by
    show BabyBearField.inv ⟨0, by native_decide⟩ = ⟨0, by native_decide⟩
    simp only [BabyBearField.inv, beq_self_eq_true, ↓reduceIte, BabyBearField.zero]
  div := BabyBearField.div
  div_eq_mul_inv := fun a b => by rfl
  zpow := fun n a => if n ≥ 0
                     then BabyBearField.pow a n.toNat
                     else BabyBearField.inv (BabyBearField.pow a (-n).toNat)
  zpow_zero' := fun a => by
    simp only [ge_iff_le, le_refl, ↓reduceIte, Int.toNat_zero, BabyBearField.pow]
    rfl
  zpow_succ' := fun n a => by
    simp only [ge_iff_le]
    rw [if_pos (Int.natCast_nonneg n.succ)]
    rw [if_pos (Int.natCast_nonneg n)]
    simp only [Int.toNat_natCast]
    apply toZMod_injective
    rw [toZMod_mul, toZMod_pow, toZMod_pow]
    rw [pow_succ', mul_comm]
  zpow_neg' := fun n a => by
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
    rw [if_pos (Int.natCast_nonneg (n + 1))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]
    rfl
  nnratCast := fun q => (q.num : BabyBearField) / (q.den : BabyBearField)
  nnratCast_def := fun q => by rfl
  nnqsmul := fun q a => ((q.num : BabyBearField) / (q.den : BabyBearField)) * a
  nnqsmul_def := fun q a => by rfl
  ratCast := fun q => (q.num : BabyBearField) / (q.den : BabyBearField)
  ratCast_def := fun q => by rfl
  qsmul := fun q a => ((q.num : BabyBearField) / (q.den : BabyBearField)) * a
  qsmul_def := fun q a => by rfl

end AmoLean.Field.BabyBear

/-! ## Part 11: Quick Tests -/

open AmoLean.Field.BabyBear in
open BabyBearField in
#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     BABYBEAR FIELD TESTS (Lean)                             ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println s!"ORDER = {ORDER}"
  IO.println ""

  -- Test 1: Zero + Zero
  let r1 := add zero zero
  IO.println s!"0 + 0 = {r1} (expected: 0)"

  -- Test 2: One + One
  let r2 := add one one
  IO.println s!"1 + 1 = {r2} (expected: 2)"

  -- Test 3: (p-1) + 1 = 0
  let pMinus1 : BabyBearField := ⟨ORDER - 1, by native_decide⟩
  let r3 := add pMinus1 one
  IO.println s!"(p-1) + 1 = {r3} (expected: 0)"

  -- Test 4: (p-1) + (p-1) = p-2
  let r4 := add pMinus1 pMinus1
  let expected4 := ORDER - 2
  IO.println s!"(p-1) + (p-1) = {r4} (expected: {expected4})"

  -- Test 5: (p-1) * (p-1) = 1
  let r5 := mul pMinus1 pMinus1
  IO.println s!"(p-1) * (p-1) = {r5} (expected: 1)"

  -- Test 6: Inverse verification
  let x : BabyBearField := ofNat 12345
  let xInv := inv x
  let r6 := mul x xInv
  IO.println s!"x * x^(-1) = {r6} (expected: 1)"

  -- Test 7: Generator g=31, g^(p-1) = 1
  let g : BabyBearField := ⟨31, by native_decide⟩
  let r7 := pow g (ORDER.toNat - 1)
  IO.println s!"31^(p-1) = {r7} (expected: 1)"

  -- Test 8: g^((p-1)/2) should be p-1 (= -1)
  let r8 := pow g ((ORDER.toNat - 1) / 2)
  IO.println s!"31^((p-1)/2) = {r8} (expected: {ORDER - 1} = -1)"

  IO.println ""
  IO.println "Tests completed."
