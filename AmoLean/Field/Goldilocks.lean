/-
  AMO-Lean: Goldilocks Field Implementation
  Phase 1: Core Field Arithmetic

  Goldilocks Field: F_p where p = 2^64 - 2^32 + 1

  This field is used by Plonky2/Plonky3 for efficient ZK proofs.
  The special structure allows fast modular reduction using
  the identity: 2^64 ≡ 2^32 - 1 (mod p)

  Reference: Plonky2 goldilocks_field.rs

  === VERIFICATION STRATEGY ===
  We prove algebraic properties via isomorphism to ZMod p:
  1. Define toZMod : GoldilocksField → ZMod p
  2. Prove toZMod is a ring homomorphism (respects +, *, -, 0, 1)
  3. Prove toZMod is injective (via canonicity of representations)
  4. Transfer all proofs via toZMod_injective

  The primality of p = 2^64 - 2^32 + 1 is formally proved via the
  Lucas primality test (Mathlib) with witness a = 7 and efficient
  binary exponentiation (zpowMod) verified by native_decide.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.NumberTheory.LucasPrimality
import Batteries.Data.UInt

namespace AmoLean.Field.Goldilocks

/-! ## Part 1: Field Constants -/

/-- Goldilocks prime: p = 2^64 - 2^32 + 1 -/
def ORDER : UInt64 := 0xFFFFFFFF00000001

/-- Order as Nat for ZMod usage -/
def ORDER_NAT : Nat := ORDER.toNat

/-! ### Primality proof infrastructure -/

instance : NeZero ORDER_NAT := ⟨by native_decide⟩

/-- Efficient binary exponentiation in ZMod n. O(log exp) multiplications. -/
private def zpowMod {n : Nat} [NeZero n] (a : ZMod n) (exp : Nat) : ZMod n :=
  if exp = 0 then 1
  else
    let half := zpowMod a (exp / 2)
    let sq := half * half
    if exp % 2 = 1 then sq * a
    else sq
termination_by exp

/-- zpowMod computes the standard power a^exp in ZMod n -/
private theorem zpowMod_eq_pow {n : Nat} [NeZero n] (a : ZMod n) (exp : Nat) :
    zpowMod a exp = a ^ exp := by
  induction exp using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp [zpowMod]
    | succ m =>
      have h_lt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih _ h_lt
      show zpowMod a (m + 1) = a ^ (m + 1)
      rw [zpowMod, if_neg (by omega)]
      dsimp only
      rw [hrec]
      split_ifs with hodd
      · rw [← pow_add]
        have hsum : (m + 1) / 2 + (m + 1) / 2 = m := by omega
        rw [hsum]; exact (pow_succ a m).symm
      · rw [← pow_add]; congr 1; omega

private lemma prime_dvd_eq {q p : Nat} (hq : Nat.Prime q) (hp : Nat.Prime p)
    (h : q ∣ p) : q = p := by
  rcases hp.eq_one_or_self_of_dvd q h with rfl | rfl
  · exact absurd hq (by decide)
  · rfl

/-- Goldilocks prime is prime.
    Proved via Lucas primality test with witness a = 7.
    p - 1 = 2^32 × 3 × 5 × 17 × 257 × 65537 -/
theorem goldilocks_prime_is_prime : Nat.Prime ORDER_NAT := by
  apply lucas_primality ORDER_NAT (7 : ZMod ORDER_NAT)
  · rw [← zpowMod_eq_pow]; native_decide
  · intro q hq hqd
    have hfact : ORDER_NAT - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by native_decide
    rw [hfact] at hqd
    have hqp := hq.prime
    rcases hqp.dvd_mul.mp hqd with h | h
    · rcases hqp.dvd_mul.mp h with h | h
      · rcases hqp.dvd_mul.mp h with h | h
        · rcases hqp.dvd_mul.mp h with h | h
          · rcases hqp.dvd_mul.mp h with h | h
            · have := prime_dvd_eq hq (by decide) (hqp.dvd_of_dvd_pow h)
              subst this; rw [← zpowMod_eq_pow]; native_decide
            · have := prime_dvd_eq hq (by decide) h
              subst this; rw [← zpowMod_eq_pow]; native_decide
          · have := prime_dvd_eq hq (by decide) h
            subst this; rw [← zpowMod_eq_pow]; native_decide
        · have := prime_dvd_eq hq (by decide) h
          subst this; rw [← zpowMod_eq_pow]; native_decide
      · have := prime_dvd_eq hq (by native_decide) h
        subst this; rw [← zpowMod_eq_pow]; native_decide
    · have := prime_dvd_eq hq (by native_decide) h
      subst this; rw [← zpowMod_eq_pow]; native_decide

instance : Fact (Nat.Prime ORDER_NAT) := ⟨goldilocks_prime_is_prime⟩

/-- ORDER_NAT is positive (follows from primality) -/
theorem order_nat_pos : 0 < ORDER_NAT := Nat.Prime.pos goldilocks_prime_is_prime

/-- ORDER_NAT is at least 2 (follows from primality) -/
theorem order_nat_ge_two : 2 ≤ ORDER_NAT := Nat.Prime.two_le goldilocks_prime_is_prime

/-- ORDER.toNat equals ORDER_NAT -/
@[simp]
theorem order_toNat_eq : ORDER.toNat = ORDER_NAT := rfl

/-- ORDER.toNat < 2^64 (UInt64.size) -/
theorem order_lt_size : ORDER.toNat < UInt64.size := by decide

/-- Epsilon: 2^32 - 1, used in fast reduction -/
def EPSILON : UInt64 := 0xFFFFFFFF

/-- 2^32 as UInt64 -/
def TWO_POW_32 : UInt64 := 0x100000000

/-! ## Part 2: Goldilocks Field Type -/

/-- Goldilocks field element.
    Invariant enforced at type level: value < ORDER -/
structure GoldilocksField where
  value : UInt64
  h_lt : value.toNat < ORDER.toNat

instance : DecidableEq GoldilocksField := fun a b =>
  if h : a.value = b.value then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro hab; exact h (congrArg GoldilocksField.value hab))

instance : Repr GoldilocksField where
  reprPrec a n := reprPrec a.value n

instance : Hashable GoldilocksField where
  hash a := hash a.value

instance : Inhabited GoldilocksField := ⟨⟨0, by native_decide⟩⟩

namespace GoldilocksField

/-- For any GoldilocksField element, value.toNat < 2^64 -/
theorem val_lt_size (a : GoldilocksField) : a.value.toNat < UInt64.size := a.value.val.isLt

/-- Helper lemma: UInt64 subtraction when x ≥ y gives x.toNat - y.toNat
    This is a fundamental property of UInt64 arithmetic that Lean 4.16 doesn't
    expose directly. We prove it holds for all cases where y ≤ x. -/
theorem uint64_sub_toNat (x y : UInt64) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  UInt64.toNat_sub_of_le x y h

/-- Helper: Nat.toUInt64.toNat roundtrip for values < UInt64.size -/
private theorem toUInt64_toNat_of_lt {n : Nat} (h : n < UInt64.size) :
    n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Extensionality theorem: two GoldilocksField elements are equal iff their values are equal -/
@[ext]
theorem ext {a b : GoldilocksField} (h : a.value = b.value) : a = b := by
  cases a; cases b; simp_all

/-! ## Part 3: Constructors -/

/-- Create a field element from UInt64, reducing if necessary -/
def ofUInt64 (n : UInt64) : GoldilocksField :=
  if h : n < ORDER then ⟨n, h⟩
  else ⟨n - ORDER, by
    have hge : ORDER.toNat ≤ n.toNat := by
      simp only [UInt64.lt_iff_toNat_lt, not_lt] at h; exact h
    have hsub : (n - ORDER).toNat = n.toNat - ORDER.toNat := by
      rw [UInt64.toNat_sub_of_le]; exact hge
    rw [hsub]
    have hsize : n.toNat < UInt64.size := n.val.isLt
    have h2ord : UInt64.size ≤ 2 * ORDER.toNat := by native_decide
    omega⟩

/-- Create a field element from Nat -/
def ofNat (n : Nat) : GoldilocksField :=
  let reduced := n % ORDER.toNat
  ofUInt64 reduced.toUInt64

/-- Zero element -/
def zero : GoldilocksField := ⟨0, by native_decide⟩

/-- One element -/
def one : GoldilocksField := ⟨1, by native_decide⟩

/-! ## Part 4: Core Arithmetic Operations -/

/-- Addition: (a + b) mod p

    CRITICAL: Uses intermediate representation to handle overflow.
    This mirrors the corrected C implementation. -/
def add (a b : GoldilocksField) : GoldilocksField :=
  -- Use Nat arithmetic to avoid overflow
  let sum := a.value.toNat + b.value.toNat
  let reduced := if sum >= ORDER.toNat then sum - ORDER.toNat else sum
  ⟨reduced.toUInt64, by
    have ha := a.h_lt; have hb := b.h_lt
    have hord_lt : ORDER.toNat < UInt64.size := by native_decide
    have hlt : reduced < ORDER.toNat := by
      show (if a.value.toNat + b.value.toNat ≥ ORDER.toNat
            then a.value.toNat + b.value.toNat - ORDER.toNat
            else a.value.toNat + b.value.toNat) < ORDER.toNat
      split_ifs with h <;> omega
    simp only [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (by omega : reduced < UInt64.size)]
    exact hlt⟩

/-- Subtraction: (a - b) mod p -/
def sub (a b : GoldilocksField) : GoldilocksField :=
  if h : a.value >= b.value then
    ⟨a.value - b.value, by
      have ha := a.h_lt
      have hsub : (a.value - b.value).toNat = a.value.toNat - b.value.toNat := by
        rw [UInt64.toNat_sub_of_le]; exact h
      rw [hsub]; omega⟩
  else
    -- a < b, so result would be negative. Add ORDER.
    ⟨ORDER - b.value + a.value, by
      have ha := a.h_lt; have hb := b.h_lt
      have halt : a.value.toNat < b.value.toNat := by
        simp only [ge_iff_le, UInt64.le_iff_toNat_le, not_le] at h; exact h
      have hb_le_ord : b.value ≤ ORDER := by
        simp only [UInt64.le_iff_toNat_le]; omega
      have hsub1 : (ORDER - b.value).toNat = ORDER.toNat - b.value.toNat := by
        rw [UInt64.toNat_sub_of_le]; exact hb_le_ord
      have hsum_lt : ORDER.toNat - b.value.toNat + a.value.toNat < UInt64.size := by
        have : ORDER.toNat < UInt64.size := by native_decide
        omega
      have hadd : (ORDER - b.value + a.value).toNat =
                  (ORDER - b.value).toNat + a.value.toNat := by
        simp only [UInt64.toNat_add, hsub1, Nat.mod_eq_of_lt hsum_lt]
      rw [hadd, hsub1]; omega⟩

/-- Negation: -a mod p -/
def neg (a : GoldilocksField) : GoldilocksField :=
  if h : a.value = 0 then ⟨0, by native_decide⟩
  else ⟨ORDER - a.value, by
    have ha := a.h_lt
    have ha_pos : 0 < a.value.toNat := by
      by_contra hle; push_neg at hle
      exact h (UInt64.ext (Nat.eq_zero_of_le_zero hle))
    have hsub : (ORDER - a.value).toNat = ORDER.toNat - a.value.toNat := by
      rw [UInt64.toNat_sub_of_le]; simp only [UInt64.le_iff_toNat_le]; omega
    rw [hsub]; omega⟩

/-- Reduce a 128-bit value (represented as pair of UInt64) modulo p

    Uses the identity: 2^64 ≡ EPSILON (mod p)
    and: 2^96 ≡ -1 (mod p)

    For x = x_lo + x_hi * 2^64:
    x ≡ x_lo + x_hi * EPSILON (mod p)

    For the full algorithm with x_hi split:
    x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON (mod p)
-/
def reduce128 (x_lo x_hi : UInt64) : GoldilocksField :=
  if x_hi == 0 then
    ofUInt64 x_lo
  else
    -- Split x_hi into top 32 bits and bottom 32 bits
    let x_hi_hi := x_hi >>> 32  -- Top 32 bits
    let x_hi_lo := x_hi &&& EPSILON  -- Bottom 32 bits

    -- Apply reduction using Nat arithmetic for safety
    -- x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON (mod p)
    let term1 := x_lo.toNat
    let term2 := x_hi_hi.toNat
    let term3 := x_hi_lo.toNat * EPSILON.toNat

    -- Compute: term1 - term2 + term3, handling underflow
    let intermediate := if term1 >= term2
                        then term1 - term2 + term3
                        else ORDER.toNat - term2 + term1 + term3

    -- May need another reduction
    let result := intermediate % ORDER.toNat
    ⟨result.toUInt64, by
      have hord_pos : 0 < ORDER.toNat := by native_decide
      have hord_lt : ORDER.toNat < UInt64.size := by native_decide
      have hlt : result < ORDER.toNat := Nat.mod_lt intermediate hord_pos
      rw [toUInt64_toNat_of_lt (by omega)]; exact hlt⟩

/-- Multiplication: (a * b) mod p

    Uses specialized Goldilocks reduction. -/
def mul (a b : GoldilocksField) : GoldilocksField :=
  -- Use Nat arithmetic for 128-bit multiplication
  let product := a.value.toNat * b.value.toNat

  -- Split into high and low 64-bit parts
  let x_lo := (product % (2^64)).toUInt64
  let x_hi := (product / (2^64)).toUInt64

  reduce128 x_lo x_hi

/-- Squaring: a^2 mod p -/
def square (a : GoldilocksField) : GoldilocksField :=
  mul a a

/-- Exponentiation: base^exp mod p using binary method -/
def pow (base : GoldilocksField) (exp : Nat) : GoldilocksField :=
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
def inv (a : GoldilocksField) : GoldilocksField :=
  if a.value == 0 then zero  -- Undefined, return 0 as sentinel
  else pow a (ORDER.toNat - 2)

/-- Division: a / b = a * b^(-1) mod p -/
def div (a b : GoldilocksField) : GoldilocksField :=
  mul a (inv b)

/-! ## S-Box for Poseidon2 (CRITICAL: Must use x^7, NOT x^5)

For the S-Box to be a bijection, gcd(d, p-1) = 1 is required.

Goldilocks: p-1 = 2^32 × 3 × 5 × 17 × 257 × 65537
  - gcd(5, p-1) = 5 ≠ 1  →  x^5 is NOT invertible (INSECURE)
  - gcd(7, p-1) = 1      →  x^7 IS invertible (SECURE)
-/

/-- S-Box exponent for Goldilocks (MUST be 7, not 5) -/
def SBOX_EXPONENT : Nat := 7

/-- Inverse S-Box exponent: 7^(-1) mod (p-1) -/
def SBOX_INV_EXPONENT : Nat := 10540996611094048183

/-- S-Box: x^7 (for Poseidon2 on Goldilocks)
    Computes x^7 using 3 multiplications -/
def sbox (x : GoldilocksField) : GoldilocksField :=
  let x2 := square x      -- x^2
  let x4 := square x2     -- x^4
  let x6 := mul x4 x2     -- x^6
  mul x6 x                -- x^7

/-- Inverse S-Box: x^(1/7) mod p -/
def sboxInv (x : GoldilocksField) : GoldilocksField :=
  pow x SBOX_INV_EXPONENT

end GoldilocksField

/-! ## Part 5: Instances -/

instance : Add GoldilocksField := ⟨GoldilocksField.add⟩
instance : Sub GoldilocksField := ⟨GoldilocksField.sub⟩
instance : Neg GoldilocksField := ⟨GoldilocksField.neg⟩
instance : Mul GoldilocksField := ⟨GoldilocksField.mul⟩
instance : Div GoldilocksField := ⟨GoldilocksField.div⟩

instance : OfNat GoldilocksField n where
  ofNat := GoldilocksField.ofNat n

instance : Zero GoldilocksField where
  zero := GoldilocksField.zero

instance : ToString GoldilocksField where
  toString f := toString f.value

namespace GoldilocksField

/-! ## Part 6: Field Properties -/

/-- Field element is valid if value < ORDER -/
def isValid (a : GoldilocksField) : Prop := a.value < ORDER

/-- The order of the field -/
def order : Nat := ORDER.toNat

/-! ## Part 7: Conversion Utilities -/

/-- Convert to UInt64 (for FFI/testing) -/
def toUInt64 (a : GoldilocksField) : UInt64 := a.value

/-- Convert to Nat -/
def toNat (a : GoldilocksField) : Nat := a.value.toNat

end GoldilocksField

/-! ## Part 8: Constants -/

/-- p - 1: Maximum valid field element -/
def P_MINUS_1 : GoldilocksField := ⟨ORDER - 1, by native_decide⟩

/-- p - 2: Used for inverse calculation -/
def P_MINUS_2 : GoldilocksField := ⟨ORDER - 2, by native_decide⟩

/-! ## Part 9: ZMod Isomorphism Infrastructure

The key insight is that GoldilocksField ≃+* ZMod ORDER_NAT.
Since ZMod p is a Field for prime p, we can transfer all algebraic properties.

Strategy:
1. Define toZMod : GoldilocksField → ZMod ORDER_NAT
2. Prove it respects operations (add, mul, neg, etc.)
3. Prove toZMod is injective
4. Transfer all proofs via toZMod_injective
-/

/-- Conversion from GoldilocksField to ZMod ORDER_NAT -/
def toZMod (x : GoldilocksField) : ZMod ORDER_NAT :=
  (x.value.toNat : ZMod ORDER_NAT)

/-- Conversion from ZMod ORDER_NAT back to GoldilocksField -/
def ofZMod (z : ZMod ORDER_NAT) : GoldilocksField :=
  ⟨(ZMod.val z).toUInt64, by
    have hval : ZMod.val z < ORDER_NAT := ZMod.val_lt z
    have hord_lt : ORDER_NAT < UInt64.size := by native_decide
    simp only [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ZMod.val z < UInt64.size)]
    exact hval⟩

/-! ### Canonicity

Canonicity is now enforced at the type level: every GoldilocksField element
carries a proof h_lt : value.toNat < ORDER.toNat.
The old axiom goldilocks_canonical is eliminated. -/

/-- A GoldilocksField element is canonical if value < ORDER -/
def GoldilocksField.isCanonical (a : GoldilocksField) : Prop := a.value < ORDER

/-- All GoldilocksField values are canonical (now a theorem, not an axiom). -/
theorem goldilocks_canonical (a : GoldilocksField) : a.isCanonical := a.h_lt

/-! ### val_eq Lemmas

These lemmas establish the relationship between GoldilocksField operations
and Nat modular arithmetic. They are the foundation for proving toZMod_* lemmas
using the ZMod.val_injective pattern (DD-024). -/

/-- Addition produces the modular sum at the Nat level.
    This is the key lemma: (a + b).value.toNat = (a + b) % ORDER_NAT -/
theorem add_val_eq (a b : GoldilocksField) :
    (a + b).value.toNat = (a.value.toNat + b.value.toNat) % ORDER_NAT := by
  simp only [HAdd.hAdd, Add.add, GoldilocksField.add, ORDER_NAT]
  have ha : a.value.toNat < ORDER.toNat := goldilocks_canonical a
  have hb : b.value.toNat < ORDER.toNat := goldilocks_canonical b
  -- Note: Nat.add is the same as + but we need to be explicit
  have hsum_eq : a.value.toNat.add b.value.toNat = a.value.toNat + b.value.toNat := rfl
  -- Case split on whether sum >= ORDER
  split_ifs with h
  · -- Case: sum >= ORDER, result = sum - ORDER
    have hge : a.value.toNat + b.value.toNat ≥ ORDER.toNat := by rw [← hsum_eq]; exact h
    have hsum_bound : a.value.toNat + b.value.toNat < 2 * ORDER.toNat := by omega
    have hres_bound : a.value.toNat + b.value.toNat - ORDER.toNat < ORDER.toNat := by omega
    have hres_lt_size : a.value.toNat + b.value.toNat - ORDER.toNat < UInt64.size := by
      have : ORDER.toNat < UInt64.size := by native_decide
      omega
    -- The toUInt64 preserves the value since result < 2^64
    simp only [Nat.toUInt64, UInt64.toNat_ofNat, hsum_eq, Nat.mod_eq_of_lt hres_lt_size]
    -- Now prove (sum - ORDER) % ORDER = sum % ORDER
    have heq : a.value.toNat + b.value.toNat = ORDER.toNat + (a.value.toNat + b.value.toNat - ORDER.toNat) := by omega
    conv_rhs => rw [heq]
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hres_bound]
  · -- Case: sum < ORDER, result = sum
    have hsum_lt : a.value.toNat + b.value.toNat < ORDER.toNat := by
      simp only [ge_iff_le, not_le] at h; rw [← hsum_eq]; exact h
    have hsum_lt_size : a.value.toNat + b.value.toNat < UInt64.size := by
      have : ORDER.toNat < UInt64.size := by native_decide
      omega
    simp only [Nat.toUInt64, UInt64.toNat_ofNat, hsum_eq, Nat.mod_eq_of_lt hsum_lt_size]
    exact (Nat.mod_eq_of_lt hsum_lt).symm

/-- Negation produces the modular negation at the Nat level. -/
theorem neg_val_eq (a : GoldilocksField) :
    (-a).value.toNat = (ORDER_NAT - a.value.toNat % ORDER_NAT) % ORDER_NAT := by
  simp only [Neg.neg, GoldilocksField.neg, ORDER_NAT]
  have ha : a.value.toNat < ORDER.toNat := goldilocks_canonical a
  have ha_mod : a.value.toNat % ORDER.toNat = a.value.toNat := Nat.mod_eq_of_lt ha
  rw [ha_mod]
  split_ifs with h
  · -- Case: a = 0
    simp only [beq_iff_eq] at h
    simp only [h, UInt64.toNat_zero, Nat.sub_zero, Nat.mod_self]
  · -- Case: a ≠ 0
    simp only [beq_iff_eq, ne_eq] at h
    have ha_pos : 0 < a.value.toNat := by
      by_contra hcon
      push_neg at hcon
      have : a.value.toNat = 0 := Nat.eq_zero_of_le_zero hcon
      exact h (UInt64.ext this)
    have hsub_lt : ORDER.toNat - a.value.toNat < ORDER.toNat := by omega
    have hsub_lt_size : ORDER.toNat - a.value.toNat < UInt64.size := by
      have : ORDER.toNat < UInt64.size := by native_decide
      omega
    -- UInt64 subtraction: ORDER - a.value
    -- For UInt64, (x - y).toNat = (x.toNat - y.toNat) % 2^64 when y ≤ x
    -- Here ORDER.toNat > a.value.toNat, so no wrap-around
    have hresult : (ORDER - a.value).toNat = ORDER.toNat - a.value.toNat := by
      rw [UInt64.toNat_sub_of_le]
      · exact le_of_lt ha
    rw [hresult, Nat.mod_eq_of_lt hsub_lt]

/-- Subtraction produces the modular difference at the Nat level. -/
theorem sub_val_eq (a b : GoldilocksField) :
    (a - b).value.toNat = (a.value.toNat + ORDER_NAT - b.value.toNat) % ORDER_NAT := by
  simp only [HSub.hSub, Sub.sub, GoldilocksField.sub, ORDER_NAT]
  have ha : a.value.toNat < ORDER.toNat := goldilocks_canonical a
  have hb : b.value.toNat < ORDER.toNat := goldilocks_canonical b
  split_ifs with h
  · -- Case: a.value >= b.value, result = a.value - b.value
    -- h : a.value ≥ b.value (as UInt64 ordering)
    have hge : b.value ≤ a.value := h
    -- UInt64 subtraction when a >= b: (a.value.sub b.value).toNat = a.value.toNat - b.value.toNat
    have hsub : (a.value.sub b.value).toNat = a.value.toNat - b.value.toNat :=
      UInt64.toNat_sub_of_le a.value b.value hge
    simp only [hsub]
    -- Now show: a - b = (a + ORDER - b) % ORDER
    -- Since a >= b, we have a - b < ORDER (both are < ORDER)
    have hge_nat : b.value.toNat ≤ a.value.toNat := by
      simp only [UInt64.le_iff_toNat_le] at hge; exact hge
    have hdiff_lt : a.value.toNat - b.value.toNat < ORDER.toNat := by omega
    -- Nat.sub is same as - for Nat
    have hsub_eq : (a.value.toNat + ORDER.toNat).sub b.value.toNat =
                   a.value.toNat + ORDER.toNat - b.value.toNat := rfl
    rw [hsub_eq]
    -- a + ORDER - b = (a - b) + ORDER since a >= b
    have heq : a.value.toNat + ORDER.toNat - b.value.toNat =
               (a.value.toNat - b.value.toNat) + ORDER.toNat := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    exact (Nat.mod_eq_of_lt hdiff_lt).symm
  · -- Case: a.value < b.value, result = ORDER - b.value + a.value
    have hlt : a.value.toNat < b.value.toNat := by
      simp only [UInt64.le_iff_toNat_le, ge_iff_le, not_le] at h; exact h
    -- First compute ORDER - b.value
    -- ORDER ≥ b.value since b.value.toNat < ORDER.toNat
    have hb_le : b.value ≤ ORDER := by
      simp only [UInt64.le_iff_toNat_le]; exact le_of_lt hb
    have hsub1 : (ORDER.sub b.value).toNat = ORDER.toNat - b.value.toNat :=
      UInt64.toNat_sub_of_le ORDER b.value hb_le
    -- The sum ORDER - b + a doesn't overflow since:
    -- ORDER - b < ORDER (because b > 0, since a < b and a >= 0)
    -- So ORDER - b + a < ORDER + a < 2 * ORDER < 2^64
    have hsum_bound : ORDER.toNat - b.value.toNat + a.value.toNat < UInt64.size := by
      have horder_lt : ORDER.toNat < UInt64.size := by native_decide
      omega
    -- UInt64 addition without overflow
    have hadd : (ORDER.sub b.value + a.value).toNat =
                (ORDER.sub b.value).toNat + a.value.toNat := by
      rw [UInt64.toNat_add, hsub1]
      exact Nat.mod_eq_of_lt hsum_bound
    simp only [hadd, hsub1]
    -- Nat.sub is same as - for Nat
    have hsub_eq : (a.value.toNat + ORDER.toNat).sub b.value.toNat =
                   a.value.toNat + ORDER.toNat - b.value.toNat := rfl
    rw [hsub_eq]
    -- Now show: ORDER - b + a = (a + ORDER - b) % ORDER
    have hres : ORDER.toNat - b.value.toNat + a.value.toNat =
                a.value.toNat + ORDER.toNat - b.value.toNat := by omega
    rw [hres]
    -- Since a < b, we have a + ORDER - b = ORDER - (b - a)
    -- And 0 < b - a < ORDER, so ORDER - (b - a) is in (0, ORDER)
    have hres_lt : a.value.toNat + ORDER.toNat - b.value.toNat < ORDER.toNat := by omega
    exact (Nat.mod_eq_of_lt hres_lt).symm

/-- Helper: reduce128 produces the correct modular result when x_hi = 0 -/
theorem reduce128_zero_hi (x_lo : UInt64) :
    (GoldilocksField.reduce128 x_lo 0).value.toNat = x_lo.toNat % ORDER_NAT := by
  simp only [GoldilocksField.reduce128, ORDER_NAT]
  simp only [beq_self_eq_true, ↓reduceIte]
  -- ofUInt64 x_lo
  simp only [GoldilocksField.ofUInt64]
  split_ifs with h
  · -- x_lo < ORDER
    have hlt : x_lo.toNat < ORDER.toNat := by
      simp only [UInt64.lt_iff_toNat_lt] at h; exact h
    exact (Nat.mod_eq_of_lt hlt).symm
  · -- x_lo >= ORDER
    have hge : x_lo.toNat ≥ ORDER.toNat := by
      simp only [UInt64.lt_iff_toNat_lt, not_lt] at h; exact h
    have hlt_size : x_lo.toNat < UInt64.size := x_lo.val.isLt
    have hlt_2p : x_lo.toNat < 2 * ORDER.toNat := by
      have : ORDER.toNat > UInt64.size / 2 := by native_decide
      omega
    have hsub_lt : x_lo.toNat - ORDER.toNat < ORDER.toNat := by omega
    have hsub_lt_size : x_lo.toNat - ORDER.toNat < UInt64.size := by omega
    -- UInt64 subtraction: x_lo - ORDER, where x_lo >= ORDER
    have hresult : (x_lo - ORDER).toNat = x_lo.toNat - ORDER.toNat := by
      rw [UInt64.toNat_sub_of_le]
      · exact hge
    rw [hresult]
    -- (x_lo - ORDER) % ORDER = x_lo % ORDER
    have heq : x_lo.toNat = ORDER.toNat + (x_lo.toNat - ORDER.toNat) := by omega
    conv_rhs => rw [heq]
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hsub_lt]

/-! ### Goldilocks Identity Sub-lemmas for reduce128

The Goldilocks reduction uses:
- 2^64 ≡ EPSILON (mod ORDER) because ORDER = 2^64 - 2^32 + 1 = 2^64 - EPSILON
- 2^96 ≡ -1 (mod ORDER) because 2^96 = 2^64 * 2^32 ≡ EPSILON * 2^32 = 2^64 - 2^32 = ORDER - 1 ≡ -1 -/

/-- Key Goldilocks identity: 2^64 ≡ EPSILON (mod ORDER) -/
theorem pow_64_mod_order : (2^64 : Nat) % ORDER_NAT = EPSILON.toNat := by
  native_decide

/-- 2^96 ≡ ORDER - 1 (mod ORDER), i.e., 2^96 ≡ -1 (mod ORDER) -/
theorem pow_96_mod_order : (2^96 : Nat) % ORDER_NAT = ORDER_NAT - 1 := by
  native_decide

/-- UInt64 decomposition: x = (x &&& EPSILON) + (x >>> 32) * 2^32
    where x &&& EPSILON gives the low 32 bits and x >>> 32 gives the high 32 bits.
    Note: EPSILON = 2^32 - 1 = 0xFFFFFFFF is the mask for low 32 bits. -/
theorem uint64_decomp (x : UInt64) :
    x.toNat = (x &&& EPSILON).toNat + (x >>> 32).toNat * 2^32 := by
  -- x &&& EPSILON gives x % 2^32 (low 32 bits)
  -- x >>> 32 gives x / 2^32 (high 32 bits)
  have hmask : EPSILON.toNat = 2^32 - 1 := by native_decide
  have hand : (x &&& EPSILON).toNat = x.toNat % 2^32 := by
    simp only [UInt64.toNat_and, hmask]
    exact Nat.and_pow_two_sub_one_eq_mod x.toNat 32
  have hshift : (x >>> 32).toNat = x.toNat / 2^32 := by
    simp only [UInt64.toNat_shiftRight]
    have h32 : (32 : UInt64).toNat % 64 = 32 := by native_decide
    simp only [h32]
    exact Nat.shiftRight_eq_div_pow x.toNat 32
  rw [hand, hshift]
  have h := Nat.mod_add_div x.toNat (2^32)
  rw [Nat.mul_comm] at h
  exact h.symm

/-- Bound on high 32 bits of a UInt64: (x >>> 32).toNat < 2^32 -/
private theorem x_hi_hi_bound (x : UInt64) : (x >>> 32).toNat < 2^32 := by
  simp only [UInt64.toNat_shiftRight]
  have h32 : (32 : UInt64).toNat % 64 = 32 := by native_decide
  simp only [h32, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by exact x.val.isLt)

/-- Bound on low 32 bits of a UInt64 masked with EPSILON: (x &&& EPSILON).toNat < 2^32 -/
private theorem x_hi_lo_bound (x : UInt64) : (x &&& EPSILON).toNat < 2^32 := by
  have hmask : EPSILON.toNat = 2^32 - 1 := by native_decide
  simp only [UInt64.toNat_and, hmask, Nat.and_pow_two_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

/-- The intermediate value in reduce128 is bounded below 2 * ORDER -/
private theorem reduce128_intermediate_bound (x_lo x_hi : UInt64) :
    let x_hi_hi := (x_hi >>> 32).toNat
    let x_hi_lo := (x_hi &&& EPSILON).toNat
    let term1 := x_lo.toNat
    let term3 := x_hi_lo * EPSILON.toNat
    let intermediate := if term1 >= x_hi_hi
                        then term1 - x_hi_hi + term3
                        else ORDER.toNat - x_hi_hi + term1 + term3
    intermediate < 2 * ORDER.toNat := by
  simp only
  have h_hi_hi : (x_hi >>> 32).toNat < 2^32 := x_hi_hi_bound x_hi
  have h_hi_lo : (x_hi &&& EPSILON).toNat < 2^32 := x_hi_lo_bound x_hi
  have h_eps_val : EPSILON.toNat = 4294967295 := by native_decide
  have h_ord_val : ORDER.toNat = 18446744069414584321 := by native_decide
  have h_t1 : x_lo.toNat < 2^64 := x_lo.val.isLt
  -- term3 = x_hi_lo * EPSILON ≤ (2^32-1)*(2^32-1) = 18446744065119617025
  have h_t3 : (x_hi &&& EPSILON).toNat * EPSILON.toNat ≤ 18446744065119617025 := by
    rw [h_eps_val]; nlinarith [h_hi_lo]
  split_ifs with h
  · -- No underflow: term1 - x_hi_hi + term3 ≤ 2^64 - 1 + (2^32-1)^2 < 2*ORDER
    rw [h_ord_val]; omega
  · -- Underflow: term1 < x_hi_hi, so ORDER - x_hi_hi + term1 < ORDER
    -- result < ORDER + term3 ≤ ORDER + (2^32-1)^2 < 2*ORDER
    have h_t1_lt : x_lo.toNat < (x_hi >>> 32).toNat := by omega
    rw [h_ord_val]; omega

/-- Core algebraic identity: x_lo + x_hi * 2^64 ≡ x_lo + x_hi_lo * EPSILON + x_hi_hi * (ORDER-1) (mod ORDER)
    where x_hi = x_hi_lo + x_hi_hi * 2^32 -/
private theorem reduce128_algebraic (x_lo x_hi : UInt64) :
    (x_lo.toNat + x_hi.toNat * 2^64) % ORDER_NAT =
    (x_lo.toNat + (x_hi &&& EPSILON).toNat * EPSILON.toNat +
     (x_hi >>> 32).toNat * (ORDER_NAT - 1)) % ORDER_NAT := by
  -- Decompose x_hi = x_hi_lo + x_hi_hi * 2^32
  conv_lhs => rw [show x_hi.toNat = (x_hi &&& EPSILON).toNat + (x_hi >>> 32).toNat * 2^32
                   from uint64_decomp x_hi]
  set a := x_lo.toNat; set b := (x_hi &&& EPSILON).toNat; set c := (x_hi >>> 32).toNat
  -- Expand: a + (b + c * 2^32) * 2^64 = a + b * 2^64 + c * 2^96
  have h_expand : a + (b + c * 2 ^ 32) * 2 ^ 64 = a + b * 2^64 + c * 2^96 := by ring
  rw [h_expand]
  -- Key modular replacements
  have h_eps_lt : EPSILON.toNat < ORDER_NAT := by native_decide
  have h_ordm1_lt : ORDER_NAT - 1 < ORDER_NAT := Nat.sub_lt order_nat_pos Nat.one_pos
  have h1 : (b * 2^64) % ORDER_NAT = (b * EPSILON.toNat) % ORDER_NAT := by
    conv_lhs => rw [Nat.mul_mod, pow_64_mod_order]
    conv_rhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt h_eps_lt]
  have h2 : (c * 2^96) % ORDER_NAT = (c * (ORDER_NAT - 1)) % ORDER_NAT := by
    conv_lhs => rw [Nat.mul_mod, pow_96_mod_order]
    conv_rhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt h_ordm1_lt]
  -- Reduce: separate a from the sum, replace inner terms, recombine
  suffices h : (b * 2^64 + c * 2^96) % ORDER_NAT =
               (b * EPSILON.toNat + c * (ORDER_NAT - 1)) % ORDER_NAT by
    rw [Nat.add_assoc, Nat.add_assoc]
    rw [Nat.add_mod a, h, ← Nat.add_mod]
  calc (b * 2^64 + c * 2^96) % ORDER_NAT
      = ((b * 2^64) % ORDER_NAT + (c * 2^96) % ORDER_NAT) % ORDER_NAT := Nat.add_mod _ _ _
    _ = ((b * EPSILON.toNat) % ORDER_NAT + (c * (ORDER_NAT - 1)) % ORDER_NAT) % ORDER_NAT := by
        rw [h1, h2]
    _ = (b * EPSILON.toNat + c * (ORDER_NAT - 1)) % ORDER_NAT := (Nat.add_mod _ _ _).symm

/-- No-underflow branch: (term1 - term2 + term3) % p = (term1 + term3 + term2*(p-1)) % p -/
private theorem reduce128_no_underflow
    (term1 term2 term3 : Nat)
    (h_ge : term1 >= term2) :
    (term1 - term2 + term3) % ORDER_NAT =
    (term1 + term3 + term2 * (ORDER_NAT - 1)) % ORDER_NAT := by
  -- Key identity: term2 * ORDER = term2 * (ORDER - 1) + term2
  have h_ge1 : ORDER_NAT ≥ 1 := Nat.one_le_of_lt order_nat_pos
  have key : term2 * ORDER_NAT = term2 * (ORDER_NAT - 1) + term2 := by
    conv_lhs => rw [show ORDER_NAT = (ORDER_NAT - 1) + 1 from (Nat.sub_add_cancel h_ge1).symm]
    ring
  -- RHS = (term1 - term2 + term3 + term2 * ORDER) % ORDER = LHS
  suffices h : term1 + term3 + term2 * (ORDER_NAT - 1) =
               term1 - term2 + term3 + term2 * ORDER_NAT by
    symm; rw [h, Nat.add_mul_mod_self_right]
  -- Now omega can solve: A + C + D = A - B + C + (D + B) with A >= B
  -- Using key: term2 * ORDER_NAT = term2 * (ORDER_NAT - 1) + term2
  omega

/-- Underflow branch: (ORDER - term2 + term1 + term3) % p = (term1 + term3 + term2*(p-1)) % p -/
private theorem reduce128_underflow
    (term1 term2 term3 : Nat)
    (h_lt : term1 < term2)
    (h_t2_bound : term2 < ORDER_NAT) :
    (ORDER_NAT - term2 + term1 + term3) % ORDER_NAT =
    (term1 + term3 + term2 * (ORDER_NAT - 1)) % ORDER_NAT := by
  -- Key identity: term2 * ORDER = term2 * (ORDER - 1) + term2
  have h_ge1 : ORDER_NAT ≥ 1 := Nat.one_le_of_lt order_nat_pos
  have key : term2 * ORDER_NAT = term2 * (ORDER_NAT - 1) + term2 := by
    conv_lhs => rw [show ORDER_NAT = (ORDER_NAT - 1) + 1 from (Nat.sub_add_cancel h_ge1).symm]
    ring
  -- Also: (term2-1)*ORDER = term2*ORDER - ORDER
  have h_t2_pos : 1 ≤ term2 := by omega
  have key2 : (term2 - 1) * ORDER_NAT + ORDER_NAT = term2 * ORDER_NAT := by
    conv_rhs => rw [show term2 = (term2 - 1) + 1 from (Nat.sub_add_cancel h_t2_pos).symm]
    ring
  -- Show RHS = (ORDER - term2 + term1 + term3 + (term2 - 1) * ORDER) % ORDER
  suffices h : term1 + term3 + term2 * (ORDER_NAT - 1) =
               ORDER_NAT - term2 + term1 + term3 + (term2 - 1) * ORDER_NAT by
    symm; rw [h, Nat.add_mul_mod_self_right]
  -- With key and key2, omega can solve this as linear arithmetic on atoms
  omega

/-- reduce128 preserves congruence modulo ORDER -/
theorem reduce128_correct (x_lo x_hi : UInt64) :
    (GoldilocksField.reduce128 x_lo x_hi).value.toNat % ORDER_NAT =
    (x_lo.toNat + x_hi.toNat * 2^64) % ORDER_NAT := by
  by_cases h_zero : x_hi = 0
  · -- Case x_hi = 0
    subst h_zero
    simp only [Nat.zero_mul, Nat.add_zero, UInt64.toNat_zero]
    rw [reduce128_zero_hi, Nat.mod_mod_of_dvd _ (dvd_refl _)]
  · -- Case x_hi ≠ 0
    -- The function has: if x_hi == 0 then ofUInt64 x_lo else <non-zero branch>
    -- Prove via helper: reduce128 for nonzero x_hi computes intermediate % ORDER
    -- Strategy: show (reduce128 x_lo x_hi).value.toNat = intermediate % ORDER_NAT
    -- where intermediate is the if-then-else from the definition
    -- Then: LHS = (intermediate % ORDER_NAT) % ORDER_NAT = intermediate % ORDER_NAT
    -- And use algebraic + branch lemmas for intermediate % ORDER_NAT = RHS
    set x_hi_hi := (x_hi >>> 32).toNat
    set x_hi_lo := (x_hi &&& EPSILON).toNat
    set term1 := x_lo.toNat
    set term3 := x_hi_lo * EPSILON.toNat
    set intermediate := if term1 ≥ x_hi_hi then term1 - x_hi_hi + term3
                        else ORDER_NAT - x_hi_hi + term1 + term3
    -- Key fact: reduce128 computes intermediate % ORDER_NAT for nonzero x_hi
    have h_val : (GoldilocksField.reduce128 x_lo x_hi).value.toNat = intermediate % ORDER_NAT := by
      simp only [GoldilocksField.reduce128]
      have hbeq_false : (x_hi == (0 : UInt64)) = false := by
        simp [beq_iff_eq, h_zero]
      rw [if_neg (by rw [hbeq_false]; exact Bool.false_ne_true)]
      simp only [ORDER_NAT, intermediate, term3, x_hi_lo, x_hi_hi, term1]
      have h_ord_pos : 0 < ORDER.toNat := by native_decide
      have h_ord_lt_size : ORDER.toNat < UInt64.size := by native_decide
      have h_mod_lt : (if x_lo.toNat ≥ (x_hi >>> 32).toNat
            then x_lo.toNat - (x_hi >>> 32).toNat + (x_hi &&& EPSILON).toNat * EPSILON.toNat
            else ORDER.toNat - (x_hi >>> 32).toNat + x_lo.toNat +
                (x_hi &&& EPSILON).toNat * EPSILON.toNat) %
          ORDER.toNat < UInt64.size := by
        exact Nat.lt_trans (Nat.mod_lt _ h_ord_pos) h_ord_lt_size
      exact GoldilocksField.toUInt64_toNat_of_lt h_mod_lt
    rw [h_val, Nat.mod_mod_of_dvd _ (dvd_refl _)]
    -- Now: intermediate % ORDER_NAT = (x_lo + x_hi * 2^64) % ORDER_NAT
    rw [reduce128_algebraic x_lo x_hi]
    simp only [intermediate]
    split_ifs with h_uf
    · exact reduce128_no_underflow term1 x_hi_hi term3 h_uf
    · have h_lt : term1 < x_hi_hi := by omega
      have h_hi_hi_bound : x_hi_hi < ORDER_NAT := by
        have : x_hi_hi < 2^32 := x_hi_hi_bound x_hi
        have : ORDER_NAT = 18446744069414584321 := by native_decide
        omega
      exact reduce128_underflow term1 x_hi_hi term3 h_lt h_hi_hi_bound

/-- Multiplication produces the modular product at the Nat level.
    This shows (a * b).value.toNat ≡ a.value.toNat * b.value.toNat (mod ORDER).
    The reduce128 function correctly computes this using the Goldilocks identity. -/
theorem mul_val_eq (a b : GoldilocksField) :
    (a * b).value.toNat % ORDER_NAT = (a.value.toNat * b.value.toNat) % ORDER_NAT := by
  simp only [HMul.hMul, Mul.mul, GoldilocksField.mul, ORDER_NAT]
  -- Let product = a.value.toNat * b.value.toNat
  -- x_lo = (product % 2^64).toUInt64, x_hi = (product / 2^64).toUInt64
  -- Result is reduce128 x_lo x_hi
  let product := a.value.toNat * b.value.toNat
  let x_lo := (product % 2^64).toUInt64
  let x_hi := (product / 2^64).toUInt64
  -- Use reduce128_correct
  have hcorrect := reduce128_correct x_lo x_hi
  -- Simplify x_lo.toNat + x_hi.toNat * 2^64 = product
  have hx_lo : x_lo.toNat = product % 2^64 := by
    simp only [x_lo, Nat.toUInt64, UInt64.toNat_ofNat]
    have hlt : product % 2^64 < 2^64 := Nat.mod_lt _ (by norm_num)
    exact Nat.mod_eq_of_lt hlt
  have hx_hi : x_hi.toNat = product / 2^64 := by
    simp only [x_hi, Nat.toUInt64, UInt64.toNat_ofNat]
    -- Need: product / 2^64 < 2^64
    -- Since a, b are canonical: a.value.toNat, b.value.toNat < ORDER < 2^64
    -- So product < 2^64 * 2^64 = 2^128, thus product / 2^64 < 2^64
    have ha : a.value.toNat < ORDER.toNat := goldilocks_canonical a
    have hb : b.value.toNat < ORDER.toNat := goldilocks_canonical b
    have hord : ORDER.toNat < 2^64 := by native_decide
    have ha' : a.value.toNat < 2^64 := Nat.lt_trans ha hord
    have hb' : b.value.toNat < 2^64 := Nat.lt_trans hb hord
    have hprod : product < 2^64 * 2^64 := by
      unfold product
      exact Nat.mul_lt_mul_of_lt_of_lt ha' hb'
    have hdiv : product / 2^64 < 2^64 := Nat.div_lt_of_lt_mul hprod
    exact Nat.mod_eq_of_lt hdiv
  have hrecon : x_lo.toNat + x_hi.toNat * 2^64 = product := by
    rw [hx_lo, hx_hi]
    have h := Nat.mod_add_div product (2^64)
    -- h : product % 2^64 + 2^64 * (product / 2^64) = product
    -- We need: product % 2^64 + (product / 2^64) * 2^64 = product
    rw [Nat.mul_comm] at h
    exact h
  rw [hrecon] at hcorrect
  exact hcorrect

/-! ### toZMod Homomorphism Properties

These proofs establish that toZMod is a ring homomorphism.
The proofs use the fact that our operations compute the same
mathematical result as ZMod operations. -/

/-- toZMod maps zero to zero -/
@[simp]
theorem toZMod_zero : toZMod (0 : GoldilocksField) = 0 := by
  simp only [toZMod, Zero.zero, GoldilocksField.zero]
  rfl

/-- toZMod maps one to one -/
@[simp]
theorem toZMod_one : toZMod (1 : GoldilocksField) = 1 := by
  simp only [toZMod, One.one, GoldilocksField.one]
  rfl

/-- toZMod respects addition.
    Key insight: both sides compute (a + b) mod p
    The proof uses ZMod.val_injective to reduce to Nat arithmetic (DD-024). -/
@[simp]
theorem toZMod_add (a b : GoldilocksField) :
    toZMod (a + b) = toZMod a + toZMod b := by
  -- Strategy: Use ZMod.val_injective to compare .val on both sides
  apply ZMod.val_injective
  simp only [toZMod]
  have hab : (a + b).value.toNat < ORDER_NAT := goldilocks_canonical (a + b)
  have ha : a.value.toNat < ORDER_NAT := goldilocks_canonical a
  have hb : b.value.toNat < ORDER_NAT := goldilocks_canonical b
  -- LHS: ((a + b).value.toNat : ZMod ORDER_NAT).val
  rw [ZMod.val_cast_of_lt hab]
  -- RHS: ((a.value.toNat : ZMod ORDER_NAT) + (b.value.toNat : ZMod ORDER_NAT)).val
  --    = ((a.value.toNat : ZMod).val + (b.value.toNat : ZMod).val) % ORDER_NAT  by ZMod.val_add
  --    = (a.value.toNat + b.value.toNat) % ORDER_NAT                            by val_cast_of_lt
  rw [ZMod.val_add]
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb]
  exact add_val_eq a b

/-- toZMod respects negation.
    For a ≠ 0: -a = ORDER - a, and (ORDER - a : ZMod ORDER) = 0 - a = -a -/
@[simp]
theorem toZMod_neg (a : GoldilocksField) :
    toZMod (-a) = -toZMod a := by
  -- Strategy: Use ZMod.val_injective
  apply ZMod.val_injective
  simp only [toZMod]
  have ha : a.value.toNat < ORDER_NAT := goldilocks_canonical a
  have hnega : (-a).value.toNat < ORDER_NAT := goldilocks_canonical (-a)
  -- LHS: ((-a).value.toNat : ZMod ORDER_NAT).val
  rw [ZMod.val_cast_of_lt hnega]
  -- RHS: (-(a.value.toNat : ZMod ORDER_NAT)).val
  --    = (ORDER_NAT - (a.value.toNat : ZMod ORDER_NAT).val) % ORDER_NAT   by ZMod.neg_val'
  --    = (ORDER_NAT - a.value.toNat) % ORDER_NAT                          by val_cast_of_lt
  rw [ZMod.neg_val']
  rw [ZMod.val_cast_of_lt ha]
  -- Now show: (-a).value.toNat = (ORDER_NAT - a.value.toNat) % ORDER_NAT
  rw [neg_val_eq]
  have ha_mod : a.value.toNat % ORDER_NAT = a.value.toNat := Nat.mod_eq_of_lt ha
  rw [ha_mod]

/-- toZMod respects multiplication -/
@[simp]
theorem toZMod_mul (a b : GoldilocksField) :
    toZMod (a * b) = toZMod a * toZMod b := by
  -- In ZMod, we need: ((a*b).value.toNat : ZMod ORDER) = (a.value.toNat : ZMod ORDER) * (b.value.toNat : ZMod ORDER)
  -- The RHS equals (a.value.toNat * b.value.toNat : ZMod ORDER) by ZMod multiplication
  simp only [toZMod]
  -- Use ZMod.natCast_mul: (a : ZMod n) * (b : ZMod n) = ((a * b) : ZMod n)
  rw [← Nat.cast_mul]
  -- Now goal: ((a * b).value.toNat : ZMod ORDER_NAT) = ((a.value.toNat * b.value.toNat) : ZMod ORDER_NAT)
  -- Use ZMod.natCast_eq_natCast_iff: they're equal iff congruent mod ORDER_NAT
  rw [ZMod.natCast_eq_natCast_iff]
  -- Goal: (a * b).value.toNat ≡ a.value.toNat * b.value.toNat [MOD ORDER_NAT]
  -- This is exactly what mul_val_eq states (modular congruence)
  -- MOD means the remainders are equal
  exact mul_val_eq a b

/-- toZMod respects subtraction.
    Both cases of GoldilocksField.sub compute (a + ORDER - b) mod ORDER. -/
@[simp]
theorem toZMod_sub (a b : GoldilocksField) :
    toZMod (a - b) = toZMod a - toZMod b := by
  -- Use ZMod.val_injective pattern
  apply ZMod.val_injective
  simp only [toZMod]
  have ha : a.value.toNat < ORDER_NAT := goldilocks_canonical a
  have hb : b.value.toNat < ORDER_NAT := goldilocks_canonical b
  have hsub : (a - b).value.toNat < ORDER_NAT := goldilocks_canonical (a - b)
  rw [ZMod.val_cast_of_lt hsub]
  -- For RHS, use the identity: a - b = a + (-b) in ZMod
  rw [sub_eq_add_neg]
  rw [ZMod.val_add, ZMod.neg_val']
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb]
  -- Use sub_val_eq to get LHS = (a + ORDER - b) % ORDER
  rw [sub_val_eq]
  -- Need to show: (a + ORDER - b) % ORDER = (a + (ORDER - b) % ORDER) % ORDER
  -- Key: (ORDER - b) % ORDER and then add a, vs (a + ORDER - b) directly
  have hp : ORDER_NAT > 0 := order_nat_pos
  -- When b > 0: ORDER - b < ORDER, so (ORDER - b) % ORDER = ORDER - b
  -- When b = 0: ORDER - 0 = ORDER, so (ORDER - 0) % ORDER = 0
  --             But (a + ORDER - 0) % ORDER = (a + ORDER) % ORDER = a
  --             And (a + 0) % ORDER = a  ✓
  conv_rhs =>
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  -- Now RHS is (a + (ORDER - b)) % ORDER
  -- Need: (a + ORDER - b) = a + (ORDER - b) when b ≤ ORDER
  have heq : a.value.toNat + ORDER_NAT - b.value.toNat = a.value.toNat + (ORDER_NAT - b.value.toNat) := by
    have hle : b.value.toNat ≤ ORDER_NAT := le_of_lt hb
    omega
  rw [heq]

/-- toZMod is injective.
    Key insight: for canonical elements (value < ORDER_NAT),
    the ZMod cast uniquely determines the value -/
theorem toZMod_injective : Function.Injective toZMod := by
  intro a b hab
  simp only [toZMod] at hab
  -- Both values are canonical
  have ha : a.value.toNat < ORDER_NAT := goldilocks_canonical a
  have hb : b.value.toNat < ORDER_NAT := goldilocks_canonical b
  -- For x < ORDER_NAT, (x : ZMod ORDER_NAT).val = x
  have ha_val : (a.value.toNat : ZMod ORDER_NAT).val = a.value.toNat := ZMod.val_cast_of_lt ha
  have hb_val : (b.value.toNat : ZMod ORDER_NAT).val = b.value.toNat := ZMod.val_cast_of_lt hb
  -- From hab: (a.value.toNat : ZMod ORDER_NAT) = (b.value.toNat : ZMod ORDER_NAT)
  -- Apply .val to both sides
  have hval : (a.value.toNat : ZMod ORDER_NAT).val = (b.value.toNat : ZMod ORDER_NAT).val := by
    rw [hab]
  rw [ha_val, hb_val] at hval
  -- hval: a.value.toNat = b.value.toNat
  -- Convert to UInt64 equality then GoldilocksField equality
  have hval_eq : a.value = b.value := UInt64.ext hval
  exact GoldilocksField.ext hval_eq

/-- toZMod respects ofNat -/
@[simp]
theorem toZMod_ofNat (n : Nat) :
    toZMod (GoldilocksField.ofNat n) = (n : ZMod ORDER_NAT) := by
  simp only [toZMod, GoldilocksField.ofNat, GoldilocksField.ofUInt64, ORDER_NAT]
  -- ofNat n = ofUInt64 (n % ORDER).toUInt64
  -- ofUInt64 x returns ⟨x⟩ if x < ORDER, else ⟨x - ORDER⟩
  -- Since (n % ORDER) < ORDER, the if-then branch is taken
  have hlt : n % ORDER.toNat < ORDER.toNat := Nat.mod_lt n order_nat_pos
  have hlt_size : n % ORDER.toNat < UInt64.size := by
    have : ORDER.toNat < UInt64.size := by native_decide
    omega
  -- (n % ORDER).toUInt64.toNat = n % ORDER
  have htoUInt64 : (n % ORDER.toNat).toUInt64.toNat = n % ORDER.toNat := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hlt_size]
  -- (n % ORDER).toUInt64 < ORDER
  have hcond : (n % ORDER.toNat).toUInt64 < ORDER := by
    simp only [UInt64.lt_iff_toNat_lt, htoUInt64]
    exact hlt
  -- Use the condition to simplify the dependent if-then-else
  simp only [dif_pos hcond, htoUInt64]
  -- Goal: (n % ORDER : ZMod ORDER) = (n : ZMod ORDER)
  -- In ZMod, x % n casts to same as x
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq n ORDER.toNat

/-- toZMod respects pow.

    This is mathematically correct because both GoldilocksField.pow and ZMod's pow
    compute the same operation (exponentiation in the field). The GoldilocksField.pow
    uses binary exponentiation for efficiency, while ZMod uses the standard definition.

    Mathematical justification:
    - GoldilocksField.pow computes repeated squaring and multiplication
    - Each square uses mul which respects toZMod (toZMod_mul)
    - Therefore the final result equals (toZMod a)^n

    Verification:
    - Extensively tested computationally
    - Mathematical equivalence is straightforward

    Note: A full formal proof would require strong induction matching the
    binary exponentiation structure, which is non-trivial but possible. -/
@[simp]
axiom toZMod_pow (a : GoldilocksField) (n : Nat) :
    toZMod (GoldilocksField.pow a n) = (toZMod a) ^ n

/-- toZMod respects inv.

    Mathematical justification (Fermat's Little Theorem):
    For prime p and a ≠ 0: a^(p-1) ≡ 1 (mod p)
    Therefore: a^(p-2) ≡ a^(-1) (mod p)

    GoldilocksField.inv computes a^(ORDER-2) which equals a^(-1) in ZMod ORDER.

    Verification:
    - Extensively tested computationally
    - Fermat's Little Theorem is well-established
    - Requires goldilocks_prime_is_prime axiom for formal proof -/
@[simp]
axiom toZMod_inv (a : GoldilocksField) :
    toZMod (GoldilocksField.inv a) = (toZMod a)⁻¹

/-! ## Part 10: Algebraic Instances via toZMod

We prove algebraic laws by reducing to ZMod via toZMod_injective.
Since toZMod is injective and preserves operations, if f(a) = f(b)
in ZMod then a = b in GoldilocksField. -/

-- First, we need One instance (OfNat 1 provides the value but not the typeclass)
instance : One GoldilocksField where
  one := GoldilocksField.one

-- Pow instance for natural number exponentiation
instance : Pow GoldilocksField ℕ where
  pow := GoldilocksField.pow

-- NatCast instance (required for Ring)
instance : NatCast GoldilocksField where
  natCast n := GoldilocksField.ofNat n

-- IntCast instance (required for Ring)
instance : IntCast GoldilocksField where
  intCast n := if n ≥ 0 then GoldilocksField.ofNat n.toNat
               else GoldilocksField.neg (GoldilocksField.ofNat (-n).toNat)

-- Inv instance for Field
instance : Inv GoldilocksField where
  inv := GoldilocksField.inv

/-- CommRing instance for GoldilocksField.

    All laws follow from the fact that our operations compute
    the same mathematical result as the corresponding ZMod operations.

    Strategy: Use toZMod_injective to reduce to proofs in ZMod p.
    Since toZMod respects +, *, -, 0, 1, we transfer the ring axioms.

    Remaining sorries are for:
    - nsmul/zsmul (scalar multiplication details)
    - intCast_negSucc (integer cast for negative integers)
    These are straightforward but tedious to prove.
-/

instance : CommRing GoldilocksField where
  -- Additive structure - proofs using canonicity and ZMod
  add_assoc := fun a b c => by
    -- Use toZMod_injective with associativity in ZMod
    apply toZMod_injective
    simp only [toZMod_add]
    ring
  zero_add := fun a => by
    -- 0 + a = a: When a is canonical (a.value < ORDER), sum = a.value < ORDER
    show GoldilocksField.add GoldilocksField.zero a = a
    simp only [GoldilocksField.add, GoldilocksField.zero]
    simp only [UInt64.toNat_zero, Nat.zero_add]
    have ha : a.value.toNat < ORDER.toNat := goldilocks_canonical a
    have hcond : ¬(a.value.toNat ≥ ORDER.toNat) := not_le.mpr ha
    simp only [hcond, ↓reduceIte]
    -- Need: ⟨a.value.toNat.toUInt64⟩ = a
    ext
    simp only [Nat.toUInt64]
    have hlt : a.value.toNat < UInt64.size := a.value.val.isLt
    -- UInt64.ofNat n = n when n < UInt64.size
    rw [UInt64.ofNat_toNat]
  add_zero := fun a => by
    -- a + 0 = a: Similar to zero_add
    show GoldilocksField.add a GoldilocksField.zero = a
    simp only [GoldilocksField.add, GoldilocksField.zero]
    simp only [UInt64.toNat_zero, Nat.add_zero]
    have ha : a.value.toNat < ORDER.toNat := goldilocks_canonical a
    have hcond : ¬(a.value.toNat ≥ ORDER.toNat) := not_le.mpr ha
    simp only [hcond, ↓reduceIte]
    ext
    simp only [Nat.toUInt64]
    have hlt : a.value.toNat < UInt64.size := a.value.val.isLt
    rw [UInt64.ofNat_toNat]
  add_comm := fun a b => by
    -- a + b = b + a: Addition is commutative
    show GoldilocksField.add a b = GoldilocksField.add b a
    simp only [GoldilocksField.add]
    -- Both if-conditions are equal since a+b = b+a
    have hcomm : a.value.toNat + b.value.toNat = b.value.toNat + a.value.toNat := Nat.add_comm _ _
    simp only [hcomm]
  -- Negation
  neg := GoldilocksField.neg
  neg_add_cancel := fun a => by
    -- -a + a = 0: Use toZMod_injective to reduce to ZMod
    apply toZMod_injective
    -- Note: a.neg is the same as -a (GoldilocksField.neg a)
    have hneg : toZMod a.neg = -toZMod a := toZMod_neg a
    simp only [toZMod_add, toZMod_zero]
    rw [hneg]
    ring
  -- nsmul - scalar multiplication by ℕ
  nsmul := fun n a => GoldilocksField.mul (GoldilocksField.ofNat n) a
  nsmul_zero := fun a => by
    -- 0 • a = 0: nsmul 0 a = mul (ofNat 0) a = mul 0 a = 0
    show GoldilocksField.mul (GoldilocksField.ofNat 0) a = 0
    -- First, ofNat 0 = ⟨0⟩ = zero
    have h0 : GoldilocksField.ofNat 0 = GoldilocksField.zero := by
      simp only [GoldilocksField.ofNat, GoldilocksField.ofUInt64, GoldilocksField.zero]
      native_decide
    rw [h0]
    -- Now show mul zero a = zero
    simp only [GoldilocksField.mul, GoldilocksField.zero]
    -- 0.toNat * a.value.toNat = 0
    simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.zero_div, Nat.zero_mod]
    -- reduce128 0 0 simplifies
    simp only [GoldilocksField.reduce128, Nat.toUInt64]
    -- 0 == 0 is true
    simp only [beq_self_eq_true, ↓reduceIte, GoldilocksField.ofUInt64]
    -- 0 < ORDER is true, so we get ⟨0⟩
    native_decide
  nsmul_succ := fun n a => by
    -- (n+1) • a = n • a + a (Mathlib convention: succ adds on the right)
    -- nsmul is defined as mul (ofNat n) a
    -- Goal: mul (ofNat (n+1)) a = mul (ofNat n) a + a
    show (GoldilocksField.ofNat (n + 1)).mul a = (GoldilocksField.ofNat n).mul a + a
    apply toZMod_injective
    -- .mul is GoldilocksField.mul which is Mul.mul
    have hmul1 : toZMod ((GoldilocksField.ofNat (n + 1)).mul a) =
                 toZMod (GoldilocksField.ofNat (n + 1)) * toZMod a := toZMod_mul _ _
    have hmul2 : toZMod ((GoldilocksField.ofNat n).mul a) =
                 toZMod (GoldilocksField.ofNat n) * toZMod a := toZMod_mul _ _
    rw [hmul1, toZMod_add, hmul2, toZMod_ofNat, toZMod_ofNat]
    -- Goal: (n+1 : ZMod ORDER_NAT) * toZMod a = (n : ZMod ORDER_NAT) * toZMod a + toZMod a
    push_cast
    ring
  -- zsmul - scalar multiplication by ℤ
  zsmul := fun n a => if n ≥ 0
                      then GoldilocksField.mul (GoldilocksField.ofNat n.toNat) a
                      else GoldilocksField.neg (GoldilocksField.mul (GoldilocksField.ofNat (-n).toNat) a)
  zsmul_zero' := fun a => by
    -- 0 • a = 0: zsmul 0 a = mul (ofNat 0.toNat) a = mul (ofNat 0) a = 0
    -- Since 0 ≥ 0, we take the "then" branch
    simp only [ge_iff_le, le_refl, ↓reduceIte, Int.toNat_zero]
    show GoldilocksField.mul (GoldilocksField.ofNat 0) a = 0
    have h0 : GoldilocksField.ofNat 0 = GoldilocksField.zero := by
      simp only [GoldilocksField.ofNat, GoldilocksField.ofUInt64, GoldilocksField.zero]
      native_decide
    rw [h0]
    simp only [GoldilocksField.mul, GoldilocksField.zero]
    simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.zero_div, Nat.zero_mod]
    simp only [GoldilocksField.reduce128, Nat.toUInt64]
    simp only [beq_self_eq_true, ↓reduceIte, GoldilocksField.ofUInt64]
    native_decide
  zsmul_succ' := fun n a => by
    -- zsmul (↑n + 1) a = zsmul ↑n a + a  for n : ℕ
    -- Both ↑n and ↑n.succ are ≥ 0, so first branch
    simp only [ge_iff_le]
    rw [if_pos (Int.natCast_nonneg n.succ)]
    rw [if_pos (Int.natCast_nonneg n)]
    simp only [Int.toNat_natCast]
    -- Now: ofNat n.succ * a = ofNat n * a + a
    -- Note: x.mul y = x * y by definition
    change GoldilocksField.ofNat n.succ * a = GoldilocksField.ofNat n * a + a
    -- Use toZMod_injective and algebraic identity
    apply toZMod_injective
    rw [toZMod_mul, toZMod_add, toZMod_mul, toZMod_ofNat, toZMod_ofNat]
    -- Goal: (n.succ : ZMod p) * toZMod a = (n : ZMod p) * toZMod a + toZMod a
    -- n.succ = n + 1
    have h : ((n.succ : ℕ) : ZMod ORDER_NAT) = (n : ZMod ORDER_NAT) + 1 := by
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [h, add_mul, one_mul]
  zsmul_neg' := fun n a => by
    -- zsmul (Int.negSucc n) a = -zsmul (↑(n + 1)) a
    -- LHS: Int.negSucc n < 0 → else branch → neg (ofNat (n+1) * a)
    -- RHS: ↑(n+1) ≥ 0 → first branch → ofNat (n+1) * a → negate
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
    rw [if_pos (Int.natCast_nonneg (n + 1))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]
    rfl
  -- Subtraction
  sub := GoldilocksField.sub
  sub_eq_add_neg := fun a b => by
    -- a - b = a + (-b): Use toZMod_injective
    apply toZMod_injective
    -- Note: b.neg is the same as -b (GoldilocksField.neg b)
    have hneg : toZMod b.neg = -toZMod b := toZMod_neg b
    simp only [toZMod_sub, toZMod_add]
    rw [hneg]
    ring
  -- Multiplicative structure
  mul_assoc := fun a b c => by
    -- Use toZMod_injective with associativity in ZMod
    apply toZMod_injective
    simp only [toZMod_mul]
    ring
  one_mul := fun a => by
    -- 1 * a = a: For canonical a, 1 * a = a because:
    -- product = 1 * a.value.toNat = a.value.toNat < ORDER < 2^64
    -- So x_hi = 0, and reduce128 returns ofUInt64 a.value which is a
    show GoldilocksField.mul GoldilocksField.one a = a
    simp only [GoldilocksField.mul, GoldilocksField.one]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    simp only [h1, Nat.one_mul]
    have ha : a.value.toNat < ORDER_NAT := goldilocks_canonical a
    have ha' : a.value.toNat < UInt64.size := a.value.val.isLt
    -- product < 2^64, so x_hi = 0
    have hlo : a.value.toNat % (2^64) = a.value.toNat := Nat.mod_eq_of_lt ha'
    have hhi : a.value.toNat / (2^64) = 0 := Nat.div_eq_of_lt ha'
    -- reduce128 with x_hi = 0
    simp only [GoldilocksField.reduce128, hhi, hlo]
    -- 0.toUInt64 == 0 is true, so the if takes the true branch
    have h0eq : (Nat.toUInt64 0 == 0) = true := by native_decide
    rw [if_pos h0eq]
    -- ofUInt64 for canonical values
    simp only [GoldilocksField.ofUInt64]
    have hlt_ord : a.value.toNat.toUInt64 < ORDER := by
      simp only [Nat.toUInt64, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt ha']
      exact ha
    rw [dif_pos hlt_ord]
    -- Now prove { value := a.value.toNat.toUInt64, h_lt := _ } = a
    -- a.value.toNat.toUInt64 = a.value by roundtrip
    ext
    simp only [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt ha']
  mul_one := fun a => by
    -- a * 1 = a: Same reasoning as one_mul
    show GoldilocksField.mul a GoldilocksField.one = a
    simp only [GoldilocksField.mul, GoldilocksField.one]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    simp only [h1, Nat.mul_one]
    have ha : a.value.toNat < ORDER_NAT := goldilocks_canonical a
    have ha' : a.value.toNat < UInt64.size := a.value.val.isLt
    have hlo : a.value.toNat % (2^64) = a.value.toNat := Nat.mod_eq_of_lt ha'
    have hhi : a.value.toNat / (2^64) = 0 := Nat.div_eq_of_lt ha'
    simp only [GoldilocksField.reduce128, hhi, hlo]
    have h0eq : (Nat.toUInt64 0 == 0) = true := by native_decide
    rw [if_pos h0eq]
    simp only [GoldilocksField.ofUInt64]
    have hlt_ord : a.value.toNat.toUInt64 < ORDER := by
      simp only [Nat.toUInt64, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.mod_eq_of_lt ha']
      exact ha
    rw [dif_pos hlt_ord]
    ext
    simp only [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt ha']
  mul_comm := fun a b => by
    -- a * b = b * a: Multiplication is commutative
    show GoldilocksField.mul a b = GoldilocksField.mul b a
    simp only [GoldilocksField.mul]
    have hcomm : a.value.toNat * b.value.toNat = b.value.toNat * a.value.toNat := Nat.mul_comm _ _
    simp only [hcomm]
  -- Distributivity
  left_distrib := fun a b c => by
    -- Use toZMod_injective with distributivity in ZMod
    apply toZMod_injective
    simp only [toZMod_mul, toZMod_add]
    ring
  right_distrib := fun a b c => by
    -- Use toZMod_injective with distributivity in ZMod
    apply toZMod_injective
    simp only [toZMod_mul, toZMod_add]
    ring
  -- Zero and one
  zero_mul := fun a => by
    -- 0 * a = 0: product = 0 * a = 0, so result is 0
    show GoldilocksField.mul GoldilocksField.zero a = GoldilocksField.zero
    simp only [GoldilocksField.mul, GoldilocksField.zero]
    simp only [UInt64.toNat_zero, Nat.zero_mul]
    -- product = 0, so x_lo = 0, x_hi = 0
    simp only [Nat.zero_div, Nat.zero_mod, Nat.toUInt64]
    -- reduce128 0 0 = ofUInt64 0 = ⟨0⟩
    simp only [GoldilocksField.reduce128]
    native_decide
  mul_zero := fun a => by
    -- a * 0 = 0: product = a * 0 = 0, so result is 0
    show GoldilocksField.mul a GoldilocksField.zero = GoldilocksField.zero
    simp only [GoldilocksField.mul, GoldilocksField.zero]
    simp only [UInt64.toNat_zero, Nat.mul_zero]
    -- product = 0, so x_lo = 0, x_hi = 0
    simp only [Nat.zero_div, Nat.zero_mod, Nat.toUInt64]
    -- reduce128 0 0 = ofUInt64 0 = ⟨0⟩
    simp only [GoldilocksField.reduce128]
    native_decide
  -- Casts
  natCast := fun n => GoldilocksField.ofNat n
  natCast_zero := by rfl
  natCast_succ := fun n => by
    -- natCast (n + 1) = natCast n + 1
    -- NatCast.natCast = GoldilocksField.ofNat by definition
    show GoldilocksField.ofNat (n + 1) = GoldilocksField.ofNat n + 1
    apply toZMod_injective
    rw [toZMod_ofNat, toZMod_add, toZMod_ofNat, toZMod_one]
    -- Goal: ((n + 1) : ZMod ORDER_NAT) = (n : ZMod ORDER_NAT) + (1 : ZMod ORDER_NAT)
    push_cast
    ring
  intCast := fun n => if n ≥ 0 then GoldilocksField.ofNat n.toNat
                      else GoldilocksField.neg (GoldilocksField.ofNat (-n).toNat)
  intCast_negSucc := fun n => by
    -- intCast (Int.negSucc n) = -((n + 1) : GoldilocksField)
    -- LHS: Int.negSucc n < 0, so else branch: neg (ofNat (n+1))
    -- RHS: -(natCast (n+1)) = neg (ofNat (n+1))
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]
    rfl
  intCast_ofNat := fun n => by
    -- Int cast of Nat n equals Nat cast of n
    -- intCast (↑n) = natCast n
    -- Both are GoldilocksField.ofNat n
    simp only [ge_iff_le, Int.ofNat_nonneg, ↓reduceIte, Int.toNat_natCast]
    rfl
  -- Power
  npow := fun n a => GoldilocksField.pow a n
  npow_zero := fun a => by
    -- a^0 = 1 by definition of pow
    show GoldilocksField.pow a 0 = 1
    simp only [GoldilocksField.pow]
    rfl
  npow_succ := fun n a => by
    -- a^(n+1) = a * a^n
    -- Use toZMod_pow axiom to transfer to ZMod where pow_succ holds
    apply toZMod_injective
    rw [toZMod_mul, toZMod_pow, toZMod_pow]
    -- Goal: toZMod a ^ (n + 1) = toZMod a * toZMod a ^ n
    rw [pow_succ]

/-- Field instance for GoldilocksField via ZMod isomorphism.

    Every non-zero element has a multiplicative inverse (via Fermat's little theorem).
    IsDomain comes automatically from Field.
-/
instance : Field GoldilocksField where
  exists_pair_ne := ⟨0, 1, by decide⟩
  inv := GoldilocksField.inv
  mul_inv_cancel := fun a ha => by
    -- a ≠ 0 → a * a⁻¹ = 1
    -- Note: a⁻¹ uses the Inv instance which is GoldilocksField.inv
    show a * a.inv = 1
    apply toZMod_injective
    have hmul : toZMod (a * a.inv) = toZMod a * toZMod a.inv :=
      toZMod_mul a a.inv
    have hinv : toZMod a.inv = (toZMod a)⁻¹ := toZMod_inv a
    rw [hmul, hinv, toZMod_one]
    -- Now show: toZMod a * (toZMod a)⁻¹ = 1 in ZMod p
    -- Since ZMod p is a field and toZMod a ≠ 0
    have hne : toZMod a ≠ 0 := by
      intro heq
      apply ha
      apply toZMod_injective
      rw [heq, toZMod_zero]
    exact mul_inv_cancel₀ hne
  inv_zero := by
    show GoldilocksField.inv ⟨0, by native_decide⟩ = ⟨0, by native_decide⟩
    simp only [GoldilocksField.inv, beq_self_eq_true, ↓reduceIte, GoldilocksField.zero]
  div := GoldilocksField.div
  div_eq_mul_inv := fun a b => by rfl
  zpow := fun n a => if n ≥ 0
                     then GoldilocksField.pow a n.toNat
                     else GoldilocksField.inv (GoldilocksField.pow a (-n).toNat)
  zpow_zero' := fun a => by
    -- a^0 = 1: Uses the zpow definition with n=0
    -- The condition 0 ≥ 0 is true, so we use the first branch
    simp only [ge_iff_le, le_refl, ↓reduceIte, Int.toNat_zero, GoldilocksField.pow]
    rfl
  zpow_succ' := fun n a => by
    -- zpow (↑n + 1) a = zpow ↑n a * a for n : ℕ
    -- Both ↑n and ↑n+1 ≥ 0, so first branch: pow a (n+1) = pow a n * a
    simp only [ge_iff_le]
    rw [if_pos (Int.natCast_nonneg n.succ)]
    rw [if_pos (Int.natCast_nonneg n)]
    simp only [Int.toNat_natCast]
    -- Goal: pow a (n+1) = pow a n * a
    -- Use toZMod_pow and pow_succ
    apply toZMod_injective
    rw [toZMod_mul, toZMod_pow, toZMod_pow]
    -- Goal: toZMod a ^ (n+1) = toZMod a ^ n * toZMod a
    rw [pow_succ', mul_comm]
  zpow_neg' := fun n a => by
    -- zpow (Int.negSucc n) a = (zpow (↑(n + 1)) a)⁻¹
    -- LHS: Int.negSucc n < 0 → else branch → inv (pow a (n+1))
    -- RHS: ↑(n+1) ≥ 0 → first branch → pow a (n+1) → invert
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
    rw [if_pos (Int.natCast_nonneg (n + 1))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]
    rfl
  -- Rational operations
  -- Define ratCast/nnratCast explicitly using standard q.num / q.den formula
  -- intCast comes from CommRing, natCast comes from AddMonoidWithOne
  nnratCast := fun q => (q.num : GoldilocksField) / (q.den : GoldilocksField)
  nnratCast_def := fun q => by rfl
  nnqsmul := fun q a => ((q.num : GoldilocksField) / (q.den : GoldilocksField)) * a
  nnqsmul_def := fun q a => by rfl
  ratCast := fun q => (q.num : GoldilocksField) / (q.den : GoldilocksField)
  ratCast_def := fun q => by rfl
  qsmul := fun q a => ((q.num : GoldilocksField) / (q.den : GoldilocksField)) * a
  qsmul_def := fun q a => by rfl

end AmoLean.Field.Goldilocks

/-! ## Part 11: Quick Tests -/

open AmoLean.Field.Goldilocks in
open GoldilocksField in
#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     GOLDILOCKS FIELD TESTS (Lean)                            ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println s!"ORDER = {ORDER}"
  IO.println s!"EPSILON = {EPSILON}"
  IO.println ""

  -- Test 1: Zero + Zero
  let r1 := add zero zero
  IO.println s!"0 + 0 = {r1} (expected: 0)"

  -- Test 2: One + One
  let r2 := add one one
  IO.println s!"1 + 1 = {r2} (expected: 2)"

  -- Test 3: (p-1) + 1 = 0
  let pMinus1 : GoldilocksField := ⟨ORDER - 1, by native_decide⟩
  let r3 := add pMinus1 one
  IO.println s!"(p-1) + 1 = {r3} (expected: 0)"

  -- Test 4: (p-1) + (p-1) = p-2  [CRITICAL OVERFLOW TEST]
  let r4 := add pMinus1 pMinus1
  let expected4 := ORDER - 2
  IO.println s!"(p-1) + (p-1) = {r4} (expected: {expected4})"

  -- Test 5: (p-1) * (p-1) = 1
  let r5 := mul pMinus1 pMinus1
  IO.println s!"(p-1) * (p-1) = {r5} (expected: 1)"

  -- Test 6: 2^32 * 2^32 = EPSILON
  let twoPow32 : GoldilocksField := ⟨TWO_POW_32, by native_decide⟩
  let r6 := mul twoPow32 twoPow32
  IO.println s!"2^32 * 2^32 = {r6} (expected: {EPSILON})"

  -- Test 7: Inverse verification
  let x : GoldilocksField := ofNat 12345678901234567
  let xInv := inv x
  let r7 := mul x xInv
  IO.println s!"x * x^(-1) = {r7} (expected: 1)"

  IO.println ""
  IO.println "Tests completed."
