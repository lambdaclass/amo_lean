/-
  AMO-Lean: Goldilocks Field Implementation
  Phase 1: Core Field Arithmetic

  Goldilocks Field: F_p where p = 2^64 - 2^32 + 1

  This field is used by Plonky2/Plonky3 for efficient ZK proofs.
  The special structure allows fast modular reduction using
  the identity: 2^64 ≡ 2^32 - 1 (mod p)

  Reference: Plonky2 goldilocks_field.rs
-/

namespace AmoLean.Field.Goldilocks

/-! ## Part 1: Field Constants -/

/-- Goldilocks prime: p = 2^64 - 2^32 + 1 -/
def ORDER : UInt64 := 0xFFFFFFFF00000001

/-- Epsilon: 2^32 - 1, used in fast reduction -/
def EPSILON : UInt64 := 0xFFFFFFFF

/-- 2^32 as UInt64 -/
def TWO_POW_32 : UInt64 := 0x100000000

/-! ## Part 2: Goldilocks Field Type -/

/-- Goldilocks field element.
    Invariant: value < ORDER -/
structure GoldilocksField where
  value : UInt64
  -- Note: We don't enforce value < ORDER at the type level
  -- for simplicity, but all operations maintain this invariant
  deriving Repr, DecidableEq, Hashable

instance : Inhabited GoldilocksField := ⟨⟨0⟩⟩

namespace GoldilocksField

/-! ## Part 3: Constructors -/

/-- Create a field element from UInt64, reducing if necessary -/
def ofUInt64 (n : UInt64) : GoldilocksField :=
  if n < ORDER then ⟨n⟩
  else ⟨n - ORDER⟩

/-- Create a field element from Nat -/
def ofNat (n : Nat) : GoldilocksField :=
  let reduced := n % ORDER.toNat
  ofUInt64 reduced.toUInt64

/-- Zero element -/
def zero : GoldilocksField := ⟨0⟩

/-- One element -/
def one : GoldilocksField := ⟨1⟩

/-! ## Part 4: Core Arithmetic Operations -/

/-- Addition: (a + b) mod p

    CRITICAL: Uses intermediate representation to handle overflow.
    This mirrors the corrected C implementation. -/
def add (a b : GoldilocksField) : GoldilocksField :=
  -- Use Nat arithmetic to avoid overflow
  let sum := a.value.toNat + b.value.toNat
  let reduced := if sum >= ORDER.toNat then sum - ORDER.toNat else sum
  ⟨reduced.toUInt64⟩

/-- Subtraction: (a - b) mod p -/
def sub (a b : GoldilocksField) : GoldilocksField :=
  if a.value >= b.value then
    ⟨a.value - b.value⟩
  else
    -- a < b, so result would be negative. Add ORDER.
    ⟨ORDER - b.value + a.value⟩

/-- Negation: -a mod p -/
def neg (a : GoldilocksField) : GoldilocksField :=
  if a.value == 0 then ⟨0⟩
  else ⟨ORDER - a.value⟩

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
    ⟨result.toUInt64⟩

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

-- Note: One typeclass is provided by OfNat 1
-- instance : One GoldilocksField where
--   one := GoldilocksField.one

instance : ToString GoldilocksField where
  toString f := toString f.value

namespace GoldilocksField

/-! ## Part 6: Field Properties (Axioms for future proofs) -/

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
def P_MINUS_1 : GoldilocksField := ⟨ORDER - 1⟩

/-- p - 2: Used for inverse calculation -/
def P_MINUS_2 : GoldilocksField := ⟨ORDER - 2⟩

end AmoLean.Field.Goldilocks

/-! ## Part 9: Quick Tests -/

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
  let pMinus1 : GoldilocksField := ⟨ORDER - 1⟩
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
  let twoPow32 : GoldilocksField := ⟨TWO_POW_32⟩
  let r6 := mul twoPow32 twoPow32
  IO.println s!"2^32 * 2^32 = {r6} (expected: {EPSILON})"

  -- Test 7: Inverse verification
  let x : GoldilocksField := ofNat 12345678901234567
  let xInv := inv x
  let r7 := mul x xInv
  IO.println s!"x * x^(-1) = {r7} (expected: 1)"

  IO.println ""
  IO.println "Tests completed."
