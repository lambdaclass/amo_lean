/-
  AMO-Lean: NTT Field Type Class
  Phase 5: NTT Core - Task 1.1

  Lightweight type class for fields supporting NTT operations.

  Design Decision DD-013: We define our own NTTField type class instead of
  using Mathlib's Field because:
  1. Mathlib Field requires ratCast : ℚ → K (unnecessary for NTT)
  2. Our field instances (Goldilocks) already have arithmetic defined
  3. IsPrimitiveRoot from Mathlib only requires CommMonoid (lightweight)

  This approach is inspired by risc0-lean4's field hierarchy.
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs

namespace AmoLean.NTT

/-! ## Part 1: NTTField Type Class

A field suitable for NTT must support:
- Addition, subtraction, multiplication
- Multiplicative inverse (for non-zero elements)
- A characteristic (prime p)
- Exponentiation

We don't require division as a primitive; it can be derived from inverse.
-/

/-- Minimal type class for fields supporting NTT operations.

This is intentionally lighter than Mathlib's `Field`:
- No `ratCast` requirement
- No proof obligations (those are in NTTFieldLawful)
- Compatible with execution-focused implementations
-/
class NTTField (F : Type*) extends Add F, Sub F, Neg F, Mul F, Zero F, One F where
  /-- Multiplicative inverse. Returns 0 for input 0 (sentinel). -/
  inv : F → F
  /-- Exponentiation by natural number -/
  pow : F → Nat → F
  /-- The characteristic (prime order) of the field -/
  char : Nat
  /-- Check if element is zero -/
  isZero : F → Bool

namespace NTTField

variable {F : Type*} [NTTField F]

/-- Division: a / b = a * b⁻¹ -/
def div (a b : F) : F := a * inv b

/-- Square: a² -/
def square (a : F) : F := a * a

/-- Cube: a³ -/
def cube (a : F) : F := a * a * a

end NTTField

/-! ## Part 2: Lawful NTTField (with proofs)

For theorem proving, we need algebraic laws. These are separated from
the computational class so that execution doesn't require carrying proofs.
-/

/-- NTTField with algebraic laws proven.

This is used when we need to prove correctness theorems.
-/
class NTTFieldLawful (F : Type*) extends NTTField F where
  /-- Addition is commutative -/
  add_comm : ∀ a b : F, a + b = b + a
  /-- Addition is associative -/
  add_assoc : ∀ a b c : F, (a + b) + c = a + (b + c)
  /-- Zero is additive identity -/
  add_zero : ∀ a : F, a + 0 = a
  /-- Additive inverse -/
  add_neg : ∀ a : F, a + (-a) = 0
  /-- Subtraction definition: a - b = a + (-b) -/
  sub_def : ∀ a b : F, a - b = a + (-b)
  /-- Multiplication is commutative -/
  mul_comm : ∀ a b : F, a * b = b * a
  /-- Multiplication is associative -/
  mul_assoc : ∀ a b c : F, (a * b) * c = a * (b * c)
  /-- One is multiplicative identity -/
  mul_one : ∀ a : F, a * 1 = a
  /-- Distributivity -/
  mul_add : ∀ a b c : F, a * (b + c) = a * b + a * c
  /-- Multiplicative inverse law (for non-zero) -/
  mul_inv : ∀ a : F, isZero a = false → a * inv a = 1
  /-- Zero times anything is zero -/
  zero_mul : ∀ a : F, 0 * a = 0
  /-- Power of zero -/
  pow_zero : ∀ a : F, pow a 0 = 1
  /-- Power of one -/
  pow_one : ∀ a : F, pow a 1 = a
  /-- Power successor -/
  pow_succ : ∀ a : F, ∀ n : Nat, pow a (n + 1) = a * pow a n

/-! ## Part 3: Derived Theorems for NTTFieldLawful -/

namespace NTTFieldLawful

variable {F : Type*} [NTTFieldLawful F]

/-- Left additive identity -/
theorem zero_add (a : F) : 0 + a = a := by
  rw [add_comm, add_zero]

/-- One times a equals a -/
theorem one_mul (a : F) : 1 * a = a := by
  rw [mul_comm, mul_one]

/-- Right distributivity -/
theorem add_mul (a b c : F) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

/-- Left additive inverse -/
theorem neg_add (a : F) : (-a) + a = 0 := by
  rw [add_comm, add_neg]

/-- Zero negated is zero (derived: 0 + 0 = 0 so -0 = 0) -/
theorem neg_zero : (-(0 : F)) = 0 := by
  have h : (0 : F) + 0 = 0 := add_zero 0
  -- 0 + (-0) = 0, and 0 + 0 = 0, so -0 = 0 by uniqueness
  have h1 : 0 + (-0) = (0 : F) := add_neg 0
  -- We need: if a + b = 0 and a + c = 0 then b = c
  -- From 0 + 0 = 0 and 0 + (-0) = 0:
  calc -(0 : F) = 0 + (-(0 : F)) := by rw [zero_add]
    _ = (0 + 0) + (-(0 : F)) := by rw [add_zero]
    _ = 0 + (0 + (-(0 : F))) := by rw [add_assoc]
    _ = 0 + 0 := by rw [add_neg]
    _ = 0 := by rw [add_zero]

/-- Uniqueness of additive inverse: if a + b = 0 then b = -a -/
theorem eq_neg_of_add_eq_zero (a b : F) (h : a + b = 0) : b = -a := by
  calc b = 0 + b := by rw [zero_add]
    _ = ((-a) + a) + b := by rw [neg_add]
    _ = (-a) + (a + b) := by rw [add_assoc]
    _ = (-a) + 0 := by rw [h]
    _ = -a := by rw [add_zero]

/-- Double negation: -(-a) = a -/
theorem neg_neg (a : F) : -(-a) = a := by
  symm
  apply eq_neg_of_add_eq_zero
  exact neg_add a

/-- Negation distributes over multiplication (left): (-a) * b = -(a * b) -/
theorem neg_mul (a b : F) : (-a) * b = -(a * b) := by
  apply eq_neg_of_add_eq_zero
  calc (a * b) + ((-a) * b) = (a + (-a)) * b := by rw [← add_mul]
    _ = 0 * b := by rw [add_neg]
    _ = 0 := by rw [zero_mul]

/-- Negation distributes over multiplication (right): a * (-b) = -(a * b) -/
theorem mul_neg (a b : F) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

/-- Multiplication by -1 (left): (-1) * a = -a -/
theorem neg_one_mul (a : F) : (-1) * a = -a := by
  rw [neg_mul, one_mul]

/-- Multiplication by -1 (right): a * (-1) = -a -/
theorem mul_neg_one (a : F) : a * (-1) = -a := by
  rw [mul_comm, neg_one_mul]

/-- Subtraction of negative: a - (-b) = a + b -/
theorem sub_neg (a b : F) : a - (-b) = a + b := by
  rw [sub_def, neg_neg]

/-- Negation distributes over subtraction: -(a - b) = -a + b -/
theorem neg_sub (a b : F) : -(a - b) = -a + b := by
  rw [sub_def]
  -- Need: -(a + (-b)) = -a + b
  -- Show (a + (-b)) + (-a + b) = 0, then by uniqueness -a + b = -(a + (-b))
  symm
  apply eq_neg_of_add_eq_zero
  calc (a + (-b)) + (-a + b)
      = a + ((-b) + (-a + b)) := by rw [add_assoc]
    _ = a + ((-b) + ((-a) + b)) := by rfl
    _ = a + (((-b) + (-a)) + b) := by rw [← add_assoc (-b)]
    _ = a + (((-a) + (-b)) + b) := by rw [add_comm (-b) (-a)]
    _ = a + ((-a) + ((-b) + b)) := by rw [add_assoc (-a)]
    _ = a + ((-a) + 0) := by rw [neg_add]
    _ = a + (-a) := by rw [add_zero]
    _ = 0 := by rw [add_neg]

/-- Power of 2 -/
theorem pow_two (a : F) : NTTField.pow a 2 = a * a := by
  rw [show (2 : Nat) = 1 + 1 by rfl, pow_succ, pow_one]

/-- Power addition law -/
theorem pow_add (a : F) (m n : Nat) : NTTField.pow a (m + n) = NTTField.pow a m * NTTField.pow a n := by
  induction n with
  | zero => simp [pow_zero, mul_one]
  | succ n ih =>
    -- Goal: pow a (m + (n + 1)) = pow a m * pow a (n + 1)
    rw [Nat.add_succ, pow_succ, ih, pow_succ]
    -- Now: a * (pow a m * pow a n) = pow a m * (a * pow a n)
    -- Use associativity and commutativity
    rw [← mul_assoc, mul_comm a (NTTField.pow a m), mul_assoc]

/-- Power multiplication law -/
theorem pow_mul (a : F) (m n : Nat) : NTTField.pow a (m * n) = NTTField.pow (NTTField.pow a m) n := by
  induction n with
  | zero => simp [Nat.mul_zero, pow_zero]
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, ih, pow_succ, mul_comm]

end NTTFieldLawful

/-! ## Part 4: CommMonoid Instance

This allows using Mathlib's IsPrimitiveRoot with our NTTField.
IsPrimitiveRoot only requires CommMonoid, which is lightweight.
-/

/-- Convert NTTFieldLawful to CommMonoid for Mathlib compatibility.

This allows us to use `IsPrimitiveRoot` from Mathlib without
importing the full Field hierarchy.
-/
instance instCommMonoidOfNTTFieldLawful (F : Type*) [NTTFieldLawful F] : CommMonoid F where
  mul := (· * ·)
  one := 1
  mul_assoc := NTTFieldLawful.mul_assoc
  one_mul := NTTFieldLawful.one_mul
  mul_one := NTTFieldLawful.mul_one
  mul_comm := NTTFieldLawful.mul_comm

/-! ## Part 5: Helper Functions for NTT -/

namespace NTTField

variable {F : Type*} [NTTField F]

/-- Compute ω^i for a given twiddle factor -/
def twiddle (omega : F) (i : Nat) : F := pow omega i

/-- Compute n⁻¹ mod p (needed for inverse NTT normalization) -/
def invN (n : Nat) : F :=
  inv (pow 1 0 + (List.range (n - 1)).foldl (fun acc _ => acc + 1) 0)

end NTTField

end AmoLean.NTT
