/-
  AMO-Lean: NTT Field Type Class
  Phase 5: NTT Core - Task 1.1

  Type class for fields supporting NTT operations.

  Design Decision DD-013 (REVISED):
  NTTField now extends CommRing from Mathlib to avoid typeclass diamonds.
  This ensures that:
  1. There is only ONE definition of 0, 1, +, *, -, etc.
  2. Mathlib tactics (ring, simp, etc.) work automatically
  3. Finset.sum and BigOperators integrate seamlessly

  The specific NTT operations (inv, pow, char, isZero) are still defined here.
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Defs

namespace AmoLean.NTT

/-! ## Part 1: NTTField Type Class

A field suitable for NTT must support:
- Ring operations (from CommRing)
- Multiplicative inverse (for non-zero elements)
- A characteristic (prime p)
- Exponentiation

NTTField extends CommRing to inherit all algebraic structure from Mathlib.
-/

/-- Type class for fields supporting NTT operations.

    Extends CommRing to integrate with Mathlib's algebraic hierarchy.
    This eliminates typeclass diamonds for Zero, Add, Mul, etc.

    The NTT-specific fields are:
    - inv: Multiplicative inverse (returns 0 for 0 as sentinel)
    - char: Field characteristic (prime order)
    - isZero: Efficient zero check

    Note: Exponentiation uses the standard ^ operator from Monoid (via CommRing).
    This ensures compatibility with Mathlib tactics (ring, simp, etc.).
-/
class NTTField (F : Type*) extends CommRing F where
  /-- Multiplicative inverse. Returns 0 for input 0 (sentinel). -/
  inv : F → F
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

Since NTTField now extends CommRing, all algebraic laws come from Mathlib.
NTTFieldLawful adds only the NTT-specific laws (for pow and inv).
-/

/-- NTTField with laws for NTT-specific operations.

    The algebraic laws (add_comm, mul_assoc, etc.) come from CommRing.
    Power laws (pow_zero, pow_succ, etc.) come from Monoid.
    This class adds laws for the NTT-specific inv operation.
-/
class NTTFieldLawful (F : Type*) extends NTTField F where
  /-- Multiplicative inverse law (for non-zero) -/
  mul_inv : ∀ a : F, isZero a = false → a * inv a = 1

/-! ## Part 3: Derived Theorems for NTTFieldLawful

    All algebraic laws come from CommRing (via Mathlib).
    All power laws come from Monoid (via CommRing).
    No additional theorems needed here - use Mathlib's pow_zero, pow_succ,
    pow_add, pow_mul directly.
-/

namespace NTTFieldLawful

variable {F : Type*} [NTTFieldLawful F]

-- Power laws are now available from Monoid:
-- - pow_zero : a ^ 0 = 1
-- - pow_succ : a ^ (n + 1) = a * a ^ n
-- - pow_add : a ^ (m + n) = a ^ m * a ^ n
-- - pow_mul : a ^ (m * n) = (a ^ m) ^ n
-- - sq : a ^ 2 = a * a

end NTTFieldLawful

/-! ## Part 4: CommMonoid Instance

    Note: CommMonoid is now automatically available from CommRing.
    The explicit instance is no longer needed.
-/

/-! ## Part 5: Helper Functions for NTT -/

namespace NTTField

variable {F : Type*} [NTTField F]

/-- Compute ω^i for a given twiddle factor -/
def twiddle (omega : F) (i : Nat) : F := omega ^ i

/-- Compute n⁻¹ mod p (needed for inverse NTT normalization) -/
def invN (n : Nat) : F :=
  inv ((1 : F) ^ 0 + (List.range (n - 1)).foldl (fun acc _ => acc + 1) 0)

end NTTField

end AmoLean.NTT
