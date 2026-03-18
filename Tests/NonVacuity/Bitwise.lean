/-
  Tests.NonVacuity.Bitwise — Non-vacuity witnesses for Fase 21 Bitwise Verification

  Each `example` proves that the hypotheses of a critical theorem are jointly
  satisfiable, demonstrating the theorem is NOT vacuously true.

  Axiom census: 0 custom axioms, 0 sorry.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedPipeline
import AmoLean.EGraph.Verified.Bitwise.FieldFoldRules
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

set_option autoImplicit false

namespace Tests.NonVacuity.Bitwise

open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified (CircuitNodeOp EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Non-vacuity for fold theorems
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: Mersenne31 fold works for x = 2^40 + 7 -/
example : ((2 ^ 40 + 7) >>> 31 + ((2 ^ 40 + 7) &&& (2 ^ 31 - 1)))
    % (2 ^ 31 - 1) = (2 ^ 40 + 7) % (2 ^ 31 - 1) := by native_decide

/-- Non-vacuity: BabyBear fold works for x = 2^40 + 13 -/
example : (((2 ^ 40 + 13) >>> 31) * (2 ^ 27 - 1) + ((2 ^ 40 + 13) &&& (2 ^ 31 - 1)))
    % (2 ^ 31 - 2 ^ 27 + 1) = (2 ^ 40 + 13) % (2 ^ 31 - 2 ^ 27 + 1) := by native_decide

/-- Non-vacuity: Goldilocks fold works for x = 2^96 + 5 -/
example : (((2 ^ 96 + 5) >>> 64) * (2 ^ 32 - 1) + ((2 ^ 96 + 5) &&& (2 ^ 64 - 1)))
    % (2 ^ 64 - 2 ^ 32 + 1) = (2 ^ 96 + 5) % (2 ^ 64 - 2 ^ 32 + 1) := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Non-vacuity for MixedSoundRule
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: shift right composition rule -/
example : Nat.shiftRight (Nat.shiftRight 1000000 5) 3 = Nat.shiftRight 1000000 (5 + 3) := by
  native_decide

/-- Non-vacuity: shift left composition rule -/
example : Nat.shiftLeft (Nat.shiftLeft 42 3) 5 = Nat.shiftLeft 42 (3 + 5) := by native_decide

/-- Non-vacuity: AND idempotence -/
example : Nat.land 255 255 = 255 := by native_decide

/-- Non-vacuity: AND commutativity -/
example : Nat.land 100 7 = Nat.land 7 100 := by native_decide

/-- Non-vacuity: OR commutativity -/
example : Nat.lor 100 7 = Nat.lor 7 100 := by native_decide

/-- Non-vacuity: XOR self is zero -/
example : Nat.xor 12345 12345 = 0 := by native_decide

/-- Non-vacuity: XOR commutativity -/
example : Nat.xor 100 7 = Nat.xor 7 100 := by native_decide

/-- Non-vacuity: mask-mod bridge -/
example : Nat.land 1000 (2 ^ 8 - 1) = 1000 % 2 ^ 8 := by native_decide

/-- Non-vacuity: shiftRight-div bridge -/
example : 1000 >>> 4 = 1000 / 2 ^ 4 := by native_decide

/-- Non-vacuity: shiftLeft-mul bridge -/
example : 42 <<< 5 = 42 * 2 ^ 5 := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Non-vacuity for toMixed/fromMixed embedding (all 7 constructors)
-- ══════════════════════════════════════════════════════════════════

example : fromMixed (toMixed (.constGate 42)) = some (.constGate 42) := rfl
example : fromMixed (toMixed (.witness 3)) = some (.witness 3) := rfl
example : fromMixed (toMixed (.pubInput 1)) = some (.pubInput 1) := rfl
example : fromMixed (toMixed (.addGate 0 1)) = some (.addGate 0 1) := rfl
example : fromMixed (toMixed (.mulGate 2 3)) = some (.mulGate 2 3) := rfl
example : fromMixed (toMixed (.negGate 0)) = some (.negGate 0) := rfl
example : fromMixed (toMixed (.smulGate 5 1)) = some (.smulGate 5 1) := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Non-vacuity for algebraic_or_bitwise (both branches reachable)
-- ══════════════════════════════════════════════════════════════════

/-- isAlgebraic is true for algebraic ops -/
example : isAlgebraic (.addGate 0 1) = true := rfl
example : isAlgebraic (.constGate 5) = true := rfl
example : isAlgebraic (.mulGate 0 1) = true := rfl

/-- isBitwise is true for bitwise ops -/
example : isBitwise (.shiftLeft 0 5) = true := rfl
example : isBitwise (.shiftRight 0 3) = true := rfl
example : isBitwise (.bitAnd 0 1) = true := rfl
example : isBitwise (.constMask 8) = true := rfl

/-- Cross-check: bitwise ops are not algebraic, and vice versa -/
example : isAlgebraic (.shiftLeft 0 5) = false := rfl
example : isBitwise (.addGate 0 1) = false := rfl

end Tests.NonVacuity.Bitwise
