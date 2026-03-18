/-
  AmoLean.EGraph.Verified.Bitwise.OverflowBounds — Bitwise operations preserve bounds

  B68 (HOJA independiente): Proves that bitwise ops preserve width bounds,
  and that pure-bitwise MixedExpr evaluation is bounded.

  Deliverables:
  - Single-value bounds for bitwise ops (AND, OR, XOR, shift)
  - evalMixed_bitwise_bounded: pure bitwise MixedExpr evaluates within bounds
-/
import AmoLean.EGraph.Verified.Bitwise.MixedExtract

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.OverflowBounds

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Single-value bounds for bitwise ops
-- ══════════════════════════════════════════════════════════════════

/-- AND result is bounded by the right operand. -/
theorem val_land_bounded (a b w : Nat) (hb : b < 2 ^ w) :
    Nat.land a b < 2 ^ w :=
  Nat.lt_of_le_of_lt Nat.and_le_right hb

/-- OR result is bounded when both operands are bounded (via Nat.lor_lt_two_pow). -/
theorem val_lor_bounded (a b w : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.lor a b < 2 ^ w := by
  exact Nat.lor_lt_two_pow ha hb

/-- XOR result is bounded when both operands are bounded. -/
theorem val_xor_bounded (a b w : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.xor a b < 2 ^ w := by
  exact Nat.xor_lt_two_pow ha hb

/-- Right shift always reduces the value. -/
theorem val_shiftRight_bounded (a n w : Nat) (ha : a < 2 ^ w) :
    a >>> n < 2 ^ w :=
  Nat.lt_of_le_of_lt (Nat.shiftRight_le a n) ha

/-- Left shift grows bounds by the shift amount. -/
theorem val_shiftLeft_bounded (a n w : Nat) (ha : a < 2 ^ w) :
    a <<< n < 2 ^ (w + n) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos n)

/-- Constant mask (2^n - 1) is bounded by width n. -/
theorem val_constMask_bounded (n : Nat) : 2 ^ n - 1 < 2 ^ n :=
  Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos

-- ══════════════════════════════════════════════════════════════════
-- Section 2: IsBitwiseOnly + evalMixed_bitwise_bounded
-- ══════════════════════════════════════════════════════════════════

/-- Predicate: expression uses only non-growing bitwise operations. -/
def IsBitwiseOnly : MixedExpr → Bool
  | .constE _        => true
  | .witnessE _      => true
  | .pubInputE _     => true
  | .addE _ _        => false
  | .mulE _ _        => false
  | .negE _          => true
  | .smulE _ _       => false
  | .shiftLeftE _ _  => false
  | .shiftRightE a _ => IsBitwiseOnly a
  | .bitAndE a b     => IsBitwiseOnly a && IsBitwiseOnly b
  | .bitXorE a b     => IsBitwiseOnly a && IsBitwiseOnly b
  | .bitOrE a b      => IsBitwiseOnly a && IsBitwiseOnly b
  | .constMaskE _    => false

/-- All environment values bounded at width w. -/
def BoundedEnv (env : MixedEnv) (w : Nat) : Prop :=
  (∀ i, env.constVal i < 2 ^ w) ∧
  (∀ i, env.witnessVal i < 2 ^ w) ∧
  (∀ i, env.pubInputVal i < 2 ^ w)

/-- Pure bitwise expressions preserve the width bound. -/
theorem evalMixed_bitwise_bounded (e : MixedExpr) (env : MixedEnv) (w : Nat)
    (henv : BoundedEnv env w) (hbw : IsBitwiseOnly e = true) :
    e.eval env < 2 ^ w := by
  induction e with
  | constE n => exact henv.1 n
  | witnessE n => exact henv.2.1 n
  | pubInputE n => exact henv.2.2 n
  | addE _ _ => simp [IsBitwiseOnly] at hbw
  | mulE _ _ => simp [IsBitwiseOnly] at hbw
  | negE _ => simp [MixedExpr.eval]; exact Nat.two_pow_pos w
  | smulE _ _ => simp [IsBitwiseOnly] at hbw
  | shiftLeftE _ _ => simp [IsBitwiseOnly] at hbw
  | constMaskE _ => simp [IsBitwiseOnly] at hbw
  | shiftRightE a n ih =>
    simp [IsBitwiseOnly] at hbw
    simp only [MixedExpr.eval]
    exact val_shiftRight_bounded _ n w (ih hbw)
  | bitAndE a b iha ihb =>
    simp [IsBitwiseOnly, Bool.and_eq_true] at hbw
    simp only [MixedExpr.eval]
    exact val_land_bounded _ _ w (ihb hbw.2)
  | bitXorE a b iha ihb =>
    simp [IsBitwiseOnly, Bool.and_eq_true] at hbw
    simp only [MixedExpr.eval]
    exact val_xor_bounded _ _ w (iha hbw.1) (ihb hbw.2)
  | bitOrE a b iha ihb =>
    simp [IsBitwiseOnly, Bool.and_eq_true] at hbw
    simp only [MixedExpr.eval]
    exact val_lor_bounded _ _ w (iha hbw.1) (ihb hbw.2)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: AND preserves 8-bit bounds. -/
example : Nat.land 0xFF 0x0F < 2 ^ 8 := by native_decide

/-- Smoke: shift right preserves bounds. -/
example : (256 >>> 4) < 2 ^ 9 :=
  val_shiftRight_bounded 256 4 9 (by omega)

/-- Smoke: constMask is bounded. -/
example : 2 ^ 8 - 1 < 2 ^ 8 := val_constMask_bounded 8

/-- Smoke: bitwise expression bounded. -/
example : IsBitwiseOnly (.bitAndE (.witnessE 0) (.witnessE 1)) = true := rfl

end AmoLean.EGraph.Verified.Bitwise.OverflowBounds
