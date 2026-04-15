import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge
import Mathlib.Data.Nat.Bitwise

/-!
# AmoLean.EGraph.Verified.Bitwise.BitVecBridge

BitVec dual representation for MixedNodeOp evaluation.

evalMixedOp operates on Nat (concrete arithmetic). This module provides a
PARALLEL evaluation on BitVec for code emission verification and proves that
for values within bit width, Nat evaluation = BitVec.toNat evaluation.

## Architecture

1. **evalMixedBV**: Mirrors evalMixedOp but evaluates on `BitVec w`
2. **InBounds / EnvInBounds**: Predicates bounding values to `< 2^w`
3. **liftBV**: Lifts a bounded Nat valuation to BitVec
4. **Per-operation bridges**: One theorem per MixedNodeOp constructor
   - Bitwise (AND, OR, XOR, shiftRight): unconditional
   - shiftLeft, constMask: conditional on width/overflow
   - Arithmetic (add, mul, smul): conditional on no overflow
   - Constants/witnesses: conditional on EnvInBounds
5. **Master bridges**: Combined theorems for bitwise and arithmetic classes

## Key results

- `bridge_bitAnd`, `bridge_bitOr`, `bridge_bitXor`, `bridge_shiftRight`:
    Unconditional — InBounds alone suffices
- `bridge_shiftLeft`: Conditional on no overflow (shiftLeft < 2^w)
- `bridge_addGate`, `bridge_mulGate`, `bridge_smulGate`:
    Conditional on ArithNoOverflow
- `evalMixed_bv_agree_nonexpanding`: Master theorem for non-expanding bitwise ops
- `evalMixed_bv_agree`: Full capstone bridge (all 13 constructors)
- `evalMixed_bv_agree_mod`: Unconditional modular bridge (equality mod 2^w)

## Mathlib coverage

All proofs use Lean core BitVec lemmas (toNat_and, toNat_or, toNat_xor,
toNat_shiftLeft, toNat_ushiftRight, toNat_add, toNat_mul, toNat_ofNat)
plus Mathlib Nat bounds (and_lt_two_pow, or_lt_two_pow, xor_lt_two_pow).
No gaps found — all bridges are sorry-free.

## References

- BitwiseBridge.lean (Nat-level bridges)
- MixedNodeOp.lean (evalMixedOp definition)
- TrustHash chi5/chiNat pattern (dual representation for verification)
-/

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified (CircuitNodeOp CircuitEnv EClassId)

set_option autoImplicit false

/-! ## BitVec evaluation function -/

/-- Evaluate a MixedNodeOp on `BitVec w`, mirroring `evalMixedOp` but in the
    bitvector world. Arithmetic wraps mod `2^w`; bitwise ops are exact.
    Constants and witnesses are projected from the environment and truncated. -/
def evalMixedBV (w : Nat) (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → BitVec w) : BitVec w :=
  match op with
  -- Algebraic (mirror evalMixedOp)
  | .constGate n    => BitVec.ofNat w (env.constVal n)
  | .witness n      => BitVec.ofNat w (env.witnessVal n)
  | .pubInput n     => BitVec.ofNat w (env.pubInputVal n)
  | .addGate a b    => v a + v b
  | .mulGate a b    => v a * v b
  | .negGate _      => BitVec.ofNat w 0
  | .smulGate n a   => BitVec.ofNat w (env.constVal n) * v a
  -- Bitwise
  | .shiftLeft a n  => v a <<< n
  | .shiftRight a n => v a >>> n
  | .bitAnd a b     => v a &&& v b
  | .bitXor a b     => v a ^^^ v b
  | .bitOr a b      => v a ||| v b
  | .constMask n    => BitVec.ofNat w (2 ^ n - 1)
  | .subGate a b    => v a - v b
  | .reduceGate a p   => BitVec.ofNat w ((v a).toNat % p)
  | .kronPack a b ww  => BitVec.ofNat w ((v a).toNat + (v b).toNat * 2 ^ ww)
  | .kronUnpackLo a ww => BitVec.ofNat w ((v a).toNat % 2 ^ ww)
  | .kronUnpackHi a ww => BitVec.ofNat w ((v a).toNat / 2 ^ ww)
  -- Modular reduction alternatives: all semantically x % p
  | .montyReduce a p _mu   => BitVec.ofNat w ((v a).toNat % p)
  | .barrettReduce a p _m  => BitVec.ofNat w ((v a).toNat % p)
  | .harveyReduce a p      => BitVec.ofNat w ((v a).toNat % p)
  | .conditionalSub a p    =>
    let va := (v a).toNat; BitVec.ofNat w (if va ≥ p then va - p else va)

/-! ## Boundedness predicates -/

/-- All values in a Nat valuation are within bit width `w`. -/
def InBounds (w : Nat) (v : EClassId → Nat) : Prop :=
  ∀ (id : EClassId), v id < 2 ^ w

/-- All environment values (constants, witnesses, public inputs) are within bit width `w`. -/
def EnvInBounds (w : Nat) (env : MixedEnv) : Prop :=
  (∀ (n : Nat), env.constVal n < 2 ^ w) ∧
  (∀ (n : Nat), env.witnessVal n < 2 ^ w) ∧
  (∀ (n : Nat), env.pubInputVal n < 2 ^ w)

/-- An arithmetic operation does not overflow at bit width `w`. -/
def ArithNoOverflow (w : Nat) (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → Nat) : Prop :=
  match op with
  | .addGate a b    => v a + v b < 2 ^ w
  | .mulGate a b    => v a * v b < 2 ^ w
  | .smulGate n a   => env.constVal n * v a < 2 ^ w
  | .shiftLeft a n  => Nat.shiftLeft (v a) n < 2 ^ w
  | .subGate a b    => v b ≤ v a
  | .reduceGate a p   => v a % p < 2 ^ w
  | .kronPack a b ww  => v a + v b * 2 ^ ww < 2 ^ w
  | .kronUnpackLo a ww => v a % 2 ^ ww < 2 ^ w
  | .kronUnpackHi a ww => v a / 2 ^ ww < 2 ^ w
  | .montyReduce a p _   => v a % p < 2 ^ w
  | .barrettReduce a p _ => v a % p < 2 ^ w
  | .harveyReduce a p    => v a % p < 2 ^ w
  | .conditionalSub a p  => (if v a ≥ p then v a - p else v a) < 2 ^ w
  | _               => True

/-! ## Lifting: Nat valuation → BitVec valuation -/

/-- Lift a Nat valuation to a BitVec valuation by truncation. -/
def liftBV (w : Nat) (v : EClassId → Nat) : EClassId → BitVec w :=
  fun id => BitVec.ofNat w (v id)

/-- liftBV roundtrip: `toNat ∘ liftBV = v` when all values are in bounds. -/
theorem liftBV_toNat (w : Nat) (v : EClassId → Nat) (hb : InBounds w v)
    (id : EClassId) :
    (liftBV w v id).toNat = v id := by
  simp [liftBV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb id)]

/-! ## Elementary BitVec bridge lemmas (Nat ↔ BitVec) -/

/-- AND on Nat agrees with AND on BitVec. -/
theorem nat_land_eq_bv_and (a b : Nat) (w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.land a b = (BitVec.ofNat w a &&& BitVec.ofNat w b).toNat := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

/-- OR on Nat agrees with OR on BitVec. -/
theorem nat_lor_eq_bv_or (a b : Nat) (w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.lor a b = (BitVec.ofNat w a ||| BitVec.ofNat w b).toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

/-- XOR on Nat agrees with XOR on BitVec. -/
theorem nat_xor_eq_bv_xor (a b : Nat) (w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.xor a b = (BitVec.ofNat w a ^^^ BitVec.ofNat w b).toNat := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

/-- Right shift on Nat agrees with unsigned right shift on BitVec. -/
theorem nat_shiftRight_eq_bv_ushiftRight (a : Nat) (n w : Nat)
    (ha : a < 2 ^ w) :
    Nat.shiftRight a n = (BitVec.ofNat w a >>> n).toNat := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rfl

/-- Left shift on Nat agrees with left shift on BitVec when no overflow occurs. -/
theorem nat_shiftLeft_eq_bv_shiftLeft (a : Nat) (n w : Nat)
    (ha : a < 2 ^ w) (hno : a <<< n < 2 ^ w) :
    Nat.shiftLeft a n = (BitVec.ofNat w a <<< n).toNat := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  exact (Nat.mod_eq_of_lt hno).symm

/-- Addition on Nat agrees with addition on BitVec when no overflow occurs. -/
theorem nat_add_eq_bv_add (a b : Nat) (w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hsum : a + b < 2 ^ w) :
    a + b = (BitVec.ofNat w a + BitVec.ofNat w b).toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hsum]

/-- Multiplication on Nat agrees with multiplication on BitVec when no overflow occurs. -/
theorem nat_mul_eq_bv_mul (a b : Nat) (w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hprod : a * b < 2 ^ w) :
    a * b = (BitVec.ofNat w a * BitVec.ofNat w b).toNat := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hprod]

/-- Constant mask `2^n - 1` agrees with its BitVec representation when `n ≤ w`. -/
theorem constMask_eq_bv (n w : Nat) (hn : n ≤ w) :
    2 ^ n - 1 = (BitVec.ofNat w (2 ^ n - 1)).toNat := by
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos)
    (Nat.pow_le_pow_right (by omega) hn))).symm

/-! ## Bitwise bounds preservation -/

/-- AND preserves InBounds (unconditional: result ≤ right operand). -/
theorem land_lt_two_pow (a b w : Nat) (hb : b < 2 ^ w) :
    Nat.land a b < 2 ^ w := by
  have : a &&& b < 2 ^ w := Nat.and_lt_two_pow a hb
  exact this

/-- OR preserves InBounds. -/
theorem lor_lt_two_pow (a b w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.lor a b < 2 ^ w := by
  have : a ||| b < 2 ^ w := Nat.or_lt_two_pow ha hb
  exact this

/-- XOR preserves InBounds. -/
theorem xor_lt_two_pow (a b w : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.xor a b < 2 ^ w := by
  have : a ^^^ b < 2 ^ w := Nat.xor_lt_two_pow ha hb
  exact this

/-- Right shift preserves InBounds (result ≤ original). -/
theorem shiftRight_lt_two_pow (a n w : Nat) (ha : a < 2 ^ w) :
    Nat.shiftRight a n < 2 ^ w :=
  Nat.lt_of_le_of_lt (Nat.shiftRight_le a n) ha

/-- Constant mask is in bounds when `n ≤ w`. -/
theorem constMask_lt_two_pow (n w : Nat) (hn : n ≤ w) :
    2 ^ n - 1 < 2 ^ w :=
  Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos)
    (Nat.pow_le_pow_right (by omega) hn)

/-! ## Per-operation bridge theorems -/

/-- bitAnd bridge: unconditional (InBounds suffices). -/
theorem bridge_bitAnd (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a b : EClassId) :
    evalMixedOp (.bitAnd a b) env v =
    (evalMixedBV w (.bitAnd a b) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
  rfl

/-- bitOr bridge: unconditional (InBounds suffices). -/
theorem bridge_bitOr (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a b : EClassId) :
    evalMixedOp (.bitOr a b) env v =
    (evalMixedBV w (.bitOr a b) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
  rfl

/-- bitXor bridge: unconditional (InBounds suffices). -/
theorem bridge_bitXor (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a b : EClassId) :
    evalMixedOp (.bitXor a b) env v =
    (evalMixedBV w (.bitXor a b) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
  rfl

/-- shiftRight bridge: unconditional (shift right never increases value). -/
theorem bridge_shiftRight (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a : EClassId) (n : Nat) :
    evalMixedOp (.shiftRight a n) env v =
    (evalMixedBV w (.shiftRight a n) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  rfl

/-- shiftLeft bridge: conditional on no overflow. -/
theorem bridge_shiftLeft (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a : EClassId) (n : Nat)
    (hno : Nat.shiftLeft (v a) n < 2 ^ w) :
    evalMixedOp (.shiftLeft a n) env v =
    (evalMixedBV w (.shiftLeft a n) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  exact (Nat.mod_eq_of_lt hno).symm

/-- constMask bridge: conditional on `n ≤ w`. -/
theorem bridge_constMask (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (n : Nat) (hn : n ≤ w) :
    evalMixedOp (.constMask n) env v =
    (evalMixedBV w (.constMask n) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV]
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (constMask_lt_two_pow n w hn)).symm

/-- addGate bridge: conditional on no overflow. -/
theorem bridge_addGate (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a b : EClassId) (hno : v a + v b < 2 ^ w) :
    evalMixedOp (.addGate a b) env v =
    (evalMixedBV w (.addGate a b) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
      Nat.mod_eq_of_lt hno]

/-- subGate bridge: conditional on no underflow (Nat subtraction agrees with BitVec subtraction).
    When `v b ≤ v a`, the Nat subtraction `v a - v b` equals `(liftBV a - liftBV b).toNat`.
    Note: requires both no-underflow (v b ≤ v a) and result in bounds. -/
theorem bridge_subGate (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a b : EClassId)
    (hle : v b ≤ v a) :
    evalMixedOp (.subGate a b) env v =
    (evalMixedBV w (.subGate a b) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
  -- Goal: v a - v b = (2 ^ w - v b + v a) % 2 ^ w
  have ha := hb a
  have hb' := hb b
  have hsub_lt : v a - v b < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
  -- Rewrite: 2^w - v b + v a = (v a - v b) + 2^w
  have key : 2 ^ w - v b + v a = v a - v b + 2 ^ w := by
    have h1 : v b ≤ 2 ^ w := Nat.le_of_lt hb'
    have h2 : v b ≤ v a := hle
    omega
  rw [key, Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]

/-- mulGate bridge: conditional on no overflow. -/
theorem bridge_mulGate (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (a b : EClassId) (hno : v a * v b < 2 ^ w) :
    evalMixedOp (.mulGate a b) env v =
    (evalMixedBV w (.mulGate a b) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
      Nat.mod_eq_of_lt hno]

/-- smulGate bridge: conditional on no overflow and env in bounds. -/
theorem bridge_smulGate (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (hb : InBounds w v) (henv : EnvInBounds w env)
    (n : Nat) (a : EClassId) (hno : env.constVal n * v a < 2 ^ w) :
    evalMixedOp (.smulGate n a) env v =
    (evalMixedBV w (.smulGate n a) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV, liftBV]
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (henv.1 n), Nat.mod_eq_of_lt (hb a),
      Nat.mod_eq_of_lt hno]

/-- negGate bridge: unconditional (always 0). -/
theorem bridge_negGate (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (a : EClassId) :
    evalMixedOp (.negGate a) env v =
    (evalMixedBV w (.negGate a) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV]
  rw [BitVec.toNat_ofNat]
  exact (Nat.zero_mod (2 ^ w)).symm

/-- constGate bridge: conditional on EnvInBounds. -/
theorem bridge_constGate (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (henv : EnvInBounds w env) (n : Nat) :
    evalMixedOp (.constGate n) env v =
    (evalMixedBV w (.constGate n) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.1 n)]

/-- witness bridge: conditional on EnvInBounds. -/
theorem bridge_witness (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (henv : EnvInBounds w env) (n : Nat) :
    evalMixedOp (.witness n) env v =
    (evalMixedBV w (.witness n) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.2.1 n)]

/-- pubInput bridge: conditional on EnvInBounds. -/
theorem bridge_pubInput (w : Nat) (env : MixedEnv) (v : EClassId → Nat)
    (henv : EnvInBounds w env) (n : Nat) :
    evalMixedOp (.pubInput n) env v =
    (evalMixedBV w (.pubInput n) env (liftBV w v)).toNat := by
  simp only [evalMixedOp, evalMixedBV]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.2.2 n)]

/-! ## Non-expanding bitwise predicate -/

/-- A bitwise operation is *non-expanding*: the output is bounded by the inputs
    without any overflow condition. Covers AND, OR, XOR, shiftRight. -/
def isNonExpanding : MixedNodeOp → Bool
  | .bitAnd _ _     => true
  | .bitOr _ _      => true
  | .bitXor _ _     => true
  | .shiftRight _ _ => true
  | _               => false

/-- Non-expanding ops are a subset of bitwise ops. -/
theorem isNonExpanding_of_isBitwise (op : MixedNodeOp)
    (h : isNonExpanding op = true) : isBitwise op = true := by
  cases op <;> simp [isNonExpanding, isBitwise] at h ⊢

/-- Non-expanding bitwise ops preserve InBounds. -/
theorem nonExpanding_preserves_bounds (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → Nat) (w : Nat) (hb : InBounds w v)
    (hne : isNonExpanding op = true) :
    evalMixedOp op env v < 2 ^ w := by
  cases op <;> simp [isNonExpanding] at hne <;> simp only [evalMixedOp]
  case bitAnd a b =>
    exact land_lt_two_pow (v a) (v b) w (hb b)
  case bitOr a b =>
    exact lor_lt_two_pow (v a) (v b) w (hb a) (hb b)
  case bitXor a b =>
    exact xor_lt_two_pow (v a) (v b) w (hb a) (hb b)
  case shiftRight a n =>
    exact shiftRight_lt_two_pow (v a) n w (hb a)

/-! ## Master bridge theorems -/

/-- **Master bridge for non-expanding bitwise ops**: AND, OR, XOR, shiftRight.
    For these operations, `InBounds` alone suffices — no overflow condition needed.

    This is the key theorem for code emission: any non-expanding bitwise
    operation evaluated on Nat gives the same result as evaluating the
    corresponding BitVec operation and converting back with toNat. -/
theorem evalMixed_bv_agree_nonexpanding (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → Nat) (w : Nat) (hb : InBounds w v)
    (hne : isNonExpanding op = true) :
    evalMixedOp op env v =
    (evalMixedBV w op env (liftBV w v)).toNat := by
  cases op <;> simp [isNonExpanding] at hne <;> simp only [evalMixedOp, evalMixedBV, liftBV]
  case bitAnd a b =>
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rfl
  case bitOr a b =>
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rfl
  case bitXor a b =>
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rfl
  case shiftRight a n =>
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
    rfl

/-- **Master bridge for arithmetic ops**: add, mul, smul.
    Requires `InBounds`, `EnvInBounds`, and `ArithNoOverflow`. -/
theorem evalMixed_bv_agree_arith (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → Nat) (w : Nat)
    (hb : InBounds w v) (henv : EnvInBounds w env)
    (hno : ArithNoOverflow w op env v) :
    (isAlgebraic op = true) →
    evalMixedOp op env v =
    (evalMixedBV w op env (liftBV w v)).toNat := by
  intro halg
  cases op <;> simp [isAlgebraic] at halg <;>
    simp only [evalMixedOp, evalMixedBV, liftBV]
  case constGate n =>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.1 n)]
  case witness n =>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.2.1 n)]
  case pubInput n =>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.2.2 n)]
  case addGate a b =>
    have h : v a + v b < 2 ^ w := hno
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
        Nat.mod_eq_of_lt h]
  case mulGate a b =>
    have h : v a * v b < 2 ^ w := hno
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
        Nat.mod_eq_of_lt h]
  case negGate _ =>
    rw [BitVec.toNat_ofNat]
    exact (Nat.zero_mod (2 ^ w)).symm
  case smulGate n a =>
    have h : env.constVal n * v a < 2 ^ w := hno
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (henv.1 n), Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case subGate a b =>
    have hle : v b ≤ v a := hno
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    have hsub_lt : v a - v b < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hb a)
    have hbw : v b ≤ 2 ^ w := Nat.le_of_lt (hb b)
    have key : 2 ^ w - v b + v a = v a - v b + 2 ^ w := by
      calc 2 ^ w - v b + v a
          = 2 ^ w + v a - v b := by rw [Nat.sub_add_comm hbw]
        _ = 2 ^ w + (v a - v b) := by rw [Nat.add_sub_assoc hle]
        _ = v a - v b + 2 ^ w := by rw [Nat.add_comm]
    rw [key, Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]
  case reduceGate a p =>
    have h : v a % p < 2 ^ w := hno
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case kronPack a b ww =>
    have h : v a + v b * 2 ^ ww < 2 ^ w := hno
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
        Nat.mod_eq_of_lt h]
  case kronUnpackLo a ww =>
    have h : v a % 2 ^ ww < 2 ^ w := hno
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case kronUnpackHi a ww =>
    have h : v a / 2 ^ ww < 2 ^ w := hno
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case montyReduce a p mu =>
    have h : v a % p < 2 ^ w := hno
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case barrettReduce a p m =>
    have h : v a % p < 2 ^ w := hno
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case harveyReduce a p =>
    have h : v a % p < 2 ^ w := hno
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case conditionalSub a p =>
    have h : (if v a ≥ p then v a - p else v a) < 2 ^ w := hno
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt h]

/-! ## Full bridge (all ops) -/

/-- Operation-specific bounds required for exact (non-modular) BitVec agreement.

    **Contract**: For `constMask n`, requires `n ≤ w` (mask fits in bit width).
    The catch-all `| _ => True` covers operations with no additional bounds beyond
    `InBounds w v` (bitwise AND/OR/XOR, shifts within bounds, constants, witnesses).

    **Important**: Passing `constMask n` with `n > w` violates this contract and makes
    `evalMixed_bv_agree` vacuously true for that operation. In practice, `solinasFoldMixedExpr`
    always uses `cfg.a` which is validated upstream in `SolinasConfig`. -/
def OpInBounds (w : Nat) (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → Nat) : Prop :=
  match op with
  | .addGate a b    => v a + v b < 2 ^ w
  | .mulGate a b    => v a * v b < 2 ^ w
  | .smulGate n a   => env.constVal n * v a < 2 ^ w
  | .shiftLeft a n  => Nat.shiftLeft (v a) n < 2 ^ w
  | .subGate a b    => v b ≤ v a
  | .constMask n    => n ≤ w
  | .reduceGate a p   => v a % p < 2 ^ w
  | .kronPack a b ww  => v a + v b * 2 ^ ww < 2 ^ w
  | .kronUnpackLo a ww => v a % 2 ^ ww < 2 ^ w
  | .kronUnpackHi a ww => v a / 2 ^ ww < 2 ^ w
  | .montyReduce a p _   => v a % p < 2 ^ w
  | .barrettReduce a p _ => v a % p < 2 ^ w
  | .harveyReduce a p    => v a % p < 2 ^ w
  | .conditionalSub a p  => (if v a ≥ p then v a - p else v a) < 2 ^ w
  | _               => True

/-- **Full bridge**: for ANY MixedNodeOp, if values and environment are in bounds
    and the operation-specific overflow condition holds, then Nat evaluation
    agrees with BitVec.toNat evaluation.

    This is the capstone theorem: it unifies all per-operation bridges into a
    single statement suitable for code emission verification. -/
theorem evalMixed_bv_agree (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → Nat) (w : Nat)
    (hb : InBounds w v) (henv : EnvInBounds w env)
    (hop : OpInBounds w op env v) :
    evalMixedOp op env v =
    (evalMixedBV w op env (liftBV w v)).toNat := by
  cases op <;> simp only [evalMixedOp, evalMixedBV, liftBV]
  case constGate n =>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.1 n)]
  case witness n =>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.2.1 n)]
  case pubInput n =>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (henv.2.2 n)]
  case addGate a b =>
    have hno : v a + v b < 2 ^ w := hop
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
        Nat.mod_eq_of_lt hno]
  case mulGate a b =>
    have hno : v a * v b < 2 ^ w := hop
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
        Nat.mod_eq_of_lt hno]
  case negGate _ =>
    rw [BitVec.toNat_ofNat]
    exact (Nat.zero_mod (2 ^ w)).symm
  case smulGate n a =>
    have hno : env.constVal n * v a < 2 ^ w := hop
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (henv.1 n), Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt hno]
  case subGate a b =>
    have hle : v b ≤ v a := hop
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    have hsub_lt : v a - v b < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hb a)
    have hbw : v b ≤ 2 ^ w := Nat.le_of_lt (hb b)
    have key : 2 ^ w - v b + v a = v a - v b + 2 ^ w := by
      calc 2 ^ w - v b + v a
          = 2 ^ w + v a - v b := by rw [Nat.sub_add_comm hbw]
        _ = 2 ^ w + (v a - v b) := by rw [Nat.add_sub_assoc hle]
        _ = v a - v b + 2 ^ w := by rw [Nat.add_comm]
    rw [key, Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]
  case shiftLeft a n =>
    have hno : Nat.shiftLeft (v a) n < 2 ^ w := hop
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
    exact (Nat.mod_eq_of_lt hno).symm
  case shiftRight a n =>
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
    rfl
  case bitAnd a b =>
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rfl
  case bitXor a b =>
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rfl
  case bitOr a b =>
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rfl
  case constMask n =>
    have hn : n ≤ w := hop
    rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (constMask_lt_two_pow n w hn)).symm
  case reduceGate a p =>
    have h : v a % p < 2 ^ w := hop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case kronPack a b ww =>
    have h : v a + v b * 2 ^ ww < 2 ^ w := hop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b),
        Nat.mod_eq_of_lt h]
  case kronUnpackLo a ww =>
    have h : v a % 2 ^ ww < 2 ^ w := hop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case kronUnpackHi a ww =>
    have h : v a / 2 ^ ww < 2 ^ w := hop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case montyReduce a p mu =>
    have h : v a % p < 2 ^ w := hop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case barrettReduce a p m =>
    have h : v a % p < 2 ^ w := hop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case harveyReduce a p =>
    have h : v a % p < 2 ^ w := hop
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a),
        Nat.mod_eq_of_lt h]
  case conditionalSub a p =>
    have h : (if v a ≥ p then v a - p else v a) < 2 ^ w := hop
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt h]

/-! ## Non-vacuity: concrete instantiation of the master bridge -/

/-- Non-vacuity witness for evalMixed_bv_agree: 8-bit AND of 0x0F and 0xFF.
    Demonstrates all hypotheses are jointly satisfiable. -/
example : evalMixedOp (.bitAnd 0 1)
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun id => if id == 0 then 15 else if id == 1 then 255 else 0) =
    (evalMixedBV 8 (.bitAnd 0 1)
      { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
      (liftBV 8 (fun id => if id == 0 then 15 else if id == 1 then 255 else 0))).toNat :=
  by native_decide

/-- Non-vacuity witness for evalMixed_bv_agree: 32-bit addition 100 + 200. -/
example : evalMixedOp (.addGate 0 1)
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun id => if id == 0 then 100 else if id == 1 then 200 else 0) =
    (evalMixedBV 32 (.addGate 0 1)
      { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
      (liftBV 32 (fun id => if id == 0 then 100 else if id == 1 then 200 else 0))).toNat :=
  by native_decide

/-- Non-vacuity: InBounds, EnvInBounds, OpInBounds are all satisfiable together. -/
example : ∃ (w : Nat) (env : MixedEnv) (v : EClassId → Nat) (op : MixedNodeOp),
    InBounds w v ∧ EnvInBounds w env ∧ OpInBounds w op env v ∧
    evalMixedOp op env v =
      (evalMixedBV w op env (liftBV w v)).toNat := by
  refine ⟨8,
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 },
    fun _ => 0,
    .bitAnd 0 1,
    ?_, ?_, ?_, ?_⟩
  · intro id; exact Nat.two_pow_pos 8
  · exact ⟨fun _ => Nat.two_pow_pos 8, fun _ => Nat.two_pow_pos 8, fun _ => Nat.two_pow_pos 8⟩
  · trivial
  · native_decide

/-! ## Modular bridge: BitVec evaluation agrees mod 2^w (unconditional) -/

/-- For ALL operations (including arithmetic with overflow), the Nat evaluation
    agrees with BitVec evaluation mod `2^w`. This is unconditional but weaker
    than `evalMixed_bv_agree` — the result is equality mod `2^w` rather than
    exact equality. Useful for modular arithmetic contexts (field reduction). -/
theorem evalMixed_bv_agree_mod (op : MixedNodeOp) (env : MixedEnv)
    (v : EClassId → Nat) (w : Nat)
    (hb : InBounds w v) (henv : EnvInBounds w env)
    (hcm : ∀ (n : Nat), op = .constMask n → n ≤ w)
    (hsub : ∀ (a b : EClassId), op = .subGate a b → v b ≤ v a) :
    evalMixedOp op env v % 2 ^ w =
    (evalMixedBV w op env (liftBV w v)).toNat := by
  cases op <;> simp only [evalMixedOp, evalMixedBV, liftBV]
  case constGate n => rw [BitVec.toNat_ofNat]
  case witness n => rw [BitVec.toNat_ofNat]
  case pubInput n => rw [BitVec.toNat_ofNat]
  case addGate a b =>
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
  case mulGate a b =>
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
  case negGate _ => rw [BitVec.toNat_ofNat]
  case smulGate n a =>
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (henv.1 n), Nat.mod_eq_of_lt (hb a)]
  case subGate a b =>
    have hle := hsub a b rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    -- Goal: (v a - v b) % 2^w = (2^w - v b + v a) % 2^w
    have hbw : v b ≤ 2 ^ w := Nat.le_of_lt (hb b)
    have hba : v b ≤ v a := hle
    -- Rewrite RHS: 2^w - v b + v a = (v a - v b) + 2^w
    have key : 2 ^ w - v b + v a = v a - v b + 2 ^ w := by
      calc 2 ^ w - v b + v a
          = 2 ^ w + v a - v b := by rw [Nat.sub_add_comm hbw]
        _ = 2 ^ w + (v a - v b) := by rw [Nat.add_sub_assoc hba]
        _ = v a - v b + 2 ^ w := by rw [Nat.add_comm]
    rw [key, Nat.add_mod_right]
  case shiftLeft a n =>
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
    rfl
  case shiftRight a n =>
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
    rw [Nat.mod_eq_of_lt (shiftRight_lt_two_pow (v a) n w (hb a))]
    rfl
  case bitAnd a b =>
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rw [Nat.mod_eq_of_lt (land_lt_two_pow (v a) (v b) w (hb b))]
    rfl
  case bitXor a b =>
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rw [Nat.mod_eq_of_lt (xor_lt_two_pow (v a) (v b) w (hb a) (hb b))]
    rfl
  case bitOr a b =>
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
    rw [Nat.mod_eq_of_lt (lor_lt_two_pow (v a) (v b) w (hb a) (hb b))]
    rfl
  case constMask n => rw [BitVec.toNat_ofNat]
  case reduceGate a p =>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  case kronPack a b ww =>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hb a), Nat.mod_eq_of_lt (hb b)]
  case kronUnpackLo a ww =>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  case kronUnpackHi a ww =>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  case montyReduce a p mu =>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  case barrettReduce a p m =>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  case harveyReduce a p =>
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]
  case conditionalSub a p =>
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb a)]

end AmoLean.EGraph.Verified.Bitwise
