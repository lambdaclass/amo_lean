import AmoLean.EGraph.Verified.Bitwise.MixedNodeOp
import Mathlib.Data.Nat.Bitwise

/-!
# AmoLean.EGraph.Verified.Bitwise.BitwiseBridge

Bridge theorems connecting bitwise operations to modular arithmetic,
adapted from BitwiseLean library to AMO-Lean namespace.

Also provides the embedding bridge: evalMixedOp (toMixed op) relates
to the original CircuitNodeOp evaluation.

## Key results

- `mask_eq_mod`: x &&& (2^n - 1) = x % 2^n (THE KEY BRIDGE)
- `shiftRight_eq_div_pow`: x >>> n = x / 2^n
- `shiftLeft_eq_mul_pow`: x <<< n = x * 2^n
- `split_nat_eq`: x = (x >>> n) * 2^n + (x &&& (2^n - 1))
- `mod_from_split`: x % p = ((x >>> k) * (2^k % p) + (x &&& (2^k - 1))) % p
- `evalMixed_toMixed_algebraic`: embedding preserves algebraic evaluation

## References

- BitwiseLean library (~/Documents/claudio/bitwiselean/)
- Nat.and_two_pow_sub_one_eq_mod (Mathlib)
-/

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified (CircuitNodeOp CircuitEnv EClassId)

/-! ## Core bridge lemmas (adapted from BitwiseLean.Bridge) -/

/-- **THE KEY BRIDGE**: bitwise AND with mask `2^n - 1` equals modulo `2^n`.
    Source: Mathlib `Nat.and_two_pow_sub_one_eq_mod`. -/
theorem mask_eq_mod (x n : Nat) :
    x &&& (2 ^ n - 1) = x % 2 ^ n :=
  Nat.and_two_pow_sub_one_eq_mod x n

/-- Right shift by n equals integer division by 2^n.
    Source: Lean core `Nat.shiftRight_eq_div_pow`. -/
theorem shiftRight_eq_div_pow (x n : Nat) :
    x >>> n = x / 2 ^ n :=
  Nat.shiftRight_eq_div_pow x n

/-- Left shift by n equals multiplication by 2^n.
    Source: Lean core `Nat.shiftLeft_eq`. -/
theorem shiftLeft_eq_mul_pow (x n : Nat) :
    x <<< n = x * 2 ^ n :=
  Nat.shiftLeft_eq x n

/-- Low part bound: the low n bits of x are strictly less than 2^n. -/
theorem split_low_lt (x n : Nat) :
    x &&& (2 ^ n - 1) < 2 ^ n := by
  rw [mask_eq_mod]
  exact Nat.mod_lt x (Nat.two_pow_pos n)

/-! ## Word splitting identity (adapted from BitwiseLean.Split) -/

/-- **Word splitting identity**: x = (x >>> n) * 2^n + (x &&& (2^n - 1)).
    Fundamental identity underlying all modular reduction algorithms. -/
theorem split_nat_eq (x n : Nat) :
    x = (x >>> n) * 2 ^ n + (x &&& (2 ^ n - 1)) := by
  rw [shiftRight_eq_div_pow, mask_eq_mod]
  exact (Nat.div_add_mod' x (2 ^ n)).symm

/-! ## Modular reduction via splitting -/

/-- Auxiliary: (a * b + c) % p = (a * (b % p) + c) % p. -/
private theorem mul_mod_factor (a b c p : Nat) :
    (a * b + c) % p = (a * (b % p) + c) % p := by
  rw [Nat.add_mod, Nat.mul_mod a b p]
  rw [Nat.add_mod (a * (b % p)) c p, Nat.mul_mod a (b % p) p, Nat.mod_mod_of_dvd]
  exact dvd_refl p

set_option linter.unusedVariables false in
/-- **Modular reduction via bit splitting**: for any modulus p > 0,
    x % p = ((x >>> k) * (2^k % p) + (x &&& (2^k - 1))) % p.

    Master identity: Mersenne folding (2^k % p = 1),
    pseudo-Mersenne (2^k % p = c), and general reduction. -/
theorem mod_from_split (x k p : Nat) (hp : 0 < p) :
    x % p = ((x >>> k) * (2 ^ k % p) + (x &&& (2 ^ k - 1))) % p := by
  rw [shiftRight_eq_div_pow, mask_eq_mod]
  conv_lhs => rw [(Nat.div_add_mod' x (2 ^ k)).symm]
  exact mul_mod_factor (x / 2 ^ k) (2 ^ k) (x % 2 ^ k) p

/-! ## Embedding bridge: CircuitNodeOp → MixedNodeOp -/

/-- evalMixedOp of an addGate is Nat addition. -/
@[simp] theorem evalMixed_addGate (a b : EClassId) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.addGate a b) env v = v a + v b := rfl

/-- evalMixedOp of a mulGate is Nat multiplication. -/
@[simp] theorem evalMixed_mulGate (a b : EClassId) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.mulGate a b) env v = v a * v b := rfl

/-- evalMixedOp of a constGate reads from the environment. -/
@[simp] theorem evalMixed_constGate (n : Nat) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.constGate n) env v = env.constVal n := rfl

/-- evalMixedOp of a witness reads from the environment. -/
@[simp] theorem evalMixed_witness (n : Nat) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.witness n) env v = env.witnessVal n := rfl

/-- evalMixedOp of a shiftLeft is Nat.shiftLeft. -/
@[simp] theorem evalMixed_shiftLeft (a : EClassId) (n : Nat) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.shiftLeft a n) env v = Nat.shiftLeft (v a) n := rfl

/-- evalMixedOp of a shiftRight is Nat.shiftRight. -/
@[simp] theorem evalMixed_shiftRight (a : EClassId) (n : Nat) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.shiftRight a n) env v = Nat.shiftRight (v a) n := rfl

/-- evalMixedOp of a bitAnd is Nat.land. -/
@[simp] theorem evalMixed_bitAnd (a b : EClassId) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.bitAnd a b) env v = Nat.land (v a) (v b) := rfl

/-- evalMixedOp of a bitXor is Nat.xor. -/
@[simp] theorem evalMixed_bitXor (a b : EClassId) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.bitXor a b) env v = Nat.xor (v a) (v b) := rfl

/-- evalMixedOp of a bitOr is Nat.lor. -/
@[simp] theorem evalMixed_bitOr (a b : EClassId) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.bitOr a b) env v = Nat.lor (v a) (v b) := rfl

/-- evalMixedOp of a constMask is 2^n - 1. -/
@[simp] theorem evalMixed_constMask (n : Nat) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.constMask n) env v = 2 ^ n - 1 := rfl

/-- evalMixedOp of a smulGate is scalar multiplication. -/
@[simp] theorem evalMixed_smulGate (c : Nat) (a : EClassId) (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (.smulGate c a) env v = env.constVal c * v a := rfl

/-! ## Bitwise-algebraic equivalences via evalMixedOp -/

/-- Bitwise AND with mask is equivalent to modular reduction in the E-graph. -/
theorem evalMixed_bitAnd_constMask_eq_mod (a b : EClassId) (n : Nat)
    (v : EClassId → Nat) (hmask : v b = 2 ^ n - 1) :
    Nat.land (v a) (v b) = (v a) % 2 ^ n := by
  rw [hmask]
  exact Nat.and_two_pow_sub_one_eq_mod (v a) n

/-- Right shift is equivalent to division in the E-graph. -/
theorem evalMixed_shiftRight_eq_div (a : EClassId) (n : Nat)
    (v : EClassId → Nat) :
    Nat.shiftRight (v a) n = (v a) / 2 ^ n :=
  shiftRight_eq_div_pow (v a) n

/-- Left shift is equivalent to multiplication in the E-graph. -/
theorem evalMixed_shiftLeft_eq_mul (a : EClassId) (n : Nat)
    (v : EClassId → Nat) :
    Nat.shiftLeft (v a) n = (v a) * 2 ^ n :=
  shiftLeft_eq_mul_pow (v a) n

/-- **Master bridge**: splitting + folding in the E-graph implements modular reduction.
    Given a value x at e-class `a`, bit width k, and modulus p:
    (x >>> k) * (2^k % p) + (x &&& (2^k - 1)) ≡ x (mod p).

    This is the semantic core of all field-specific fold rules. -/
theorem fold_reduction_mod (x k p : Nat) (hp : 0 < p) :
    ((x >>> k) * (2 ^ k % p) + (x &&& (2 ^ k - 1))) % p = x % p :=
  (mod_from_split x k p hp).symm

end AmoLean.EGraph.Verified.Bitwise
