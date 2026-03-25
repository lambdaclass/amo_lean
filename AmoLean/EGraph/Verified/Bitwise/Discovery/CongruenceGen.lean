import AmoLean.EGraph.Verified.Bitwise.FieldFoldRules
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

/-!
# AmoLean.EGraph.Verified.Bitwise.Discovery.CongruenceGen

Congruence rule generation: for a prime `p` with bit width `w`, derive rewrite
rules `x * 2^k ≡ x * (2^k % p) (mod p)` for a bounded range of `k` values
around `w`.

## Key results

- `CongruenceEntry`: records `k`, `residue = 2^k % p`, and `prime`
- `computeCongruences`: enumerates entries for k in [w-2, 2w+2]
- `congruenceRule`: packages one entry as a `MixedSoundRule` (with explicit proof)
- `congruenceRuleOf`: packages `(p, k)` directly as a `MixedSoundRule`
- `generateCongruenceRules`: batch generation for all entries

## Design

The soundness of each rule follows from `Nat.mul_mod`:
  `(v 0 * 2^k) % p = (v 0 % p * (2^k % p)) % p = (v 0 * residue) % p`
where `residue = 2^k % p`. Since both LHS and RHS reduce modulo `p`, the
rewrite is unconditionally sound.

## References

- FieldFoldRules.lean: babybear_prime, mersenne31_prime, goldilocks_prime
- BitwiseRules.lean: MixedSoundRule structure
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise (MixedEnv MixedSoundRule FieldFoldRule)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: CongruenceEntry structure
-- ══════════════════════════════════════════════════════════════════

/-- A congruence entry recording that `2^k % prime = residue`. -/
structure CongruenceEntry where
  /-- The exponent -/
  k : Nat
  /-- The residue: 2^k % prime -/
  residue : Nat
  /-- The prime modulus -/
  prime : Nat
  deriving Repr, DecidableEq, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Compute congruences for a range of k values
-- ══════════════════════════════════════════════════════════════════

/-- Compute congruence entries `2^k % p` for k from `bitWidth - 2` to `2 * bitWidth + 2`.
    Uses `List.range` + `map` so that each entry has `residue = 2^k % p` and
    `prime = p` definitionally. Typically produces ~36 entries for 31-bit primes. -/
def computeCongruences (p : Nat) (bitWidth : Nat) : List CongruenceEntry :=
  let lo := if bitWidth ≥ 2 then bitWidth - 2 else 0
  let hi := 2 * bitWidth + 3  -- exclusive upper bound
  (List.range (hi - lo)).map fun i =>
    let k := lo + i
    ⟨k, 2 ^ k % p, p⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Correctness lemmas
-- ══════════════════════════════════════════════════════════════════

/-- Key algebraic identity: `(a * b) % p = (a * (b % p)) % p`.
    Follows from `Nat.mul_mod` and `Nat.mod_mod`. -/
theorem mul_mod_residue (a b p : Nat) :
    (a * b) % p = (a * (b % p)) % p := by
  rw [Nat.mul_mod, Nat.mul_mod a (b % p) p, Nat.mod_mod]

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Rule generation
-- ══════════════════════════════════════════════════════════════════

/-- Create a `MixedSoundRule` from a congruence entry with an explicit proof
    that `entry.residue = 2^entry.k % entry.prime`.
    Rule: `(x * 2^k) % p = (x * residue) % p`.

    Soundness follows from `mul_mod_residue`. -/
def congruenceRule (entry : CongruenceEntry)
    (hres : entry.residue = 2 ^ entry.k % entry.prime) : MixedSoundRule where
  name := s!"congr_2^{entry.k}_mod_{entry.prime}"
  lhsEval := fun _ v => (v 0 * 2 ^ entry.k) % entry.prime
  rhsEval := fun _ v => (v 0 * entry.residue) % entry.prime
  soundness := fun _ v => by
    rw [hres, mul_mod_residue]

/-- Create a `MixedSoundRule` directly from prime `p` and exponent `k`.
    Rule: `(x * 2^k) % p = (x * (2^k % p)) % p`.

    This variant avoids the need for an explicit residue proof since
    both sides use `2^k % p` directly. Used by `generateCongruenceRules`. -/
def congruenceRuleOf (p k : Nat) : MixedSoundRule where
  name := s!"congr_2^{k}_mod_{p}"
  lhsEval := fun _ v => (v 0 * 2 ^ k) % p
  rhsEval := fun _ v => (v 0 * (2 ^ k % p)) % p
  soundness := fun _ v => mul_mod_residue (v 0) (2 ^ k) p

/-- Generate all congruence rules for prime `p` with bit width `bitWidth`.
    Each rule rewrites `(x * 2^k) % p` to `(x * residue) % p` where
    `residue = 2^k % p`, for k in `[bitWidth-2, 2*bitWidth+2]`. -/
def generateCongruenceRules (p : Nat) (bitWidth : Nat) : List MixedSoundRule :=
  (computeCongruences p bitWidth).map fun entry =>
    congruenceRuleOf entry.prime entry.k

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Concrete instantiations
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise (babybear_prime babybear_prime_pos
  mersenne31_prime mersenne31_prime_pos goldilocks_prime goldilocks_prime_pos)

/-- BabyBear congruence entries (k in [29..64], 36 entries around bit width 31). -/
def babybearCongruences : List CongruenceEntry :=
  computeCongruences babybear_prime 31

/-- Mersenne31 congruence entries. -/
def mersenne31Congruences : List CongruenceEntry :=
  computeCongruences mersenne31_prime 31

/-- Goldilocks congruence entries. -/
def goldilocksCongruences : List CongruenceEntry :=
  computeCongruences goldilocks_prime 64

/-- BabyBear congruence rules. -/
def babybearCongruenceRules : List MixedSoundRule :=
  generateCongruenceRules babybear_prime 31

/-- Mersenne31 congruence rules. -/
def mersenne31CongruenceRules : List MixedSoundRule :=
  generateCongruenceRules mersenne31_prime 31

/-- Goldilocks congruence rules. -/
def goldilocksCongruenceRules : List MixedSoundRule :=
  generateCongruenceRules goldilocks_prime 64

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Verification examples
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear prime = 2013265921. -/
example : babybear_prime = 2013265921 := by native_decide

/-- 2^31 % babybear_prime = 2^27 - 1 = 134217727. -/
example : 2 ^ 31 % babybear_prime = 134217727 := by native_decide

/-- 2^32 % babybear_prime. -/
example : 2 ^ 32 % babybear_prime = 268435454 := by native_decide

/-- Mersenne31: 2^31 % mersenne31_prime = 1 (characteristic identity). -/
example : 2 ^ 31 % mersenne31_prime = 1 := by native_decide

/-- We generate 36 entries for BabyBear (k in [29..64]). -/
example : babybearCongruences.length = 36 := by native_decide

/-- We generate 36 entries for Mersenne31 (k in [29..64]). -/
example : mersenne31Congruences.length = 36 := by native_decide

/-- We generate 69 entries for Goldilocks (k in [62..130]). -/
example : goldilocksCongruences.length = 69 := by native_decide

/-- Spot check: BabyBear entry for k=31 exists. -/
example : (babybearCongruences.find? (fun e => e.k == 31)).isSome = true := by native_decide

/-- Rules list length matches entries (BabyBear). -/
example : babybearCongruenceRules.length = 36 := by native_decide

/-- Rules list length matches entries (Mersenne31). -/
example : mersenne31CongruenceRules.length = 36 := by native_decide

/-- Rules list length matches entries (Goldilocks). -/
example : goldilocksCongruenceRules.length = 69 := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Non-vacuity examples
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: congruenceRule produces a rule whose soundness is not vacuous.
    BabyBear k=31: LHS = RHS on concrete valuation v := fun _ => 42. -/
example : let entry : CongruenceEntry := ⟨31, 2 ^ 31 % babybear_prime, babybear_prime⟩
    let rule := congruenceRule entry rfl
    let v : EClassId → Nat := fun _ => 42
    let env : MixedEnv := ⟨fun _ => 0, fun _ => 0, 0⟩
    rule.lhsEval env v = rule.rhsEval env v := by native_decide

/-- Non-vacuity: Mersenne31 k=31, residue=1. -/
example : let entry : CongruenceEntry := ⟨31, 2 ^ 31 % mersenne31_prime, mersenne31_prime⟩
    let rule := congruenceRule entry rfl
    let v : EClassId → Nat := fun _ => 100
    let env : MixedEnv := ⟨fun _ => 0, fun _ => 0, 0⟩
    rule.lhsEval env v = rule.rhsEval env v := by native_decide

/-- Non-vacuity: congruenceRuleOf on BabyBear. -/
example : let rule := congruenceRuleOf babybear_prime 31
    let v : EClassId → Nat := fun _ => 42
    let env : MixedEnv := ⟨fun _ => 0, fun _ => 0, 0⟩
    rule.lhsEval env v = rule.rhsEval env v := by native_decide

/-- Aggregate rule generation produces non-empty lists. -/
example : babybearCongruenceRules.length > 0 := by native_decide
example : mersenne31CongruenceRules.length > 0 := by native_decide
example : goldilocksCongruenceRules.length > 0 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
