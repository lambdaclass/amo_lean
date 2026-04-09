import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge

/-!
# AmoLean.EGraph.Verified.Bitwise.FieldFoldRules

Field-specific folding reduction rules for Mersenne31, BabyBear, and Goldilocks.

Each rule expresses that a bitwise fold operation (shift + mask + add/mul) computes
the same result modulo the field prime as the identity (no-op). This is the core
optimization identity used in ZK-friendly field implementations.

## Key results

- `two_pow_mod_mersenne`: 2^k % (2^k - 1) = 1 for k ≥ 2
- `two_pow_mod_pseudo_mersenne`: 2^k % (2^k - c) = c for 0 < c, 2*c < 2^k
- `mersenne_fold_correct`: fold via addition ≡ identity (mod 2^k - 1)
- `pseudo_mersenne_fold_correct`: fold via scalar multiply ≡ identity (mod 2^k - c)
- `mersenne31_fold_rule`, `babybear_fold_rule`, `goldilocks_fold_rule`: packaged rules

## References

- BitwiseBridge.lean: `fold_reduction_mod`, `mod_from_split`
- BitwiseLean library: MersenneFold.lean, PseudoMersenneFold.lean
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

/-! ## FieldFoldRule structure -/

/-- A conditional sound rewrite rule for field-specific fold operations.
    The rule is sound when the side condition holds: under `sideCond`,
    the bitwise fold evaluation equals the specification modulo `prime`. -/
structure FieldFoldRule where
  /-- Human-readable name for the rule -/
  name : String
  /-- The field prime -/
  prime : Nat
  /-- Bit width used for splitting -/
  bitWidth : Nat
  /-- The fold operation on the LHS (bitwise implementation) -/
  foldEval : Nat → Nat
  /-- The specification on the RHS (modular arithmetic) -/
  specEval : Nat → Nat
  /-- Side condition: input must satisfy this (e.g., bounded) -/
  sideCond : Nat → Prop
  /-- The prime is positive -/
  prime_pos : 0 < prime
  /-- Soundness: under the side condition, fold ≡ spec (mod prime) -/
  soundness : ∀ (x : Nat), sideCond x → foldEval x % prime = specEval x % prime

/-! ## Helper: 2^k % (2^k - 1) = 1 for Mersenne primes -/

/-- For k ≥ 2, we have 2^k = (2^k - 1) + 1, hence 2^k % (2^k - 1) = 1. -/
theorem two_pow_mod_mersenne (k : Nat) (hk : 2 ≤ k) :
    2 ^ k % (2 ^ k - 1) = 1 := by
  have h4 : 4 ≤ 2 ^ k := le_trans (show 4 ≤ 2 ^ 2 by omega)
    (Nat.pow_le_pow_right (by omega : 0 < 2) hk)
  have hp : 1 < 2 ^ k - 1 := by omega
  -- Show (1 + (2^k - 1)) % (2^k - 1) = 1  via  Nat.add_mod_right
  have step1 : (1 + (2 ^ k - 1)) % (2 ^ k - 1) = 1 % (2 ^ k - 1) :=
    Nat.add_mod_right 1 (2 ^ k - 1)
  rw [show 1 + (2 ^ k - 1) = 2 ^ k from by omega] at step1
  rw [step1]
  exact Nat.mod_eq_of_lt hp

/-! ## Helper: 2^k % (2^k - c) = c for pseudo-Mersenne primes -/

/-- For 0 < c and 2*c < 2^k, we have 2^k = (2^k - c) + c,
    hence 2^k % (2^k - c) = c. -/
theorem two_pow_mod_pseudo_mersenne (k c : Nat) (hc : 0 < c) (hc2 : 2 * c < 2 ^ k) :
    2 ^ k % (2 ^ k - c) = c := by
  have hpk : c < 2 ^ k := by omega
  have hp : c < 2 ^ k - c := by omega
  -- Show (c + (2^k - c)) % (2^k - c) = c  via  Nat.add_mod_right
  have step1 : (c + (2 ^ k - c)) % (2 ^ k - c) = c % (2 ^ k - c) :=
    Nat.add_mod_right c (2 ^ k - c)
  rw [show c + (2 ^ k - c) = 2 ^ k from by omega] at step1
  rw [step1]
  exact Nat.mod_eq_of_lt hp

/-! ## Mersenne fold correctness -/

/-- **Mersenne fold identity**: for p = 2^k - 1 with k ≥ 2,
    ((x >>> k) + (x &&& (2^k - 1))) % p = x % p.

    Since 2^k % p = 1, the general fold_reduction_mod simplifies:
    (x >>> k) * 1 + (x &&& (2^k - 1)) = (x >>> k) + (x &&& (2^k - 1)). -/
theorem mersenne_fold_correct (x k : Nat) (hk : 2 ≤ k) :
    ((x >>> k) + (x &&& (2 ^ k - 1))) % (2 ^ k - 1) = x % (2 ^ k - 1) := by
  have hp : 0 < 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k := le_trans (show 4 ≤ 2 ^ 2 by omega)
      (Nat.pow_le_pow_right (by omega : 0 < 2) hk)
    omega
  -- Use fold_reduction_mod with the substitution 2^k % (2^k - 1) = 1
  have key := fold_reduction_mod x k (2 ^ k - 1) hp
  rw [two_pow_mod_mersenne k hk, Nat.mul_one] at key
  exact key

/-! ## Pseudo-Mersenne fold correctness -/

/-- **Pseudo-Mersenne fold identity**: for p = 2^k - c with 0 < c, 2*c < 2^k,
    ((x >>> k) * c + (x &&& (2^k - 1))) % p = x % p.

    Since 2^k % p = c, the general fold_reduction_mod gives exactly this. -/
theorem pseudo_mersenne_fold_correct (x k c : Nat) (hc : 0 < c) (hc2 : 2 * c < 2 ^ k) :
    ((x >>> k) * c + (x &&& (2 ^ k - 1))) % (2 ^ k - c) = x % (2 ^ k - c) := by
  have hp : 0 < 2 ^ k - c := by omega
  have key := fold_reduction_mod x k (2 ^ k - c) hp
  rw [two_pow_mod_pseudo_mersenne k c hc hc2] at key
  exact key

/-! ## Concrete field parameters -/

/-- Mersenne31 prime: p = 2^31 - 1 = 2147483647 -/
def mersenne31_prime : Nat := 2 ^ 31 - 1

/-- BabyBear prime: p = 2^31 - 2^27 + 1.
    Written as 2^31 - c where c = 2^27 - 1 = 134217727. -/
def babybear_prime : Nat := 2 ^ 31 - 2 ^ 27 + 1

/-- Goldilocks prime: p = 2^64 - 2^32 + 1.
    Written as 2^64 - c where c = 2^32 - 1 = 4294967295. -/
def goldilocks_prime : Nat := 2 ^ 64 - 2 ^ 32 + 1

/-- BabyBear correction constant: c = 2^27 - 1 -/
def babybear_c : Nat := 2 ^ 27 - 1

/-- Goldilocks correction constant: c = 2^32 - 1 -/
def goldilocks_c : Nat := 2 ^ 32 - 1

/-! ## Concrete parameter lemmas -/

theorem mersenne31_prime_eq : mersenne31_prime = 2 ^ 31 - 1 := rfl

theorem babybear_prime_eq : babybear_prime = 2 ^ 31 - babybear_c := by
  simp only [babybear_prime, babybear_c]; omega

theorem goldilocks_prime_eq : goldilocks_prime = 2 ^ 64 - goldilocks_c := by
  simp only [goldilocks_prime, goldilocks_c]; omega

theorem mersenne31_prime_pos : 0 < mersenne31_prime := by decide

theorem babybear_prime_pos : 0 < babybear_prime := by decide

theorem goldilocks_prime_pos : 0 < goldilocks_prime := by decide

theorem babybear_c_pos : 0 < babybear_c := by decide

theorem goldilocks_c_pos : 0 < goldilocks_c := by decide

theorem babybear_c_bound : 2 * babybear_c < 2 ^ 31 := by decide

theorem goldilocks_c_bound : 2 * goldilocks_c < 2 ^ 64 := by decide

/-! ## Field-specific fold rules -/

/-- **Mersenne31 fold rule**: for p = 2^31 - 1,
    ((x >>> 31) + (x &&& (2^31 - 1))) % p = x % p.

    This is the core Mersenne folding identity used in Plonky3's Mersenne31 field. -/
def mersenne31_fold_rule : FieldFoldRule where
  name := "mersenne31_fold"
  prime := mersenne31_prime
  bitWidth := 31
  foldEval := fun x => (x >>> 31) + (x &&& (2 ^ 31 - 1))
  specEval := fun x => x
  sideCond := fun _ => True
  prime_pos := mersenne31_prime_pos
  soundness := fun x _ => by
    unfold mersenne31_prime
    exact mersenne_fold_correct x 31 (by omega)

/-- **BabyBear fold rule**: for p = 2^31 - (2^27 - 1),
    ((x >>> 31) * (2^27 - 1) + (x &&& (2^31 - 1))) % p = x % p.

    This is the pseudo-Mersenne folding identity used in Plonky3's BabyBear field. -/
def babybear_fold_rule : FieldFoldRule where
  name := "babybear_fold"
  prime := babybear_prime
  bitWidth := 31
  foldEval := fun x => (x >>> 31) * babybear_c + (x &&& (2 ^ 31 - 1))
  specEval := fun x => x
  sideCond := fun _ => True
  prime_pos := babybear_prime_pos
  soundness := fun x _ => by
    rw [babybear_prime_eq]
    unfold babybear_c
    exact pseudo_mersenne_fold_correct x 31 (2 ^ 27 - 1) (by decide) (by decide)

/-- **Goldilocks fold rule**: for p = 2^64 - (2^32 - 1),
    ((x >>> 64) * (2^32 - 1) + (x &&& (2^64 - 1))) % p = x % p.

    This is the pseudo-Mersenne folding identity used in Plonky3's Goldilocks field. -/
def goldilocks_fold_rule : FieldFoldRule where
  name := "goldilocks_fold"
  prime := goldilocks_prime
  bitWidth := 64
  foldEval := fun x => (x >>> 64) * goldilocks_c + (x &&& (2 ^ 64 - 1))
  specEval := fun x => x
  sideCond := fun _ => True
  prime_pos := goldilocks_prime_pos
  soundness := fun x _ => by
    rw [goldilocks_prime_eq]
    unfold goldilocks_c
    exact pseudo_mersenne_fold_correct x 64 (2 ^ 32 - 1) (by decide) (by decide)

/-! ## Rule collection -/

/-- All field-specific fold rules for the three Plonky3 fields. -/
def allFieldFoldRules : List FieldFoldRule :=
  [mersenne31_fold_rule, babybear_fold_rule, goldilocks_fold_rule]

/-- The collection contains exactly 3 rules. -/
theorem allFieldFoldRules_length : allFieldFoldRules.length = 3 := rfl

/-! ## Convenience: direct fold theorems for each field -/

/-- Direct theorem: Mersenne31 fold correctness. -/
theorem mersenne31_fold (x : Nat) :
    ((x >>> 31) + (x &&& (2 ^ 31 - 1))) % mersenne31_prime = x % mersenne31_prime := by
  unfold mersenne31_prime
  exact mersenne_fold_correct x 31 (by omega)

/-- Direct theorem: BabyBear fold correctness. -/
theorem babybear_fold (x : Nat) :
    ((x >>> 31) * babybear_c + (x &&& (2 ^ 31 - 1))) % babybear_prime =
    x % babybear_prime := by
  rw [babybear_prime_eq]
  unfold babybear_c
  exact pseudo_mersenne_fold_correct x 31 (2 ^ 27 - 1) (by decide) (by decide)

/-- Direct theorem: Goldilocks fold correctness. -/
theorem goldilocks_fold (x : Nat) :
    ((x >>> 64) * goldilocks_c + (x &&& (2 ^ 64 - 1))) % goldilocks_prime =
    x % goldilocks_prime := by
  rw [goldilocks_prime_eq]
  unfold goldilocks_c
  exact pseudo_mersenne_fold_correct x 64 (2 ^ 32 - 1) (by decide) (by decide)

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity: mersenne_fold_correct is not vacuously true.
    Concrete witness: x = 100, k = 31. -/
example : ((100 >>> 31) + (100 &&& (2 ^ 31 - 1))) % (2 ^ 31 - 1) = 100 % (2 ^ 31 - 1) :=
  mersenne_fold_correct 100 31 (by omega)

/-- Non-vacuity: pseudo_mersenne_fold_correct with BabyBear parameters. -/
example : ((100 >>> 31) * (2 ^ 27 - 1) + (100 &&& (2 ^ 31 - 1))) % (2 ^ 31 - (2 ^ 27 - 1)) =
    100 % (2 ^ 31 - (2 ^ 27 - 1)) :=
  pseudo_mersenne_fold_correct 100 31 (2 ^ 27 - 1) (by decide) (by decide)

/-- Non-vacuity: all three FieldFoldRule instances have satisfiable side conditions. -/
example : ∀ r ∈ allFieldFoldRules, r.sideCond 42 := by
  intro r hr
  simp only [allFieldFoldRules, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact trivial
  · exact trivial
  · exact trivial

/-- Non-vacuity: all three rules produce correct results for a concrete value.
    Tests with x = 2^32 + 7 (a value that actually exercises the fold). -/
example : ∀ r ∈ allFieldFoldRules,
    r.foldEval (2 ^ 32 + 7) % r.prime = r.specEval (2 ^ 32 + 7) % r.prime := by
  intro r hr
  simp only [allFieldFoldRules, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact mersenne31_fold_rule.soundness _ trivial
  · exact babybear_fold_rule.soundness _ trivial
  · exact goldilocks_fold_rule.soundness _ trivial

end AmoLean.EGraph.Verified.Bitwise
