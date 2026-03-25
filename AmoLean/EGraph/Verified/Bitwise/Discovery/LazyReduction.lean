import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

/-!
# AmoLean.EGraph.Verified.Bitwise.Discovery.LazyReduction

Lazy modular reduction via verified interval analysis.

When computing in a prime field (e.g., BabyBear with p = 2013265921), we can
defer `mod p` as long as intermediate values stay within the machine word.
This module tracks **upper bounds** (`IntervalBound.maxVal`) on intermediate
results and decides whether a reduction can be safely postponed.

## Key idea

After an addition `a + b` where `a, b ≤ M`, the result is `≤ 2M`.
If `2M < 2^wordSize - p`, then `a + b` still fits in the word and we can
defer the `mod p` to a later point — saving one reduction.

## Contents

- `IntervalBound`: upper-bound tracker with combinators for add/mul/shift/mask.
- `canDeferReduction`: decision procedure (Bool) for safe deferral.
- `canDeferReduction_sound`: proof that the decision is correct.
- `LazyReductionRule`: stateful wrapper that tracks the current bound and
  updates it after each operation.
- Concrete examples for BabyBear (p = 2013265921, wordSize = 64).
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

-- ══════════════════════════════════════════════════════════════════
-- Section 1: IntervalBound — upper-bound tracker
-- ══════════════════════════════════════════════════════════════════

/-- An upper bound on the absolute value of an intermediate result.
    If a value `x` has bound `b`, then `x ≤ b.maxVal`. -/
structure IntervalBound where
  /-- Upper bound on the value. -/
  maxVal : Nat
  deriving Repr, DecidableEq, Inhabited

/-- After adding two values bounded by `a` and `b`, the result is bounded
    by `a.maxVal + b.maxVal`. -/
def IntervalBound.add (a b : IntervalBound) : IntervalBound :=
  { maxVal := a.maxVal + b.maxVal }

/-- After multiplying two values bounded by `a` and `b`, the result is bounded
    by `a.maxVal * b.maxVal`. -/
def IntervalBound.mul (a b : IntervalBound) : IntervalBound :=
  { maxVal := a.maxVal * b.maxVal }

/-- After left-shifting a value bounded by `a` by `k` bits, the result is
    bounded by `a.maxVal * 2^k`. -/
def IntervalBound.shift (a : IntervalBound) (k : Nat) : IntervalBound :=
  { maxVal := a.maxVal * 2 ^ k }

/-- The result of masking with `2^k - 1` is bounded by `2^k - 1`. -/
def IntervalBound.mask (k : Nat) : IntervalBound :=
  { maxVal := 2 ^ k - 1 }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: IntervalBound correctness lemmas
-- ══════════════════════════════════════════════════════════════════

theorem IntervalBound.add_spec (a b : IntervalBound)
    (x y : Nat) (hx : x ≤ a.maxVal) (hy : y ≤ b.maxVal) :
    x + y ≤ (IntervalBound.add a b).maxVal := by
  simp [IntervalBound.add]
  omega

theorem IntervalBound.mul_spec (a b : IntervalBound)
    (x y : Nat) (hx : x ≤ a.maxVal) (hy : y ≤ b.maxVal) :
    x * y ≤ (IntervalBound.mul a b).maxVal := by
  simp [IntervalBound.mul]
  exact Nat.mul_le_mul hx hy

theorem IntervalBound.shift_spec (a : IntervalBound) (k : Nat)
    (x : Nat) (hx : x ≤ a.maxVal) :
    x * 2 ^ k ≤ (IntervalBound.shift a k).maxVal := by
  simp [IntervalBound.shift]
  exact Nat.mul_le_mul_right (2 ^ k) hx

theorem IntervalBound.mask_spec (k : Nat) (x : Nat) :
    x % 2 ^ k ≤ (IntervalBound.mask k).maxVal := by
  simp [IntervalBound.mask]
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 3: canDeferReduction — safe deferral decision
-- ══════════════════════════════════════════════════════════════════

/-- Can we safely defer `mod p` after adding two values each bounded by
    `bound.maxVal`?  True when `bound.maxVal + bound.maxVal < 2^wordSize - prime`,
    meaning an addition of two bounded values stays strictly below the
    overflow threshold `2^wordSize - prime`. -/
def canDeferReduction (bound : IntervalBound) (wordSize : Nat) (prime : Nat) : Bool :=
  bound.maxVal + bound.maxVal < 2 ^ wordSize - prime

/-- If `canDeferReduction` returns `true`, then for any `a, b ≤ bound.maxVal`,
    we have `a + b < 2^wordSize`.  This guarantees no word overflow. -/
theorem canDeferReduction_sound
    (bound : IntervalBound) (wordSize : Nat) (prime : Nat)
    (hprime : prime ≤ 2 ^ wordSize)
    (hdefer : canDeferReduction bound wordSize prime = true)
    (a b : Nat) (ha : a ≤ bound.maxVal) (hb : b ≤ bound.maxVal) :
    a + b < 2 ^ wordSize := by
  simp [canDeferReduction] at hdefer
  omega

/-- Variant: under `canDeferReduction`, the sum also stays below `2^wordSize - prime`,
    which means a subsequent subtraction by `prime` (conditional reduction) is safe. -/
theorem canDeferReduction_no_overflow
    (bound : IntervalBound) (wordSize : Nat) (prime : Nat)
    (hdefer : canDeferReduction bound wordSize prime = true)
    (a b : Nat) (ha : a ≤ bound.maxVal) (hb : b ≤ bound.maxVal) :
    a + b < 2 ^ wordSize - prime := by
  simp [canDeferReduction] at hdefer
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 4: LazyReductionRule — stateful deferral tracker
-- ══════════════════════════════════════════════════════════════════

/-- A lazy reduction rule tracks the current bound on intermediate values
    and whether a `mod p` reduction can still be deferred. -/
structure LazyReductionRule where
  /-- Human-readable name. -/
  name : String
  /-- The prime modulus. -/
  prime : Nat
  /-- Machine word size in bits. -/
  wordSize : Nat
  /-- Current upper bound on intermediate values. -/
  currentBound : IntervalBound
  /-- Whether reduction can still be deferred (computed). -/
  canDefer : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Create a lazy reduction rule from a prime, word size, and initial bound.
    `canDefer` is computed automatically from `canDeferReduction`. -/
def mkLazyRule (prime wordSize : Nat) (bound : IntervalBound) : LazyReductionRule :=
  { name := "lazy_mod_" ++ toString prime
    prime := prime
    wordSize := wordSize
    currentBound := bound
    canDefer := canDeferReduction bound wordSize prime }

/-- Update the rule after an addition with another bounded value.
    The new bound is `currentBound.add otherBound`, and `canDefer` is recomputed. -/
def afterAdd (rule : LazyReductionRule) (otherBound : IntervalBound) : LazyReductionRule :=
  let newBound := rule.currentBound.add otherBound
  { rule with
    currentBound := newBound
    canDefer := canDeferReduction newBound rule.wordSize rule.prime }

/-- Update the rule after a multiplication with another bounded value.
    The new bound is `currentBound.mul otherBound`, and `canDefer` is recomputed. -/
def afterMul (rule : LazyReductionRule) (otherBound : IntervalBound) : LazyReductionRule :=
  let newBound := rule.currentBound.mul otherBound
  { rule with
    currentBound := newBound
    canDefer := canDeferReduction newBound rule.wordSize rule.prime }

/-- Should we insert a `mod p` reduction now?  True when deferral is no longer safe. -/
def shouldReduce (rule : LazyReductionRule) : Bool := !rule.canDefer

-- ══════════════════════════════════════════════════════════════════
-- Section 5: LazyReductionRule correctness
-- ══════════════════════════════════════════════════════════════════

theorem mkLazyRule_canDefer (prime wordSize : Nat) (bound : IntervalBound) :
    (mkLazyRule prime wordSize bound).canDefer
      = canDeferReduction bound wordSize prime := by
  simp [mkLazyRule]

theorem afterAdd_bound (rule : LazyReductionRule) (otherBound : IntervalBound) :
    (afterAdd rule otherBound).currentBound
      = rule.currentBound.add otherBound := by
  simp [afterAdd]

theorem afterMul_bound (rule : LazyReductionRule) (otherBound : IntervalBound) :
    (afterMul rule otherBound).currentBound
      = rule.currentBound.mul otherBound := by
  simp [afterMul]

theorem shouldReduce_iff (rule : LazyReductionRule) :
    shouldReduce rule = true ↔ rule.canDefer = false := by
  simp [shouldReduce]

theorem afterAdd_preserves_prime (rule : LazyReductionRule) (otherBound : IntervalBound) :
    (afterAdd rule otherBound).prime = rule.prime := by
  simp [afterAdd]

theorem afterAdd_preserves_wordSize (rule : LazyReductionRule) (otherBound : IntervalBound) :
    (afterAdd rule otherBound).wordSize = rule.wordSize := by
  simp [afterAdd]

theorem afterMul_preserves_prime (rule : LazyReductionRule) (otherBound : IntervalBound) :
    (afterMul rule otherBound).prime = rule.prime := by
  simp [afterMul]

theorem afterMul_preserves_wordSize (rule : LazyReductionRule) (otherBound : IntervalBound) :
    (afterMul rule otherBound).wordSize = rule.wordSize := by
  simp [afterMul]

/-- Monotonicity: if `canDeferReduction` holds for a bound, it holds for any
    smaller bound. Directly implies chain safety: if the final accumulated
    bound defers, all prefix bounds defer too. -/
theorem canDeferReduction_mono (b1 b2 : IntervalBound) (wordSize prime : Nat)
    (hle : b1.maxVal ≤ b2.maxVal)
    (hdefer : canDeferReduction b2 wordSize prime = true) :
    canDeferReduction b1 wordSize prime = true := by
  simp [canDeferReduction] at *
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Concrete examples — BabyBear (p = 2013265921, 64-bit)
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear prime: 2013265921 = 15 * 2^27 + 1. -/
private def bbPrime : Nat := 2013265921

/-- BabyBear initial bound: values start below the prime. -/
private def bbInitBound : IntervalBound := { maxVal := bbPrime - 1 }

/-- After creating a BabyBear lazy rule, deferral is initially possible. -/
example : (mkLazyRule bbPrime 64 bbInitBound).canDefer = true := by native_decide

/-- After one addition, deferral is still possible (2M < 2^64 - p by a wide margin). -/
example :
    let rule := mkLazyRule bbPrime 64 bbInitBound
    let rule1 := afterAdd rule bbInitBound
    rule1.canDefer = true := by native_decide

/-- After two additions, deferral is still possible. -/
example :
    let rule := mkLazyRule bbPrime 64 bbInitBound
    let rule1 := afterAdd rule bbInitBound
    let rule2 := afterAdd rule1 bbInitBound
    rule2.canDefer = true := by native_decide

/-- After three additions, deferral is still possible for 64-bit BabyBear. -/
example :
    let rule := mkLazyRule bbPrime 64 bbInitBound
    let rule1 := afterAdd rule bbInitBound
    let rule2 := afterAdd rule1 bbInitBound
    let rule3 := afterAdd rule2 bbInitBound
    rule3.canDefer = true := by native_decide

/-- Bound grows linearly with additions. -/
example :
    let rule := mkLazyRule bbPrime 64 bbInitBound
    let rule1 := afterAdd rule bbInitBound
    rule1.currentBound.maxVal = 2 * bbInitBound.maxVal := by native_decide

/-- With a 32-bit word, even one addition triggers reduction for BabyBear
    (since 2 * (p-1) > 2^32 - p). -/
example :
    let rule := mkLazyRule bbPrime 32 bbInitBound
    shouldReduce (afterAdd rule bbInitBound) = true := by native_decide

/-- After a single multiplication the bound is (p-1)^2 ≈ 4×10^18, which still
    fits in 64 bits, so deferral is possible. -/
example :
    let rule := mkLazyRule bbPrime 64 bbInitBound
    (afterMul rule bbInitBound).canDefer = true := by native_decide

/-- But after two consecutive multiplications without reduction, the bound
    is (p-1)^3 which far exceeds 64 bits, so reduction is required. -/
example :
    let rule := mkLazyRule bbPrime 64 bbInitBound
    let rule1 := afterMul rule bbInitBound
    shouldReduce (afterMul rule1 bbInitBound) = true := by native_decide

/-- Mask operation: masking with 2^31 - 1 gives a small bound. -/
example : (IntervalBound.mask 31).maxVal = 2147483647 := by native_decide

/-- A masked value (31 bits) can defer many additions in 64-bit. -/
example :
    let smallBound := IntervalBound.mask 31
    let rule := mkLazyRule bbPrime 64 smallBound
    let rule1 := afterAdd rule smallBound
    let rule2 := afterAdd rule1 smallBound
    let rule3 := afterAdd rule2 smallBound
    let rule4 := afterAdd rule3 smallBound
    rule4.canDefer = true := by native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
