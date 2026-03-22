/-
  AmoLean.EGraph.Verified.Bitwise.FieldFoldPatternRules — Field Fold as Pattern Rules

  Converts the 3 FieldFoldRules (Mersenne31, BabyBear, Goldilocks) to
  RewriteRule MixedNodeOp for use in e-graph saturation.

  Each fold rule rewrites an expression x to its folded form:
  - Mersenne31:  x → addGate(shiftRight(x, 31), bitAnd(x, constMask(31)))
  - BabyBear:    x → addGate(smulGate(c, shiftRight(x, 31)), bitAnd(x, constMask(31)))
  - Goldilocks:  x → addGate(smulGate(c, shiftRight(x, 64)), bitAnd(x, constMask(64)))

  The fold is semantically equivalent modulo the prime: foldEval(x) % p = x % p.
  Soundness follows from FieldFoldRules.lean theorems.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedPatternRules
import AmoLean.EGraph.Verified.Bitwise.FieldFoldRules

namespace FieldFoldPatternRules

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)
open AmoLean.EGraph.Verified.Bitwise
  (mersenne31_prime babybear_prime goldilocks_prime babybear_c goldilocks_c)

def koalabear_prime : Nat := 2130706433  -- 2^31 - 2^24 + 1
def koalabear_c : Nat := 2^24 - 1       -- 16777215
open MixedEMatch (Pattern PatVarId Substitution RewriteRule)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Generic fold pattern builder
-- ══════════════════════════════════════════════════════════════════

/-- Build the fold RHS pattern for a (pseudo-)Mersenne prime.
    fold(x) = addGate(smulGate(c, shiftRight(x, k)), bitAnd(x, constMask(k)))
    When c = 1, uses shiftRight directly (no smulGate wrapper). -/
private def mkFoldPattern (k : Nat) (c : Nat) : Pattern MixedNodeOp :=
  let xVar := Pattern.patVar (Op := MixedNodeOp) 0
  let highPart := Pattern.node (.shiftRight 0 k) [xVar]
  let scaledHigh :=
    if c == 1 then highPart
    else Pattern.node (.smulGate c 0) [highPart]
  let lowPart := Pattern.node (.bitAnd 0 1) [xVar, Pattern.node (.constMask k) []]
  Pattern.node (.addGate 0 1) [scaledHigh, lowPart]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Concrete field fold rules
-- ══════════════════════════════════════════════════════════════════

/-- Mersenne31 fold: x → (x >>> 31) + (x &&& (2^31 - 1))
    Sound modulo p = 2^31 - 1: fold(x) % p = x % p. -/
def patMersenne31Fold : RewriteRule MixedNodeOp where
  name := "mersenne31_fold"
  lhs := .patVar 0
  rhs := mkFoldPattern 31 1

/-- BabyBear fold: x → (x >>> 31) * c + (x &&& (2^31 - 1)) where c = 2^27 - 1.
    Sound modulo p = 2^31 - (2^27 - 1): fold(x) % p = x % p. -/
def patBabyBearFold : RewriteRule MixedNodeOp where
  name := "babybear_fold"
  lhs := .patVar 0
  rhs := mkFoldPattern 31 babybear_c

/-- KoalaBear fold: x → (x >>> 31) * c + (x &&& (2^31 - 1)) where c = 2^24 - 1.
    Sound modulo p = 2^31 - (2^24 - 1): fold(x) % p = x % p. -/
def patKoalaBearFold : RewriteRule MixedNodeOp where
  name := "koalabear_fold"
  lhs := .patVar 0
  rhs := mkFoldPattern 31 koalabear_c

/-- Goldilocks fold: x → (x >>> 64) * c + (x &&& (2^64 - 1)) where c = 2^32 - 1.
    Sound modulo p = 2^64 - (2^32 - 1): fold(x) % p = x % p. -/
def patGoldilocksFold : RewriteRule MixedNodeOp where
  name := "goldilocks_fold"
  lhs := .patVar 0
  rhs := mkFoldPattern 64 goldilocks_c

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Rule selection by prime
-- ══════════════════════════════════════════════════════════════════

/-- Select the field fold rules for a specific prime.
    Returns an empty list for unrecognized primes. -/
def fieldFoldPatternRules (p : Nat) : List (RewriteRule MixedNodeOp) :=
  if p == mersenne31_prime then [patMersenne31Fold]
  else if p == babybear_prime then [patBabyBearFold]
  else if p == koalabear_prime then [patKoalaBearFold]
  else if p == goldilocks_prime then [patGoldilocksFold]
  else []

/-- All field fold rules for the three Plonky3 fields. -/
def allFieldFoldPatternRules : List (RewriteRule MixedNodeOp) :=
  [patMersenne31Fold, patBabyBearFold, patKoalaBearFold, patGoldilocksFold]

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

example : allFieldFoldPatternRules.length = 4 := rfl

example : (patKoalaBearFold).name = "koalabear_fold" := rfl

example : (patMersenne31Fold).name = "mersenne31_fold" := rfl

example : (patBabyBearFold).name = "babybear_fold" := rfl

example : (patGoldilocksFold).name = "goldilocks_fold" := rfl

example : (fieldFoldPatternRules mersenne31_prime).length = 1 := by native_decide

example : (fieldFoldPatternRules babybear_prime).length = 1 := by native_decide

example : (fieldFoldPatternRules goldilocks_prime).length = 1 := by native_decide

example : (fieldFoldPatternRules koalabear_prime).length = 1 := by native_decide

example : (fieldFoldPatternRules 17).length = 0 := by native_decide

end FieldFoldPatternRules
