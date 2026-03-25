/-
  AmoLean.EGraph.Verified.Bitwise.MixedPatternRules — Pattern-based Rewrite Rules

  Converts the 10 MixedSoundRule from BitwiseRules.lean to Pattern-based
  RewriteRule MixedNodeOp for use in e-graph saturation.

  7 structural rules (direct Pattern rewrites):
  - shift_right_compose, shift_left_compose
  - and_self, and_comm, or_comm, xor_self_zero, xor_comm

  3 bridge rules (semantic equivalences, also as Pattern where possible):
  - shiftLeft_mul_bridge: shiftLeft(x, n) ↔ mulGate(x, constGate(2^n))
  - mask_mod_bridge: annotation only (no 'mod' in MixedNodeOp)
  - shiftRight_div_bridge: annotation only (no 'div' in MixedNodeOp)
-/
import AmoLean.EGraph.Verified.Bitwise.MixedEMatch

namespace MixedPatternRules

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)
open MixedEMatch (Pattern PatVarId Substitution RewriteRule)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Helper — skeleton ops for patterns
-- ══════════════════════════════════════════════════════════════════

/-- Skeleton op for binary patterns. Uses distinct child IDs (0, 1) so that
    Pattern.eval's zip-based lookup can distinguish the two children. -/
def skelBitAnd : MixedNodeOp := .bitAnd 0 1
def skelBitOr  : MixedNodeOp := .bitOr 0 1
def skelBitXor : MixedNodeOp := .bitXor 0 1
def skelAddGate : MixedNodeOp := .addGate 0 1
def skelMulGate : MixedNodeOp := .mulGate 0 1

/-- Skeleton op for shift with specific shift amount n. -/
def skelShiftRight (n : Nat) : MixedNodeOp := .shiftRight 0 n
def skelShiftLeft (n : Nat) : MixedNodeOp := .shiftLeft 0 n

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Shift composition rules (parametric in a, b)
-- ══════════════════════════════════════════════════════════════════

/-- `shiftRight(shiftRight(x, a), b) → shiftRight(x, a + b)` -/
def patShiftRightCompose (a b : Nat) : RewriteRule MixedNodeOp where
  name := "shift_right_compose"
  lhs := .node (skelShiftRight b) [.node (skelShiftRight a) [.patVar 0]]
  rhs := .node (skelShiftRight (a + b)) [.patVar 0]

/-- `shiftLeft(shiftLeft(x, a), b) → shiftLeft(x, a + b)` -/
def patShiftLeftCompose (a b : Nat) : RewriteRule MixedNodeOp where
  name := "shift_left_compose"
  lhs := .node (skelShiftLeft b) [.node (skelShiftLeft a) [.patVar 0]]
  rhs := .node (skelShiftLeft (a + b)) [.patVar 0]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Bitwise identities
-- ══════════════════════════════════════════════════════════════════

/-- `bitAnd(x, x) → x` -/
def patAndSelf : RewriteRule MixedNodeOp where
  name := "and_self"
  lhs := .node skelBitAnd [.patVar 0, .patVar 0]
  rhs := .patVar 0

/-- `bitAnd(x, y) → bitAnd(y, x)` -/
def patAndComm : RewriteRule MixedNodeOp where
  name := "and_comm"
  lhs := .node skelBitAnd [.patVar 0, .patVar 1]
  rhs := .node skelBitAnd [.patVar 1, .patVar 0]

/-- `bitOr(x, y) → bitOr(y, x)` -/
def patOrComm : RewriteRule MixedNodeOp where
  name := "or_comm"
  lhs := .node skelBitOr [.patVar 0, .patVar 1]
  rhs := .node skelBitOr [.patVar 1, .patVar 0]

/-- `bitXor(x, x) → negGate(x)` (negGate always evaluates to 0 on Nat).
    Uses negGate instead of constGate(0) to avoid env-dependence. -/
def patXorSelfZero : RewriteRule MixedNodeOp where
  name := "xor_self_zero"
  lhs := .node skelBitXor [.patVar 0, .patVar 0]
  rhs := .node (.negGate 0) [.patVar 0]

/-- `bitXor(x, y) → bitXor(y, x)` -/
def patXorComm : RewriteRule MixedNodeOp where
  name := "xor_comm"
  lhs := .node skelBitXor [.patVar 0, .patVar 1]
  rhs := .node skelBitXor [.patVar 1, .patVar 0]

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Bridge rules (structural, where possible)
-- ══════════════════════════════════════════════════════════════════

/-- `shiftLeft(x, n) → mulGate(x, constGate(2^n))`
    Bridge: shift-left is multiplication by power of two. -/
def patShiftLeftMulBridge (n : Nat) : RewriteRule MixedNodeOp where
  name := "shiftLeft_mul_bridge"
  lhs := .node (skelShiftLeft n) [.patVar 0]
  rhs := .node skelMulGate [.patVar 0, .node (.constGate (2 ^ n)) []]

/-- `bitAnd(x, constMask(n)) → bitAnd(x, constMask(n))`
    Bridge annotation: establishes that `x &&& (2^n - 1) = x % 2^n`.
    Identity rule — actual equivalence is semantic (MixedSoundRule in BitwiseRules). -/
def patMaskModBridge (n : Nat) : RewriteRule MixedNodeOp where
  name := "mask_mod_bridge"
  lhs := .node skelBitAnd [.patVar 0, .node (.constMask n) []]
  rhs := .node skelBitAnd [.patVar 0, .node (.constMask n) []]

/-- `shiftRight(x, n) → shiftRight(x, n)`
    Bridge annotation: establishes that `x >>> n = x / 2^n`.
    Identity rule — actual equivalence is semantic (MixedSoundRule in BitwiseRules). -/
def patShiftRightDivBridge (n : Nat) : RewriteRule MixedNodeOp where
  name := "shiftRight_div_bridge"
  lhs := .node (skelShiftRight n) [.patVar 0]
  rhs := .node (skelShiftRight n) [.patVar 0]

-- ══════════════════════════════════════════════════════════════════
-- Section 4b: Shift-add decomposition rules (uses subGate)
-- ══════════════════════════════════════════════════════════════════

def skelSubGate : MixedNodeOp := .subGate 0 1

/-- `x * (2^k - 1) → (x << k) - x` — shift-sub decomposition.
    Replaces multiplication by Mersenne-1 constant with shifts.
    Valid for any k. On ARM, saves 2 cycles (shift+sub=2 vs mul=3). -/
def patMulMersenneSub (k : Nat) : RewriteRule MixedNodeOp where
  name := s!"mul_{2^k-1}_to_shift_sub"
  lhs := .node skelMulGate [.patVar 0, .node (.constGate (2^k - 1)) []]
  rhs := .node skelSubGate [.node (skelShiftLeft k) [.patVar 0], .patVar 0]

/-- Concrete instances for Plonky3 correction constants. -/
def patMulBabyBearCorrSub : RewriteRule MixedNodeOp := patMulMersenneSub 27   -- 2^27-1 = 134217727
def patMulKoalaBearCorrSub : RewriteRule MixedNodeOp := patMulMersenneSub 24  -- 2^24-1 = 16777215
def patMulGoldilocksCorrSub : RewriteRule MixedNodeOp := patMulMersenneSub 32 -- 2^32-1 = 4294967295

/-- Also commuted: `(2^k - 1) * x → (x << k) - x` -/
def patMulMersenneSubComm (k : Nat) : RewriteRule MixedNodeOp where
  name := s!"mul_{2^k-1}_to_shift_sub_comm"
  lhs := .node skelMulGate [.node (.constGate (2^k - 1)) [], .patVar 0]
  rhs := .node skelSubGate [.node (skelShiftLeft k) [.patVar 0], .patVar 0]

/-- `smulGate(2^k - 1, x) → (x << k) - x` — shift-sub for scalar multiply.
    This is the form the field fold rules actually produce in the e-graph. -/
def patSmulMersenneSub (k : Nat) : RewriteRule MixedNodeOp where
  name := s!"smul_{2^k-1}_to_shift_sub"
  lhs := .node (.smulGate (2^k - 1) 0) [.patVar 0]
  rhs := .node skelSubGate [.node (skelShiftLeft k) [.patVar 0], .patVar 0]

/-- All shift-add decomposition rules for Phase 3.
    Includes both mulGate and smulGate variants. -/
def shiftAddPatternRules : List (RewriteRule MixedNodeOp) :=
  [ -- mulGate variants (for explicit multiplication nodes)
    patMulMersenneSub 27,  patMulMersenneSubComm 27   -- BabyBear
  , patMulMersenneSub 24,  patMulMersenneSubComm 24   -- KoalaBear
  , patMulMersenneSub 32,  patMulMersenneSubComm 32   -- Goldilocks
    -- smulGate variants (the form field fold rules actually produce)
  , patSmulMersenneSub 27                              -- BabyBear
  , patSmulMersenneSub 24                              -- KoalaBear
  , patSmulMersenneSub 32                              -- Goldilocks
  ]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Rule collections
-- ══════════════════════════════════════════════════════════════════

/-- All structural rewrite rules (7 non-trivial rewrites + 1 bridge).
    These are the rules that actually modify the e-graph during saturation. -/
def allBitwisePatternRules (shiftA shiftB : Nat := 4) (maskN : Nat := 8)
    : List (RewriteRule MixedNodeOp) :=
  [ patShiftRightCompose shiftA shiftB
  , patShiftLeftCompose shiftA shiftB
  , patAndSelf
  , patAndComm
  , patOrComm
  , patXorSelfZero
  , patXorComm
  , patShiftLeftMulBridge maskN
  ]

/-- All 10 rules including bridge annotations. -/
def allBitwisePatternRulesWithBridges (shiftA shiftB : Nat := 4) (maskN : Nat := 8)
    : List (RewriteRule MixedNodeOp) :=
  allBitwisePatternRules shiftA shiftB maskN ++
  [ patMaskModBridge maskN
  , patShiftRightDivBridge maskN
  ]

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

example : (allBitwisePatternRules).length = 8 := rfl

example : (allBitwisePatternRulesWithBridges).length = 10 := rfl

example : (patAndSelf).name = "and_self" := rfl

example : (patXorSelfZero).name = "xor_self_zero" := rfl

example : (patShiftRightCompose 4 4).name = "shift_right_compose" := rfl

example : (patShiftLeftMulBridge 8).name = "shiftLeft_mul_bridge" := rfl

end MixedPatternRules
