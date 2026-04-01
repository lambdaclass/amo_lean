/-
  AMO-Lean Ultra — Ruler Bridge
  Converts RuleCandidate (Ruler CVec discovery) to RewriteRule MixedNodeOp (e-graph saturation).

  The Ruler discovers equivalences via concrete evaluation (CVec matching).
  The e-graph saturates via pattern-based rewriting.
  This bridge maps function names in RuleCandidates to Pattern MixedNodeOp
  via a hand-written registry.

  Consumes: RulerDiscovery (RuleCandidate), MixedEMatch (RewriteRule, Pattern)
  Consumed by: UltraPipeline (feeds discovered rules into saturate)
-/
import AmoLean.EGraph.Verified.Bitwise.RulerDiscovery
import AmoLean.EGraph.Verified.Bitwise.MixedEMatch

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.RulerBridge

open AmoLean.EGraph.Verified.Bitwise.Ruler (RuleCandidate CVecMatchMode
  discoverRules nttTestInputs)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)
open MixedEMatch (Pattern RewriteRule)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Name → Pattern Registry
-- ══════════════════════════════════════════════════════════════════

/-- Map a Ruler function name to its Pattern MixedNodeOp representation.
    The `p` parameter is the field prime (for reduceGate/harveyReduce).
    The `k` is shift bits, `c` is the Solinas constant (for shift patterns).

    sameShape (MixedEMatch.lean:90) zeroes all EClassId children before comparison,
    so the 0 placeholders in constructor args are ignored during matching. -/
def nameToPattern (name : String) (p k c : Nat) : Option (Pattern MixedNodeOp) :=
  -- Reduction strategies: both "solinas_fold" and "mod_reduce" are generic reduction
  if name == "solinas_fold" || name == "mod_reduce" then
    some (.node (.reduceGate 0 p) [.patVar 0])
  else if name == "harvey_cond" then
    some (.node (.harveyReduce 0 p) [.patVar 0])
  -- Shift decomposition patterns (KoalaBear: x * c = (x << k) - x)
  else if name == "mul_const" then
    some (.node (.mulGate 0 0) [.patVar 0, .node (.constGate c) []])
  else if name == "shift_sub" then
    some (.node (.subGate 0 0) [.node (.shiftLeft 0 k) [.patVar 0], .patVar 0])
  else
    none

-- ══════════════════════════════════════════════════════════════════
-- Section 2: RuleCandidate → RewriteRule Conversion
-- ══════════════════════════════════════════════════════════════════

/-- Convert a RuleCandidate (Ruler discovery) to a RewriteRule MixedNodeOp.
    Returns none if either LHS or RHS name is not in the registry. -/
def ruleCandidateToRewriteRule (rc : RuleCandidate) (p k c : Nat) :
    Option (RewriteRule MixedNodeOp) := do
  let lhsPat ← nameToPattern rc.lhsName p k c
  let rhsPat ← nameToPattern rc.rhsName p k c
  some {
    name := rc.name
    lhs := lhsPat
    rhs := rhsPat
    sideCondCheck := none
  }

/-- Convert all RuleCandidates to RewriteRules, filtering unresolvable names. -/
def ruleCandidatesToRewriteRules (candidates : List RuleCandidate) (p k c : Nat) :
    List (RewriteRule MixedNodeOp) :=
  candidates.filterMap (ruleCandidateToRewriteRule · p k c)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Parametric Discovery
-- ══════════════════════════════════════════════════════════════════

/-- Discover reduction equivalences for ANY prime.
    Generalizes discoverBabyBearRules by taking p (prime), k (shift bits),
    c (Solinas constant) as parameters. -/
def discoverReductionRules (p k c : Nat) : List RuleCandidate :=
  let solinasFold (x : Nat) : Nat := (x >>> k) * c + (x &&& (2^k - 1))
  let modReduce (x : Nat) : Nat := x % p
  let harveyCond (x : Nat) : Nat := if x ≥ p then x - p else x
  discoverRules
    [("solinas_fold", solinasFold),
     ("mod_reduce", modReduce),
     ("harvey_cond", harveyCond)]
    nttTestInputs (.modN p)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- nameToPattern resolves known names. -/
example : (nameToPattern "solinas_fold" 2013265921 31 134217727).isSome = true := rfl
example : (nameToPattern "harvey_cond" 2013265921 31 0).isSome = true := rfl
example : (nameToPattern "mul_const" 0 24 16777215).isSome = true := rfl
example : (nameToPattern "shift_sub" 0 24 0).isSome = true := rfl
example : (nameToPattern "unknown" 0 0 0).isNone = true := rfl

/-- Parametric discovery finds rules for BabyBear. -/
example : (discoverReductionRules 2013265921 31 134217727).length > 0 := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.RulerBridge
