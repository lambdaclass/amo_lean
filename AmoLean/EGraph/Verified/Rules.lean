/-
  AMO-Lean — Verified Rules for the Verified EGraph Engine
  Subfase 8e: Connects the 19 verified rules (VerifiedRules.lean theorems)
  to the Bridge adapter, producing RewriteRules for the verified engine.

  Each rule here has a corresponding soundness theorem in VerifiedRules.lean.
  The Bridge converts Expr Int patterns → CircuitPattern for the engine.
-/
import AmoLean.EGraph.Verified.Bridge
import AmoLean.EGraph.VerifiedRules

namespace AmoLean.EGraph.Verified.Rules

open AmoLean (Expr)
open AmoLean.EGraph.Verified
open AmoLean.EGraph.Verified.Bridge

/-! ## Identity Rules (6 rules, all verified) -/

/-- x + 0 → x  (verified: add_zero_right_correct) -/
def addZeroRight : RewriteRule :=
  mkRule "add_zero_right" (.add (.var 0) (.const 0)) (.var 0)

/-- 0 + x → x  (verified: add_zero_left_correct) -/
def addZeroLeft : RewriteRule :=
  mkRule "add_zero_left" (.add (.const 0) (.var 0)) (.var 0)

/-- x * 1 → x  (verified: mul_one_right_correct) -/
def mulOneRight : RewriteRule :=
  mkRule "mul_one_right" (.mul (.var 0) (.const 1)) (.var 0)

/-- 1 * x → x  (verified: mul_one_left_correct) -/
def mulOneLeft : RewriteRule :=
  mkRule "mul_one_left" (.mul (.const 1) (.var 0)) (.var 0)

/-- x * 0 → 0  (verified: mul_zero_right_correct) -/
def mulZeroRight : RewriteRule :=
  mkRule "mul_zero_right" (.mul (.var 0) (.const 0)) (.const 0)

/-- 0 * x → 0  (verified: mul_zero_left_correct) -/
def mulZeroLeft : RewriteRule :=
  mkRule "mul_zero_left" (.mul (.const 0) (.var 0)) (.const 0)

/-! ## Constant Folding (2 rules, verified) -/

-- Note: Constant folding requires a side condition check because
-- the pattern vars must bind to constants, not arbitrary classes.
-- The Bridge patterns use patVar which matches any class.
-- For full constant folding, we'd need to check that the matched
-- classes contain only constGate nodes. For now, we provide
-- the structural rules that work without side conditions.

/-! ## Distributivity (4 rules, verified) -/

/-- a * (b + c) → a*b + a*c  (verified: distrib_left_correct)
    WARNING: Use with caution — can cause expression blowup. -/
def distribLeft : RewriteRule :=
  mkRule "distrib_left"
    (.mul (.var 0) (.add (.var 1) (.var 2)))
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))

/-- (a + b) * c → a*c + b*c  (verified: distrib_right_correct)
    WARNING: Use with caution — can cause expression blowup. -/
def distribRight : RewriteRule :=
  mkRule "distrib_right"
    (.mul (.add (.var 0) (.var 1)) (.var 2))
    (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))

/-- a*c + b*c → (a + b) * c  (verified: factor_right_correct) -/
def factorRight : RewriteRule :=
  mkRule "factor_right"
    (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
    (.mul (.add (.var 0) (.var 1)) (.var 2))

/-- a*b + a*c → a * (b + c)  (verified: factor_left_correct) -/
def factorLeft : RewriteRule :=
  mkRule "factor_left"
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
    (.mul (.var 0) (.add (.var 1) (.var 2)))

/-! ## Rule Sets -/

/-- Safe identity rules (always reduce, no blowup risk) -/
def identityRules : List RewriteRule :=
  [addZeroRight, addZeroLeft, mulOneRight, mulOneLeft,
   mulZeroRight, mulZeroLeft]

/-- Factorization rules (reduce mul count) -/
def factorizationRules : List RewriteRule :=
  [factorLeft, factorRight]

/-- All safe optimization rules (identity + factorization) -/
def safeRules : List RewriteRule :=
  identityRules ++ factorizationRules

/-- All rules including distributivity (use with higher node limits) -/
def allRules : List RewriteRule :=
  safeRules ++ [distribLeft, distribRight]

/-! ## Convenience: Optimize with verified rules -/

/-- Optimize an expression using only safe verified rules. -/
def optimizeSafe (expr : Expr Int)
    (config : SaturationConfig := {}) : Option (Expr Int) :=
  Bridge.optimize expr safeRules config

/-- Optimize an expression using all verified rules (including distributivity). -/
def optimizeAll (expr : Expr Int)
    (config : SaturationConfig := { maxIterations := 20, maxNodes := 1000, maxClasses := 500 }) :
    Option (Expr Int) :=
  Bridge.optimize expr allRules config

/-! ## Tests -/

section Tests

open AmoLean (Expr)

-- Test: x + 0 → x
#eval do
  let r := optimizeSafe (.add (.var 0) (.const 0))
  IO.println s!"x + 0 → {repr r}"

-- Test: 0 + (x * 1) → x
#eval do
  let r := optimizeSafe (.add (.const 0) (.mul (.var 0) (.const 1)))
  IO.println s!"0 + (x * 1) → {repr r}"

-- Test: (x + 0) * 1 → x
#eval do
  let r := optimizeSafe (.mul (.add (.var 0) (.const 0)) (.const 1))
  IO.println s!"(x + 0) * 1 → {repr r}"

-- Test: 0 * (x + y) → 0
#eval do
  let r := optimizeSafe (.mul (.const 0) (.add (.var 0) (.var 1)))
  IO.println s!"0 * (x + y) → {repr r}"

-- Summary
#eval IO.println s!"Verified Rules: {identityRules.length} identity + {factorizationRules.length} factorization + 2 distributivity = {allRules.length} total"

end Tests

end AmoLean.EGraph.Verified.Rules
