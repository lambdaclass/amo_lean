/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.VerificationOracle

  N26.5: Post-extraction verification oracle for discovered MixedExpr candidates.
  Verifies that a candidate expression semantically matches the reduce specification
  (x % p) via test-based and formal verification.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedExtract
import AmoLean.EGraph.Verified.Bitwise.Discovery.ReduceSpecAxiom

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified (CircuitEnv)

-- ════════════════════════════════════════════════════════════════
-- Section 1: evalMixedExpr — evaluation alias
-- ════════════════════════════════════════════════════════════════

/-- Evaluate a MixedExpr in an environment. Alias for MixedExpr.eval. -/
abbrev evalMixedExpr (expr : MixedExpr) (env : MixedEnv) : Nat :=
  expr.eval env

-- ════════════════════════════════════════════════════════════════
-- Section 2: VerificationResult
-- ════════════════════════════════════════════════════════════════

/-- Result of verifying a candidate expression against a reduce spec. -/
inductive VerificationResult where
  | verified (p : Nat)
  | failed (p : Nat) (counterexample : Nat)
  | untested

/-- Check if a VerificationResult is verified. -/
def VerificationResult.isVerified : VerificationResult → Bool
  | .verified _ => true
  | _ => false

/-- Check if a VerificationResult is failed. -/
def VerificationResult.isFailed : VerificationResult → Bool
  | .failed _ _ => true
  | _ => false

-- ════════════════════════════════════════════════════════════════
-- Section 3: testVerify — test-based verification
-- ════════════════════════════════════════════════════════════════

/-- Build a MixedEnv where witness 0 = x, everything else = 0. -/
def mkWitnessEnv (x : Nat) : MixedEnv :=
  { constVal := fun _ => 0, witnessVal := fun _ => x, pubInputVal := fun _ => 0 }

/-- Test-based verification: check that expr computes x % p on a set of test inputs. -/
def testVerify (expr : MixedExpr) (p : Nat) (testInputs : List Nat) : VerificationResult :=
  if p == 0 then .failed p 0
  else
    match testInputs.find? (fun x =>
      evalMixedExpr expr (mkWitnessEnv x) != x % p) with
    | some cx => .failed p cx
    | none => .verified p

-- ════════════════════════════════════════════════════════════════
-- Section 4: defaultTestInputs
-- ════════════════════════════════════════════════════════════════

/-- Default test inputs: boundary values, multiples of p, and large values. -/
def defaultTestInputs (p : Nat) : List Nat :=
  [0, 1, p - 1, p, p + 1, 2 * p - 1, 2 * p, 3 * p + 7, 1000000007, 2 ^ 31]

-- ════════════════════════════════════════════════════════════════
-- Section 5: verifyCandidate — high-level API
-- ════════════════════════════════════════════════════════════════

/-- Verify a candidate expression against a ReduceSpec. -/
def verifyCandidate (expr : MixedExpr) (spec : ReduceSpec) : VerificationResult :=
  testVerify expr spec.p (defaultTestInputs spec.p)

-- ════════════════════════════════════════════════════════════════
-- Section 6: FormalVerification
-- ════════════════════════════════════════════════════════════════

/-- A MixedExpr is formally verified to compute x % p when it evaluates
    to x % p for all possible witness values. -/
def FormallyVerified (expr : MixedExpr) (p : Nat) : Prop :=
  ∀ (x : Nat),
    evalMixedExpr expr (mkWitnessEnv x) = x % p

/-- reduceE (witnessE 0) trivially computes x % p by definition. -/
theorem reduceE_formally_verified (p : Nat) :
    FormallyVerified (.reduceE (.witnessE 0) p) p := by
  intro x
  simp [evalMixedExpr, mkWitnessEnv, MixedExpr.eval]

/-- evalMixedOp for reduceGate directly computes x % p. -/
theorem reduceE_spec (p x : Nat) :
    evalMixedOp (.reduceGate 0 p)
      (mkWitnessEnv x)
      (fun _ => x) = x % p := by
  simp [evalMixedOp]

-- ════════════════════════════════════════════════════════════════
-- Section 7: Smoke tests
-- ════════════════════════════════════════════════════════════════

-- reduceE passes test verification for BabyBear
example : (verifyCandidate (.reduceE (.witnessE 0) 2013265921) babybearSpec).isVerified = true := by
  native_decide

-- witness alone fails verification (it's not x % p)
example : (verifyCandidate (.witnessE 0) babybearSpec).isFailed = true := by
  native_decide

-- FormallyVerified is non-vacuous: concrete instance for BabyBear prime
example : FormallyVerified (.reduceE (.witnessE 0) 2013265921) 2013265921 :=
  reduceE_formally_verified 2013265921

end AmoLean.EGraph.Verified.Bitwise.Discovery
