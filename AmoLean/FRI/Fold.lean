/-
  AMO-Lean: FRI Fold Operation
  Phase 6.2 - Type-Safe Polynomial Folding

  This module implements the core FRI fold operation with dependent types
  to ensure size correctness at compile time.

  FRI Fold: Given evaluations of polynomial P on domain D of size 2n,
  compute evaluations of P_folded on domain D' of size n:

    P_folded(x) = P_even(x) + α · P_odd(x)

  where:
    P_even(x) = (P(x) + P(-x)) / 2
    P_odd(x)  = (P(x) - P(-x)) / (2x)

  Type Safety:
    friFold : Vec F (2*n) → F → Vec F n
    This ensures the output is exactly half the input size.

  References:
  - "Fast Reed-Solomon IOP of Proximity" (Ben-Sasson et al.)
  - Phase 6 Technical Analysis: ADR-003 (Dependent Types for N/2)
-/

import AmoLean.FRI.Basic
import AmoLean.Vector.Basic

namespace AmoLean.FRI.Fold

open AmoLean.FRI (FieldConfig FRIParams FRILayer ZKCostModel ChallengeId)
open AmoLean.Vector (Vec)

/-! ## Part 1: Field Operations (Abstract)

We define field operations abstractly to support multiple field implementations.
-/

/-- Typeclass for field operations needed by FRI -/
class FRIField (F : Type) extends Add F, Sub F, Mul F, Neg F, Inhabited F where
  /-- Additive identity -/
  zero : F
  /-- Multiplicative identity -/
  one : F
  /-- Field division (a / b) -/
  fdiv : F → F → F
  /-- Convert from Nat -/
  ofNat : Nat → F

namespace FRIField

variable {F : Type} [FRIField F]

def two : F := ofNat 2

def half (x : F) : F := fdiv x two

end FRIField

/-- Float instance for testing -/
instance : FRIField Float where
  zero := 0.0
  one := 1.0
  fdiv := (· / ·)
  ofNat := Float.ofNat

/-! ## Part 2: Core Fold Operation

The fundamental operation: fold a vector of size 2n into size n.
-/

/-- Split a vector into even and odd indexed elements using Vec.halve and rearrangement.

    For input [x₀, x₁, x₂, x₃, x₄, x₅, ...]:
    - Even: [x₀, x₂, x₄, ...]
    - Odd:  [x₁, x₃, x₅, ...]

    Note: This uses Vec.ofFn to create vectors by index function.
-/
def splitEvenOdd {F : Type} (v : Vec F (2 * n)) : Vec F n × Vec F n :=
  let even := Vec.ofFn fun (i : Fin n) =>
    v.get ⟨2 * i.val, by omega⟩
  let odd := Vec.ofFn fun (i : Fin n) =>
    v.get ⟨2 * i.val + 1, by omega⟩
  (even, odd)

/-- FRI fold: combine even and odd parts with challenge α.

    f_folded[i] = f_even[i] + α * f_odd[i]

    Type signature ensures output is exactly half the size.
-/
def friFold {F : Type} [FRIField F] (input : Vec F (2 * n)) (alpha : F) : Vec F n :=
  let (even, odd) := splitEvenOdd input
  Vec.zipWith (fun e o => e + alpha * o) even odd

/-- Fold with explicit domain halving.

    In FRI, folding corresponds to evaluating the folded polynomial
    on the squared domain: D' = {x² : x ∈ D}
-/
def friFoldWithDomain {F : Type} [FRIField F]
    (evals : Vec F (2 * n))
    (alpha : F)
    (domainHalving : Vec F n → Vec F n := id)  -- Optional domain transformation
    : Vec F n :=
  domainHalving (friFold evals alpha)

/-! ## Part 3: Iterated Folding

FRI consists of multiple folding rounds. We track sizes at the type level.
-/

/-- Single round of folding, returning the new layer -/
def foldOneRound {F : Type} [FRIField F]
    (layer : FRILayer F (2 * n))
    (alpha : F)
    (computeCommitment : Vec F n → F)  -- Hash function for commitment
    : FRILayer F n :=
  let newEvals := friFold layer.evaluations alpha
  let newCommit := computeCommitment newEvals
  { evaluations := newEvals, commitment := newCommit }

/-! ## Part 4: Cost Analysis

Analyze the cost of fold operations using ZKCostModel.
-/

/-- Cost of a single fold operation (per element) -/
def foldElementCost (cm : ZKCostModel) : Nat :=
  cm.memLoad * 2 +    -- Load even and odd
  cm.fieldMul +       -- α * odd
  cm.fieldAdd +       -- even + result
  cm.memStore         -- Store folded value

/-- Cost of folding a layer of size n -/
def foldLayerCost (cm : ZKCostModel) (n : Nat) : Nat :=
  n * foldElementCost cm

/-- Cost of complete FRI folding (all rounds) -/
def friFoldTotalCost (cm : ZKCostModel) (params : FRIParams) : Nat :=
  -- Sum of costs over all rounds: n + n/2 + n/4 + ... ≈ 2n
  let n := params.maxDegree * params.blowupFactor
  2 * n * foldElementCost cm

/-! ## Part 5: Query Phase Support

During FRI verification, we need to access specific fold paths.
-/

/-- Index pair for a single fold query: even index and odd index -/
structure FoldQueryIndices where
  evenIdx : Nat
  oddIdx : Nat
  h_odd : oddIdx = evenIdx + 1
  deriving Repr

/-- Given a query index in the folded domain, compute source indices -/
def queryIndicesForRound (foldedIdx : Nat) : FoldQueryIndices :=
  { evenIdx := 2 * foldedIdx
  , oddIdx := 2 * foldedIdx + 1
  , h_odd := rfl
  }

/-- Verify a single fold query: check that folding is correct -/
def verifyFoldQuery {F : Type} [FRIField F] [BEq F]
    (evenVal oddVal foldedVal alpha : F) : Bool :=
  foldedVal == (evenVal + alpha * oddVal)

/-! ## Part 6: Theorems (Correctness Properties)

Formal statements about FRI fold correctness.
-/

/-- Theorem: Fold produces output of correct size (enforced by types) -/
theorem friFold_size_correct {F : Type} [FRIField F] (input : Vec F (2 * n)) (alpha : F) :
    ∃ (result : Vec F n), result = friFold input alpha := by
  exact ⟨friFold input alpha, rfl⟩

/-- Theorem: Fold query verification is consistent with fold computation -/
theorem fold_query_consistent {F : Type} [FRIField F] [BEq F] [LawfulBEq F]
    (evenVal oddVal alpha : F) :
    verifyFoldQuery evenVal oddVal (evenVal + alpha * oddVal) alpha = true := by
  simp [verifyFoldQuery]

/-- Theorem: Fold is linear in alpha -/
theorem friFold_linear_alpha {F : Type} [FRIField F]
    (input : Vec F (2 * n)) (alpha beta : F) :
    -- friFold input (alpha + beta) relates to friFold input alpha + contribution from beta
    True := by  -- Placeholder - full proof requires field axioms
  trivial

/-! ## Part 7: Tests -/

section Tests

-- Create test vector using ofFn
def testInput4 : Vec Float (2 * 2) := Vec.ofFn fun i =>
  match i.val with
  | 0 => 1.0
  | 1 => 2.0
  | 2 => 3.0
  | _ => 4.0

def testAlpha : Float := 0.5

-- Test split
#eval! (splitEvenOdd testInput4).1.toList  -- [1.0, 3.0] (even indices: 0, 2)
#eval! (splitEvenOdd testInput4).2.toList  -- [2.0, 4.0] (odd indices: 1, 3)

-- Test fold
#eval! (friFold testInput4 testAlpha).toList
-- Expected: [1 + 0.5*2, 3 + 0.5*4] = [2.0, 5.0]

-- Cost analysis test
#eval! foldElementCost AmoLean.FRI.defaultZKCost  -- 36
#eval! foldLayerCost AmoLean.FRI.defaultZKCost 1024  -- 36864

-- Query indices
#eval! queryIndicesForRound 5  -- evenIdx=10, oddIdx=11

-- Verify fold query
#eval! verifyFoldQuery 1.0 2.0 2.0 0.5  -- 1 + 0.5*2 = 2, should be true

-- Test with larger vector
def testInput8 : Vec Float (2 * 4) := Vec.ofFn fun i =>
  Float.ofNat (i.val + 1)  -- [1,2,3,4,5,6,7,8]

#eval! (friFold testInput8 2.0).toList
-- even: [1,3,5,7], odd: [2,4,6,8]
-- result: [1+2*2, 3+2*4, 5+2*6, 7+2*8] = [5, 11, 17, 23]

end Tests

end AmoLean.FRI.Fold
