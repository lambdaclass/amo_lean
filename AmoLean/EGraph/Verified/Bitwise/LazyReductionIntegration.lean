/-
  AmoLean.EGraph.Verified.Bitwise.LazyReductionIntegration — B74

  Connect the lazy reduction spike to the MixedRunner pipeline.
  When the e-graph has a `reduceGate` node, check if bounds allow
  deferring reduction.

  Key components:
  - `BoundedEGraph`: e-graph with per-class upper bounds (function-based)
  - `propagateBounds`: compute output bound from a `MixedNodeOp`
  - `shouldInsertReduce`: decide when reduction is mandatory
  - `initBounds`: initialize witness bounds
  - `butterflySafeIters`: max lazy iterations before overflow
-/
import AmoLean.EGraph.Verified.Bitwise.LazyReductionSpike_aux
import AmoLean.EGraph.Verified.Bitwise.Discovery.LazyReduction

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.LazyReductionIntegration

open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)
open AmoLean.EGraph.Verified.Bitwise.Discovery (IntervalBound canDeferReduction)
open AmoLean.EGraph.Verified.Bitwise.LazyReductionSpike (canDeferReduce canLazyNTT)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: BoundedEGraph — e-graph with per-class upper bounds
-- ══════════════════════════════════════════════════════════════════

/-- An e-graph annotated with upper bounds per e-class.
    `bounds` is a function mapping each e-class id to its upper bound.
    Uses a function rather than a HashMap for simplicity and decidability. -/
structure BoundedEGraph where
  /-- Upper bound for each e-class. -/
  bounds : EClassId → Nat
  /-- The target prime modulus. -/
  prime : Nat
  /-- Machine word width in bits. -/
  wordWidth : Nat

/-- Default BoundedEGraph: all bounds are 0, prime = 0, wordWidth = 64. -/
instance : Inhabited BoundedEGraph :=
  ⟨{ bounds := fun _ => 0, prime := 0, wordWidth := 64 }⟩

/-- Look up the bound for an e-class. -/
def BoundedEGraph.getBound (bg : BoundedEGraph) (id : EClassId) : Nat :=
  bg.bounds id

-- ══════════════════════════════════════════════════════════════════
-- Section 2: propagateBounds — compute output bound from node type
-- ══════════════════════════════════════════════════════════════════

/-- Compute the upper bound of a node's output given bounds on its children.
    Each operation has a sound over-approximation:
    - addGate(a,b):    bound(a) + bound(b)
    - mulGate(a,b):    bound(a) * bound(b)
    - reduceGate(a,p): p - 1 (always bounded by prime - 1 after reduction)
    - subGate(a,b):    bound(a) (truncated sub cannot exceed a)
    - shiftRight(a,n): bound(a) / 2^n + 1 (ceiling division)
    - shiftLeft(a,n):  bound(a) * 2^n
    - constGate(n):    n
    - witness(n):      from BoundedEGraph (default: full word)
    - other unary:     bound(a)
    - other binary:    bound(a) + bound(b) -/
def propagateBounds (op : MixedNodeOp) (bg : BoundedEGraph) : Nat :=
  match op with
  | .addGate a b     => bg.getBound a + bg.getBound b
  | .mulGate a b     => bg.getBound a * bg.getBound b
  | .reduceGate _ p  => if p > 0 then p - 1 else 0
  | .subGate a _     => bg.getBound a
  | .shiftRight a n  => bg.getBound a / 2 ^ n + 1
  | .shiftLeft a n   => bg.getBound a * 2 ^ n
  | .constGate n     => n
  | .witness _       => 2 ^ bg.wordWidth - 1
  | .pubInput _      => 2 ^ bg.wordWidth - 1
  | .smulGate _ a    => bg.getBound a * (2 ^ bg.wordWidth - 1)
  | .negGate a       => bg.getBound a
  | .bitAnd a b      => min (bg.getBound a) (bg.getBound b)
  | .bitXor a b      => bg.getBound a + bg.getBound b
  | .bitOr a b       => bg.getBound a + bg.getBound b
  | .constMask n     => 2 ^ n - 1
  | .kronPack a b w  => bg.getBound a + bg.getBound b * 2 ^ w
  | .kronUnpackLo _ w => 2 ^ w - 1
  | .kronUnpackHi a w => bg.getBound a / 2 ^ w + 1
  -- Modular reduction alternatives: all produce x % p, so bound is p - 1
  | .montyReduce _ p _   => if p > 0 then p - 1 else 0
  | .barrettReduce _ p _ => if p > 0 then p - 1 else 0
  | .harveyReduce _ p    => if p > 0 then p - 1 else 0

-- ══════════════════════════════════════════════════════════════════
-- Section 3: shouldInsertReduce — decide when reduction is mandatory
-- ══════════════════════════════════════════════════════════════════

/-- Should we insert a `reduceGate` after this operation?
    True when the accumulated bound threatens overflow:
    - bound >= 2^wordWidth (direct overflow), OR
    - bound >= p * p (multiplying two values this large would overflow even with
      lazy reduction on the product) -/
def shouldInsertReduce (bound : Nat) (p : Nat) (wordWidth : Nat) : Bool :=
  bound >= 2 ^ wordWidth || bound >= p * p

/-- Correctness: if shouldInsertReduce is false, the bound fits in the word. -/
theorem shouldInsertReduce_false_fits (bound p wordWidth : Nat)
    (h : shouldInsertReduce bound p wordWidth = false) :
    bound < 2 ^ wordWidth := by
  simp [shouldInsertReduce, Bool.or_eq_false_iff] at h
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 4: initBounds — initialize e-class bounds
-- ══════════════════════════════════════════════════════════════════

/-- Initialize a BoundedEGraph where all e-classes have the same input bound.
    In practice, witness nodes start with `inputBound` (typically `p - 1`). -/
def initBounds (inputBound : Nat) (p wordWidth : Nat) : BoundedEGraph :=
  { bounds := fun _ => inputBound
    prime := p
    wordWidth := wordWidth }

/-- Initialize with a specific list of (id, bound) pairs. Other ids get `defaultBound`. -/
def initBoundsFrom (pairs : List (EClassId × Nat)) (defaultBound : Nat)
    (p wordWidth : Nat) : BoundedEGraph :=
  { bounds := fun id =>
      match pairs.find? (fun pair => pair.1 == id) with
      | some (_, b) => b
      | none => defaultBound
    prime := p
    wordWidth := wordWidth }

/-- Insert/update a bound for a single e-class. -/
def BoundedEGraph.insertBound (bg : BoundedEGraph) (id : EClassId) (bound : Nat) :
    BoundedEGraph :=
  { bg with bounds := fun id' => if id' == id then bound else bg.bounds id' }

-- ══════════════════════════════════════════════════════════════════
-- Section 5: butterflySafeIters — max lazy iterations before overflow
-- ══════════════════════════════════════════════════════════════════

/-- Maximum number of butterfly iterations that can be performed lazily
    (without intermediate reduction) before overflow.

    Each butterfly layer roughly doubles the bound. Starting from `p`,
    after `k` layers the bound is approximately `2^k * p`.
    We need `2^k * p < 2^wordWidth`, so `k < wordWidth - Nat.log2 p`.

    Returns 0 if `p = 0` (degenerate case). -/
def butterflySafeIters (p : Nat) (wordWidth : Nat) : Nat :=
  if p == 0 then 0
  else
    let logP := Nat.log2 p
    if wordWidth > logP then wordWidth - logP - 1
    else 0

/-- butterflySafeIters is consistent with canLazyNTT from the spike:
    computes `wordWidth - log2(p) - 1` for positive `p`. -/
theorem butterflySafeIters_spec (p wordWidth : Nat) (hp : 0 < p)
    (hpw : Nat.log2 p < wordWidth) :
    butterflySafeIters p wordWidth = wordWidth - Nat.log2 p - 1 := by
  simp [butterflySafeIters, Nat.ne_of_gt hp, hpw]

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Integration helpers
-- ══════════════════════════════════════════════════════════════════

/-- Process a node: compute its bound and decide whether to insert a reduce.
    Returns `(outputBound, needsReduce)`. -/
def processNode (op : MixedNodeOp) (bg : BoundedEGraph) : Nat × Bool :=
  let bound := propagateBounds op bg
  (bound, shouldInsertReduce bound bg.prime bg.wordWidth)

/-- Process a node and update the BoundedEGraph with the result.
    Returns `(updatedBG, needsReduce)`. -/
def processAndUpdate (op : MixedNodeOp) (outputId : EClassId)
    (bg : BoundedEGraph) : BoundedEGraph × Bool :=
  let (bound, needsReduce) := processNode op bg
  (bg.insertBound outputId bound, needsReduce)

/-- Batch-process a list of (node, outputId) pairs, threading bounds through. -/
def processNodeList (ops : List (MixedNodeOp × EClassId))
    (bg : BoundedEGraph) : BoundedEGraph × List (EClassId × Bool) :=
  ops.foldl (fun (acc : BoundedEGraph × List (EClassId × Bool)) pair =>
    let (bg', results) := acc
    let (op, outId) := pair
    let (bg'', needsReduce) := processAndUpdate op outId bg'
    (bg'', results ++ [(outId, needsReduce)])
  ) (bg, [])

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke tests
-- ══════════════════════════════════════════════════════════════════

private def testBg : BoundedEGraph := initBounds 100 31 64

/-- Smoke: propagateBounds for addGate. -/
example : propagateBounds (.addGate 0 1) testBg = 200 := rfl

/-- Smoke: propagateBounds for mulGate. -/
example : propagateBounds (.mulGate 0 1) testBg = 10000 := rfl

/-- Smoke: propagateBounds for reduceGate always returns p-1. -/
example : propagateBounds (.reduceGate 0 31) testBg = 30 := rfl

/-- Smoke: propagateBounds for subGate returns bound(a). -/
example : propagateBounds (.subGate 0 1) testBg = 100 := rfl

/-- Smoke: propagateBounds for shiftRight. -/
example : propagateBounds (.shiftRight 0 2) testBg = 26 := rfl

/-- Smoke: shouldInsertReduce is false when well within bounds. -/
example : shouldInsertReduce 200 31 64 = false := by native_decide

/-- Smoke: shouldInsertReduce triggers on overflow. -/
example : shouldInsertReduce (2^64) 31 64 = true := by native_decide

/-- Smoke: shouldInsertReduce triggers when bound >= p*p. -/
example : shouldInsertReduce 961 31 64 = true := by native_decide

/-- Smoke: butterflySafeIters for BabyBear (p ~ 2^31) in u64. -/
example : butterflySafeIters (2^31) 64 = 32 := by native_decide

/-- Smoke: butterflySafeIters for small prime in u32. -/
example : butterflySafeIters 31 32 = 27 := by native_decide

/-- Smoke: processNode returns correct bound and needsReduce. -/
example : processNode (.addGate 0 1) testBg = (200, false) := rfl

/-- Smoke: insertBound updates a single class. -/
example : (testBg.insertBound 0 500).getBound 0 = 500 := rfl

/-- Smoke: insertBound does not affect other classes. -/
example : (testBg.insertBound 0 500).getBound 1 = 100 := rfl

/-- Smoke: initBoundsFrom with specific pairs. -/
example : (initBoundsFrom [(0, 50), (1, 200)] 100 31 64).getBound 0 = 50 := rfl

end AmoLean.EGraph.Verified.Bitwise.LazyReductionIntegration
