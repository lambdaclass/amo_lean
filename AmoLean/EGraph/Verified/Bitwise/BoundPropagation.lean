/-
  AMO-Lean Ultra — Phase 22: BoundPropagation
  Domain-specific bound rules for NTT field arithmetic.

  Provides `BoundRuleFactory` constructors that generate FRESH
  bound rules each iteration, reading the CURRENT DAG state.

  Key exports:
  - `mkFieldFactory`: creates a BoundRuleFactory for a given field prime
  - `ReductionChoice`: solinasFold | montgomery | harvey | lazy
  - `stageBoundFactor`: compute output bound after a reduction
  - Theorems: reduce_bound, add_bound_prop, harvey_1br, etc.
-/
import AmoLean.EGraph.Verified.Bitwise.MultiRelMixed

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.BoundProp

open AmoLean.EGraph.VerifiedExtraction (EGraph EClassId ENode EClass)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp DirectedRelGraph BoundedByKP)
open AmoLean.EGraph.Verified.Bitwise.MultiRel (State BoundRule BoundRuleFactory)
open MixedPipeline (MixedEGraph)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Core Bound Theorems
-- ══════════════════════════════════════════════════════════════════

def reductionBoundFactor : MixedNodeOp → Nat
  | .reduceGate _ _ => 1
  | .montyReduce _ _ _ => 1
  | .barrettReduce _ _ _ => 1
  | .harveyReduce _ _ => 2
  | _ => 0

theorem reduce_bound (x p : Nat) (hp : 0 < p) : x % p < 1 * p := by
  rw [Nat.one_mul]; exact Nat.mod_lt x hp

theorem add_bound_prop (a b p k₁ k₂ : Nat) (ha : a < k₁ * p) (hb : b < k₂ * p) :
    a + b < (k₁ + k₂) * p := BoundedByKP_add ha hb

theorem mul_bound_prop (a b p k₁ k₂ : Nat) (ha : a < k₁ * p) (hb : b < k₂ * p) :
    a * b < (k₁ * p) * (k₂ * p) := Nat.mul_lt_mul_of_lt_of_lt ha hb

theorem sub_bound_prop (a b p k : Nat) (ha : a < k * p) : a - b < k * p :=
  Nat.lt_of_le_of_lt (Nat.sub_le a b) ha

theorem ct_sum_bound (a wb p k₁ k₂ : Nat) (ha : a < k₁ * p) (hwb : wb < k₂ * p) :
    a + wb < (k₁ + k₂) * p := add_bound_prop a wb p k₁ k₂ ha hwb

theorem harvey_1br (x p : Nat) (hx : x < 2 * p) (hp : 0 < p) :
    (if x ≥ p then x - p else x) < p := by split <;> omega

theorem harvey_2br (x p : Nat) (hx : x < 2 * p) (hge : x ≥ p) : x - p < p := by omega

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Sentinel Encoding
-- ══════════════════════════════════════════════════════════════════

/-- Sentinel base for encoding bound factors in edge targets. -/
def sentinelBase : Nat := 1000000

def encodeBoundFactor (k : Nat) : EClassId := sentinelBase + k

def decodeBoundFactor (sentinel : EClassId) : Option Nat :=
  if sentinel ≥ sentinelBase then some (sentinel - sentinelBase) else none

theorem decode_encode (k : Nat) : decodeBoundFactor (encodeBoundFactor k) = some k := by
  simp [decodeBoundFactor, encodeBoundFactor, sentinelBase]

/-- Build a bound lookup from a relation DAG's sentinel edges. -/
def buildBoundLookup (dag : DirectedRelGraph) : EClassId → Option Nat :=
  fun classId =>
    dag.successors classId |>.foldl (fun best dst =>
      match decodeBoundFactor dst with
      | some k => match best with
        | some bestK => if k < bestK then some k else some bestK
        | none => some k
      | none => best
    ) none

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Concrete BoundRule Constructors
-- ══════════════════════════════════════════════════════════════════

def isReductionOp : MixedNodeOp → Bool
  | .reduceGate _ _ | .montyReduce _ _ _ | .barrettReduce _ _ _ | .harveyReduce _ _ => true
  | _ => false

/-- Scan e-graph for reduction nodes, add sentinel edges encoding their bounds. -/
def mkReductionBoundRule (p : Nat) (relIdx : Nat) : BoundRule where
  name := s!"reduction_bound_p{p}"
  relIdx := relIdx
  apply := fun g =>
    g.classes.toList.foldl (fun acc (classId, eclass) =>
      let bestK := eclass.nodes.foldl (fun best node =>
        let k := reductionBoundFactor node.op
        if k > 0 && (best == 0 || k < best) then k else best
      ) 0
      if bestK > 0 then acc ++ [(classId, encodeBoundFactor bestK)]
      else acc
    ) []

/-- Scan e-graph for add nodes where both children have known bounds.
    The bound lookup is passed in, but it's created from the CURRENT
    DAG state by the factory — not frozen at initialization. -/
def mkAddBoundRule (relIdx : Nat) (lookup : EClassId → Option Nat) : BoundRule where
  name := "add_bound_propagation"
  relIdx := relIdx
  apply := fun g =>
    g.classes.toList.foldl (fun acc (classId, eclass) =>
      let result := eclass.nodes.foldl (fun best node =>
        match node.op with
        | .addGate child1 child2 =>
          match lookup child1, lookup child2 with
          | some k1, some k2 => some (k1 + k2)
          | _, _ => best
        | _ => best
      ) (none : Option Nat)
      match result with
      | some k => acc ++ [(classId, encodeBoundFactor k)]
      | none => acc
    ) []

-- ══════════════════════════════════════════════════════════════════
-- Section 4: BoundRuleFactory Constructors
-- ══════════════════════════════════════════════════════════════════

/-- Create a BoundRuleFactory for a given field prime.
    The factory reads the CURRENT DAG state each time it's called,
    so mkAddBoundRule always sees the latest bounds. -/
def mkFieldFactory (p : Nat) (relIdx : Nat := 0) : BoundRuleFactory := fun s =>
  let currentLookup :=
    if h : relIdx < s.relEntries.size
    then buildBoundLookup s.relEntries[relIdx].dag
    else fun _ => none
  [mkReductionBoundRule p relIdx, mkAddBoundRule relIdx currentLookup]

def babyBearFactory : BoundRuleFactory := mkFieldFactory 2013265921
def mersenne31Factory : BoundRuleFactory := mkFieldFactory 2147483647
def goldilocksFactory : BoundRuleFactory := mkFieldFactory 18446744069414584321

-- ══════════════════════════════════════════════════════════════════
-- Section 5: ReductionChoice + Stage Analysis
-- ══════════════════════════════════════════════════════════════════

inductive ReductionChoice where
  | solinasFold | montgomery | harvey | lazy
  deriving Repr, BEq, Inhabited

def boundAfterReduction : ReductionChoice → Nat
  | .solinasFold => 2 | .montgomery => 1 | .harvey => 2 | .lazy => 0

def stageBoundFactor (inputK : Nat) (reduction : ReductionChoice) : Nat :=
  match reduction with
  | .lazy => inputK + 1
  | r => boundAfterReduction r

def lazyReductionSafe (currentK : Nat) (p : Nat) : Bool :=
  (currentK + 1) * p < 2 ^ 64

def computeStageBounds (stages : List ReductionChoice) (initialK : Nat) : List Nat :=
  stages.scanl stageBoundFactor initialK

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : 17 % 5 < 1 * 5 := reduce_bound 17 5 (by omega)
example : 3 + 4 < (1 + 1) * 5 := by native_decide
example : lazyReductionSafe 100 2013265921 = true := by native_decide
example : computeStageBounds [.lazy, .lazy, .solinasFold] 1 = [1, 2, 3, 2] := by native_decide
example : decodeBoundFactor (encodeBoundFactor 3) = some 3 := by native_decide
example : reductionBoundFactor (.montyReduce 0 0 0) = 1 := rfl
example : reductionBoundFactor (.harveyReduce 0 0) = 2 := rfl

/-- Factory produces non-empty rules for a state with a bounds DAG. -/
example : (babyBearFactory (State.empty.addRelation "bounds")).length = 2 := rfl

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.BoundProp
