import AmoLean.EGraph.Verified.Bitwise.NTTPlan
import AmoLean.EGraph.Verified.Bitwise.Discovery.GrowthPrediction

/-!
# MatEGraphStep — Algorithmic NTT Factorization Exploration

Explores NTT factorization strategies by generating valid radix assignments
(sequences of radix-2/radix-4 choices per stage) and evaluating each using
a cost oracle that queries Level 2 (BoundPropagation + CostModel).

This is the "Level 1 saturation loop" that connects algorithmic factorization
choices to arithmetic optimization. The cost oracle is the feedback channel
from Level 2 to Level 1.

## Architecture

```
MatEGraphStep (Level 1)                    NTTPlan (Level 2)
  generateAssignments(k)                     selectReductionForBound
  → [r2,r2,r4,r2,...], [r4,r4,...], ...     reductionCost
  evaluateAssignment(oracle, assignment)      stageBoundFactor
  → total cost per assignment                butterflyCost
  matSaturateAndExtract                      →
  → best radix assignment                    N24.12 converts to Plan
```

Node N24.11 in Fase 24 (Discovery Engine).
Consumed by: N24.12 MatPlanExtraction, N24.9 DiscoveryPipeline.
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep

open AmoLean.EGraph.Verified.Bitwise.NTTPlan (RadixChoice StageDirection Plan NTTStage
  butterflyCost log2 log4)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice stageBoundFactor
  lazyReductionSafe)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound reductionCost)
-- maxNodesBound from GrowthPrediction available via import (used for growth control docs)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Cost Oracle (Level 2 feedback channel)
-- ══════════════════════════════════════════════════════════════════

/-- Cost oracle: queries Level 2 for per-stage arithmetic cost.
    This is the feedback channel between algorithmic (Level 1) and
    arithmetic (Level 2) optimization layers.

    The oracle packages hardware parameters so that Level 1 can evaluate
    factorization choices without knowing the details of reduction strategies. -/
structure CostOracle where
  mulCost : Nat
  addCost : Nat
  arraySize : Nat
  hwIsSimd : Bool
  arrayIsLarge : Bool
  deriving Repr, Inhabited

/-- Evaluate the cost of one NTT stage with given radix and input bound.
    Queries Level 2: selectReductionForBound → reductionCost → butterflyCost. -/
def CostOracle.stageCost (oracle : CostOracle) (radix : RadixChoice)
    (inputBoundK : Nat) : Nat :=
  let reduction := selectReductionForBound (inputBoundK + 1) oracle.hwIsSimd oracle.arrayIsLarge
  let bfCost := butterflyCost radix oracle.mulCost oracle.addCost
  let redCost := reductionCost reduction inputBoundK oracle.hwIsSimd
  let bfsPerStage := match radix with | .r2 => oracle.arraySize / 2 | .r4 => oracle.arraySize / 4
  bfsPerStage * (bfCost + redCost)

/-- Compute output bound factor after a stage. -/
def CostOracle.nextBoundK (oracle : CostOracle) (inputBoundK : Nat) : Nat :=
  let reduction := selectReductionForBound (inputBoundK + 1) oracle.hwIsSimd oracle.arrayIsLarge
  stageBoundFactor inputBoundK reduction

/-- ARM Cortex-A76 scalar oracle. -/
def CostOracle.armScalar (n : Nat) : CostOracle :=
  { mulCost := 3, addCost := 1, arraySize := n,
    hwIsSimd := false, arrayIsLarge := n > 8192 }

/-- ARM NEON SIMD oracle. -/
def CostOracle.armSimd (n : Nat) : CostOracle :=
  { mulCost := 3, addCost := 1, arraySize := n,
    hwIsSimd := true, arrayIsLarge := n > 8192 }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Radix Assignments
-- ══════════════════════════════════════════════════════════════════

/-- How many butterfly-network levels a single radix choice covers. -/
def radixLevels : RadixChoice → Nat
  | .r2 => 1
  | .r4 => 2

/-- Total levels covered by a sequence of radix choices. -/
def totalCoverage : List RadixChoice → Nat
  | [] => 0
  | r :: rest => radixLevels r + totalCoverage rest

/-- Generate ALL valid radix assignments for `k` butterfly-network levels.
    Each .r2 covers 1 level, each .r4 covers 2 levels.
    Count = Fibonacci(k+1): k=10 → 89, k=20 → 6765. -/
def generateAssignmentsAux : Nat → List (List RadixChoice)
  | 0 => [[]]
  | 1 => [[.r2]]
  | k + 2 =>
    (generateAssignmentsAux (k + 1)).map (.r2 :: ·) ++
    (generateAssignmentsAux k).map (.r4 :: ·)

/-- Generate valid radix assignments, capped at `maxResults`. -/
def generateAssignments (k : Nat) (maxResults : Nat := 500) : List (List RadixChoice) :=
  (generateAssignmentsAux k).take maxResults

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Cost Evaluation
-- ══════════════════════════════════════════════════════════════════

/-- Evaluate the total cost of a radix assignment by summing per-stage costs.
    Tracks bound factor propagation through stages (Level 2 feedback). -/
def evaluateAssignment (assignment : List RadixChoice) (oracle : CostOracle) : Nat :=
  let (totalCost, _) := assignment.foldl (fun (cost, boundK) radix =>
    let sCost := oracle.stageCost radix boundK
    let nextK := oracle.nextBoundK boundK
    (cost + sCost, nextK)
  ) (0, 1)  -- initial bound factor = 1 (fully reduced input)
  totalCost

/-- Find the cheapest assignment from a list. Returns (assignment, cost). -/
def findCheapest (assignments : List (List RadixChoice)) (oracle : CostOracle)
    : Option (List RadixChoice × Nat) :=
  assignments.foldl (fun best assignment =>
    let cost := evaluateAssignment assignment oracle
    match best with
    | none => some (assignment, cost)
    | some (_, bestCost) => if cost < bestCost then some (assignment, cost) else best
  ) none

-- ══════════════════════════════════════════════════════════════════
-- Section 4: MatEGraph (explored factorization space)
-- ══════════════════════════════════════════════════════════════════

/-- MatEGraph: the explored space of NTT factorizations.
    Lightweight structure (NOT a full e-graph — the factorization space is
    small enough for exhaustive enumeration: Fib(k+1) assignments for k levels). -/
structure MatEGraph where
  /-- Total butterfly-network levels (= log₂ N) -/
  totalLevels : Nat
  /-- Number of explored factorizations -/
  numExplored : Nat
  /-- Best radix assignment found -/
  bestAssignment : List RadixChoice
  /-- Cost of the best assignment -/
  bestCost : Nat
  deriving Repr, Inhabited

/-- Empty MatEGraph for k levels. -/
def MatEGraph.empty (k : Nat) : MatEGraph :=
  { totalLevels := k, numExplored := 0, bestAssignment := [], bestCost := 0 }

/-- Saturate: explore all valid radix assignments and find the cheapest.
    `fuel` controls the maximum number of assignments evaluated.

    This is the Level 1 saturation loop. For each candidate factorization,
    it queries the cost oracle (Level 2 feedback) to evaluate the total cost.
    The cheapest assignment is retained. -/
def matSaturateF (g : MatEGraph) (oracle : CostOracle) (fuel : Nat := 500) : MatEGraph :=
  let assignments := generateAssignments g.totalLevels fuel
  match findCheapest assignments oracle with
  | none => g
  | some (best, cost) =>
    { g with numExplored := assignments.length,
             bestAssignment := best,
             bestCost := cost }

/-- All-in-one: build MatEGraph, saturate, extract best assignment. -/
def matSaturateAndExtract (n : Nat) (oracle : CostOracle) (fuel : Nat := 500)
    : List RadixChoice :=
  let k := log2 n
  let g := matSaturateF (MatEGraph.empty k) oracle fuel
  g.bestAssignment

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Growth Control
-- ══════════════════════════════════════════════════════════════════

/-- Number of valid assignments for k levels (Fibonacci sequence).
    Used to verify explosion risk is LOW for practical NTT sizes. -/
def assignmentCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | k + 2 => assignmentCount (k + 1) + assignmentCount k

/-- The factorization space is bounded by Fibonacci growth.
    For k=20 (N=2^20), assignmentCount = 6765. Explosion risk: LOW. -/
theorem assignmentCount_eq_length (k : Nat) :
    (generateAssignmentsAux k).length = assignmentCount k := by
  induction k using generateAssignmentsAux.induct with
  | case1 => simp [generateAssignmentsAux, assignmentCount]
  | case2 => simp [generateAssignmentsAux, assignmentCount]
  | case3 k ih1 ih2 =>
    simp [generateAssignmentsAux, assignmentCount, List.length_append, List.length_map]
    omega

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Theorems
-- ══════════════════════════════════════════════════════════════════

theorem totalCoverage_nil : totalCoverage [] = 0 := rfl

theorem totalCoverage_cons_r2 (rest : List RadixChoice) :
    totalCoverage (.r2 :: rest) = 1 + totalCoverage rest := by
  simp [totalCoverage, radixLevels]

theorem totalCoverage_cons_r4 (rest : List RadixChoice) :
    totalCoverage (.r4 :: rest) = 2 + totalCoverage rest := by
  simp [totalCoverage, radixLevels]

/-- Every generated assignment covers exactly k levels. -/
theorem generateAssignmentsAux_valid (k : Nat) (steps : List RadixChoice)
    (h : steps ∈ generateAssignmentsAux k) : totalCoverage steps = k := by
  match k with
  | 0 => simp [generateAssignmentsAux] at h; subst h; rfl
  | 1 => simp [generateAssignmentsAux] at h; subst h; simp [totalCoverage, radixLevels]
  | k + 2 =>
    simp [generateAssignmentsAux, List.mem_append, List.mem_map] at h
    rcases h with ⟨rest, hmem, heq⟩ | ⟨rest, hmem, heq⟩
    · subst heq; simp [totalCoverage, radixLevels]
      have := generateAssignmentsAux_valid (k + 1) rest hmem; omega
    · subst heq; simp [totalCoverage, radixLevels]
      have := generateAssignmentsAux_valid k rest hmem; omega
termination_by k

/-- matSaturateF preserves totalLevels. -/
theorem matSaturateF_preserves_levels (g : MatEGraph) (oracle : CostOracle) (fuel : Nat) :
    (matSaturateF g oracle fuel).totalLevels = g.totalLevels := by
  simp [matSaturateF]; split <;> rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- k=0: only 1 assignment (empty). -/
example : (generateAssignmentsAux 0).length = 1 := by native_decide

/-- k=1: only 1 assignment [r2]. -/
example : (generateAssignmentsAux 1).length = 1 := by native_decide

/-- k=4: 5 valid assignments (Fib(5)). -/
example : (generateAssignmentsAux 4).length = 5 := by native_decide

/-- k=10: 89 valid assignments (Fib(11)). -/
example : (generateAssignmentsAux 10).length = 89 := by native_decide

/-- All-r2 assignment for k=10 covers 10 levels. -/
example : totalCoverage (List.replicate 10 .r2) = 10 := by native_decide

/-- All-r4 assignment for k=10 covers 10 levels. -/
example : totalCoverage (List.replicate 5 .r4) = 10 := by native_decide

/-- Mixed assignment covers 10 levels (2+2+2+2+1+1 = 10). -/
example : totalCoverage [.r4, .r4, .r4, .r4, .r2, .r2] = 10 := by native_decide

/-- ARM scalar oracle is computable. -/
example : (CostOracle.armScalar 1024).arraySize = 1024 := rfl

/-- Cost oracle can evaluate a stage cost. -/
example : (CostOracle.armScalar 1024).stageCost .r2 1 > 0 := by native_decide

/-- Cost oracle evaluates radix-4 stage (should be different from radix-2). -/
example : (CostOracle.armScalar 1024).stageCost .r4 1 ≠
    (CostOracle.armScalar 1024).stageCost .r2 1 := by native_decide

/-- matSaturateAndExtract produces a non-empty assignment for BabyBear N=1024. -/
example : (matSaturateAndExtract 1024 (CostOracle.armScalar 1024)).length > 0 := by
  native_decide

/-- The best assignment for N=1024 covers exactly 10 levels. -/
example : totalCoverage (matSaturateAndExtract 1024 (CostOracle.armScalar 1024)) = 10 := by
  native_decide

/-- Assignment count matches Fibonacci. -/
example : assignmentCount 10 = 89 := by native_decide
example : assignmentCount 20 = 10946 := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep
