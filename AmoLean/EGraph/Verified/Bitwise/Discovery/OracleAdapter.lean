/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.OracleAdapter

  C26.3: Bridges the discovery pipeline (Level 2: modular reduction) with
  the NTT plan optimizer (Level 1: radix factorization via CostOracle).

  When discoverReduction finds an optimized reduction implementation,
  its actual hardware cost can replace the heuristic `reductionCost`
  used by CostOracle.stageCost. This lets matSaturateF make radix
  choices informed by the actual discovered reduction cost.
-/
import AmoLean.EGraph.Verified.Bitwise.Discovery.SpecDrivenRunner
import AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp HardwareCost mixedOpCost arm_cortex_a76)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (RadixChoice)
open AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep (CostOracle MatEGraph
  matSaturateF evaluateAssignment findCheapest generateAssignments)

-- ════════════════════════════════════════════════════════════════
-- Section 1: MixedExpr cost computation (hardware-aware)
-- ════════════════════════════════════════════════════════════════

/-- Compute the hardware cost of a MixedExpr tree by summing per-node costs.
    Uses the same `mixedOpCost` as the e-graph extraction layer. -/
def exprCostHW (hw : HardwareCost) : MixedExpr → Nat
  | .constE _           => mixedOpCost hw (.constGate 0)
  | .witnessE _         => mixedOpCost hw (.witness 0)
  | .pubInputE _        => mixedOpCost hw (.pubInput 0)
  | .addE a b           => mixedOpCost hw (.addGate 0 0) + exprCostHW hw a + exprCostHW hw b
  | .mulE a b           => mixedOpCost hw (.mulGate 0 0) + exprCostHW hw a + exprCostHW hw b
  | .negE a             => mixedOpCost hw (.negGate 0) + exprCostHW hw a
  | .smulE n a          => mixedOpCost hw (.smulGate n 0) + exprCostHW hw a
  | .shiftLeftE a n     => mixedOpCost hw (.shiftLeft 0 n) + exprCostHW hw a
  | .shiftRightE a n    => mixedOpCost hw (.shiftRight 0 n) + exprCostHW hw a
  | .bitAndE a b        => mixedOpCost hw (.bitAnd 0 0) + exprCostHW hw a + exprCostHW hw b
  | .bitXorE a b        => mixedOpCost hw (.bitXor 0 0) + exprCostHW hw a + exprCostHW hw b
  | .bitOrE a b         => mixedOpCost hw (.bitOr 0 0) + exprCostHW hw a + exprCostHW hw b
  | .constMaskE _       => mixedOpCost hw (.constMask 0)
  | .subE a b           => mixedOpCost hw (.subGate 0 0) + exprCostHW hw a + exprCostHW hw b
  | .reduceE a p        => mixedOpCost hw (.reduceGate 0 p) + exprCostHW hw a
  | .kronPackE a b w    => mixedOpCost hw (.kronPack 0 0 w) + exprCostHW hw a + exprCostHW hw b
  | .kronUnpackLoE a w  => mixedOpCost hw (.kronUnpackLo 0 w) + exprCostHW hw a
  | .kronUnpackHiE a w  => mixedOpCost hw (.kronUnpackHi 0 w) + exprCostHW hw a
  | .montyReduceE a p mu => mixedOpCost hw (.montyReduce 0 p mu) + exprCostHW hw a
  | .barrettReduceE a p m => mixedOpCost hw (.barrettReduce 0 p m) + exprCostHW hw a
  | .harveyReduceE a p  => mixedOpCost hw (.harveyReduce 0 p) + exprCostHW hw a
  | .conditionalSubE a p => mixedOpCost hw (.conditionalSub 0 p) + exprCostHW hw a

/-- Extract the reduction cost from a DiscoveryResult.
    If discovery succeeded, returns the hardware cost of the optimized expression.
    If it failed, returns a large fallback cost. -/
def discoveryReductionCost (result : DiscoveryResult) (hw : HardwareCost) : Nat :=
  match result.optimizedExpr with
  | some expr => exprCostHW hw expr
  | none => 100  -- fallback: expensive, so matSaturateF uses heuristic defaults

-- ════════════════════════════════════════════════════════════════
-- Section 2: Discovery-aware stage cost evaluation
-- ════════════════════════════════════════════════════════════════

/-- Stage cost using discovered reduction cost instead of heuristic.
    Replaces `CostOracle.stageCost` when discovery has found an implementation. -/
def discoveryAwareStageCost (oracle : CostOracle) (discoveredRedCost : Nat)
    (radix : RadixChoice) : Nat :=
  -- Approximate butterfly cost from oracle params (mirrors MatEGraphStep.stageCost)
  let bfCost := match radix with
    | .r2 => oracle.mulCost + 2 * oracle.addCost + oracle.mulCost
    | .r4 => 3 * oracle.mulCost + 8 * oracle.addCost + 4 * oracle.mulCost
  let bfsPerStage := match radix with
    | .r2 => oracle.arraySize / 2
    | .r4 => oracle.arraySize / 4
  bfsPerStage * (bfCost + discoveredRedCost)

/-- Evaluate total cost of a radix assignment using discovered reduction cost.
    Unlike `evaluateAssignment` which queries `selectReductionForBound` per stage,
    this uses the same discovered cost for ALL stages (the discovered reduction
    is prime-specific, not bound-dependent). -/
def evaluateAssignmentWithDiscovery (assignment : List RadixChoice)
    (oracle : CostOracle) (discoveredRedCost : Nat) : Nat :=
  assignment.foldl (fun cost radix =>
    cost + discoveryAwareStageCost oracle discoveredRedCost radix
  ) 0

/-- Find the cheapest radix assignment using discovered reduction cost. -/
def findCheapestWithDiscovery (assignments : List (List RadixChoice))
    (oracle : CostOracle) (discoveredRedCost : Nat)
    : Option (List RadixChoice × Nat) :=
  assignments.foldl (fun best assignment =>
    let cost := evaluateAssignmentWithDiscovery assignment oracle discoveredRedCost
    match best with
    | none => some (assignment, cost)
    | some (_, bestCost) => if cost < bestCost then some (assignment, cost) else best
  ) none

/-- Discovery-aware saturation: same as matSaturateF but uses discovered
    reduction cost for evaluation. -/
def matSaturateWithDiscovery (g : MatEGraph) (oracle : CostOracle)
    (discoveredRedCost : Nat) (fuel : Nat := 500) : MatEGraph :=
  let assignments := generateAssignments g.totalLevels fuel
  match findCheapestWithDiscovery assignments oracle discoveredRedCost with
  | none => g
  | some (best, cost) =>
    { g with numExplored := assignments.length,
             bestAssignment := best,
             bestCost := cost }

-- ════════════════════════════════════════════════════════════════
-- Section 3: Theorems
-- ════════════════════════════════════════════════════════════════

/-- exprCostHW is non-negative (trivially true for Nat but useful as API). -/
theorem exprCostHW_nonneg (hw : HardwareCost) (expr : MixedExpr) :
    exprCostHW hw expr ≥ 0 := Nat.zero_le _

/-- Constants and witnesses are free (zero cost). -/
theorem exprCostHW_const_zero (hw : HardwareCost) (n : Nat) :
    exprCostHW hw (.constE n) = 0 := rfl

theorem exprCostHW_witness_zero (hw : HardwareCost) (n : Nat) :
    exprCostHW hw (.witnessE n) = 0 := rfl

/-- Discovery-aware stage cost scales linearly with butterflies per stage. -/
theorem discoveryAware_r2_cost (oracle : CostOracle) (drc : Nat) :
    discoveryAwareStageCost oracle drc .r2 =
      (oracle.arraySize / 2) * (oracle.mulCost + 2 * oracle.addCost + oracle.mulCost + drc) := rfl

theorem discoveryAware_r4_cost (oracle : CostOracle) (drc : Nat) :
    discoveryAwareStageCost oracle drc .r4 =
      (oracle.arraySize / 4) * (3 * oracle.mulCost + 8 * oracle.addCost + 4 * oracle.mulCost + drc) := rfl

-- ════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ════════════════════════════════════════════════════════════════

-- Witness node costs 0
example : exprCostHW arm_cortex_a76 (.witnessE 0) = 0 := rfl

-- Simple add costs: add(witness, witness) = addCost + 0 + 0
example : exprCostHW arm_cortex_a76 (.addE (.witnessE 0) (.witnessE 1)) =
    mixedOpCost arm_cortex_a76 (.addGate 0 0) := by native_decide

-- Discovery-aware cost with zero reduction cost reduces to just butterfly cost
example : discoveryAwareStageCost (CostOracle.armScalar 1024) 0 .r2 =
    512 * (3 + 2 * 1 + 3 + 0) := rfl

-- discoveryReductionCost returns 100 for failed discovery
example : discoveryReductionCost
    { optimizedExpr := none, seed := .witnessE 0, prime := 0,
      verified := false } arm_cortex_a76 = 100 := rfl

-- ════════════════════════════════════════════════════════════════
-- Section 5: Per-Stage OracleAdapter (Fase Per-Stage v3.3.0, NE.4)
-- ════════════════════════════════════════════════════════════════

/-- Per-stage discovery: runs discoverAllStages and extracts actual hardware
    costs per stage. Returns Array of per-stage reduction costs.

    Stages where discovery returns .lazy get the Solinas fold cost (matching
    codegen semantics where lazy = Solinas fold). -/
def discoveryReductionCostPerStage (p : Nat) (numStages bitwidth : Nat)
    (hw : HardwareCost) (hwIsSimd : Bool := false) : Array Nat :=
  if h1 : p > 0 then
    if h2 : p < 2 ^ bitwidth then
      let spec : ReduceSpec := { p, w := bitwidth, p_pos := h1, p_lt_bound := h2 }
      let results := discoverAllStages spec numStages bitwidth hwIsSimd hw
      results.toArray.map fun r =>
        match r.optimizedExpr with
        | some expr => exprCostHW hw expr
        | none => 100  -- fallback: expensive
    else (List.replicate numStages 100).toArray
  else (List.replicate numStages 100).toArray

/-- Per-stage version of evaluateAssignmentWithDiscovery.
    Uses per-stage costs instead of uniform cost. -/
def evaluateAssignmentPerStage (assignment : List RadixChoice)
    (oracle : CostOracle) (perStageCosts : Array Nat) : Nat :=
  (assignment.zip (List.range assignment.length)).foldl (fun cost (radix, idx) =>
    let redCost := if h : idx < perStageCosts.size then perStageCosts[idx] else 100
    cost + discoveryAwareStageCost oracle redCost radix
  ) 0

end AmoLean.EGraph.Verified.Bitwise.Discovery
