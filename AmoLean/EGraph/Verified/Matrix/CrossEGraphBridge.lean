/-
  AmoLean.EGraph.Verified.Matrix.CrossEGraphBridge

  The VERIFIED cross-e-graph protocol: uses MatEGraph (not MatOp)
  to produce a MatExpr that flows through lowering_algebraic_correct.

  This replaces the unverified CrossEGraphProtocol for NTT optimization.
  The old protocol (CrossEGraphProtocol.lean) is kept for backward compat.

  Architecture:
    1. Insert dft(n) into MatEGraph
    2. Apply BreakdownRules (CT, radix-4) as rewrite rules
    3. Query MixedEGraph for butterfly costs (per-strategy)
    4. ILP extraction selects the cheapest factorization
    5. Extract as verified MatExpr
    6. Flow to lowering_algebraic_correct → verified code
-/
import AmoLean.EGraph.Verified.Matrix.BreakdownBridge
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Matrix.CrossEGraphBridge

open AmoLean.EGraph.Matrix (MatEGraph MatEClassId MatENode)
open AmoLean.EGraph.Matrix.MatEGraph (addMatExpr extractMatExpr)
open AmoLean.EGraph.Verified.Matrix.BreakdownBridge
  (EGraphBreakdownRule standardEGraphRules saturateBreakdowns optimizeNTTFactorization)
open AmoLean.EGraph.Verified.Bitwise (HardwareCost arm_cortex_a76)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound reductionCost)
open AmoLean.Matrix (MatExpr)

/-- Result of the verified cross-e-graph optimization.
    Contains the optimized MatExpr that can be passed to lowering_algebraic_correct. -/
structure VerifiedOptResult where
  /-- The optimized factorization as a verified MatExpr. -/
  factorization : Σ' (m n : Nat), MatExpr Nat m n
  /-- The per-butterfly cost from the arithmetic e-graph. -/
  butterflyCost : Nat
  /-- The total estimated cost. -/
  totalCost : Nat

/-- Verified joint optimization: explore factorizations via MatEGraph,
    query arithmetic costs, extract the optimal verified MatExpr.

    This is the replacement for `jointOptimize` in CrossEGraphProtocol.lean.
    The key difference: the result is a `MatExpr` (verified, dimension-indexed)
    instead of a `FactorizationTree` (unverified, flat array). -/
def verifiedJointOptimize (n p : Nat) (hw : HardwareCost) :
    Option VerifiedOptResult :=
  -- Step 1: Optimize NTT factorization via MatEGraph
  match optimizeNTTFactorization n with
  | none => none
  | some factorization =>
    -- Step 2: Query arithmetic e-graph for butterfly cost
    let boundK := 1  -- initial bound factor
    let isSimd := hw.isSimd
    let isLarge := n > 4096
    let reduction := selectReductionForBound boundK isSimd isLarge
    let bfCost := reductionCost reduction boundK isSimd

    -- Step 3: Estimate total cost (butterflies × cost + overhead)
    let numButterflies := n / 2  -- simplified: n/2 butterflies per stage (approx)
    let totalCost := numButterflies * bfCost

    some {
      factorization := factorization
      butterflyCost := bfCost
      totalCost := totalCost
    }

-- ══════════════════════════════════════════════════════════════════
-- N27.15: Cross-Level Cost Queries
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)

/-- Query the per-butterfly reduction cost for a specific stage context.
    This is the cross-level bridge: the algorithmic level (MatEGraph) asks
    the implementation level (Mixed e-graph) "what does a butterfly cost
    with the optimal reduction for this stage on this hardware?"

    Returns (reductionChoice, cost, outputBoundK). -/
def queryButterflyReduceCost (p : Nat) (hw : HardwareCost)
    (radix : Nat) (inputBoundK : Nat) (bitwidth : Nat := 64) :
    ReductionChoice × Nat × Nat :=
  let isSimd := hw.isSimd
  let isLarge := false  -- default; can be parameterized
  let reduction := selectReductionForBound inputBoundK isSimd isLarge
  let bfCost := reductionCost reduction inputBoundK isSimd
  -- Scale cost by radix (radix-4 has more ops per butterfly)
  let scaledCost := bfCost * (if radix == 4 then 3 else 1)
  let outputK := match reduction with
    | .lazy => inputBoundK + 1
    | .solinasFold => 2
    | .montgomery => 1
    | .harvey => 2
  (reduction, scaledCost, outputK)

/-- Query costs for ALL stages of an NTT, propagating bounds. -/
def queryAllStageCosts (p n : Nat) (hw : HardwareCost) (radix : Nat := 2)
    (bitwidth : Nat := 64) : List (Nat × ReductionChoice × Nat × Nat) :=
  let numStages := if n > 1 then Nat.log2 n else 0
  go 0 numStages 1 []
where
  go (stage : Nat) (total : Nat) (currentK : Nat)
      (acc : List (Nat × ReductionChoice × Nat × Nat)) :
      List (Nat × ReductionChoice × Nat × Nat) :=
    if stage ≥ total then acc.reverse
    else
      let (red, cost, nextK) := queryButterflyReduceCost p hw radix currentK bitwidth
      go (stage + 1) total nextK ((stage, red, cost, nextK) :: acc)
  termination_by total - stage

-- Smoke tests
#eval do
  match verifiedJointOptimize 8 2013265921 arm_cortex_a76 with
  | some result =>
    let ⟨m, n, _⟩ := result.factorization
    IO.println s!"BabyBear N=8: {m}x{n}, bf_cost={result.butterflyCost}, total={result.totalCost}"
  | none => IO.println "Optimization failed"

#eval do
  match verifiedJointOptimize 1024 2013265921 arm_cortex_a76 with
  | some result =>
    let ⟨m, n, _⟩ := result.factorization
    IO.println s!"BabyBear N=1024: {m}x{n}, bf_cost={result.butterflyCost}, total={result.totalCost}"
  | none => IO.println "Optimization failed"

end AmoLean.EGraph.Verified.Matrix.CrossEGraphBridge
