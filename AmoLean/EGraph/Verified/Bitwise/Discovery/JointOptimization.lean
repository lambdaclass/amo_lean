/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.JointOptimization

  C26.4: Coordinates Level 1 (NTT plan via matSaturateF) with Level 2
  (modular reduction discovery via discoverReduction). The joint pipeline:
    1. Discovers optimized reduction for the prime
    2. Computes actual hardware cost of discovered implementation
    3. Runs NTT factorization with discovery-aware cost oracle
    4. Returns combined result: best reduction + best NTT plan + total cost
-/
import AmoLean.EGraph.Verified.Bitwise.Discovery.OracleAdapter

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedEnv HardwareCost arm_cortex_a76)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (PreservesCV)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (RadixChoice)
open AmoLean.EGraph.Verified.Bitwise.Discovery.MatEGraphStep (CostOracle MatEGraph
  matSaturateF evaluateAssignment)
open MixedRunner (GuidedMixedConfig)

-- ════════════════════════════════════════════════════════════════
-- Section 1: JointResult structure
-- ════════════════════════════════════════════════════════════════

/-- Result of joint optimization: reduction discovery + NTT plan. -/
structure JointResult where
  /-- Discovery result (reduction implementation). -/
  discovery : DiscoveryResult
  /-- Best NTT radix assignment found by matSaturateF. -/
  bestPlan : List RadixChoice
  /-- Total NTT cost using discovered reduction. -/
  planCost : Nat
  /-- Cost of the discovered reduction implementation (per invocation). -/
  reductionCost : Nat
  /-- Improvement: heuristic cost - discovery cost (negative = discovery worse). -/
  costDelta : Int

-- ════════════════════════════════════════════════════════════════
-- Section 2: Joint optimization pipeline
-- ════════════════════════════════════════════════════════════════

/-- Joint optimization: discover reduction, then optimize NTT plan.

    Steps:
    1. `discoverReduction` finds the best modular reduction for the prime
    2. `exprCostHW` computes its actual hardware cost
    3. `matSaturateWithDiscovery` finds the best NTT factorization
       using the discovered reduction cost
    4. For comparison, also runs `matSaturateF` with heuristic oracle

    Parameters:
    - `spec`: the prime + word width (ReduceSpec)
    - `hw`: hardware cost model
    - `n`: NTT array size (must be power of 2)
    - `oracle`: cost oracle for NTT evaluation -/
def jointOptimize (spec : ReduceSpec) (hw : HardwareCost)
    (n : Nat) (oracle : CostOracle)
    (cfg : GuidedMixedConfig := .default) : JointResult :=
  -- Step 1: Discover reduction
  let disc := discoverReduction spec hw cfg
  -- Step 2: Compute discovered cost
  let discCost := discoveryReductionCost disc hw
  -- Step 3: NTT plan with discovered cost (k = number of NTT stages)
  let k := n.log2
  let gDisc := matSaturateWithDiscovery (MatEGraph.empty k) oracle discCost
  -- Step 4: Heuristic baseline for comparison
  let gHeur := matSaturateF (MatEGraph.empty k) oracle
  let heurCost := gHeur.bestCost
  { discovery := disc
    bestPlan := gDisc.bestAssignment
    planCost := gDisc.bestCost
    reductionCost := discCost
    costDelta := (heurCost : Int) - (gDisc.bestCost : Int) }

/-- Simplified joint optimization with ARM scalar defaults. -/
def jointOptimizeScalar (spec : ReduceSpec) (n : Nat)
    (hw : HardwareCost := arm_cortex_a76) : JointResult :=
  jointOptimize spec hw n (CostOracle.armScalar n)

/-- Simplified joint optimization with ARM SIMD defaults. -/
def jointOptimizeSimd (spec : ReduceSpec) (n : Nat)
    (hw : HardwareCost := arm_cortex_a76) : JointResult :=
  jointOptimize spec hw n (CostOracle.armSimd n)

-- ════════════════════════════════════════════════════════════════
-- Section 3: Theorem — discovery preserves soundness
-- ════════════════════════════════════════════════════════════════

/-- Joint optimization preserves the discovery pipeline's soundness:
    the underlying insertReduceSpec preserves ConsistentValuation. -/
theorem jointOptimize_sound (spec : ReduceSpec) (env : MixedEnv) :
    PreservesCV env (insertReduceSpec spec) :=
  discoverReduction_pipeline_sound spec env

-- ════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests (lightweight; heavy tests in NonVacuity)
-- ════════════════════════════════════════════════════════════════

-- Structural: JointResult fields are accessible
example : (JointResult.mk
    { optimizedExpr := none, seed := .witnessE 0, prime := 0,
      verified := false }
    [.r2, .r4] 100 50 (-50 : Int)).reductionCost = 50 := rfl

example : (JointResult.mk
    { optimizedExpr := none, seed := .witnessE 0, prime := 0,
      verified := false }
    [.r2, .r4] 100 50 (-50 : Int)).bestPlan.length = 2 := rfl

end AmoLean.EGraph.Verified.Bitwise.Discovery
