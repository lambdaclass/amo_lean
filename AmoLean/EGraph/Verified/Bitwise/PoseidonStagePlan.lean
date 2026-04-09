import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT

/-!
# PoseidonStagePlan — Bound-Aware Reduction for Poseidon S-box Operations

Poseidon uses S-box x^d (d=7 for BabyBear, d=5 for BN254). After exponentiation,
the bound explodes (~p^d for unreduced inputs). This module instantiates the
existing bound-aware reduction infrastructure for Poseidon round operations.

Key insight: after S-box, bounds are too large for Harvey or lazy reduction.
Montgomery or Solinas fold is mandatory. The per-round analysis distinguishes
full rounds (all S-boxes, aggressive reduction needed) from partial rounds
(1 S-box, potentially cheaper).

Node N25.2 in Fase 25 (FRI/Poseidon Integration).
Consumed by: N25.3 PrimitivesIntegration.
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.PoseidonStagePlan

open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice stageBoundFactor
  lazyReductionSafe boundAfterReduction)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (selectReductionForBound reductionCostForHW)
open AmoLean.EGraph.Verified.Bitwise (HardwareCost arm_cortex_a76)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Poseidon Configuration
-- ══════════════════════════════════════════════════════════════════

/-- Poseidon round type: full rounds apply S-box to all state elements,
    partial rounds apply S-box to only one element. -/
inductive PoseidonRoundType where
  | full    -- S-box applied to all t state elements
  | partialRound -- S-box applied to 1 state element
  deriving Repr, BEq, Inhabited

/-- Configuration for Poseidon bound analysis. -/
structure PoseidonConfig where
  /-- Field prime p -/
  prime : Nat
  /-- S-box exponent d (7 for BabyBear/Mersenne31, 5 for BN254) -/
  sboxExponent : Nat
  /-- State width t (number of field elements in state) -/
  stateWidth : Nat
  /-- Number of full rounds (at start and end) -/
  fullRounds : Nat
  /-- Number of partial rounds (in the middle) -/
  partialRounds : Nat
  /-- Hardware SIMD flag -/
  hwIsSimd : Bool := false
  /-- Large array flag -/
  arrayIsLarge : Bool := false
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Bound Analysis
-- ══════════════════════════════════════════════════════════════════

/-- Bound factor after S-box x^d.
    If input bound is k (i.e., x < k*p), then x^d < (k*p)^d.
    For reduced inputs (k=1): x^d < p^d, so output bound factor = p^(d-1).
    But this is ENORMOUS — for BabyBear d=7: bound ~p^6 ≈ 2^186.
    In practice, we reduce BEFORE exponentiation when possible.

    Conservative model: output bound = inputK^d (multiplicative growth). -/
def sboxOutputBound (inputK : Nat) (d : Nat) : Nat :=
  -- For reduced inputs (inputK=1), x^d < p, so bound stays 1 (within field)
  -- For unreduced inputs, bound grows multiplicatively
  if inputK ≤ 1 then 1
  else inputK ^ d

/-- After MDS matrix multiplication (linear layer): bound grows by state width.
    MDS mixes all t elements: each output is a linear combination of t inputs.
    Output bound ≤ t * inputK (sum of t bounded elements). -/
def mdsOutputBound (inputK : Nat) (stateWidth : Nat) : Nat :=
  stateWidth * inputK

/-- Bound after one full Poseidon round: S-box → MDS → add round constant.
    S-box: inputK → sboxOutputBound(inputK, d)
    MDS: sboxBound → mdsOutputBound(sboxBound, t)
    Add constant: mdsbound + 1 (negligible)
    For reduced inputs: 1 → 1 → t → t+1. -/
def fullRoundOutputBound (cfg : PoseidonConfig) (inputK : Nat) : Nat :=
  let afterSbox := sboxOutputBound inputK cfg.sboxExponent
  let afterMDS := mdsOutputBound afterSbox cfg.stateWidth
  afterMDS + 1

/-- Bound after one partial round: only 1 S-box, rest are identity.
    One element gets S-box, t-1 elements stay. MDS mixes all.
    Bound ≈ (t-1) * inputK + sboxOutputBound(inputK, d) + 1. -/
def partialRoundOutputBound (cfg : PoseidonConfig) (inputK : Nat) : Nat :=
  let sboxBound := sboxOutputBound inputK cfg.sboxExponent
  let identityBound := inputK
  -- MDS: weighted sum of 1 sbox output + (t-1) identity outputs
  let afterMDS := sboxBound + (cfg.stateWidth - 1) * identityBound
  afterMDS + 1

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Reduction Selection
-- ══════════════════════════════════════════════════════════════════

/-- Select optimal reduction after a Poseidon round.
    Full rounds with reduced inputs: bound = t+1 (small), can use Harvey if t ≤ 3.
    Partial rounds: depends on accumulated bound. -/
def selectPoseidonReduction (cfg : PoseidonConfig) (roundBound : Nat)
    : ReductionChoice :=
  selectReductionForBound roundBound cfg.hwIsSimd cfg.arrayIsLarge

/-- Should we reduce between Poseidon rounds?
    Strategy: reduce after every full round (bounds grow fast with MDS mixing).
    For partial rounds: reduce only when bound exceeds threshold. -/
def shouldReduceAfterRound (cfg : PoseidonConfig) (roundType : PoseidonRoundType)
    (currentBound : Nat) : Bool :=
  match roundType with
  | .full => true  -- Always reduce after full rounds (MDS mixing amplifies bounds)
  | .partialRound =>
    -- Reduce if bound exceeds word size safety margin
    !lazyReductionSafe (currentBound + 1) cfg.prime

/-- Analyze all Poseidon rounds: return per-round (index, type, reduction, bound). -/
def poseidonRoundAnalysis (cfg : PoseidonConfig)
    : List (Nat × PoseidonRoundType × ReductionChoice × Nat) :=
  let halfFull := cfg.fullRounds / 2
  let rounds : List (Nat × PoseidonRoundType) :=
    (List.range halfFull |>.map (·, .full)) ++
    (List.range cfg.partialRounds |>.map (· + halfFull, .partialRound)) ++
    (List.range halfFull |>.map (· + halfFull + cfg.partialRounds, .full))
  rounds.foldl (fun (acc, boundK) (idx, rtype) =>
    let outputBound := match rtype with
      | .full => fullRoundOutputBound cfg boundK
      | .partialRound => partialRoundOutputBound cfg boundK
    let doReduce := shouldReduceAfterRound cfg rtype outputBound
    let reduction := if doReduce then selectPoseidonReduction cfg outputBound
                     else .lazy
    let finalBound := if doReduce then boundAfterReduction reduction else outputBound
    (acc ++ [(idx, rtype, reduction, finalBound)], finalBound)
  ) ([], 1) |>.1

/-- Cost of one Poseidon round (per state element).
    Uses reductionCostForHW (SSOT) instead of legacy reductionCost. -/
def poseidonRoundCost (cfg : PoseidonConfig) (hw : HardwareCost) (roundType : PoseidonRoundType)
    (currentBound : Nat) (mulCost addCost : Nat) : Nat :=
  -- S-box cost: d-1 multiplications (square-and-multiply for x^d)
  let sboxMuls := match roundType with
    | .full => cfg.stateWidth * (cfg.sboxExponent - 1) * mulCost
    | .partialRound => (cfg.sboxExponent - 1) * mulCost
  -- MDS cost: t^2 multiplications + t*(t-1) additions
  let mdsCost := cfg.stateWidth * cfg.stateWidth * mulCost +
                 cfg.stateWidth * (cfg.stateWidth - 1) * addCost
  -- Round constant addition: t additions
  let rcCost := cfg.stateWidth * addCost
  -- Reduction cost (if needed)
  let outputBound := match roundType with
    | .full => fullRoundOutputBound cfg currentBound
    | .partialRound => partialRoundOutputBound cfg currentBound
  let doReduce := shouldReduceAfterRound cfg roundType outputBound
  let redCost := if doReduce then
    cfg.stateWidth * reductionCostForHW hw (selectPoseidonReduction cfg outputBound)
  else 0
  sboxMuls + mdsCost + rcCost + redCost

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Concrete Configurations
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear Poseidon2 (t=16, d=7, 8 full + 13 partial rounds). -/
def babybear_t16 : PoseidonConfig :=
  { prime := 2013265921, sboxExponent := 7, stateWidth := 16,
    fullRounds := 8, partialRounds := 13 }

/-- BabyBear Poseidon2 (t=8, d=7, smaller state for hashing). -/
def babybear_t8 : PoseidonConfig :=
  { prime := 2013265921, sboxExponent := 7, stateWidth := 8,
    fullRounds := 8, partialRounds := 13 }

/-- Mersenne31 Poseidon2 (t=16, d=7). -/
def mersenne31_t16 : PoseidonConfig :=
  { prime := 2147483647, sboxExponent := 7, stateWidth := 16,
    fullRounds := 8, partialRounds := 13 }

/-- Goldilocks Poseidon (t=12, d=7). -/
def goldilocks_t12 : PoseidonConfig :=
  { prime := 18446744069414584321, sboxExponent := 7, stateWidth := 12,
    fullRounds := 8, partialRounds := 22 }

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- S-box with reduced input preserves bound = 1. -/
theorem sboxOutputBound_reduced (d : Nat) : sboxOutputBound 1 d = 1 := rfl

/-- Full round with reduced inputs: bound = stateWidth + 1. -/
theorem fullRound_bound_reduced (cfg : PoseidonConfig) :
    fullRoundOutputBound cfg 1 = cfg.stateWidth + 1 := by
  simp [fullRoundOutputBound, sboxOutputBound, mdsOutputBound]

/-- Full rounds always trigger reduction. -/
theorem fullRound_always_reduces (cfg : PoseidonConfig) (bound : Nat) :
    shouldReduceAfterRound cfg .full bound = true := rfl

/-- Poseidon round analysis produces correct number of rounds (BabyBear t=8). -/
theorem poseidonAnalysis_length_babybear_t8 :
    (poseidonRoundAnalysis babybear_t8).length = 21 := by native_decide

/-- Poseidon round analysis produces correct number of rounds (BabyBear t=16). -/
theorem poseidonAnalysis_length_babybear_t16 :
    (poseidonRoundAnalysis babybear_t16).length = 21 := by native_decide

/-- Poseidon round analysis produces correct number of rounds (Goldilocks t=12). -/
theorem poseidonAnalysis_length_goldilocks :
    (poseidonRoundAnalysis goldilocks_t12).length = 30 := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- S-box preserves bound for reduced inputs. -/
example : sboxOutputBound 1 7 = 1 := rfl

/-- S-box with unreduced inputs (k=3, d=7): bound = 3^7 = 2187. -/
example : sboxOutputBound 3 7 = 2187 := by native_decide

/-- Full round bound for BabyBear t=8, reduced: 8 + 1 = 9. -/
example : fullRoundOutputBound babybear_t8 1 = 9 := rfl

/-- Full rounds always reduce. -/
example : shouldReduceAfterRound babybear_t8 .full 100 = true := rfl

/-- BabyBear t=8 full round with reduced inputs → reduction = Solinas (bound=9 > 4). -/
example : selectPoseidonReduction babybear_t8 9 = .solinasFold := rfl

/-- BabyBear t=8 analysis has 21 rounds (8 full + 13 partial). -/
example : (poseidonRoundAnalysis babybear_t8).length = 21 := by native_decide

/-- Round cost is computable for concrete config (scalar ARM). -/
example : poseidonRoundCost babybear_t8 arm_cortex_a76 .full 1 3 1 > 0 := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.PoseidonStagePlan
