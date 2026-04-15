/-
  AmoLean.EGraph.Verified.Bitwise.NTTFactorizationRules

  Rewrite rules for the MatEGraph that enable exploration of
  NTT factorization alternatives:
    - Radix-2 vs Radix-4 split
    - DIT (Cooley-Tukey) vs DIF (Gentleman-Sande)
    - Kronecker packing for parallel NTTs

  These rules operate at the MatExpr level (algorithm structure),
  complementing the MixedNodeOp rules (arithmetic implementation).
  Together they enable cross-level optimization: the MatEGraph
  chooses the best factorization, and the Mixed e-graph chooses
  the best reduction per-butterfly.

  Key insight: Different factorizations compose differently with
  different reduction strategies. Radix-4 + Harvey lazy is 3x better
  than Radix-2 + Solinas fold, but this can only be discovered when
  both levels are connected.
-/
import AmoLean.Matrix.Basic
import AmoLean.EGraph.Vector

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.NTTFactorizationRules

open AmoLean.Matrix (MatExpr)
open AmoLean.EGraph (MatENodeOp MatEClassId MatEGraph)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Factorization descriptors
-- ══════════════════════════════════════════════════════════════════

/-- NTT factorization strategy — describes HOW to decompose an NTT. -/
inductive NTTStrategy where
  /-- Radix-2 DIT (Cooley-Tukey): log₂(N) stages × N/2 butterflies each -/
  | radix2DIT
  /-- Radix-2 DIF (Gentleman-Sande): same count, reversed order -/
  | radix2DIF
  /-- Radix-4 DIT: log₄(N) stages × N/4 butterflies, each 4-point -/
  | radix4DIT
  /-- Split-radix: hybrid of radix-2 and radix-4 -/
  | splitRadix
  /-- Kronecker-packed: two parallel NTTs in one word (BabyBear only) -/
  | kroneckerPacked
  /-- v3.11.0 F4: Two-step NTT for Goldilocks. Decomposes NTT_N as
      NTT_{N/64} × TwiddleMatrix × NTT_64, where NTT_64 uses omega_64 = 8
      (power-of-2 root, all 6 inner stages use shifts instead of multiplies).
      Outer stages use standard Cooley-Tukey with full multiplies. -/
  | twoStepGoldilocks
  deriving Repr, BEq, Inhabited

/-- Count the total operations for a factorization strategy. -/
def strategyOpCount (strategy : NTTStrategy) (n : Nat) (mulCost addCost : Nat) : Nat :=
  let log2n := Nat.log 2 n
  let log4n := Nat.log 4 n
  match strategy with
  | .radix2DIT | .radix2DIF =>
    -- log₂(N) stages × N/2 butterflies × (1 mul + 2 add) per butterfly
    log2n * (n / 2) * (mulCost + 2 * addCost)
  | .radix4DIT =>
    -- log₄(N) stages × N/4 radix-4 butterflies × (3 mul + 8 add) per butterfly
    log4n * (n / 4) * (3 * mulCost + 8 * addCost)
  | .splitRadix =>
    -- Approximately: N·log₂(N) - N + 1 muls (Yavne's formula)
    n * log2n - n + 1
  | .kroneckerPacked =>
    -- Half the operations (2 NTTs in 1 word)
    log2n * (n / 2) * (mulCost + 2 * addCost) / 2
  | .twoStepGoldilocks =>
    -- v3.11.0 F4: Inner NTT_64 (6 stages, shifts only = 0 muls) + outer NTT_{N/64}
    let innerStages := Nat.min 6 log2n  -- log₂(64) = 6, capped by total stages
    let outerStages := log2n - innerStages
    let innerCost := innerStages * (n / 2) * (2 * addCost)  -- shifts free, only add/sub
    let outerCost := outerStages * (n / 2) * (mulCost + 2 * addCost)  -- full butterflies
    innerCost + outerCost

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Strategy selection per hardware
-- ══════════════════════════════════════════════════════════════════

/-- Reduction strategy paired with factorization.
    The key insight: factorization choice interacts with reduction choice. -/
structure NTTConfig where
  factorization : NTTStrategy
  reductionCostPerButterfly : Nat  -- cycles for the reduction in each butterfly
  totalStages : Nat
  butterfliesPerStage : Nat
  deriving Repr

/-- Total cost of an NTT configuration. -/
def NTTConfig.totalCost (cfg : NTTConfig) : Nat :=
  cfg.totalStages * cfg.butterfliesPerStage * cfg.reductionCostPerButterfly

/-- BabyBear configurations for N=1024 on ARM Cortex-A76. -/
def babybear1024_configs : List NTTConfig :=
  [ -- Radix-2 DIT + Solinas fold (6 cycles/bf: shift + mul + and + add + shift + and)
    { factorization := .radix2DIT, reductionCostPerButterfly := 12,
      totalStages := 10, butterfliesPerStage := 512 }
  , -- Radix-2 DIT + Harvey lazy (3 cycles/bf: 2 cmp + 1 sub)
    { factorization := .radix2DIT, reductionCostPerButterfly := 8,
      totalStages := 10, butterfliesPerStage := 512 }
  , -- Radix-4 DIT + Harvey lazy
    { factorization := .radix4DIT, reductionCostPerButterfly := 14,
      totalStages := 5, butterfliesPerStage := 256 }
  , -- Kronecker-packed radix-2 + Solinas fold (2 butterflies per word)
    { factorization := .kroneckerPacked, reductionCostPerButterfly := 12,
      totalStages := 10, butterfliesPerStage := 256 }  -- half butterflies
  ]

/-- Find the cheapest NTT configuration from a list. -/
def cheapestConfig (configs : List NTTConfig) : Option NTTConfig :=
  configs.foldl (fun best cfg =>
    match best with
    | none => some cfg
    | some b => if cfg.totalCost < b.totalCost then some cfg else some b
  ) none

-- ══════════════════════════════════════════════════════════════════
-- Section 3: MatEGraph rewrite rules for factorization alternatives
-- ══════════════════════════════════════════════════════════════════

/-- A matrix-level rewrite rule: LHS pattern → RHS alternative. -/
structure MatRewriteRule where
  name : String
  /-- Returns true if this rule can apply to the given node. -/
  canApply : MatENodeOp → Bool
  /-- Description of what the rule does. -/
  description : String
  deriving Repr

/-- Rule: NTT_n → Radix-2 DIT factorization.
    NTT_n = (NTT_2 ⊗ I_{n/2}) · Twiddle · (I_2 ⊗ NTT_{n/2}) · L -/
def ruleRadix2DIT : MatRewriteRule where
  name := "ntt_radix2_dit"
  canApply := fun op => match op with
    | .ntt n _ => n > 2 && n % 2 == 0
    | .dft n => n > 2 && n % 2 == 0
    | _ => false
  description := "NTT_n → (NTT_2 ⊗ I_{n/2}) · T · (I_2 ⊗ NTT_{n/2}) · L"

/-- Rule: NTT_n → Radix-2 DIF factorization.
    NTT_n = L' · (I_2 ⊗ NTT_{n/2}) · Twiddle' · (NTT_2 ⊗ I_{n/2})
    (reversed stage order compared to DIT) -/
def ruleRadix2DIF : MatRewriteRule where
  name := "ntt_radix2_dif"
  canApply := fun op => match op with
    | .ntt n _ => n > 2 && n % 2 == 0
    | .dft n => n > 2 && n % 2 == 0
    | _ => false
  description := "NTT_n → L' · (I_2 ⊗ NTT_{n/2}) · T' · (NTT_2 ⊗ I_{n/2})"

/-- Rule: NTT_n → Radix-4 factorization (when n divisible by 4).
    NTT_n = (NTT_4 ⊗ I_{n/4}) · Twiddle · (I_4 ⊗ NTT_{n/4}) · L -/
def ruleRadix4DIT : MatRewriteRule where
  name := "ntt_radix4_dit"
  canApply := fun op => match op with
    | .ntt n _ => n > 4 && n % 4 == 0
    | .dft n => n > 4 && n % 4 == 0
    | _ => false
  description := "NTT_n → (NTT_4 ⊗ I_{n/4}) · T · (I_4 ⊗ NTT_{n/4}) · L"

/-- Rule: I_2 ⊗ NTT_n → Kronecker-packed NTT_n (BabyBear 31-bit).
    Two independent NTTs can be packed into one 64-bit word. -/
def ruleKroneckerPack : MatRewriteRule where
  name := "kronecker_pack_ntt"
  canApply := fun op => match op with
    | .kron _ _ 2 2 _ _ => true  -- I_2 ⊗ anything
    | _ => false
  description := "I_2 ⊗ NTT_n → KronPacked(NTT_n) for 31-bit fields"

/-- All NTT factorization rules. -/
def allNTTFactorizationRules : List MatRewriteRule :=
  [ ruleRadix2DIT, ruleRadix2DIF, ruleRadix4DIT, ruleKroneckerPack ]

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Cost-based strategy selection
-- ══════════════════════════════════════════════════════════════════

/-- Select the best NTT strategy for given parameters.
    This is the cross-level optimization: factorization × reduction → total cost. -/
def selectBestStrategy (n p : Nat) (mulCost addCost reduceCost : Nat) : NTTStrategy × Nat :=
  let candidates : List (NTTStrategy × Nat) :=
    [ (.radix2DIT, strategyOpCount .radix2DIT n mulCost addCost +
                   Nat.log 2 n * (n / 2) * reduceCost)
    , (.radix2DIF, strategyOpCount .radix2DIF n mulCost addCost +
                   Nat.log 2 n * (n / 2) * reduceCost)
    , (.radix4DIT, if n % 4 == 0 then
                     strategyOpCount .radix4DIT n mulCost addCost +
                     Nat.log 4 n * (n / 4) * reduceCost
                   else n * n)  -- prohibitively expensive if n not divisible by 4
    , (.kroneckerPacked, if p < 2^31 then
                           strategyOpCount .kroneckerPacked n mulCost addCost +
                           Nat.log 2 n * (n / 4) * reduceCost  -- half the reductions
                         else n * n)  -- only for 31-bit fields
    -- v3.11.0 F4: Two-step Goldilocks (NTT_64 × NTT_{N/64})
    -- Inner 6 stages have 0 mul cost (shifts). Only for Goldilocks (p = 2^64-2^32+1) and N ≥ 128.
    , (.twoStepGoldilocks,
        if p == 18446744069414584321 && n ≥ 128 then
          strategyOpCount .twoStepGoldilocks n mulCost addCost +
          (Nat.log 2 n - 6) * (n / 2) * reduceCost  -- only outer stages need reduce
        else n * n)  -- prohibitive for non-Goldilocks
    ]
  candidates.foldl (fun (bestStrat, bestCost) (strat, cost) =>
    if cost < bestCost then (strat, cost) else (bestStrat, bestCost)
  ) (.radix2DIT, n * n)  -- default: radix-2 with worst-case cost

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: radix-2 applicable to even sizes. -/
example : ruleRadix2DIT.canApply (.ntt 8 7) = true := rfl
example : ruleRadix2DIT.canApply (.ntt 3 7) = false := rfl

/-- Smoke: radix-4 requires divisibility by 4. -/
example : ruleRadix4DIT.canApply (.ntt 16 7) = true := rfl
example : ruleRadix4DIT.canApply (.ntt 6 7) = false := rfl

/-- Smoke: strategy cost comparison. -/
example : strategyOpCount .radix2DIT 1024 3 1 < strategyOpCount .radix4DIT 1024 3 1 := by
  native_decide

/-- Smoke: cheapest config finds the best. -/
example : (cheapestConfig babybear1024_configs).map (·.totalCost) = some 17920 := by
  native_decide

end AmoLean.EGraph.Verified.Bitwise.NTTFactorizationRules
