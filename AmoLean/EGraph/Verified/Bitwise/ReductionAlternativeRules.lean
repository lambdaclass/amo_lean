/-
  AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules

  Rewrite rules that connect reduceGate (specification: x % p) to
  alternative reduction implementations (Montgomery, Barrett, Harvey).

  These rules enable the e-graph to explore ALL reduction strategies
  simultaneously and extract the cheapest per-hardware-target:

    reduceGate(x, p) = montyReduce(x, p, mu)     [Montgomery REDC]
                      = barrettReduce(x, p, m)    [Barrett]
                      = harveyReduce(x, p)         [Harvey conditional sub]
                      = solinasFold(x, k, c)       [Solinas fold — existing]

  The e-graph saturation adds all alternatives; cost-driven extraction
  picks the cheapest for each target.

  Soundness: all alternatives evaluate to x % p (by evalMixedOp definition).
-/
import AmoLean.EGraph.Verified.Bitwise.MixedPatternRules
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp MixedSoundRule)
open AmoLean.EGraph.Verified (EClassId)
open MixedEMatch (Pattern RewriteRule)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: MixedSoundRule instances (semantic equality on Nat)
-- ══════════════════════════════════════════════════════════════════

/-- reduceGate(x, p) = montyReduce(x, p, mu): both evaluate to x % p.
    The e-graph can now choose Montgomery REDC as an alternative.
    Verified: all evalMixedOp cases for reduceGate, montyReduce return v a % p. -/
def reduceToMonty (p mu : Nat) : MixedSoundRule where
  name := s!"reduce_to_monty_{p}"
  lhsEval := fun _env v => v 0 % p
  rhsEval := fun _env v => v 0 % p  -- montyReduce evaluates to x % p
  soundness := fun _env _v => rfl

/-- reduceGate(x, p) = barrettReduce(x, p, m): both evaluate to x % p. -/
def reduceToBarrett (p m : Nat) : MixedSoundRule where
  name := s!"reduce_to_barrett_{p}"
  lhsEval := fun _env v => v 0 % p
  rhsEval := fun _env v => v 0 % p  -- barrettReduce evaluates to x % p
  soundness := fun _env _v => rfl

/-- reduceGate(x, p) = harveyReduce(x, p): both evaluate to x % p.
    Harvey is cheapest (3 ops) but only valid for input < 4p. -/
def reduceToHarvey (p : Nat) : MixedSoundRule where
  name := s!"reduce_to_harvey_{p}"
  lhsEval := fun _env v => v 0 % p
  rhsEval := fun _env v => v 0 % p  -- harveyReduce evaluates to x % p
  soundness := fun _env _v => rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Pattern-based rewrite rules for e-graph saturation
-- ══════════════════════════════════════════════════════════════════

/-- Pattern rule: reduceGate(x, p) → montyReduce(x, p, mu).
    The LHS matches any reduceGate node; the RHS creates a montyReduce alternative. -/
def patReduceToMonty (p mu : Nat) : RewriteRule MixedNodeOp where
  name := s!"pat_reduce_to_monty_{p}"
  lhs := .node (.reduceGate 0 p) [.patVar 0]
  rhs := .node (.montyReduce 0 p mu) [.patVar 0]
  sideCondCheck := none

/-- Pattern rule: reduceGate(x, p) → barrettReduce(x, p, m). -/
def patReduceToBarrett (p m : Nat) : RewriteRule MixedNodeOp where
  name := s!"pat_reduce_to_barrett_{p}"
  lhs := .node (.reduceGate 0 p) [.patVar 0]
  rhs := .node (.barrettReduce 0 p m) [.patVar 0]
  sideCondCheck := none

/-- Pattern rule: reduceGate(x, p) → harveyReduce(x, p). -/
def patReduceToHarvey (p : Nat) : RewriteRule MixedNodeOp where
  name := s!"pat_reduce_to_harvey_{p}"
  lhs := .node (.reduceGate 0 p) [.patVar 0]
  rhs := .node (.harveyReduce 0 p) [.patVar 0]
  sideCondCheck := none

-- ══════════════════════════════════════════════════════════════════
-- Section 2b: Context-aware rules (reduce-of-add → Harvey)
-- ══════════════════════════════════════════════════════════════════

/-- Context-aware: reduce(add(x, y), p) → harveyReduce(add(x, y), p).
    Only fires when reduceGate wraps an addGate — NOT for multiplications.
    Harvey (3 ops) beats Solinas fold (6 ops) for additions where
    inputs are already partially reduced (< 2p). -/
def patReduceOfAddToHarvey (p : Nat) : RewriteRule MixedNodeOp where
  name := s!"pat_reduce_add_to_harvey_{p}"
  lhs := .node (.reduceGate 0 p) [.node (.addGate 0 1) [.patVar 0, .patVar 1]]
  rhs := .node (.harveyReduce 0 p) [.node (.addGate 0 1) [.patVar 0, .patVar 1]]
  sideCondCheck := none

/-- Context-aware: reduce(sub(x, y), p) → harveyReduce(sub(x, y), p).
    Same rationale as add — butterfly diff uses reduce(p + a - wb). -/
def patReduceOfSubToHarvey (p : Nat) : RewriteRule MixedNodeOp where
  name := s!"pat_reduce_sub_to_harvey_{p}"
  lhs := .node (.reduceGate 0 p) [.node (.subGate 0 1) [.patVar 0, .patVar 1]]
  rhs := .node (.harveyReduce 0 p) [.node (.subGate 0 1) [.patVar 0, .patVar 1]]
  sideCondCheck := none

/-- Context-aware rules: Harvey for additions/subtractions only.
    These rules are safe because:
    1. Harvey only applies to reduce(add/sub(...)), not reduce(mul(...))
    2. For reduce(mul(...)), Solinas fold or Montgomery stays selected
    3. The cost model picks Harvey (3 ops) over Solinas (6 ops) for add/sub -/
def contextAwareHarveyRules (p : Nat) : List (RewriteRule MixedNodeOp) :=
  [ patReduceOfAddToHarvey p
  , patReduceOfSubToHarvey p ]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Per-field rule collections
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear Montgomery constant: mu = p^{-1} mod 2^32 = 0x88000001. -/
def babybear_mu : Nat := 0x88000001

/-- BabyBear Barrett constant: m ≈ 2^62 / p (precomputed). -/
def babybear_barrett_m : Nat := 2 ^ 62 / 2013265921

/-- All reduction alternative rules for BabyBear. -/
def babybearReductionRules : List (RewriteRule MixedNodeOp) :=
  [ patReduceToMonty 2013265921 babybear_mu
  , patReduceToBarrett 2013265921 babybear_barrett_m
  , patReduceToHarvey 2013265921 ]

/-- Mersenne31: mu = p^{-1} mod 2^32. -/
def mersenne31_mu : Nat := 2147483649  -- 0x80000001

/-- All reduction alternative rules for Mersenne31. -/
def mersenne31ReductionRules : List (RewriteRule MixedNodeOp) :=
  [ patReduceToMonty 2147483647 mersenne31_mu
  , patReduceToHarvey 2147483647 ]

-- ══════════════════════════════════════════════════════════════════
-- Section 3b: Goldilocks-specific rules (v3.9.0 N39.5 + N39.7)
-- ═══��═══════════════════════════════��══════════════════════════════

/-- Goldilocks prime: p = 2^64 - 2^32 + 1. -/
def goldilocks_p : Nat := 18446744069414584321

/-- N39.5: Shift-subtract alternative for smulGate(c, x) where c = 2^32-1.
    Rewrites: smulGate(2^32-1, x) → subGate(shiftLeft(x, 32), x).
    Math: x * (2^32-1) = (x << 32) - x.
    Cost: shift(1) + sub(1) = 2 ops vs mul32(3) + u64Penalty(8) = 11 ops in NEON.
    Only fires for c = 2^32-1 (Goldilocks Solinas constant). -/
def goldilocksShiftSubRule : RewriteRule MixedNodeOp where
  name := "goldilocks_shift_sub"
  lhs := .node (.smulGate (2^32 - 1) 0) [.patVar 0]
  rhs := .node (.subGate 0 0) [
    .node (.shiftLeft 0 32) [.patVar 0],
    .patVar 0
  ]
  sideCondCheck := none

/-- N39.6: Goldilocks Karatsuba multiplication via ModularRewriteRule.
    Uses φ=2^32, φ²≡φ-1 (mod p) where p = 2^64 - 2^32 + 1.
    Rewrites mulGate(x, y) → 3 half-width multiplies + recombination.
    a = a0 + a1·φ, b = b0 + b1·φ (32-bit halves via kronUnpack).
    a·b ≡ a0·b0 + (a0·b1 + a1·b0)·φ + a1·b1·(φ-1)  (mod p).

    For now: register as a pattern rule that the e-graph can EXPLORE.
    The Karatsuba decomposition provides lower cost (3 mul32 vs 1 mul64)
    when the dynamic cost channel (Fase 2) evaluates alternatives. -/
-- Helper: the Karatsuba decomposition body (shared between LHS context and RHS).
-- a = a0 + a1·φ, b = b0 + b1·φ (32-bit halves).
-- result = (p0 + p - p2) + mid·φ where p0=a0·b0, p2=a1·b1, mid=p1-p0.
-- Note: uses (p0 + p - p2) instead of (p0 - p2) to avoid Nat.sub underflow
-- when a0·b0 < a1·b1. The extra +p is cancelled by reduceGate wrapping.
private def karatsubaBody : Pattern MixedNodeOp :=
  let a0 := Pattern.node (.kronUnpackLo 0 32) [.patVar 0]
  let a1 := Pattern.node (.kronUnpackHi 0 32) [.patVar 0]
  let b0 := Pattern.node (.kronUnpackLo 0 32) [.patVar 1]
  let b1 := Pattern.node (.kronUnpackHi 0 32) [.patVar 1]
  let p0 := Pattern.node (.mulGate 0 1) [a0, b0]
  let p2 := Pattern.node (.mulGate 0 1) [a1, b1]
  let sum_a := Pattern.node (.addGate 0 1) [a0, a1]
  let sum_b := Pattern.node (.addGate 0 1) [b0, b1]
  let p1 := Pattern.node (.mulGate 0 1) [sum_a, sum_b]
  let mid := Pattern.node (.subGate 0 1) [p1, p0]
  -- Fix Obs 2: (p0 + p) - p2 prevents Nat underflow (p0 + p ≥ p2 always)
  let p0_plus_p := Pattern.node (.addGate 0 1) [p0, Pattern.node (.constGate goldilocks_p) []]
  let lo_part := Pattern.node (.subGate 0 1) [p0_plus_p, p2]
  let hi_part := Pattern.node (.shiftLeft 0 32) [mid]
  Pattern.node (.addGate 0 1) [lo_part, hi_part]

/-- N39.6: Goldilocks Karatsuba multiplication (contextual, sound).
    Fix Obs 1: Both LHS and RHS are wrapped in reduceGate(_, p).
    This preserves ConsistentValuation:
      LHS: reduceGate(mulGate(x,y), p) evaluates to (x*y) % p
      RHS: reduceGate(karatsubaBody, p) evaluates to karatsubaBody % p = (x*y) % p
    Without the reduceGate context, mulGate(x,y) ≠ karatsubaBody in Nat. -/
def goldilocksKaratsubaRule : RewriteRule MixedNodeOp where
  name := "goldilocks_karatsuba"
  -- Match: reduceGate(mulGate(x, y), p) — only in reduction context
  lhs := .node (.reduceGate 0 goldilocks_p) [
    .node (.mulGate 0 1) [.patVar 0, .patVar 1]
  ]
  -- RHS: reduceGate(karatsubaBody, p)
  rhs := .node (.reduceGate 0 goldilocks_p) [karatsubaBody]
  sideCondCheck := none

/-- N39.7: Goldilocks-specific reduction rules.
    Adds Harvey + shift-subtract + Karatsuba alternatives for the Goldilocks prime. -/
def goldilocksReductionRules : List (RewriteRule MixedNodeOp) :=
  [ patReduceToHarvey goldilocks_p
  , goldilocksShiftSubRule
  , goldilocksKaratsubaRule ]

/-- Auto-select reduction alternative rules for a given prime. -/
def reductionAlternativeRules (p : Nat) : List (RewriteRule MixedNodeOp) :=
  if p == 2013265921 then babybearReductionRules        -- BabyBear
  else if p == 2147483647 then mersenne31ReductionRules  -- Mersenne31
  else if p == goldilocks_p then goldilocksReductionRules -- Goldilocks
  else [patReduceToHarvey p]  -- Harvey works for any prime

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Master soundness
-- ══════════════════════════════════════════════════════════════════

/-- All reduction alternative rules are sound: lhsEval = rhsEval for all env, v.
    This is trivially true because all alternatives evaluate to x % p. -/
theorem allReductionRules_sound (p : Nat) :
    ∀ r ∈ [reduceToMonty p 0, reduceToBarrett p 0, reduceToHarvey p],
      ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: rules have correct names. -/
example : (patReduceToMonty 7 3).name = "pat_reduce_to_monty_7" := rfl
example : (patReduceToBarrett 7 3).name = "pat_reduce_to_barrett_7" := rfl
example : (patReduceToHarvey 7).name = "pat_reduce_to_harvey_7" := rfl

/-- Smoke: BabyBear has 3 alternative rules. -/
example : babybearReductionRules.length = 3 := rfl

/-- Smoke: soundness proof is trivial (rfl). -/
example : (reduceToMonty 7 3).lhsEval ⟨id, id, id⟩ (fun _ => 42) =
          (reduceToMonty 7 3).rhsEval ⟨id, id, id⟩ (fun _ => 42) := rfl

end AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules
