/-
  AmoLean.EGraph.Verified.Bitwise.HarveyPreservation — B75

  Adapt BitwiseLean's Harvey butterfly theorems into MixedSoundRule form.

  Harvey's trick: use conditional subtraction (`x - p` if `x >= p`) instead of
  full `mod p`. This is cheaper and composable across butterfly stages.

  ## Rules
  - `harveyReduceRule(p)`: Harvey reduce preserves mod p (sorry from spike)
  - `harveyBoundRule(p)`: Harvey output is < 2*p (fully proved)
  - `harveyCanonicalize(p)`: final canonicalization from [0, 2p) to [0, p)

  ## Dependencies
  - `harveyReduce`, `harveyReduce_mod`, `harveyReduce_bound` from
    `LazyReductionSpike_aux`
  - `MixedSoundRule` from `BitwiseRules`
-/
import AmoLean.EGraph.Verified.Bitwise.LazyReductionSpike_aux
import AmoLean.EGraph.Verified.Bitwise.ButterflyRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.HarveyPreservation

open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp MixedSoundRule)
open AmoLean.EGraph.Verified.Bitwise.LazyReductionSpike
  (harveyReduce harveyReduce_mod harveyReduce_bound)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: harveyReduceRule — Harvey conditional sub preserves mod p
-- ══════════════════════════════════════════════════════════════════

/-- Harvey conditional subtraction as a MixedSoundRule.
    States: `harveyReduce(x, p) % p = x % p` for all x.

    Since harveyReduce_mod in the spike has sorry (for the x >= 2p and x >= p
    cases involving Nat.mod with subtraction), this rule inherits that sorry.
    The soundness proof is conditional on `0 < p` and `x < 4*p`. For the
    universally quantified MixedSoundRule form, we assume the e-graph
    guarantees these preconditions via bound tracking (B74). -/
def harveyReduceRule (p : Nat) (hp : 0 < p) : MixedSoundRule where
  name := s!"harvey_reduce_{p}"
  lhsEval := fun _env v => harveyReduce (v 0) p % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env v => by
    -- harveyReduce(x, p) ≡ x (mod p) for ALL x, not just x < 4p.
    -- The three branches of harveyReduce each preserve mod p.
    unfold harveyReduce
    split
    · -- x >= 2p: result = x - 2p, and (x - 2p) % p = x % p
      rename_i hge
      have heq : v 0 = v 0 - 2 * p + p * 2 := by omega
      conv_rhs => rw [heq, Nat.add_mul_mod_self_left]
    · split
      · -- p ≤ x < 2p: result = x - p, and (x - p) % p = x % p
        rename_i _ hge
        have heq : v 0 = v 0 - p + p := by omega
        conv_rhs => rw [heq, Nat.add_mod_right]
      · -- x < p: trivial
        rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: harveyBoundRule — Harvey output is bounded
-- ══════════════════════════════════════════════════════════════════

/-- The Harvey reduce output is strictly less than 2*p.
    This is FULLY PROVED (no sorry) — the key property that makes
    Harvey reduction composable across butterfly stages. -/
theorem harveyBoundRule (p : Nat) (x : Nat) (hx : x < 4 * p) :
    harveyReduce x p < 2 * p :=
  harveyReduce_bound x p hx

/-- Variant: for any bounded input, Harvey reduce keeps the value in [0, 2p).
    Stated as a bound on the e-class valuation. -/
theorem harveyBound_valuation (p : Nat) (v : EClassId → Nat) (hv : v 0 < 4 * p) :
    harveyReduce (v 0) p < 2 * p :=
  harveyReduce_bound (v 0) p hv

-- ══════════════════════════════════════════════════════════════════
-- Section 3: harveyCanonicalize — final reduction from [0, 2p) to [0, p)
-- ══════════════════════════════════════════════════════════════════

/-- Single conditional subtraction to canonicalize: if x < 2p, then
    `if x >= p then x - p else x` gives the canonical representative in [0, p).
    This is the final step after all butterfly stages. -/
def canonicalize (x p : Nat) : Nat :=
  if x >= p then x - p else x

/-- Canonicalize preserves mod p when x < 2p. -/
theorem canonicalize_mod (x p : Nat) (_hp : 0 < p) (hx : x < 2 * p) :
    canonicalize x p % p = x % p := by
  unfold canonicalize
  split
  · -- x >= p: result = x - p, and x - p < p
    rename_i hge
    have hlt : x - p < p := by omega
    rw [Nat.mod_eq_of_lt hlt]
    -- Goal: x - p = x % p
    -- Since p ≤ x < 2p, x = p + (x - p) with x - p < p
    have heq : x = p + (x - p) := by omega
    conv_rhs => rw [heq]
    -- Goal: x - p = (p + (x - p)) % p
    rw [Nat.add_mod_left]
    exact (Nat.mod_eq_of_lt hlt).symm
  · -- x < p: result = x
    rfl

/-- Canonicalize output is in [0, p). -/
theorem canonicalize_lt (x p : Nat) (_hp : 0 < p) (hx : x < 2 * p) :
    canonicalize x p < p := by
  unfold canonicalize
  split <;> omega

/-- Canonicalize as a MixedSoundRule for the final e-graph rewrite.
    Composes with Harvey reduce: after all butterfly stages produce
    values in [0, 2p), this rule maps them to [0, p) = canonical mod p.

    The soundness proof IS complete (no sorry): `canonicalize(x, p) % p = x % p`
    holds unconditionally for x < 2p. We wrap with sorry only for the
    universal quantifier (where x may exceed 2p in the e-graph valuation). -/
def harveyCanonicalize (p : Nat) (hp : 0 < p) : MixedSoundRule where
  name := s!"harvey_canonicalize_{p}"
  lhsEval := fun _env v => canonicalize (v 0) p % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env v => by
    -- canonicalize(x, p) % p = x % p for ALL x.
    -- In range (x < 2p): canonicalize_mod handles it.
    -- Out of range: canonicalize(x, p) = x - p (since x ≥ p), then (x - p) % p = x % p.
    by_cases hx : v 0 < 2 * p
    · exact canonicalize_mod (v 0) p hp hx
    · push_neg at hx
      unfold canonicalize
      split
      · -- v 0 >= p: (v 0 - p) % p = v 0 % p
        rename_i hge
        have heq : v 0 = v 0 - p + p := by omega
        conv_rhs => rw [heq, Nat.add_mod_right]
      · -- v 0 < p: contradicts v 0 >= 2p
        omega

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Composition: Harvey reduce followed by canonicalize
-- ══════════════════════════════════════════════════════════════════

/-- Full Harvey pipeline: reduce then canonicalize.
    For x < 4p: canonicalize(harveyReduce(x, p), p) gives the canonical
    representative in [0, p), equal to x % p.

    Bound: harveyReduce(x, p) < 2p (proved), so canonicalize input is valid. -/
theorem harvey_full_pipeline (x p : Nat) (hp : 0 < p) (hx : x < 4 * p) :
    canonicalize (harveyReduce x p) p % p = x % p := by
  have hbound : harveyReduce x p < 2 * p := harveyReduce_bound x p hx
  rw [canonicalize_mod (harveyReduce x p) p hp hbound]
  exact harveyReduce_mod x p hp hx

/-- The full pipeline output is in [0, p). -/
theorem harvey_full_pipeline_lt (x p : Nat) (hp : 0 < p) (hx : x < 4 * p) :
    canonicalize (harveyReduce x p) p < p :=
  canonicalize_lt (harveyReduce x p) p hp (harveyReduce_bound x p hx)

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Rule collection
-- ══════════════════════════════════════════════════════════════════

/-- All Harvey-related rewrite rules for a given prime. -/
def allHarveyRules (p : Nat) (hp : 0 < p) : List MixedSoundRule :=
  [ harveyReduceRule p hp
  , harveyCanonicalize p hp ]

/-- All Harvey rules are sound (inherited from individual soundness proofs). -/
theorem allHarveyRules_sound (p : Nat) (hp : 0 < p) :
    ∀ r ∈ allHarveyRules p hp, ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: harveyReduce on small values. -/
example : harveyReduce 10 7 = 3 := by native_decide
example : harveyReduce 20 7 = 6 := by native_decide
example : harveyReduce 5 7 = 5 := by native_decide

/-- Smoke: canonicalize on small values. -/
example : canonicalize 10 7 = 3 := by native_decide
example : canonicalize 5 7 = 5 := by native_decide
example : canonicalize 13 7 = 6 := by native_decide

/-- Smoke: full pipeline. -/
example : canonicalize (harveyReduce 25 7) 7 = 25 % 7 := by native_decide
example : canonicalize (harveyReduce 10 7) 7 = 10 % 7 := by native_decide
example : canonicalize (harveyReduce 100 31) 31 = 100 % 31 := by native_decide

/-- Smoke: Harvey bound holds. -/
example : harveyReduce 25 7 < 2 * 7 := by native_decide
example : harveyReduce 100 31 < 2 * 31 := by native_decide

/-- Smoke: allHarveyRules has 2 rules. -/
example : (allHarveyRules 7 (by omega)).length = 2 := rfl

/-- Smoke: canonicalize gives canonical representative. -/
example : canonicalize (harveyReduce 27 7) 7 < 7 := by native_decide
example : canonicalize (harveyReduce 120 31) 31 < 31 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.HarveyPreservation
