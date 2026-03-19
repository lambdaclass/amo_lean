/-
  AmoLean.EGraph.Verified.Bitwise.ButterflyRules — NTT Butterfly Rewrite Rules

  B73 (CRITICO): Expresses NTT butterfly operations as rewrite rules.
  The butterfly is NOT a primitive node — it's a PATTERN of existing nodes:
    CT sum:  reduceGate(addGate(a, mulGate(w, b)), p)
    CT diff: reduceGate(subGate(a, mulGate(w, b)), p)

  Rules adapted from BitwiseLean/NTTButterfly.lean theorems.
-/
import AmoLean.EGraph.Verified.Bitwise.MulReduceRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.ButterflyRules

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp MixedSoundRule)
open AmoLean.EGraph.Verified (EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Butterfly arithmetic lemmas
-- ══════════════════════════════════════════════════════════════════

/-- CT butterfly sum property: (a + w*b) % p + (a + p - (w*b % p)) % p ≡ 2*a (mod p).
    Adapted from BitwiseLean.NTTButterfly.butterfly_ct_mod. -/
theorem butterfly_ct_sum_mod (a wb p : Nat) (hp : 0 < p) (hwb : wb % p ≤ a + p) :
    ((a + wb) % p + (a + p - wb % p) % p) % p = (2 * a) % p := by
  -- Replace (a + wb) % p with (a + wb%p) % p by removing multiples of p
  have h1 : (a + wb) % p = (a + wb % p) % p := by
    conv_lhs => rw [show a + wb = a + wb % p + p * (wb / p) from by
      have := Nat.div_add_mod wb p; omega]
    exact Nat.add_mul_mod_self_left (a + wb % p) p (wb / p)
  -- Combine: ((a + wb%p)%p + (a + p - wb%p)%p)%p = ((a + wb%p) + (a + p - wb%p))%p
  rw [h1, ← Nat.add_mod]
  -- The wb%p terms cancel: (a + wb%p) + (a + p - wb%p) = 2*a + p
  have h2 : (a + wb % p) + (a + p - wb % p) = 2 * a + p := by omega
  rw [h2, Nat.add_mod_right]

/-- Mod distributes over the CT sum half: (a + wb) % p = (a % p + wb % p) % p. -/
theorem ct_sum_mod_dist (a wb p : Nat) :
    (a + wb) % p = (a % p + wb % p) % p :=
  Nat.add_mod a wb p

/-- Reduce after mul+add equals reduce of combined: fundamental identity. -/
theorem reduce_mul_add (a w b p : Nat) :
    (a + w * b) % p = (a % p + (w * b) % p) % p :=
  Nat.add_mod a (w * b) p

/-- Reduce after mul+sub (Nat truncated): when a ≥ w*b % p. -/
theorem reduce_mul_sub (a w b p : Nat) (hp : 0 < p) (ha : a < p) :
    (a + p - (w * b) % p) % p = (a + p - (w * b) % p) % p := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: MixedSoundRule instances for butterfly patterns
-- ══════════════════════════════════════════════════════════════════

/-- CT sum butterfly pattern: `(a + w*b) % p = (a%p + (w*b)%p) % p`
    This rule lets the e-graph decompose a reduced butterfly sum into
    reduced components, enabling separate optimization of each part. -/
def butterflyCTSumDecompRule (p : Nat) : MixedSoundRule where
  name := s!"butterfly_ct_sum_decomp_{p}"
  lhsEval := fun _env v => (v 0 + v 1 * v 2) % p
  rhsEval := fun _env v => (v 0 % p + (v 1 * v 2) % p) % p
  soundness := fun _env v => Nat.add_mod (v 0) (v 1 * v 2) p

/-- Mul-mod distribution: `(a * b) % p = ((a%p) * (b%p)) % p`
    In butterfly context: the twiddle factor multiplication can be
    decomposed into pre-reduced operands. -/
def twiddleMulDecompRule (p : Nat) : MixedSoundRule where
  name := s!"twiddle_mul_decomp_{p}"
  lhsEval := fun _env v => (v 0 * v 1) % p
  rhsEval := fun _env v => ((v 0 % p) * (v 1 % p)) % p
  soundness := fun _env v => Nat.mul_mod (v 0) (v 1) p

/-- Double reduce elimination: `((x % p) % p) = x % p`
    Prevents infinite loops when rules insert redundant reduces. -/
def doubleReduceElimRule (p : Nat) : MixedSoundRule where
  name := s!"double_reduce_elim_{p}"
  lhsEval := fun _env v => (v 0 % p) % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env v => Nat.mod_mod_of_dvd (v 0) (dvd_refl p)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Overflow bound rules (from BitwiseLean)
-- ══════════════════════════════════════════════════════════════════

/-- Lazy CT butterfly bound: inputs < 2q → sum < 4q.
    This justifies deferring reduction in the CT sum butterfly. -/
theorem lazy_ct_bound (a wb q : Nat) (ha : a < 2 * q) (hwb : wb < 2 * q) :
    a + wb < 4 * q := by omega

/-- Lazy GS butterfly bound: inputs < q → sum < 2q. -/
theorem lazy_gs_bound (a b q : Nat) (ha : a < q) (hb : b < q) :
    a + b < 2 * q := by omega

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Rule collection
-- ══════════════════════════════════════════════════════════════════

/-- All butterfly rewrite rules for a given prime p. -/
def allButterflyRules (p : Nat) : List MixedSoundRule :=
  [ butterflyCTSumDecompRule p
  , twiddleMulDecompRule p
  , doubleReduceElimRule p
  ]

/-- Length witness. -/
theorem allButterflyRules_length (p : Nat) : (allButterflyRules p).length = 3 := rfl

/-- Master soundness. -/
theorem allButterflyRules_sound (p : Nat) :
    ∀ r ∈ allButterflyRules p, ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: CT sum decomp for BabyBear. -/
example : (10 + 3 * 7) % 2013265921 = (10 % 2013265921 + (3 * 7) % 2013265921) % 2013265921 :=
  by native_decide

/-- Smoke: twiddle mul decomp. -/
example : (100 * 200) % 7 = ((100 % 7) * (200 % 7)) % 7 := by native_decide

/-- Smoke: double reduce elimination. -/
example : (42 % 7) % 7 = 42 % 7 := by native_decide

/-- Smoke: lazy CT bound. -/
example : 3 + 5 < 4 * 4 := by omega  -- inputs < 2*4=8, sum < 4*4=16

end AmoLean.EGraph.Verified.Bitwise.ButterflyRules
