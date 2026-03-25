/-
  AmoLean.EGraph.Verified.Bitwise.MulReduceRules — Mul+Reduce Rewrite Rules

  B72 (CRITICO): Rules that connect multiplication with modular reduction.
  These enable the e-graph to optimize `(a * b) % p` as a rewrite chain,
  which is the fundamental operation in NTT butterfly computations.

  Rules:
  - mulReduceRule: mulGate(a,b) can be followed by reduceGate to get (a*b) % p
  - addAbsorbReduceRule: (a + (x % p)) % p = (a + x) % p
  - reduceIdempotentRule: (x % p) % p = x % p
  - subAbsorbReduceRule: (a - (x % p)) % p = (a - x) % p (when a >= x)

  Each rule is a MixedSoundRule with proven soundness.
-/
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.MulReduceRules

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp MixedSoundRule)
open AmoLean.EGraph.Verified (EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Modular arithmetic lemmas
-- ══════════════════════════════════════════════════════════════════

/-- `(x % p) % p = x % p` — reduction is idempotent. -/
theorem mod_mod_self (x p : Nat) : (x % p) % p = x % p :=
  Nat.mod_mod_of_dvd x (dvd_refl p)

/-- `(a + x % p) % p = (a + x) % p` — reduce absorbs into addition. -/
theorem add_mod_absorb (a x p : Nat) : (a + x % p) % p = (a + x) % p := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd x (dvd_refl p), ← Nat.add_mod]

/-- `(a + x) % p = (a % p + x % p) % p` — standard mod distributivity. -/
theorem add_mod_dist (a x p : Nat) : (a + x) % p = (a % p + x % p) % p :=
  Nat.add_mod a x p

-- ══════════════════════════════════════════════════════════════════
-- Section 2: MixedSoundRule instances
-- ══════════════════════════════════════════════════════════════════

/-- `(x % p) % p = x % p` — reduce is idempotent.
    In the e-graph: reduceGate(reduceGate(x, p), p) ≡ reduceGate(x, p). -/
def reduceIdempotentRule (p : Nat) : MixedSoundRule where
  name := s!"reduce_idempotent_{p}"
  lhsEval := fun _env v => (v 0 % p) % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env v => mod_mod_self (v 0) p

/-- `(a + (x % p)) % p = (a + x) % p` — reduce absorbs into addition.
    In the e-graph: reduceGate(addGate(a, reduceGate(x, p)), p) ≡ reduceGate(addGate(a, x), p). -/
def addAbsorbReduceRule (p : Nat) : MixedSoundRule where
  name := s!"add_absorb_reduce_{p}"
  lhsEval := fun _env v => (v 0 + v 1 % p) % p
  rhsEval := fun _env v => (v 0 + v 1) % p
  soundness := fun _env v => add_mod_absorb (v 0) (v 1) p

/-- `(a * b) % p = ((a % p) * (b % p)) % p` — standard multiplicative mod.
    This IS universally sound as a Nat identity. -/
def mulModDistRule (p : Nat) : MixedSoundRule where
  name := s!"mul_mod_dist_{p}"
  lhsEval := fun _env v => (v 0 * v 1) % p
  rhsEval := fun _env v => ((v 0 % p) * (v 1 % p)) % p
  soundness := fun _env v => Nat.mul_mod (v 0) (v 1) p

/-- All unconditionally sound mul-reduce rules. -/
def allMulReduceRules (p : Nat) : List MixedSoundRule :=
  [ reduceIdempotentRule p
  , addAbsorbReduceRule p
  , mulModDistRule p
  ]

/-- Master soundness for all mul-reduce rules. -/
theorem allMulReduceRules_sound (p : Nat) :
    ∀ r ∈ allMulReduceRules p, ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: reduce idempotent on BabyBear. -/
example : (42 % 2013265921) % 2013265921 = 42 % 2013265921 := by native_decide

/-- Smoke: add absorb reduce. -/
example : (10 + 42 % 7) % 7 = (10 + 42) % 7 := by native_decide

/-- Smoke: mul mod dist. -/
example : (6 * 7) % 5 = ((6 % 5) * (7 % 5)) % 5 := by native_decide

/-- Smoke: allMulReduceRules is non-empty. -/
example : (allMulReduceRules 7).length = 3 := rfl

end AmoLean.EGraph.Verified.Bitwise.MulReduceRules
