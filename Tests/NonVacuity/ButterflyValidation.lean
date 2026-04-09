/-
  Tests.NonVacuity.ButterflyValidation — B73.1 Butterfly pattern coverage tests

  Validates that butterfly rules fire on diverse syntactically equivalent representations.
-/
import AmoLean.EGraph.Verified.Bitwise.ButterflyRules
import AmoLean.EGraph.Verified.Bitwise.MulReduceRules
import AmoLean.EGraph.Verified.Bitwise.KroneckerRules

set_option autoImplicit false

namespace Tests.NonVacuity.ButterflyValidation

open AmoLean.EGraph.Verified.Bitwise (MixedSoundRule MixedEnv)
open AmoLean.EGraph.Verified.Bitwise.ButterflyRules
open AmoLean.EGraph.Verified.Bitwise.MulReduceRules
open AmoLean.EGraph.Verified.Bitwise.KroneckerRules

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Non-vacuity for mul-reduce rules
-- ══════════════════════════════════════════════════════════════════

/-- reduceIdempotent on BabyBear prime. -/
example : (42 % 2013265921) % 2013265921 = 42 % 2013265921 :=
  (reduceIdempotentRule 2013265921).soundness
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun _ => 42)

/-- addAbsorbReduce on concrete values. -/
example : (10 + 42 % 7) % 7 = (10 + 42) % 7 :=
  (addAbsorbReduceRule 7).soundness
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun pv => if pv = 0 then 10 else 42)

/-- mulModDist on concrete values. -/
example : (6 * 7) % 5 = ((6 % 5) * (7 % 5)) % 5 :=
  (mulModDistRule 5).soundness
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun pv => if pv = 0 then 6 else 7)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Non-vacuity for butterfly rules
-- ══════════════════════════════════════════════════════════════════

/-- CT sum decomposition on BabyBear. -/
example : (10 + 3 * 7) % 2013265921 = (10 % 2013265921 + (3 * 7) % 2013265921) % 2013265921 :=
  (butterflyCTSumDecompRule 2013265921).soundness
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun pv => if pv = 0 then 10 else if pv = 1 then 3 else 7)

/-- Twiddle mul decomposition. -/
example : (100 * 200) % 7 = ((100 % 7) * (200 % 7)) % 7 :=
  (twiddleMulDecompRule 7).soundness
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun pv => if pv = 0 then 100 else 200)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Non-vacuity for Kronecker rules
-- ══════════════════════════════════════════════════════════════════

/-- Unpack lo roundtrip. -/
example : (42 + 99 * 2^32) % 2^32 = 42 % 2^32 :=
  (unpackLoAfterPackRule 32).soundness
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun pv => if pv = 0 then 42 else 99)

/-- Pack fuse add. -/
example : (10 + 20 * 2^32) + (5 + 3 * 2^32) = (10 + 5) + (20 + 3) * 2^32 :=
  (packFuseAddRule 32).soundness
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun pv => if pv = 0 then 10 else if pv = 1 then 5 else if pv = 2 then 20 else 3)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Overflow bound non-vacuity
-- ══════════════════════════════════════════════════════════════════

/-- Lazy CT bound: 3 + 5 < 4*4 (inputs < 2*4=8, bound 4*4=16). -/
example : 3 + 5 < 4 * 4 := lazy_ct_bound 3 5 4 (by omega) (by omega)

/-- Lazy GS bound: 2 + 3 < 2*4 (inputs < 4, bound 2*4=8). -/
example : 2 + 3 < 2 * 4 := lazy_gs_bound 2 3 4 (by omega) (by omega)

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Rule collection non-vacuity
-- ══════════════════════════════════════════════════════════════════

example : (allButterflyRules 7).length = 3 := rfl
example : (allMulReduceRules 7).length = 3 := rfl
example : (allKroneckerRules 32).length = 3 := rfl

end Tests.NonVacuity.ButterflyValidation
