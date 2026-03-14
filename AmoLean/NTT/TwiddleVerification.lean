/-
  AMO-Lean: Twiddle Factor Verification (B93)
  Fase 18 — BitReverse + Twiddle

  Verifies that genTwiddleTable and genInvTwiddleTable produce
  the correct values: genTwiddleTable ω n = [ω^0, ω^1, ..., ω^(n-1)].

  Key results:
  1. `twiddleTable_correct` — genTwiddleTable matches (range n).map (ω ^ ·)
  2. `twiddleTable_getD_eq_pow` — element access = ω^k
  3. Concrete verifications: OMEGA_8^8 = 1, OMEGA_16^16 = 1 via native_decide
  4. `invTwiddleTable_getD_zero` — first element of inverse table is 1

  Upstream: NTT.BabyBear (genTwiddleTable, OMEGA_8, OMEGA_16)
-/

import AmoLean.NTT.BabyBear

namespace AmoLean.NTT.TwiddleVerification

open AmoLean.NTT.BabyBear
open AmoLean.Field.BabyBear

/-! ## Part 1: Twiddle Table Correctness -/

/-- genTwiddleTable ω n = (List.range n).map (BabyBearField.pow ω ·).
    This is true by definition — genTwiddleTable is defined exactly this way. -/
theorem twiddleTable_correct (ω : BabyBearField) (n : Nat) :
    genTwiddleTable ω n = (List.range n).map fun i => BabyBearField.pow ω i := by
  rfl

/-- Length of twiddle table is n. -/
theorem twiddleTable_length (ω : BabyBearField) (n : Nat) :
    (genTwiddleTable ω n).length = n := by
  simp [genTwiddleTable]

/-- Element access for twiddle table: the k-th element is ω^k. -/
theorem twiddleTable_getD_eq_pow (ω : BabyBearField) (n : Nat) (k : Nat) (hk : k < n) :
    (genTwiddleTable ω n).getD k ⟨0, by native_decide⟩ = BabyBearField.pow ω k := by
  simp [genTwiddleTable, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]

/-- Twiddle table first element is always 1 (ω^0 = 1). -/
theorem twiddleTable_first_is_one (ω : BabyBearField) (n : Nat) (hn : 0 < n) :
    (genTwiddleTable ω n).getD 0 ⟨0, by native_decide⟩ = BabyBearField.pow ω 0 := by
  exact twiddleTable_getD_eq_pow ω n 0 hn

/-! ## Part 2: Primitive Root Verification via native_decide -/

/-- OMEGA_8^8 = 1: the 8th primitive root raised to 8 is 1. -/
theorem omega8_pow8_eq_one :
    (BabyBearField.pow OMEGA_8 8).value = 1 := by native_decide

/-- OMEGA_16^16 = 1: the 16th primitive root raised to 16 is 1. -/
theorem omega16_pow16_eq_one :
    (BabyBearField.pow OMEGA_16 16).value = 1 := by native_decide

/-- OMEGA_8^4 = -1 (i.e., ORDER - 1 in BabyBear). -/
theorem omega8_pow4_eq_neg_one :
    (BabyBearField.pow OMEGA_8 4).value = ORDER - 1 := by native_decide

/-- OMEGA_16^8 = -1 (i.e., ORDER - 1 in BabyBear). -/
theorem omega16_pow8_eq_neg_one :
    (BabyBearField.pow OMEGA_16 8).value = ORDER - 1 := by native_decide

/-! ## Part 3: Inverse Twiddle Table Correctness -/

/-- The first element of the inverse twiddle table is 1. -/
theorem invTwiddleTable_getD_zero (ω : BabyBearField) (n : Nat) (hn : 0 < n) :
    (genInvTwiddleTable ω n).getD 0 ⟨0, by native_decide⟩ = BabyBearField.one := by
  simp [genInvTwiddleTable, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]

/-- Length of inverse twiddle table is n. -/
theorem invTwiddleTable_length (ω : BabyBearField) (n : Nat) :
    (genInvTwiddleTable ω n).length = n := by
  simp [genInvTwiddleTable]

/-- For k > 0, the inverse twiddle factor is ω^(n-k).
    Since ω^n = 1, we have ω^(n-k) = ω^(-k). -/
theorem invTwiddleTable_getD_pos (ω : BabyBearField) (n k : Nat)
    (hk : k < n) (hk_pos : 0 < k) :
    (genInvTwiddleTable ω n).getD k ⟨0, by native_decide⟩ = BabyBearField.pow ω (n - k) := by
  simp [genInvTwiddleTable, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  omega

/-! ## Part 4: Concrete Twiddle Table Checks -/

/-- OMEGA_8 twiddle table has 8 elements. -/
example : (genTwiddleTable OMEGA_8 8).length = 8 := by native_decide

/-- First twiddle factor for OMEGA_8 is 1. -/
example : ((genTwiddleTable OMEGA_8 8).getD 0 ⟨0, by native_decide⟩).value = 1 := by
  native_decide

/-- Product of forward and inverse twiddle factors: ω^k · ω^(n-k) = ω^n = 1.
    Checked concretely for OMEGA_8 at k=1. -/
example :
    let fwd := (genTwiddleTable OMEGA_8 8).getD 1 ⟨0, by native_decide⟩
    let inv := (genInvTwiddleTable OMEGA_8 8).getD 1 ⟨0, by native_decide⟩
    (BabyBearField.mul fwd inv).value = 1 := by native_decide

/-- Product check at k=3. -/
example :
    let fwd := (genTwiddleTable OMEGA_8 8).getD 3 ⟨0, by native_decide⟩
    let inv := (genInvTwiddleTable OMEGA_8 8).getD 3 ⟨0, by native_decide⟩
    (BabyBearField.mul fwd inv).value = 1 := by native_decide

/-! ## Part 5: Smoke Tests -/

#eval do
  let ω := OMEGA_8
  let twiddles := genTwiddleTable ω 8
  IO.println s!"OMEGA_8 twiddle table ({twiddles.length} elements):"
  for i in List.range 8 do
    let t := twiddles.getD i ⟨0, by native_decide⟩
    IO.println s!"  ω^{i} = {t.value}"
  -- Verify ω^8 = 1
  assert! (BabyBearField.pow ω 8).value == 1
  IO.println "✓ ω^8 = 1"

#eval do
  let ω := OMEGA_16
  -- Verify ω^16 = 1
  assert! (BabyBearField.pow ω 16).value == 1
  -- Verify ω^8 = -1
  assert! (BabyBearField.pow ω 8).value == ORDER - 1
  IO.println "✓ OMEGA_16: ω^16 = 1, ω^8 = -1"

#eval do
  let ω := OMEGA_8
  -- Check forward × inverse = 1 for all k
  for k in List.range 8 do
    let fwd := (genTwiddleTable ω 8).getD k ⟨0, by native_decide⟩
    let inv := (genInvTwiddleTable ω 8).getD k ⟨0, by native_decide⟩
    let prod := BabyBearField.mul fwd inv
    assert! prod.value == 1
  IO.println "✓ Forward × Inverse twiddle = 1 for all k in [0..7]"

end AmoLean.NTT.TwiddleVerification
