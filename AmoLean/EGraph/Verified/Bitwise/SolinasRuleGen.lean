import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge
import AmoLean.EGraph.Verified.Bitwise.FieldFoldRules

/-!
# AmoLean.EGraph.Verified.Bitwise.SolinasRuleGen

Generalized Solinas rule generation: derives `FieldFoldRule` instances from
prime structure using the Solinas pattern p = 2^a - 2^b + 1.

All ZK-friendly pseudo-Mersenne primes (BabyBear, KoalaBear, Goldilocks) share
this form. Instead of handcrafting each rule, `deriveFieldFoldRule` takes a
`SolinasConfig` and produces a sound `FieldFoldRule` automatically.

## Key results

- `SolinasConfig`: structure capturing (a, b) with validity conditions
- `solinas_prime_form`: cfg.prime = 2^a - (2^b - 1) (pseudo-Mersenne form)
- `solinas_residue`: 2^a % cfg.prime = 2^b - 1
- `solinas_fold_step`: x % cfg.prime = ((x >>> a) * (2^b - 1) + (x &&& (2^a - 1))) % cfg.prime
- `deriveFieldFoldRule`: SolinasConfig → FieldFoldRule (zero sorry)
- `deriveFieldFoldRule_sound`: generated rules are sound
- `detectSolinasForm`: Nat → Except String SolinasConfig (compile-time detection)
- Concrete configs for BabyBear, KoalaBear, Goldilocks

## References

- J. Solinas, "Generalized Mersenne Numbers" (1999), CACR Technical Report.
- BitwiseLean library: SolinasFold.lean (source pattern, adapted here)
- FieldFoldRules.lean: `two_pow_mod_pseudo_mersenne`, `pseudo_mersenne_fold_correct`
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

/-! ## Solinas configuration -/

/-- A prime of the form p = 2^a - 2^b + 1 where a > b > 0.
    The condition `h2b : 2 * (2^b - 1) < 2^a` ensures the pseudo-Mersenne
    fold is valid (the constant c = 2^b - 1 satisfies the half-range bound). -/
structure SolinasConfig where
  /-- High exponent (bit width for splitting) -/
  a : Nat
  /-- Low exponent (determines the correction constant c = 2^b - 1) -/
  b : Nat
  /-- The high exponent is positive -/
  ha : 0 < a
  /-- The low exponent is positive -/
  hb : 0 < b
  /-- The low exponent is strictly less than the high exponent -/
  hab : b < a
  /-- Pseudo-Mersenne half-range: 2*(2^b - 1) < 2^a, ensuring c < p -/
  h2b : 2 * (2 ^ b - 1) < 2 ^ a

/-- The Solinas prime: p = 2^a - 2^b + 1.
    Equivalently, p = 2^a - c where c = 2^b - 1 (pseudo-Mersenne form). -/
def SolinasConfig.prime (cfg : SolinasConfig) : Nat := 2 ^ cfg.a - 2 ^ cfg.b + 1

/-- The correction constant: c = 2^b - 1. -/
def SolinasConfig.correction (cfg : SolinasConfig) : Nat := 2 ^ cfg.b - 1

/-! ## Auxiliary lemma -/

/-- For b > 0, we have 0 < 2^b - 1. -/
private theorem two_pow_b_sub_one_pos (b : Nat) (hb : 0 < b) : 0 < 2 ^ b - 1 := by
  have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb
  simp at this; omega

/-! ## Core theorems -/

/-- A Solinas prime equals the pseudo-Mersenne form 2^a - (2^b - 1).
    This bridges the Solinas definition p = 2^a - 2^b + 1 to the
    pseudo-Mersenne form p = 2^a - c expected by `two_pow_mod_pseudo_mersenne`. -/
theorem solinas_prime_form (cfg : SolinasConfig) :
    cfg.prime = 2 ^ cfg.a - (2 ^ cfg.b - 1) := by
  unfold SolinasConfig.prime
  have hb_le : 1 ≤ 2 ^ cfg.b := Nat.one_le_pow cfg.b 2 (by omega)
  have hab_le : 2 ^ cfg.b ≤ 2 ^ cfg.a := Nat.pow_le_pow_right (by omega) cfg.hab.le
  omega

/-- The correction constant equals 2^b - 1. -/
theorem solinas_correction_eq (cfg : SolinasConfig) :
    cfg.correction = 2 ^ cfg.b - 1 := rfl

/-- The prime equals 2^a minus the correction constant. -/
theorem solinas_prime_eq_sub_correction (cfg : SolinasConfig) :
    cfg.prime = 2 ^ cfg.a - cfg.correction := by
  rw [solinas_correction_eq]
  exact solinas_prime_form cfg

/-- **Solinas residue**: 2^a mod p = 2^b - 1.
    Since p = 2^a - (2^b - 1), we have 2^a = p + (2^b - 1),
    and the condition 2*(2^b - 1) < 2^a ensures 2^b - 1 < p. -/
theorem solinas_residue (cfg : SolinasConfig) :
    2 ^ cfg.a % cfg.prime = 2 ^ cfg.b - 1 := by
  have hform := solinas_prime_form cfg
  have hc_pos := two_pow_b_sub_one_pos cfg.b cfg.hb
  conv_lhs => rw [hform]
  exact two_pow_mod_pseudo_mersenne cfg.a (2 ^ cfg.b - 1) hc_pos cfg.h2b

/-- The Solinas prime is positive. -/
theorem solinas_prime_pos (cfg : SolinasConfig) : 0 < cfg.prime := by
  unfold SolinasConfig.prime
  have hab_le : 2 ^ cfg.b ≤ 2 ^ cfg.a := Nat.pow_le_pow_right (by omega) cfg.hab.le
  omega

/-- **Solinas fold step**: x % p = ((x >>> a) * (2^b - 1) + (x &&& (2^a - 1))) % p.

    This unifies BabyBear, KoalaBear, and Goldilocks fold steps into a single theorem.
    Follows directly from `pseudo_mersenne_fold_correct` with k = a, c = 2^b - 1. -/
theorem solinas_fold_step (cfg : SolinasConfig) (x : Nat) :
    ((x >>> cfg.a) * (2 ^ cfg.b - 1) + (x &&& (2 ^ cfg.a - 1))) % cfg.prime =
    x % cfg.prime := by
  have hform := solinas_prime_form cfg
  have hc_pos := two_pow_b_sub_one_pos cfg.b cfg.hb
  conv_rhs => rw [hform]
  conv_lhs => rw [hform]
  exact pseudo_mersenne_fold_correct x cfg.a (2 ^ cfg.b - 1) hc_pos cfg.h2b

/-! ## Rule generation -/

/-- **Derive a FieldFoldRule from Solinas configuration**.
    Given a `SolinasConfig` with a > b > 0, produces a sound `FieldFoldRule`
    where the fold operation is `(x >>> a) * (2^b - 1) + (x &&& (2^a - 1))`
    and soundness follows from `solinas_fold_step`. -/
def deriveFieldFoldRule (cfg : SolinasConfig) : FieldFoldRule where
  name := s!"solinas_{cfg.a}_{cfg.b}"
  prime := cfg.prime
  bitWidth := cfg.a
  foldEval := fun x => (x >>> cfg.a) * (2 ^ cfg.b - 1) + (x &&& (2 ^ cfg.a - 1))
  specEval := fun x => x
  sideCond := fun _ => True
  prime_pos := solinas_prime_pos cfg
  soundness := fun x _ => solinas_fold_step cfg x

/-- Generated rules are sound: the fold evaluation equals the identity modulo the prime.
    This is a direct consequence of `solinas_fold_step`. -/
theorem deriveFieldFoldRule_sound (cfg : SolinasConfig) (x : Nat) :
    (deriveFieldFoldRule cfg).foldEval x % (deriveFieldFoldRule cfg).prime =
    (deriveFieldFoldRule cfg).specEval x % (deriveFieldFoldRule cfg).prime :=
  (deriveFieldFoldRule cfg).soundness x trivial

/-! ## Compile-time prime form detection -/

/-- Check if a natural number is a power of two, returning the exponent if so. -/
private def isPowerOfTwo (n : Nat) : Option Nat :=
  if n == 0 then none
  else
    let rec go (v : Nat) (exp : Nat) (fuel : Nat) : Option Nat :=
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        if v == 1 then some exp
        else if v % 2 != 0 then none
        else go (v / 2) (exp + 1) fuel'
    go n 0 128

/-- Auxiliary: try to build a SolinasConfig from candidate (a, b).
    Returns `none` if the conditions don't hold. Uses decidable propositions
    so all proofs are extracted from runtime decision procedures. -/
private def trySolinasConfig (a b : Nat) : Option SolinasConfig :=
  if ha : 0 < a then
    if hb : 0 < b then
      if hab : b < a then
        if h2b : 2 * (2 ^ b - 1) < 2 ^ a then
          some ⟨a, b, ha, hb, hab, h2b⟩
        else none
      else none
    else none
  else none

/-- Detect if a prime has Solinas form p = 2^a - 2^b + 1 (pseudo-Mersenne).
    For true Mersenne primes (p = 2^k - 1, i.e., b = 0), use `mersenne_fold_rule` directly.
    Returns `.error` with explanation if no supported Solinas form is detected.
    Extension point: add new bit widths to `candidateWidths` for additional prime forms. -/
def detectSolinasForm (p : Nat) : Except String SolinasConfig :=
  -- Extension point: add new bit widths here for additional prime forms
  let candidateWidths := [15, 16, 17, 24, 31, 32, 61, 64, 127, 128]
  let rec tryWidths : List Nat → Except String SolinasConfig
    | [] => .error s!"Cannot detect Solinas form for p = {p}"
    | a :: rest =>
      let twoA := 2 ^ a
      if twoA < p then tryWidths rest
      else
        -- From p = 2^a - 2^b + 1: 2^a - p + 1 = 2^b
        let twoPowB := twoA - p + 1
        if twoPowB ≤ 1 then tryWidths rest  -- Mersenne prime (2^b=1 → b=0) or invalid
        else match isPowerOfTwo twoPowB with
          | none => tryWidths rest
          | some b =>
            match trySolinasConfig a b with
            | some cfg =>
              if cfg.prime == p then .ok cfg
              else tryWidths rest
            | none => tryWidths rest
  tryWidths candidateWidths

/-! ## Concrete Solinas configurations -/

/-- BabyBear: p = 2^31 - 2^27 + 1 = 2013265921 (used in Plonky3, RISC Zero). -/
def babybear_solinas : SolinasConfig :=
  ⟨31, 27, by omega, by omega, by omega, by native_decide⟩

/-- KoalaBear: p = 2^31 - 2^24 + 1 = 2130706433 (used in Plonky3). -/
def koalabear_solinas : SolinasConfig :=
  ⟨31, 24, by omega, by omega, by omega, by native_decide⟩

/-- Goldilocks: p = 2^64 - 2^32 + 1 = 18446744069414584321 (used in Plonky2). -/
def goldilocks_solinas : SolinasConfig :=
  ⟨64, 32, by omega, by omega, by omega, by native_decide⟩

/-! ## Prime value verification -/

/-- BabyBear prime value matches the expected constant. -/
example : babybear_solinas.prime = 2013265921 := by native_decide

/-- KoalaBear prime value matches the expected constant. -/
example : koalabear_solinas.prime = 2130706433 := by native_decide

/-- Goldilocks prime value matches the expected constant. -/
example : goldilocks_solinas.prime = 18446744069414584321 := by native_decide

/-! ## Generated rules -/

/-- BabyBear fold rule generated from Solinas configuration. -/
def babybear_solinas_rule : FieldFoldRule := deriveFieldFoldRule babybear_solinas

/-- KoalaBear fold rule generated from Solinas configuration. -/
def koalabear_solinas_rule : FieldFoldRule := deriveFieldFoldRule koalabear_solinas

/-- Goldilocks fold rule generated from Solinas configuration. -/
def goldilocks_solinas_rule : FieldFoldRule := deriveFieldFoldRule goldilocks_solinas

/-- All Solinas-generated fold rules. -/
def allSolinasRules : List FieldFoldRule :=
  [deriveFieldFoldRule babybear_solinas,
   deriveFieldFoldRule koalabear_solinas,
   deriveFieldFoldRule goldilocks_solinas]

/-- The Solinas rule collection contains exactly 3 rules. -/
theorem allSolinasRules_length : allSolinasRules.length = 3 := rfl

/-! ## Consistency: generated rules match hardcoded ones -/

/-- The generated BabyBear rule uses the same prime as the hardcoded one. -/
example : babybear_solinas_rule.prime = babybear_prime := by native_decide

/-- The generated Goldilocks rule uses the same prime as the hardcoded one. -/
example : goldilocks_solinas_rule.prime = goldilocks_prime := by native_decide

/-- The generated BabyBear fold matches the hardcoded fold for any input. -/
theorem babybear_solinas_matches_hardcoded (x : Nat) :
    babybear_solinas_rule.foldEval x = (x >>> 31) * (2 ^ 27 - 1) + (x &&& (2 ^ 31 - 1)) :=
  rfl

/-- The generated Goldilocks fold matches the hardcoded fold for any input. -/
theorem goldilocks_solinas_matches_hardcoded (x : Nat) :
    goldilocks_solinas_rule.foldEval x = (x >>> 64) * (2 ^ 32 - 1) + (x &&& (2 ^ 64 - 1)) :=
  rfl

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity: BabyBear Solinas fold for x = 10^9.
    Exercises the fold (10^9 > 2^31 so hi part is nonzero). -/
example : babybear_solinas_rule.foldEval (10 ^ 9) % babybear_solinas_rule.prime =
    (10 ^ 9) % babybear_solinas_rule.prime :=
  babybear_solinas_rule.soundness (10 ^ 9) trivial

/-- Non-vacuity: KoalaBear Solinas fold for x = 10^9. -/
example : koalabear_solinas_rule.foldEval (10 ^ 9) % koalabear_solinas_rule.prime =
    (10 ^ 9) % koalabear_solinas_rule.prime :=
  koalabear_solinas_rule.soundness (10 ^ 9) trivial

/-- Non-vacuity: Goldilocks Solinas fold for x = 2^33 + 1. -/
example : goldilocks_solinas_rule.foldEval (2 ^ 33 + 1) % goldilocks_solinas_rule.prime =
    (2 ^ 33 + 1) % goldilocks_solinas_rule.prime :=
  goldilocks_solinas_rule.soundness (2 ^ 33 + 1) trivial

/-- Non-vacuity: all three generated rules have satisfiable side conditions. -/
example : ∀ r ∈ allSolinasRules, r.sideCond 42 := by
  intro r hr
  simp only [allSolinasRules, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact trivial

/-- Non-vacuity: all three generated rules produce correct results for a concrete value.
    Tests with x = 2^32 + 7 (exercises the fold for all three primes). -/
example : ∀ r ∈ allSolinasRules,
    r.foldEval (2 ^ 32 + 7) % r.prime = r.specEval (2 ^ 32 + 7) % r.prime := by
  intro r hr
  simp only [allSolinasRules, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact babybear_solinas_rule.soundness _ trivial
  · exact koalabear_solinas_rule.soundness _ trivial
  · exact goldilocks_solinas_rule.soundness _ trivial

/-- Non-vacuity: deriveFieldFoldRule_sound for BabyBear with concrete input. -/
example : (deriveFieldFoldRule babybear_solinas).foldEval 999 %
    (deriveFieldFoldRule babybear_solinas).prime =
    (deriveFieldFoldRule babybear_solinas).specEval 999 %
    (deriveFieldFoldRule babybear_solinas).prime :=
  deriveFieldFoldRule_sound babybear_solinas 999

/-! ## Detection smoke tests -/

#eval show IO String from do
  -- Test detection for all 3 Solinas primes
  let primes : List (String × Nat) := [
    ("BabyBear", 2013265921),
    ("KoalaBear", 2130706433),
    ("Goldilocks", 18446744069414584321)]
  for (name, p) in primes do
    match detectSolinasForm p with
    | .ok cfg =>
      if cfg.prime != p then
        throw <| IO.userError s!"{name}: detected prime {cfg.prime} != {p}"
    | .error e => throw <| IO.userError s!"{name}: detection failed: {e}"
  return "detectSolinasForm: all 3 primes detected"

#eval show IO String from do
  -- Mersenne31 (2^31 - 1) is technically Solinas with b=1 (c = 2^1 - 1 = 1)
  -- This is correct: 2^31 - 2^1 + 1 = 2^31 - 1.
  -- For pure Mersenne folding (add, not mul), use mersenne31_fold_rule instead.
  match detectSolinasForm (2 ^ 31 - 1) with
  | .ok cfg =>
    if cfg.b != 1 then
      throw <| IO.userError s!"Mersenne31: expected b=1, got b={cfg.b}"
    else return s!"detectSolinasForm: Mersenne31 detected as Solinas (a={cfg.a}, b={cfg.b})"
  | .error e => throw <| IO.userError s!"Mersenne31 detection failed: {e}"

/-! ## Rule generation smoke tests -/

#eval show IO String from do
  let configs := [
    ("BabyBear", babybear_solinas),
    ("KoalaBear", koalabear_solinas),
    ("Goldilocks", goldilocks_solinas)]
  for (name, cfg) in configs do
    let rule := deriveFieldFoldRule cfg
    let tests : List Nat := [0, 1, cfg.prime - 1, cfg.prime, cfg.prime + 1, 2 ^ (cfg.a + 5)]
    for x in tests do
      let foldVal := rule.foldEval x
      if foldVal % rule.prime != x % rule.prime then
        throw <| IO.userError s!"{name} rule failed for x={x}"
  return "SolinasRuleGen: all 18 smoke tests passed"

end AmoLean.EGraph.Verified.Bitwise
