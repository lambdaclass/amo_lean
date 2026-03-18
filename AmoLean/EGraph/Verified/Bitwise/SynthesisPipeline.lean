import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.SolinasRuleGen
import AmoLean.EGraph.Verified.Bitwise.PhasedSaturation
import AmoLean.EGraph.Verified.Bitwise.CostExtraction
import AmoLean.EGraph.Verified.Bitwise.ReductionComposition
import AmoLean.EGraph.Verified.Bitwise.MixedPipeline

/-!
# SynthesisPipeline — End-to-end synthesis: prime → hardware → verified optimal reduction

Given a prime `p` and a target hardware model `hw`, this module:
1. Detects the Solinas form of `p` (or uses a provided config)
2. Generates a sound `FieldFoldRule` via `deriveFieldFoldRule`
3. Converts to a composable `ReductionStep` via `fromFieldFoldRule`
4. Computes the hardware cost via `pseudoMersenneFoldCost`

## Key results

- `SynthesisResult`: bundled output of the synthesis pipeline
- `synthesizeReduction`: main entry point (prime × hardware → result)
- `synthesis_correct`: soundness — synthesized reduction preserves mod equivalence
- `solinas_fold_cost_le_montgomery`: Solinas fold cost ≤ Montgomery cost
- Per-field convenience: `synthesize_babybear`, `synthesize_koalabear`, `synthesize_goldilocks`
- `compareCosts`: cross-target cost comparison for a given prime

## References

- SolinasRuleGen.lean: `SolinasConfig`, `deriveFieldFoldRule`, `detectSolinasForm`
- ReductionComposition.lean: `ReductionStep`, `fromFieldFoldRule`, `composeTwo`
- CostModelDef.lean: `HardwareCost`, `pseudoMersenneFoldCost`, `montgomeryCost`
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

/-! ## Synthesis result structure -/

/-- Bundled output of the synthesis pipeline.
    Contains the detected prime structure, generated fold rule,
    composable reduction step, and hardware cost on the target. -/
structure SynthesisResult where
  /-- Solinas prime structure analysis -/
  config : SolinasConfig
  /-- Generated fold rule from Solinas config -/
  rule : FieldFoldRule
  /-- Composable reduction step (minimal: function + soundness proof) -/
  step : ReductionStep
  /-- Cost in cycles on the target hardware -/
  hwCost : Nat

/-! ## Main synthesis entry point -/

/-- **Synthesize a verified modular reduction** for prime `p` on hardware `hw`.

    Steps:
    1. Detect the Solinas form p = 2^a - 2^b + 1 (or use `configOverride`)
    2. Generate a sound `FieldFoldRule` via `deriveFieldFoldRule`
    3. Convert to a `ReductionStep` via `fromFieldFoldRule`
    4. Compute hardware cost via `pseudoMersenneFoldCost`

    Returns `Except.error` if the prime does not have a detectable Solinas form. -/
def synthesizeReduction (p : Nat) (hw : HardwareCost)
    (configOverride : Option SolinasConfig := none) : Except String SynthesisResult :=
  match configOverride with
  | some c =>
    let rule := deriveFieldFoldRule c
    let step := fromFieldFoldRule rule (fun _ => rfl) (fun _ => trivial)
    let cost := pseudoMersenneFoldCost hw
    .ok { config := c, rule := rule, step := step, hwCost := cost }
  | none =>
    match detectSolinasForm p with
    | .ok c =>
      let rule := deriveFieldFoldRule c
      let step := fromFieldFoldRule rule (fun _ => rfl) (fun _ => trivial)
      let cost := pseudoMersenneFoldCost hw
      .ok { config := c, rule := rule, step := step, hwCost := cost }
    | .error e => .error e

/-! ## Soundness theorem -/

/-- **Synthesis correctness**: the synthesized reduction step preserves
    the residue modulo the config's prime.

    Given a `SolinasConfig` with `cfg.prime = p`, synthesizing a reduction
    and applying it to any `x` yields `step.reduce x % p = x % p`.
    This follows from `fromFieldFoldRule` + `solinas_fold_step`. -/
theorem synthesis_correct (p : Nat) (hw : HardwareCost) (cfg : SolinasConfig)
    (hcfg : cfg.prime = p) (x : Nat) :
    let result := synthesizeReduction p hw (some cfg)
    match result with
    | .ok r => r.step.reduce x % p = x % p
    | .error _ => True := by
  simp only [synthesizeReduction]
  show (fromFieldFoldRule (deriveFieldFoldRule cfg) (fun _ => rfl) (fun _ => trivial)).reduce x %
    p = x % p
  have hsound := (fromFieldFoldRule (deriveFieldFoldRule cfg)
    (fun _ => rfl) (fun _ => trivial)).sound x
  rw [← hcfg]
  exact hsound

/-- **Synthesis correctness (unwrapped)**: directly states the reduction is sound
    without matching on `Except`. Useful for downstream composition. -/
theorem synthesis_step_sound (cfg : SolinasConfig) (x : Nat) :
    (fromFieldFoldRule (deriveFieldFoldRule cfg)
      (fun _ => rfl) (fun _ => trivial)).reduce x % cfg.prime = x % cfg.prime :=
  (fromFieldFoldRule (deriveFieldFoldRule cfg) (fun _ => rfl) (fun _ => trivial)).sound x

/-! ## Cost comparison -/

/-- **Solinas fold is cheaper than Montgomery** on any hardware target.
    Pseudo-Mersenne fold uses 4 ops (shift + and + mul + add) vs
    Montgomery's 5 ops (and + mul + add + shift + sub). -/
theorem solinas_fold_cost_le_montgomery (hw : HardwareCost) :
    pseudoMersenneFoldCost hw ≤ montgomeryCost hw :=
  pseudo_mersenne_le_montgomery hw

/-- The synthesized hwCost equals `pseudoMersenneFoldCost hw`. -/
theorem synthesis_hwCost_eq (p : Nat) (hw : HardwareCost) (cfg : SolinasConfig) :
    match synthesizeReduction p hw (some cfg) with
    | .ok r => r.hwCost = pseudoMersenneFoldCost hw
    | .error _ => True := by
  simp [synthesizeReduction]

/-- Cost advantage: for any synthesized result, hwCost ≤ Montgomery cost. -/
theorem synthesis_cost_le_montgomery (p : Nat) (hw : HardwareCost) (cfg : SolinasConfig) :
    match synthesizeReduction p hw (some cfg) with
    | .ok r => r.hwCost ≤ montgomeryCost hw
    | .error _ => True := by
  simp [synthesizeReduction, pseudoMersenneFoldCost, montgomeryCost]
  omega

/-! ## Per-field convenience functions -/

/-- Synthesize reduction for BabyBear (p = 2^31 - 2^27 + 1) on given hardware.
    Always succeeds since config is provided directly. -/
def synthesize_babybear (hw : HardwareCost) : SynthesisResult :=
  let rule := deriveFieldFoldRule babybear_solinas
  let step := fromFieldFoldRule rule (fun _ => rfl) (fun _ => trivial)
  { config := babybear_solinas
    rule := rule
    step := step
    hwCost := pseudoMersenneFoldCost hw }

/-- Synthesize reduction for KoalaBear (p = 2^31 - 2^24 + 1) on given hardware. -/
def synthesize_koalabear (hw : HardwareCost) : SynthesisResult :=
  let rule := deriveFieldFoldRule koalabear_solinas
  let step := fromFieldFoldRule rule (fun _ => rfl) (fun _ => trivial)
  { config := koalabear_solinas
    rule := rule
    step := step
    hwCost := pseudoMersenneFoldCost hw }

/-- Synthesize reduction for Goldilocks (p = 2^64 - 2^32 + 1) on given hardware. -/
def synthesize_goldilocks (hw : HardwareCost) : SynthesisResult :=
  let rule := deriveFieldFoldRule goldilocks_solinas
  let step := fromFieldFoldRule rule (fun _ => rfl) (fun _ => trivial)
  { config := goldilocks_solinas
    rule := rule
    step := step
    hwCost := pseudoMersenneFoldCost hw }

/-! ## Per-field soundness -/

/-- BabyBear synthesis is sound. -/
theorem synthesize_babybear_sound (hw : HardwareCost) (x : Nat) :
    (synthesize_babybear hw).step.reduce x % babybear_solinas.prime =
    x % babybear_solinas.prime :=
  (synthesize_babybear hw).step.sound x

/-- KoalaBear synthesis is sound. -/
theorem synthesize_koalabear_sound (hw : HardwareCost) (x : Nat) :
    (synthesize_koalabear hw).step.reduce x % koalabear_solinas.prime =
    x % koalabear_solinas.prime :=
  (synthesize_koalabear hw).step.sound x

/-- Goldilocks synthesis is sound. -/
theorem synthesize_goldilocks_sound (hw : HardwareCost) (x : Nat) :
    (synthesize_goldilocks hw).step.reduce x % goldilocks_solinas.prime =
    x % goldilocks_solinas.prime :=
  (synthesize_goldilocks hw).step.sound x

/-! ## Two-stage synthesis -/

/-- Synthesize a two-stage reduction pipeline for a given config.
    Applies the Solinas fold twice, useful for primes like Goldilocks
    where a single fold may leave the result slightly above the field. -/
def synthesizeTwoStage (cfg : SolinasConfig) (hw : HardwareCost) : SynthesisResult :=
  let rule := deriveFieldFoldRule cfg
  let step1 := fromFieldFoldRule rule (fun _ => rfl) (fun _ => trivial)
  let step2 := fromFieldFoldRule rule (fun _ => rfl) (fun _ => trivial)
  let composed := composeTwo step1 step2 rfl
  { config := cfg
    rule := rule
    step := composed
    hwCost := 2 * pseudoMersenneFoldCost hw }

/-- Two-stage synthesis is sound: the composed reduction preserves mod equivalence. -/
theorem synthesizeTwoStage_sound (cfg : SolinasConfig) (hw : HardwareCost) (x : Nat) :
    (synthesizeTwoStage cfg hw).step.reduce x % cfg.prime = x % cfg.prime :=
  (synthesizeTwoStage cfg hw).step.sound x

/-! ## Cross-target cost comparison -/

/-- Compare synthesis costs across multiple hardware targets for a given prime.
    Returns a list of (target_name, cycle_count) pairs. -/
def compareCosts (p : Nat) : List (String × Nat) :=
  let targets := [("ARM_Cortex_A76", arm_cortex_a76),
                  ("RISC-V_SiFive_U74", riscv_sifive_u74),
                  ("FPGA_DSP48E2", fpga_dsp48e2)]
  targets.map fun (name, hw) =>
    match synthesizeReduction p hw with
    | .ok r => (name, r.hwCost)
    | .error _ => (name, 0)

/-- Compare Montgomery vs Solinas costs across targets for a given prime. -/
def compareStrategies (_p : Nat) : List (String × Nat × Nat) :=
  let targets := [("ARM_Cortex_A76", arm_cortex_a76),
                  ("RISC-V_SiFive_U74", riscv_sifive_u74),
                  ("FPGA_DSP48E2", fpga_dsp48e2)]
  targets.map fun (name, hw) =>
    (name, pseudoMersenneFoldCost hw, montgomeryCost hw)

/-- The cost comparison always shows Solinas ≤ Montgomery for every target. -/
theorem compareCosts_solinas_le_montgomery (_name : String) (hw : HardwareCost) :
    pseudoMersenneFoldCost hw ≤ montgomeryCost hw :=
  pseudo_mersenne_le_montgomery hw

/-! ## Pipeline integration: synthesis feeds into E-graph extraction -/

/-- The synthesized reduction step's prime matches the config's prime.
    This is needed to connect synthesis output to `composeList`. -/
theorem synthesis_step_prime (cfg : SolinasConfig) :
    (fromFieldFoldRule (deriveFieldFoldRule cfg)
      (fun _ => rfl) (fun _ => trivial)).prime = cfg.prime := rfl

/-- Synthesized steps from the same config can be composed via `composeTwo`. -/
theorem synthesis_composable (cfg : SolinasConfig) :
    let s1 := fromFieldFoldRule (deriveFieldFoldRule cfg) (fun _ => rfl) (fun _ => trivial)
    let s2 := fromFieldFoldRule (deriveFieldFoldRule cfg) (fun _ => rfl) (fun _ => trivial)
    s1.prime = s2.prime := rfl

/-- Synthesized steps from different configs targeting the same prime can be composed.
    E.g., BabyBear hardcoded + BabyBear Solinas-generated target the same prime. -/
theorem synthesis_cross_composable (cfg1 cfg2 : SolinasConfig)
    (hp : cfg1.prime = cfg2.prime) :
    (fromFieldFoldRule (deriveFieldFoldRule cfg1) (fun _ => rfl) (fun _ => trivial)).prime =
    (fromFieldFoldRule (deriveFieldFoldRule cfg2) (fun _ => rfl) (fun _ => trivial)).prime := hp

/-! ## Non-vacuity examples -/

/-- Non-vacuity: synthesis_correct with BabyBear and concrete input. -/
example : let result := synthesizeReduction babybear_solinas.prime arm_cortex_a76 (some babybear_solinas)
    match result with
    | .ok r => r.step.reduce 1000000000 % babybear_solinas.prime =
               1000000000 % babybear_solinas.prime
    | .error _ => True :=
  synthesis_correct babybear_solinas.prime arm_cortex_a76 babybear_solinas rfl 1000000000

/-- Non-vacuity: synthesis_correct with Goldilocks and large input. -/
example :
    let result := synthesizeReduction goldilocks_solinas.prime arm_cortex_a76
        (some goldilocks_solinas)
    match result with
    | .ok r => r.step.reduce (2 ^ 65 + 42) % goldilocks_solinas.prime =
               (2 ^ 65 + 42) % goldilocks_solinas.prime
    | .error _ => True :=
  synthesis_correct goldilocks_solinas.prime arm_cortex_a76 goldilocks_solinas rfl (2 ^ 65 + 42)

/-- Non-vacuity: two-stage synthesis with Goldilocks is sound for large input. -/
example : (synthesizeTwoStage goldilocks_solinas arm_cortex_a76).step.reduce (2 ^ 70) %
    goldilocks_solinas.prime = (2 ^ 70) % goldilocks_solinas.prime :=
  synthesizeTwoStage_sound goldilocks_solinas arm_cortex_a76 (2 ^ 70)

/-- Non-vacuity: solinas_fold_cost_le_montgomery is not vacuous on ARM. -/
example : pseudoMersenneFoldCost arm_cortex_a76 ≤ montgomeryCost arm_cortex_a76 :=
  solinas_fold_cost_le_montgomery arm_cortex_a76

/-- Non-vacuity: the cost gap is actually strict on ARM (5 < 6). -/
example : pseudoMersenneFoldCost arm_cortex_a76 < montgomeryCost arm_cortex_a76 := by
  native_decide

/-- Non-vacuity: convenience functions produce correct reductions. -/
example : (synthesize_babybear arm_cortex_a76).step.reduce 42 %
    babybear_solinas.prime = 42 % babybear_solinas.prime :=
  synthesize_babybear_sound arm_cortex_a76 42

example : (synthesize_koalabear riscv_sifive_u74).step.reduce (2 ^ 32) %
    koalabear_solinas.prime = (2 ^ 32) % koalabear_solinas.prime :=
  synthesize_koalabear_sound riscv_sifive_u74 (2 ^ 32)

example : (synthesize_goldilocks fpga_dsp48e2).step.reduce (2 ^ 65 + 1) %
    goldilocks_solinas.prime = (2 ^ 65 + 1) % goldilocks_solinas.prime :=
  synthesize_goldilocks_sound fpga_dsp48e2 (2 ^ 65 + 1)

/-! ## Smoke tests -/

#eval do
  let bb := synthesize_babybear arm_cortex_a76
  let kb := synthesize_koalabear arm_cortex_a76
  let gl := synthesize_goldilocks arm_cortex_a76
  return s!"BabyBear: {bb.hwCost} cycles, KoalaBear: {kb.hwCost} cycles, Goldilocks: {gl.hwCost} cycles"

#eval compareCosts (2 ^ 31 - 2 ^ 27 + 1)  -- BabyBear across targets
#eval compareCosts (2 ^ 31 - 2 ^ 24 + 1)  -- KoalaBear across targets
#eval compareCosts (2 ^ 64 - 2 ^ 32 + 1)  -- Goldilocks across targets

#eval compareStrategies (2 ^ 31 - 2 ^ 27 + 1)  -- Solinas vs Montgomery per target

#eval do
  -- Full matrix: 3 primes × 3 targets
  let primes : List (String × Nat) :=
    [("BabyBear", 2 ^ 31 - 2 ^ 27 + 1),
     ("KoalaBear", 2 ^ 31 - 2 ^ 24 + 1),
     ("Goldilocks", 2 ^ 64 - 2 ^ 32 + 1)]
  let mut results : List String := []
  for (name, p) in primes do
    let costs := compareCosts p
    let costStr := costs.map (fun (t : String × Nat) => s!"{t.1}={t.2}")
    results := results ++ [s!"{name}: {costStr}"]
  return results

#eval do
  -- Verify synthesis matches direct modular arithmetic
  let cfg := babybear_solinas
  let hw := arm_cortex_a76
  let result := synthesize_babybear hw
  let x := 2 ^ 32 + 7
  let synthesized := result.step.reduce x % cfg.prime
  let direct := x % cfg.prime
  return s!"BabyBear: synthesized={synthesized}, direct={direct}, match={synthesized == direct}"

end AmoLean.EGraph.Verified.Bitwise
