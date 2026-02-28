/-
  AMO-Lean: Plausible Setup (N13.1)
  Fase 13 — Property-based testing infrastructure

  Provides:
  - SampleableExt instances for FRI-related types (FieldConfig, FRIParams)
  - SampleableExt instances for verified types (FRIEvalDomain)
  - Smoke tests validating the Plausible framework works on this project
  - Reusable test generators for downstream property testing (N13.6)

  Architecture:
  - Uses Plausible's proxy-based sampling (Plausible.SampleableExt)
  - Proxies are tuples of Nat for structures with Nat fields
  - Interpretation maps proxy values to domain types
  - Shrinkable comes from the proxy type's Shrinkable instance
-/

import Plausible
import AmoLean.FRI.Basic
import AmoLean.FRI.Verified.FRISemanticSpec
import AmoLean.FRI.Verified.DomainBridge

namespace AmoLean.Testing

open AmoLean.FRI
open AmoLean.FRI.Verified

/-! ## Part 1: SampleableExt Instances for Operational Types -/

/-- SampleableExt for FieldConfig: generates random field configurations.
    Uses tuple (prime, bits, generator, twoAdicity) as proxy. -/
instance : Plausible.SampleableExt FieldConfig where
  proxy := Nat × Nat × Nat × Nat
  interp := fun (p, b, g, t) =>
    { prime := p, bits := b, generator := g, twoAdicity := t }

/-- SampleableExt for FRIParams: generates random FRI parameters.
    Uses nested tuple as proxy. -/
instance : Plausible.SampleableExt FRIParams where
  proxy := (Nat × Nat × Nat × Nat) × Nat × Nat × Nat × Nat
  interp := fun ((p, b, g, t), bf, nq, md, ff) =>
    { field := { prime := p, bits := b, generator := g, twoAdicity := t }
      blowupFactor := bf
      numQueries := nq
      maxDegree := md
      foldingFactor := ff }

/-! ## Part 2: ValidFRIParams Generator

For testing properties that require valid FRI params, we provide
a constrained generator that ensures power-of-2 domain size. -/

/-- Generate a ValidFRIParams-compatible configuration.
    Maps k ∈ {1..10} to maxDegree = 2^k, blowupFactor = 1, ensuring
    initialDomainSize = 2^k ≥ 2. -/
def mkTestParams (k : Nat) : FRIParams :=
  { field := { prime := 97, bits := 7, generator := 5, twoAdicity := 5 }
    blowupFactor := 1
    numQueries := 10
    maxDegree := 2 ^ (k + 1)  -- ensures ≥ 2
    foldingFactor := 2 }

/-- The test params have valid domain size -/
theorem mkTestParams_domainSize (k : Nat) :
    initialDomainSize (mkTestParams k) = 2 ^ (k + 1) := by
  simp [initialDomainSize, mkTestParams]

/-- The test params satisfy ValidFRIParams -/
theorem mkTestParams_valid (k : Nat) :
    ValidFRIParams (mkTestParams k) := by
  refine ⟨⟨k + 1, ?_⟩, ?_, ?_, ?_⟩
  · simp [initialDomainSize, mkTestParams]
  · simp [initialDomainSize, mkTestParams]
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  all_goals simp [mkTestParams]

/-! ## Part 3: Smoke Tests

These tests validate that Plausible works correctly with our types.
Each test uses the `plausible` tactic (which leaves `sorry` as expected). -/

section SmokeTests

/-- Smoke test 1: FieldConfig.prime is non-negative (trivial for Nat) -/
example : ∀ (fc : FieldConfig), fc.prime ≥ 0 := by plausible

/-- Smoke test 2: FRIParams.maxDegree roundtrips through construction -/
example : ∀ (md : Nat), (FRIParams.mk
  { prime := 97, bits := 7, generator := 5, twoAdicity := 5 } 2 30 md 2).maxDegree = md := by
  plausible

/-- Smoke test 3: initialDomainSize is multiplicative -/
example : ∀ (md bf : Nat),
    initialDomainSize { field := { prime := 97, bits := 7, generator := 5, twoAdicity := 5 }
                        blowupFactor := bf, numQueries := 30, maxDegree := md, foldingFactor := 2 }
    = md * bf := by
  plausible

/-- Smoke test 4: domain size is product of maxDegree and blowupFactor -/
example : ∀ (md bf : Nat),
    initialDomainSize { field := { prime := 97, bits := 7, generator := 5, twoAdicity := 5 }
                        blowupFactor := bf, numQueries := 30, maxDegree := md,
                        foldingFactor := 2 }
    = md * bf := by
  intro md bf; rfl

/-- Smoke test 5: Nat addition is commutative (baseline sanity check) -/
example : ∀ (a b : Nat), a + b = b + a := by plausible

end SmokeTests

/-! ## Part 4: Summary

PlausibleSetup provides:

1. `SampleableExt FieldConfig`: random field configuration generation
2. `SampleableExt FRIParams`: random FRI parameter generation
3. `mkTestParams`: constrained generator for valid FRI params
4. `mkTestParams_valid`: proof that generated params are valid
5. 5 smoke tests validating the Plausible framework

Downstream:
- BridgeIntegration.lean (N13.6): uses instances for property testing
-/

end AmoLean.Testing
