/-
  AMO-Lean: Domain Bridge (N13.2)
  Fase 13 — Connecting operational FRIParams with verified FRIEvalDomain

  This module bridges:
  - Operational: FRIParams (FRI/Basic.lean) — computation parameters
  - Verified: FRIEvalDomain (FRI/Verified/FRISemanticSpec.lean) — algebraic domain

  Key results:
  1. `ValidFRIParams`: predicate for bridge-compatible parameters
  2. `friParamsToDomain`: construct FRIEvalDomain from FRIParams + primitive root
  3. `DomainParams`: extractable parameters from FRIEvalDomain
  4. `domainBridge_size`: domain size = params.maxDegree * params.blowupFactor
  5. `domainBridge_elements_distinct`: domain elements are injective
  6. `domainBridge_supports_folding`: domain supports squared folding
  7. `domainBridge_initial_consistent`: compatible with FRIRoundState.initial

  Architecture:
  - First file to import BOTH FRI/Basic.lean (operational) and
    FRI/Verified/FRISemanticSpec.lean (verified), creating the bridge.
  - All theorems proven with 0 sorry, 0 new axioms.
-/

import AmoLean.FRI.Basic
import AmoLean.FRI.Verified.FRISemanticSpec

namespace AmoLean.FRI.Verified

/-! ## Part 1: Valid FRI Parameters

A `ValidFRIParams` predicate captures the preconditions under which
operational `FRIParams` can produce a valid `FRIEvalDomain`. -/

/-- The initial domain size of FRI parameters (at round 0) -/
def initialDomainSize (params : FRIParams) : Nat :=
  params.maxDegree * params.blowupFactor

/-- Predicate for FRI parameters that can produce a valid evaluation domain.
    This captures the preconditions for the domain bridge to be total. -/
structure ValidFRIParams (params : FRIParams) : Prop where
  /-- Initial domain size is a power of 2 -/
  size_pow2 : ∃ k : Nat, initialDomainSize params = 2 ^ k
  /-- Initial domain size is at least 2 -/
  size_ge_two : 2 ≤ initialDomainSize params
  /-- Max degree is positive -/
  maxDeg_pos : 0 < params.maxDegree
  /-- Blowup factor is positive -/
  blowup_pos : 0 < params.blowupFactor

/-- The initial domain size equals domainSize at round 0 -/
theorem initialDomainSize_eq_domainSize_zero (params : FRIParams) :
    initialDomainSize params = params.domainSize 0 := by
  simp only [initialDomainSize, FRIParams.domainSize, pow_zero, Nat.div_one]

/-- testFRIParams are valid (domain size = 64 * 2 = 128 = 2^7) -/
theorem testFRIParams_valid : ValidFRIParams testFRIParams := by
  constructor
  · exact ⟨7, by norm_num [initialDomainSize, testFRIParams]⟩
  · simp only [initialDomainSize, testFRIParams]; omega
  · simp only [testFRIParams]; omega
  · simp only [testFRIParams]; omega

/-! ## Part 2: Domain Bridge (FRIParams → FRIEvalDomain)

The core bridge function: given valid FRI parameters and a primitive root
of unity, construct the verified FRIEvalDomain. -/

/-- Construct a verified FRIEvalDomain from operational FRIParams.

    Given:
    - `params`: operational FRI parameters
    - `ω`: a field element serving as primitive root of unity
    - Proofs that ω is primitive root of the correct order

    Returns: a `FRIEvalDomain F` suitable for verified FRI operations.

    This is THE bridge function from operational to verified worlds. -/
noncomputable def friParamsToDomain {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    FRIEvalDomain F :=
  { size := initialDomainSize params
    generator := ω
    isPrimRoot := h_prim
    size_pow2 := h_valid.size_pow2
    size_ge_two := h_valid.size_ge_two }

/-- The domain size matches the operational parameter's initial domain size -/
theorem domainBridge_size {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (friParamsToDomain params ω h_valid h_prim).size = initialDomainSize params :=
  rfl

/-- The domain generator is the provided primitive root -/
theorem domainBridge_generator {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (friParamsToDomain params ω h_valid h_prim).generator = ω :=
  rfl

/-- The domain elements are distinct (injective) -/
theorem domainBridge_elements_distinct {F : Type*} [CommRing F] [IsDomain F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    Function.Injective (friParamsToDomain params ω h_valid h_prim).elements :=
  (friParamsToDomain params ω h_valid h_prim).elements_injective

/-- The domain generator raised to domain size equals 1 -/
theorem domainBridge_generator_pow_size {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (friParamsToDomain params ω h_valid h_prim).generator ^
    (friParamsToDomain params ω h_valid h_prim).size = 1 :=
  (friParamsToDomain params ω h_valid h_prim).generator_pow_size

/-! ## Part 3: DomainParams (FRIEvalDomain → extractable parameters)

Since FRIEvalDomain does not store operational fields (numQueries,
foldingFactor, FieldConfig), we define a minimal struct capturing
the domain-relevant parameters that can be extracted. -/

/-- Minimal domain parameters extractable from an FRIEvalDomain -/
structure DomainParams where
  /-- Domain size -/
  domainSize : Nat
  /-- Domain size is a power of 2 -/
  domainSize_pow2 : ∃ k : Nat, domainSize = 2 ^ k
  /-- Domain size is at least 2 -/
  domainSize_ge2 : 2 ≤ domainSize

/-- Extract domain parameters from a verified FRIEvalDomain -/
def extractDomainParams {F : Type*} [CommRing F]
    (D : FRIEvalDomain F) : DomainParams :=
  { domainSize := D.size
    domainSize_pow2 := D.size_pow2
    domainSize_ge2 := D.size_ge_two }

/-- Extract domain parameters from valid FRIParams -/
def extractParamsDomainParams (params : FRIParams)
    (h_valid : ValidFRIParams params) : DomainParams :=
  { domainSize := initialDomainSize params
    domainSize_pow2 := h_valid.size_pow2
    domainSize_ge2 := h_valid.size_ge_two }

/-- Roundtrip: extracting domain params from a bridge-produced domain
    recovers the same domain size as extracting from the original params -/
theorem domainBridge_roundtrip {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (extractDomainParams (friParamsToDomain params ω h_valid h_prim)).domainSize =
    (extractParamsDomainParams params h_valid).domainSize :=
  rfl

/-- The roundtrip preserves the domain size value -/
theorem domainBridge_roundtrip_size {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (extractDomainParams (friParamsToDomain params ω h_valid h_prim)).domainSize =
    initialDomainSize params :=
  rfl

/-! ## Part 4: Folding Support

The domain bridge produces domains that support the `squaredDomain`
operation, which is essential for FRI's folding mechanism. -/

/-- The domain produced by the bridge supports folding when size = 2 * k -/
theorem domainBridge_supports_folding {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params))
    (k : Nat) (hk : initialDomainSize params = 2 * k) (hk_ge : 2 ≤ k) :
    let D := friParamsToDomain params ω h_valid h_prim
    (D.squaredDomain k (by exact hk) hk_ge).size = k := by
  simp only [FRIEvalDomain.squaredDomain]

/-- The folded domain's generator is the square of the original generator -/
theorem domainBridge_folded_generator {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params))
    (k : Nat) (hk : initialDomainSize params = 2 * k) (hk_ge : 2 ≤ k) :
    let D := friParamsToDomain params ω h_valid h_prim
    (D.squaredDomain k (by exact hk) hk_ge).generator = ω ^ 2 := by
  simp only [FRIEvalDomain.squaredDomain, friParamsToDomain]

/-! ## Part 5: Round State Consistency

The domain bridge is consistent with `FRIRoundState.initial`, ensuring
the verified FRI protocol can start from bridged parameters. -/

/-- The initial round state from a bridged domain has correct round number -/
theorem domainBridge_initial_round {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (FRIRoundState.initial (friParamsToDomain params ω h_valid h_prim)
      params.maxDegree).round = 0 :=
  rfl

/-- The initial round state uses the bridged domain -/
theorem domainBridge_initial_domain {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (FRIRoundState.initial (friParamsToDomain params ω h_valid h_prim)
      params.maxDegree).domain =
    friParamsToDomain params ω h_valid h_prim :=
  rfl

/-- The initial round state has the correct degree bound from params -/
theorem domainBridge_initial_degreeBound {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (FRIRoundState.initial (friParamsToDomain params ω h_valid h_prim)
      params.maxDegree).degreeBound = params.maxDegree :=
  rfl

/-- Full initial state consistency: all fields match expectations -/
theorem domainBridge_initial_consistent {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    let D := friParamsToDomain params ω h_valid h_prim
    let st := FRIRoundState.initial D params.maxDegree
    st.round = 0 ∧ st.domain = D ∧ st.degreeBound = params.maxDegree :=
  ⟨rfl, rfl, rfl⟩

/-! ## Part 6: Domain Size Properties

Properties about the relationship between operational domain size
calculations and the verified domain's size. -/

/-- Domain size equals maxDegree * blowupFactor (unfolded) -/
theorem domainBridge_size_eq_mul {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (friParamsToDomain params ω h_valid h_prim).size =
    params.maxDegree * params.blowupFactor :=
  rfl

/-- Domain size equals domainSize at round 0 -/
theorem domainBridge_size_eq_domainSize_zero {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    (friParamsToDomain params ω h_valid h_prim).size = params.domainSize 0 := by
  simp only [friParamsToDomain, FRIParams.domainSize, pow_zero, Nat.div_one,
             initialDomainSize]

/-- maxDegree is strictly less than the domain size (blowup guarantees this) -/
theorem domainBridge_degree_lt_size {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params))
    (h_blowup : 2 ≤ params.blowupFactor) :
    params.maxDegree < (friParamsToDomain params ω h_valid h_prim).size := by
  simp only [friParamsToDomain, initialDomainSize]
  have := h_valid.maxDeg_pos
  nlinarith

/-- The degree bound fits in the domain (required for FRI soundness) -/
theorem domainBridge_degreeBound_le_half
    (params : FRIParams)
    (h_blowup : params.blowupFactor = 2)
    (k : Nat) (hk : initialDomainSize params = 2 * k) :
    params.maxDegree ≤ k := by
  simp only [initialDomainSize, h_blowup] at hk
  omega

/-! ## Part 7: Bridge Composition Helpers

Utilities for composing the domain bridge with other Fase 13 bridges. -/

/-- Package: a domain bridge result bundles the domain with its provenance -/
structure DomainBridgeResult (F : Type*) [CommRing F] where
  /-- The source operational parameters -/
  params : FRIParams
  /-- Validity proof -/
  valid : ValidFRIParams params
  /-- The target verified domain -/
  domain : FRIEvalDomain F
  /-- The domain was produced by the bridge -/
  bridge_eq : domain.size = initialDomainSize params

/-- Construct a DomainBridgeResult from valid params and a primitive root -/
noncomputable def mkDomainBridgeResult {F : Type*} [CommRing F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params)) :
    DomainBridgeResult F :=
  { params := params
    valid := h_valid
    domain := friParamsToDomain params ω h_valid h_prim
    bridge_eq := rfl }

/-- The bridge result's domain size matches the source params -/
theorem DomainBridgeResult.size_eq {F : Type*} [CommRing F]
    (br : DomainBridgeResult F) :
    br.domain.size = br.params.maxDegree * br.params.blowupFactor :=
  br.bridge_eq

/-! ## Part 8: Module Index

DomainBridge provides:

1. `ValidFRIParams`: predicate for bridge-compatible operational parameters
2. `initialDomainSize`: operational domain size at round 0
3. `friParamsToDomain`: THE bridge function (FRIParams → FRIEvalDomain)
4. `DomainParams` + `extractDomainParams`: reverse direction (lossy)
5. `domainBridge_roundtrip`: roundtrip property on domain size
6. `domainBridge_size` / `_eq_mul` / `_eq_domainSize_zero`: size properties
7. `domainBridge_elements_distinct`: element injectivity
8. `domainBridge_supports_folding`: squared domain support
9. `domainBridge_initial_consistent`: FRIRoundState.initial compatibility
10. `DomainBridgeResult`: proof-carrying bridge output for downstream use

Upstream:
- FRI/Basic.lean: FRIParams, FRIParams.domainSize
- FRI/Verified/FRISemanticSpec.lean: FRIEvalDomain, FRIRoundState

Downstream:
- FoldBridge.lean (N13.4): uses DomainBridgeResult for evaluation domains
- BridgeIntegration.lean (N13.6): integration theorem
-/

end AmoLean.FRI.Verified
