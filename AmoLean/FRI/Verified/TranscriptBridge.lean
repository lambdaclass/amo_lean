/-
  AMO-Lean: Transcript Bridge (N13.3)
  Fase 13 — Connecting operational TranscriptState with verified FormalTranscript

  This module bridges:
  - Operational: TranscriptState (FRI/Transcript.lean) — FRIField + CryptoHash
  - Verified: FormalTranscript (FRI/Verified/TranscriptSpec.lean) — pure algebraic

  The bridge is a natural projection: TranscriptState has extra fields
  (domainStack, round) that are dropped when projecting to FormalTranscript.
  The core data (absorbed, squeezeCount) is shared.

  Architecture:
  - toFormalTranscript: projection (TranscriptState → FormalTranscript)
  - fromFormalTranscript: embedding with defaults
  - Commutativity: absorb/squeeze commute with the bridge
  - Determinism: bridge preserves transcript determinism
-/

import AmoLean.FRI.Transcript
import AmoLean.FRI.Verified.TranscriptSpec

namespace AmoLean.FRI.Verified

open AmoLean.FRI.Transcript (TranscriptState TranscriptResult DomainTag
  absorb absorbMany squeeze)
open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)

/-! ## Part 1: Bridge Functions -/

/-- Project operational TranscriptState to verified FormalTranscript.
    Drops domainStack and round (implementation details). -/
def toFormalTranscript {F : Type} (s : TranscriptState F) : FormalTranscript F :=
  { absorbed := s.absorbed
    squeezeCount := s.squeezeCount }

/-- Embed verified FormalTranscript into operational TranscriptState.
    Uses default values for domainStack and round. -/
def fromFormalTranscript {F : Type} (t : FormalTranscript F) : TranscriptState F :=
  { absorbed := t.absorbed
    squeezeCount := t.squeezeCount
    domainStack := []
    round := 0 }

/-- Bridge roundtrip: toFormal ∘ fromFormal = id -/
theorem bridge_roundtrip {F : Type} (t : FormalTranscript F) :
    toFormalTranscript (fromFormalTranscript t) = t := by
  simp only [toFormalTranscript, fromFormalTranscript]

/-- Projection preserves absorbed data -/
theorem toFormalTranscript_absorbed {F : Type} (s : TranscriptState F) :
    (toFormalTranscript s).absorbed = s.absorbed :=
  rfl

/-- Projection preserves squeeze count -/
theorem toFormalTranscript_squeezeCount {F : Type} (s : TranscriptState F) :
    (toFormalTranscript s).squeezeCount = s.squeezeCount :=
  rfl

/-! ## Part 2: Absorb Commutativity

The key bridge theorem: absorbing data commutes with the projection. -/

/-- **Absorb Bridge**: absorbing a single element commutes with toFormalTranscript.

    toFormalTranscript (absorb s elem) = (toFormalTranscript s).absorb elem -/
theorem transcriptBridge_absorb {F : Type}
    (s : TranscriptState F) (elem : F) :
    toFormalTranscript (absorb s elem) =
    (toFormalTranscript s).absorb elem := by
  simp only [toFormalTranscript, absorb, FormalTranscript.absorb]

/-- **AbsorbMany Bridge**: absorbing multiple elements commutes with toFormalTranscript. -/
theorem transcriptBridge_absorbMany {F : Type}
    (s : TranscriptState F) (elems : List F) :
    toFormalTranscript (absorbMany s elems) =
    (toFormalTranscript s).absorbMany elems := by
  simp only [toFormalTranscript, absorbMany, FormalTranscript.absorbMany]

/-- Absorb chain: sequential absorbs commute with the bridge -/
theorem transcriptBridge_absorb_chain {F : Type}
    (s : TranscriptState F) (a b : F) :
    toFormalTranscript (absorb (absorb s a) b) =
    ((toFormalTranscript s).absorb a).absorb b := by
  rw [transcriptBridge_absorb, transcriptBridge_absorb]

/-! ## Part 3: Squeeze Commutativity

Squeeze commutativity under the oracle bridge:
operational CryptoHash.squeeze corresponds to the formal oracle parameter. -/

/-- **Squeeze Bridge**: squeezing a challenge commutes with toFormalTranscript,
    when using CryptoHash.squeeze as the oracle.

    This is THE main squeeze bridge theorem. -/
theorem transcriptBridge_squeeze {F : Type} [FRIField F] [CryptoHash F]
    (s : TranscriptState F) :
    let opResult := squeeze s
    let (formalState, formalChallenge) :=
      (toFormalTranscript s).squeeze CryptoHash.squeeze
    toFormalTranscript opResult.state = formalState ∧
    opResult.output = formalChallenge := by
  simp only [squeeze, toFormalTranscript, FormalTranscript.squeeze]
  exact ⟨trivial, trivial⟩

/-- Squeeze bridge: state component -/
theorem transcriptBridge_squeeze_state {F : Type} [FRIField F] [CryptoHash F]
    (s : TranscriptState F) :
    toFormalTranscript (squeeze s).state =
    ((toFormalTranscript s).squeeze CryptoHash.squeeze).1 := by
  simp only [squeeze, toFormalTranscript, FormalTranscript.squeeze]

/-- Squeeze bridge: challenge component -/
theorem transcriptBridge_squeeze_challenge {F : Type} [FRIField F] [CryptoHash F]
    (s : TranscriptState F) :
    (squeeze s).output =
    ((toFormalTranscript s).squeeze CryptoHash.squeeze).2 := by
  simp only [squeeze, toFormalTranscript, FormalTranscript.squeeze]

/-! ## Part 4: Determinism Preservation

The bridge preserves the determinism property: same inputs → same outputs. -/

/-- **Determinism Bridge**: if two operational states project to the same
    formal state, their squeeze outputs agree.

    This follows from the fact that squeeze only depends on absorbed + squeezeCount,
    which are exactly the fields preserved by the projection. -/
theorem transcriptBridge_deterministic {F : Type} [FRIField F] [CryptoHash F]
    (s₁ s₂ : TranscriptState F)
    (h : toFormalTranscript s₁ = toFormalTranscript s₂) :
    (squeeze s₁).output = (squeeze s₂).output := by
  simp only [squeeze]
  have h_abs : s₁.absorbed = s₂.absorbed := by
    have := congrArg FormalTranscript.absorbed h
    simpa [toFormalTranscript] using this
  have h_cnt : s₁.squeezeCount = s₂.squeezeCount := by
    have := congrArg FormalTranscript.squeezeCount h
    simpa [toFormalTranscript] using this
  rw [h_abs, h_cnt]

/-- Two states with same absorbed data and squeeze count produce the same challenge -/
theorem squeeze_agrees_on_core_data {F : Type} [FRIField F] [CryptoHash F]
    (s₁ s₂ : TranscriptState F)
    (h_abs : s₁.absorbed = s₂.absorbed)
    (h_cnt : s₁.squeezeCount = s₂.squeezeCount) :
    (squeeze s₁).output = (squeeze s₂).output := by
  simp only [squeeze]
  rw [h_abs, h_cnt]

/-! ## Part 5: Composition Properties

Properties for composing the transcript bridge with other bridges. -/

/-- Fresh transcripts project to the same formal state (regardless of domain tag) -/
theorem toFormalTranscript_init_eq {F : Type} :
    (toFormalTranscript (TranscriptState.init (F := F) tag)).absorbed = [] ∧
    (toFormalTranscript (TranscriptState.init (F := F) tag)).squeezeCount = 0 :=
  ⟨rfl, rfl⟩

/-- The formal init corresponds to a projected operational init -/
theorem bridge_init_agreement {F : Type} (tag : DomainTag) :
    toFormalTranscript (TranscriptState.init (F := F) tag) =
    FormalTranscript.init := by
  simp only [toFormalTranscript, TranscriptState.init, FormalTranscript.init]

/-- Absorb-then-squeeze commutes with the bridge -/
theorem transcriptBridge_absorb_squeeze {F : Type} [FRIField F] [CryptoHash F]
    (s : TranscriptState F) (elem : F) :
    let opResult := squeeze (absorb s elem)
    let formalAfterAbsorb := (toFormalTranscript s).absorb elem
    let (formalState, formalChallenge) := formalAfterAbsorb.squeeze CryptoHash.squeeze
    toFormalTranscript opResult.state = formalState ∧
    opResult.output = formalChallenge := by
  simp only [squeeze, absorb, toFormalTranscript, FormalTranscript.absorb,
             FormalTranscript.squeeze]
  exact ⟨trivial, trivial⟩

/-- The bridge is compatible with the friRound abstraction from TranscriptSpec -/
theorem transcriptBridge_friRound {F : Type} [FRIField F] [CryptoHash F]
    (s : TranscriptState F) (commitment : F) :
    let opAbsorbed := absorb s commitment
    let opResult := squeeze opAbsorbed
    let formalRound :=
      friRound (toFormalTranscript s) CryptoHash.squeeze commitment
    toFormalTranscript opResult.state = formalRound.1 ∧
    opResult.output = formalRound.2 := by
  simp only [absorb, squeeze, toFormalTranscript, friRound,
             FormalTranscript.absorb, FormalTranscript.squeeze]
  exact ⟨trivial, trivial⟩

/-! ## Part 6: TranscriptBridgeResult

Proof-carrying structure for downstream use by BridgeIntegration (N13.6). -/

/-- A transcript bridge result bundles the operational state with its
    formal projection and the agreement proof. -/
structure TranscriptBridgeResult (F : Type) [FRIField F] [CryptoHash F] where
  /-- The operational transcript state -/
  opState : TranscriptState F
  /-- The formal transcript state -/
  formalState : FormalTranscript F
  /-- The bridge agreement: formal = projection of operational -/
  agreement : toFormalTranscript opState = formalState

/-- Construct a bridge result from an operational state -/
def mkTranscriptBridgeResult {F : Type} [FRIField F] [CryptoHash F]
    (s : TranscriptState F) : TranscriptBridgeResult F :=
  { opState := s
    formalState := toFormalTranscript s
    agreement := rfl }

/-- After absorb, the bridge result is maintained -/
theorem transcriptBridgeResult_after_absorb {F : Type} [FRIField F] [CryptoHash F]
    (br : TranscriptBridgeResult F) (elem : F) :
    toFormalTranscript (absorb br.opState elem) = br.formalState.absorb elem := by
  rw [transcriptBridge_absorb, br.agreement]

/-! ## Part 7: Bridge Summary

TranscriptBridge provides:

1. `toFormalTranscript`: projection (drops domainStack, round)
2. `fromFormalTranscript`: embedding with defaults
3. `bridge_roundtrip`: toFormal ∘ fromFormal = id
4. `transcriptBridge_absorb`: absorb commutes with bridge
5. `transcriptBridge_absorbMany`: absorbMany commutes with bridge
6. `transcriptBridge_squeeze`: squeeze commutes with bridge (under CryptoHash oracle)
7. `transcriptBridge_deterministic`: bridge preserves determinism
8. `transcriptBridge_friRound`: compatible with friRound abstraction
9. `TranscriptBridgeResult`: proof-carrying structure for downstream

Upstream:
- Transcript.lean: TranscriptState, absorb, squeeze
- TranscriptSpec.lean: FormalTranscript, FormalTranscript.absorb/squeeze/friRound

Downstream:
- BridgeIntegration.lean (N13.6): integration theorem
-/

end AmoLean.FRI.Verified
