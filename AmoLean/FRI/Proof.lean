/-
  AMO-Lean: FRI Proof Structures and Error Types
  Phase 3 - End-to-End Integration

  This module defines:
  1. FRIProof structure - The complete proof object
  2. VerifyError - Structured error types for diagnostics
  3. VerifyResult - Result type for verification
  4. Query structures for the query phase

  Design Decisions:
  - VerifyError captures WHERE and WHY verification failed
  - All errors include enough context for debugging
  - Proof structure is generic over field type F

  Reference: docs/poseidon/migration/PHASE2-COMPLETE.md
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Merkle

namespace AmoLean.FRI.Proof

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Merkle (MerkleProof)

/-! ## Part 1: Query Structures -/

/-- A single query in the FRI protocol.
    Contains the position and evaluation at that position.
-/
structure QueryPoint (F : Type) where
  /-- Position in the evaluation domain -/
  position : Nat
  /-- Value at this position -/
  value : F
  deriving Repr

/-- Query response for a single layer.
    Contains the queried values and Merkle authentication path.
-/
structure LayerQuery (F : Type) where
  /-- Query position in this layer -/
  position : Nat
  /-- Value at the even position (position * 2 in previous layer) -/
  evenValue : F
  /-- Value at the odd position (position * 2 + 1 in previous layer) -/
  oddValue : F
  /-- Merkle proof for the even value -/
  evenProof : MerkleProof F
  /-- Merkle proof for the odd value -/
  oddProof : MerkleProof F
  deriving Repr

/-- Complete query path through all FRI layers -/
structure QueryPath (F : Type) where
  /-- Initial query position (in the original domain) -/
  initialPosition : Nat
  /-- Queries for each layer (from layer 0 to final) -/
  layerQueries : List (LayerQuery F)
  deriving Repr

/-! ## Part 2: FRI Proof Structure -/

/-- Parameters for the FRI protocol -/
structure FRIConfig where
  /-- Initial polynomial degree -/
  initialDegree : Nat
  /-- Blowup factor (domain size = degree * blowup) -/
  blowupFactor : Nat := 2
  /-- Number of queries for soundness -/
  numQueries : Nat := 30
  /-- Final layer degree (stop folding when reached) -/
  finalDegree : Nat := 1
  deriving Repr, Inhabited

namespace FRIConfig

/-- Calculate number of folding rounds -/
def numRounds (config : FRIConfig) : Nat :=
  Nat.log2 config.initialDegree - Nat.log2 config.finalDegree

/-- Initial domain size -/
def initialDomainSize (config : FRIConfig) : Nat :=
  config.initialDegree * config.blowupFactor

/-- Domain size at a given round -/
def domainSizeAtRound (config : FRIConfig) (round : Nat) : Nat :=
  config.initialDomainSize / (2 ^ round)

end FRIConfig

/-- Complete FRI proof.
    Contains all commitments, challenges, and query responses.
-/
structure FRIProof (F : Type) where
  /-- Protocol configuration -/
  config : FRIConfig
  /-- Merkle roots for each layer (commitments) -/
  commitments : List F
  /-- Challenges derived from transcript (α values) -/
  challenges : List F
  /-- Query paths (one per query) -/
  queryPaths : List (QueryPath F)
  /-- Final layer evaluations (constant polynomial) -/
  finalLayer : List F
  deriving Repr

namespace FRIProof

/-- Number of rounds in this proof -/
def numRounds (proof : FRIProof F) : Nat :=
  proof.commitments.length

/-- Get commitment for a specific round -/
def commitmentAt (proof : FRIProof F) (round : Nat) : Option F :=
  proof.commitments.get? round

/-- Get challenge for a specific round -/
def challengeAt (proof : FRIProof F) (round : Nat) : Option F :=
  proof.challenges.get? round

end FRIProof

/-! ## Part 3: Verification Errors -/

/-- Detailed error types for verification failures.
    Each error captures exactly WHERE and WHY verification failed.
-/
inductive VerifyError (F : Type) where
  /-- Transcript challenge mismatch (Fiat-Shamir failure) -/
  | transcriptMismatch :
      (round : Nat) →
      (expectedChallenge : F) →
      (computedChallenge : F) →
      VerifyError F

  /-- Merkle path verification failed -/
  | merklePathInvalid :
      (round : Nat) →
      (queryIndex : Nat) →
      (position : Nat) →
      (expectedRoot : F) →
      (computedRoot : F) →
      VerifyError F

  /-- Fold consistency check failed -/
  | foldInconsistency :
      (round : Nat) →
      (queryIndex : Nat) →
      (position : Nat) →
      (expectedFolded : F) →
      (actualFolded : F) →
      VerifyError F

  /-- Final layer degree check failed -/
  | degreeViolation :
      (claimedDegree : Nat) →
      (actualDegree : Nat) →
      VerifyError F

  /-- Query position out of bounds -/
  | queryOutOfBounds :
      (queryIndex : Nat) →
      (position : Nat) →
      (domainSize : Nat) →
      VerifyError F

  /-- Proof structure invalid (missing data) -/
  | malformedProof :
      (description : String) →
      VerifyError F

  /-- Commitment count mismatch -/
  | commitmentCountMismatch :
      (expected : Nat) →
      (actual : Nat) →
      VerifyError F

  deriving Repr

namespace VerifyError

/-- Human-readable error description -/
def toString [FRIField F] (err : VerifyError F) : String :=
  match err with
  | .transcriptMismatch round expected computed =>
      s!"Transcript mismatch at round {round}: expected challenge {FRIField.toNat expected}, got {FRIField.toNat computed}"
  | .merklePathInvalid round qIdx pos expectedRoot computedRoot =>
      s!"Merkle path invalid at round {round}, query {qIdx}, position {pos}: expected root {FRIField.toNat expectedRoot}, computed {FRIField.toNat computedRoot}"
  | .foldInconsistency round qIdx pos expected actual =>
      s!"Fold inconsistency at round {round}, query {qIdx}, position {pos}: expected {FRIField.toNat expected}, got {FRIField.toNat actual}"
  | .degreeViolation claimed actual =>
      s!"Degree violation: claimed degree {claimed}, but found degree {actual}"
  | .queryOutOfBounds qIdx pos domainSize =>
      s!"Query {qIdx} out of bounds: position {pos} >= domain size {domainSize}"
  | .malformedProof desc =>
      s!"Malformed proof: {desc}"
  | .commitmentCountMismatch expected actual =>
      s!"Commitment count mismatch: expected {expected}, got {actual}"

instance [FRIField F] : ToString (VerifyError F) := ⟨VerifyError.toString⟩

end VerifyError

/-- Result type for verification -/
abbrev VerifyResult (F : Type) := Except (VerifyError F) Unit

/-! ## Part 4: Verification Configuration -/

/-- Configuration for verification behavior -/
structure VerifyConfig where
  /-- Enable debug logging -/
  debug : Bool := false
  /-- Logging verbosity (0=silent, 1=summary, 2=detailed, 3=trace) -/
  logLevel : Nat := 0
  /-- Check all queries even after first failure (for diagnostics) -/
  checkAllQueries : Bool := false
  deriving Repr, Inhabited

namespace VerifyConfig

def silent : VerifyConfig := { debug := false, logLevel := 0 }
def summary : VerifyConfig := { debug := true, logLevel := 1 }
def detailed : VerifyConfig := { debug := true, logLevel := 2 }
def trace : VerifyConfig := { debug := true, logLevel := 3 }

end VerifyConfig

/-! ## Part 5: Prover State -/

/-- State maintained during proof generation -/
structure ProverState (F : Type) where
  /-- Current layer evaluations -/
  currentLayer : Array F
  /-- Current domain size -/
  domainSize : Nat
  /-- Current round number -/
  round : Nat
  /-- Accumulated commitments (Merkle roots) -/
  commitments : List F
  /-- Accumulated challenges (from transcript) -/
  challenges : List F
  /-- All layer data (for query phase) -/
  layerData : List (Array F)
  deriving Repr

namespace ProverState

/-- Create initial prover state from evaluations -/
def init {F : Type} (evaluations : Array F) : ProverState F :=
  { currentLayer := evaluations
    domainSize := evaluations.size
    round := 0
    commitments := []
    challenges := []
    layerData := [evaluations] }

end ProverState

/-! ## Part 6: Summary -/

def proofSummary : String :=
  "FRI Proof Module (Phase 3)
   =========================

   1. Query Structures:
      - QueryPoint: Single evaluation point
      - LayerQuery: Query response with Merkle proofs
      - QueryPath: Complete path through all layers

   2. Proof Structure:
      - FRIConfig: Protocol parameters
      - FRIProof: Complete proof with commitments and queries

   3. Error Types:
      - VerifyError: Detailed error for each failure mode
      - VerifyResult: Except-based result type
      - Every error captures round/query/position context

   4. Configuration:
      - VerifyConfig: Debug logging options
      - ProverState: State for iterative proof generation

   Design Goals:
   - Errors tell you WHERE and WHY verification failed
   - All structures are generic over field type F
   - State machine approach enables iterative (non-recursive) implementation"

#eval IO.println proofSummary

end AmoLean.FRI.Proof
