/-
  AMO-Lean: FRI Verifier
  Phase 3 - End-to-End Integration

  This module implements the FRI verifier with structured error reporting.
  Every failure returns a VerifyError that tells you:
  - WHAT failed (Merkle path, fold consistency, etc.)
  - WHERE it failed (round, query index, position)
  - WHY it failed (expected vs actual values)

  Design Decisions:
  - Returns VerifyResult (Except VerifyError Unit), not Bool
  - Optional debug logging via VerifyConfig
  - Iterative design (no deep recursion)
  - Replays transcript deterministically

  Reference: docs/poseidon/migration/MIGRATION_AUDIT.md
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Merkle
import AmoLean.FRI.Transcript
import AmoLean.FRI.Proof
import AmoLean.FRI.Prover

namespace AmoLean.FRI.Verifier

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Merkle (MerkleProof)
open AmoLean.FRI.Transcript (TranscriptState absorb squeeze absorbCommitment)
open AmoLean.FRI.Proof (FRIConfig FRIProof VerifyError VerifyResult VerifyConfig QueryPath LayerQuery)
open AmoLean.FRI.Prover (merkleHashFn foldPair)

/-! ## Part 1: Transcript Replay -/

/-- Replay the transcript to derive challenges.
    This must produce the same challenges as the prover.
-/
def replayTranscript {F : Type} [FRIField F] [CryptoHash F]
    (commitments : List F) : List F × TranscriptState F := Id.run do
  let mut challenges : List F := []
  let mut transcript : TranscriptState F := TranscriptState.forFRI

  for commitment in commitments do
    transcript := absorbCommitment transcript commitment
    let result := squeeze transcript
    challenges := challenges ++ [result.output]
    transcript := result.state

  pure (challenges, transcript)

/-- Helper to check transcript challenges match -/
def checkTranscriptChallenges {F : Type} [FRIField F] [BEq F]
    (replayed : List F) (proofChallenges : List F) (round : Nat := 0) :
    VerifyResult F :=
  match replayed, proofChallenges with
  | [], [] => .ok ()
  | r :: rs, p :: ps =>
    if r != p then
      .error (.transcriptMismatch round r p)
    else
      checkTranscriptChallenges rs ps (round + 1)
  | _, _ => .error (.malformedProof "Challenge list length mismatch")

/-- Verify that replayed challenges match proof challenges -/
def verifyTranscript {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (proof : FRIProof F) : VerifyResult F :=
  let (replayedChallenges, _) := replayTranscript proof.commitments
  if replayedChallenges.length != proof.challenges.length then
    .error (.malformedProof s!"Challenge count mismatch: replayed {replayedChallenges.length}, proof has {proof.challenges.length}")
  else
    checkTranscriptChallenges replayedChallenges proof.challenges

/-! ## Part 2: Merkle Path Verification -/

/-- Verify a single Merkle proof against a commitment -/
def verifyMerklePath {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (proof : MerkleProof F) (leafValue : F) (expectedRoot : F) : Bool :=
  proof.verify leafValue expectedRoot merkleHashFn

/-- Verify Merkle paths for a layer query -/
def verifyLayerQueryMerkle {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (query : LayerQuery F) (commitment : F) (round : Nat) (queryIdx : Nat) :
    VerifyResult F :=
  -- Verify even value proof
  if !verifyMerklePath query.evenProof query.evenValue commitment then
    .error (.merklePathInvalid round queryIdx (query.position * 2) commitment query.evenValue)
  -- Verify odd value proof
  else if !verifyMerklePath query.oddProof query.oddValue commitment then
    .error (.merklePathInvalid round queryIdx (query.position * 2 + 1) commitment query.oddValue)
  else
    .ok ()

/-! ## Part 3: Fold Consistency Verification -/

/-- Verify fold consistency for a single query.
    Checks that: nextLayerValue = fold(evenValue, oddValue, alpha)
-/
def verifyFoldConsistency {F : Type} [FRIField F] [Add F] [Mul F] [BEq F]
    (evenValue oddValue alpha nextLayerValue : F)
    (round queryIdx position : Nat) : VerifyResult F :=
  let expectedFolded := foldPair evenValue oddValue alpha
  if expectedFolded != nextLayerValue then
    .error (.foldInconsistency round queryIdx position expectedFolded nextLayerValue)
  else
    .ok ()

/-- Helper: verify layers in a query path -/
def verifyQueryPathLayers {F : Type} [FRIField F] [CryptoHash F] [Add F] [Mul F] [BEq F]
    (layerQueries : List (LayerQuery F))
    (commitments : List F)
    (challenges : List F)
    (finalLayer : List F)
    (queryIdx : Nat)
    (round : Nat := 0) : VerifyResult F :=
  match layerQueries, commitments, challenges with
  | [], [], [] => .ok ()
  | query :: restQueries, commit :: restCommits, alpha :: restAlphas =>
    -- Verify Merkle proofs for this layer
    match verifyLayerQueryMerkle query commit round queryIdx with
    | .error e => .error e
    | .ok () =>
      -- Compute expected fold result
      let expectedFolded := foldPair query.evenValue query.oddValue alpha

      -- Check fold consistency: the fold should appear in the next layer
      match restQueries with
      | nextQuery :: _ =>
        -- Not the last layer: check fold matches next layer's value at correct position
        -- query.position in next layer could be either even or odd child of nextQuery.position
        let nextLayerValue :=
          if query.position % 2 == 0 then nextQuery.evenValue else nextQuery.oddValue
        if expectedFolded != nextLayerValue then
          .error (.foldInconsistency round queryIdx query.position expectedFolded nextLayerValue)
        else
          verifyQueryPathLayers restQueries restCommits restAlphas finalLayer queryIdx (round + 1)
      | [] =>
        -- Last layer: verify against final polynomial
        if query.position < finalLayer.length then
          let finalValue := finalLayer.get! query.position
          if expectedFolded != finalValue then
            .error (.foldInconsistency round queryIdx query.position expectedFolded finalValue)
          else
            .ok ()
        else
          .ok ()
  | _, _, _ => .error (.malformedProof s!"Query {queryIdx}: layer/commitment/challenge count mismatch")

/-- Verify a complete query path -/
def verifyQueryPath {F : Type} [FRIField F] [CryptoHash F] [Add F] [Mul F] [BEq F]
    (path : QueryPath F) (commitments : List F) (challenges : List F)
    (finalLayer : List F) (queryIdx : Nat) : VerifyResult F :=
  if path.layerQueries.length != commitments.length then
    .error (.malformedProof s!"Query {queryIdx}: layer count mismatch")
  else
    verifyQueryPathLayers path.layerQueries commitments challenges finalLayer queryIdx

/-! ## Part 4: Final Layer Verification -/

/-- Helper: check all values in final layer are equal -/
def checkFinalLayerConstant {F : Type} [BEq F]
    (values : List F) (firstValue : F) (idx : Nat := 1) : VerifyResult F :=
  match values with
  | [] => .ok ()
  | v :: rest =>
    if v != firstValue then
      .error (.degreeViolation 0 1)  -- Claimed degree 0, but found non-constant
    else
      checkFinalLayerConstant rest firstValue (idx + 1)

/-- Verify the final layer is a low-degree polynomial.
    For FRI, the final layer should be constant (degree 0).
-/
def verifyFinalLayer {F : Type} [FRIField F] [BEq F]
    (finalLayer : List F) (config : FRIConfig) : VerifyResult F :=
  if finalLayer.isEmpty then
    .error (.malformedProof "Final layer is empty")
  else if config.finalDegree == 1 then
    -- For degree 0 (constant polynomial), all values should be the same
    match finalLayer with
    | [] => .error (.malformedProof "Final layer is empty")
    | first :: rest => checkFinalLayerConstant rest first
  else
    .ok ()

/-! ## Part 5: Complete Verifier -/

/-- Helper to verify all query paths -/
def verifyAllQueryPaths {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (queryPaths : List (QueryPath F)) (commitments : List F)
    (challenges : List F) (finalLayer : List F) (queryIdx : Nat := 0) :
    VerifyResult F :=
  match queryPaths with
  | [] => .ok ()
  | path :: rest =>
    match verifyQueryPath path commitments challenges finalLayer queryIdx with
    | .error e => .error e
    | .ok () => verifyAllQueryPaths rest commitments challenges finalLayer (queryIdx + 1)

/-- Verify a complete FRI proof.

    Checks (in order):
    1. Proof structure validity
    2. Transcript replay (Fiat-Shamir challenges)
    3. Merkle path validity for each query
    4. Fold consistency for each query
    5. Final layer low-degree property

    Returns:
    - .ok () if verification succeeds
    - .error (VerifyError) with detailed failure information
-/
def verify {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (proof : FRIProof F) : VerifyResult F :=
  -- Check 1: Proof structure
  if proof.commitments.length != proof.config.numRounds then
    .error (.commitmentCountMismatch proof.config.numRounds proof.commitments.length)
  else if proof.challenges.length != proof.commitments.length then
    .error (.malformedProof "Challenge count != commitment count")
  else
    -- Check 2: Transcript replay
    match verifyTranscript proof with
    | .error e => .error e
    | .ok () =>
      -- Check 3 & 4: Query verification
      match verifyAllQueryPaths proof.queryPaths proof.commitments proof.challenges proof.finalLayer with
      | .error e => .error e
      | .ok () =>
        -- Check 5: Final layer
        verifyFinalLayer proof.finalLayer proof.config

/-- Verify with configuration (debug logging) -/
def verifyWithConfig {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (config : VerifyConfig) (proof : FRIProof F) : IO (VerifyResult F) := do
  if config.debug then
    IO.println s!"[Verifier] Starting verification"
    IO.println s!"[Verifier]   Rounds: {proof.numRounds}"
    IO.println s!"[Verifier]   Queries: {proof.queryPaths.length}"
    IO.println s!"[Verifier]   Final layer size: {proof.finalLayer.length}"

  -- Transcript check
  if config.debug && config.logLevel >= 2 then
    IO.println s!"[Verifier] Checking transcript replay..."

  let result := verify proof

  match result with
  | .ok () =>
    if config.debug then
      IO.println s!"[Verifier] Verification PASSED"
  | .error err =>
    if config.debug then
      IO.println s!"[Verifier] Verification FAILED"
      IO.println s!"[Verifier]   Error: {VerifyError.toString err}"

  return result

/-! ## Part 6: Convenience Functions -/

/-- Simple verification returning Bool (for tests that don't need diagnostics) -/
def verifyBool {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (proof : FRIProof F) : Bool :=
  match verify proof with
  | .ok () => true
  | .error _ => false

/-- Get error message if verification fails, or "OK" if it passes -/
def verifyMessage {F : Type} [FRIField F] [CryptoHash F] [BEq F]
    (proof : FRIProof F) : String :=
  match verify proof with
  | .ok () => "Verification passed"
  | .error err => s!"Verification failed: {VerifyError.toString err}"

/-! ## Part 7: Summary -/

def verifierSummary : String :=
  "FRI Verifier Module (Phase 3)
   ============================

   1. Structured Errors:
      - VerifyError tells you WHAT, WHERE, and WHY
      - No more opaque 'false' returns
      - Captures round, query index, position, expected/actual values

   2. Verification Checks:
      a) Proof structure (commitment count, etc.)
      b) Transcript replay (Fiat-Shamir correctness)
      c) Merkle path validity (for each query position)
      d) Fold consistency (fold(even,odd,α) matches next layer)
      e) Final layer low-degree (constant polynomial)

   3. Debug Logging:
      - VerifyConfig controls verbosity
      - verifyWithConfig enables logging
      - Useful for development and debugging

   4. Output Options:
      - verify: VerifyResult F (structured errors)
      - verifyBool: Bool (simple pass/fail)
      - verifyMessage: String (human-readable)

   Usage:
     match verify proof with
     | .ok () => IO.println \"Valid proof!\"
     | .error err => IO.println s!\"Invalid: {err}\""

#eval IO.println verifierSummary

end AmoLean.FRI.Verifier
