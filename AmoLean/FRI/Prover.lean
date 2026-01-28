/-
  AMO-Lean: FRI Prover
  Phase 3 - End-to-End Integration

  This module implements the FRI prover using an iterative design
  to avoid stack overflow on large polynomials.

  Design Decisions:
  - Uses `for` loops instead of recursion (no stack overflow)
  - State machine approach: ProverState → ProverState transitions
  - Generic over field type F with [FRIField F] [CryptoHash F]
  - Separated into phases: Commit, Query generation

  Performance Notes:
  - Use compiled executable for large degrees (see Benchmarks/)
  - #eval! tests should use degree ≤ 64

  Reference: docs/poseidon/migration/MIGRATION_AUDIT.md
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Merkle
import AmoLean.FRI.Transcript
import AmoLean.FRI.Proof

namespace AmoLean.FRI.Prover

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Merkle (FlatMerkle buildTree MerkleProof generateProof)
open AmoLean.FRI.Transcript (TranscriptState absorb squeeze absorbCommitment)
open AmoLean.FRI.Proof (FRIConfig FRIProof ProverState QueryPath LayerQuery)

/-! ## Part 1: Hash Function for Merkle Tree -/

/-- Get the hash function for Merkle tree construction.
    Uses CryptoHash.hash2to1 for the field type.
-/
@[inline]
def merkleHashFn {F : Type} [CryptoHash F] : F → F → F :=
  CryptoHash.hash2to1

/-! ## Part 2: FRI Fold Operation -/

/-- Fold a layer using challenge α.
    fold(even, odd, α) = even + α * odd

    Input layer has size 2n, output layer has size n.
-/
@[inline]
def foldPair {F : Type} [FRIField F] [Add F] [Mul F]
    (even odd alpha : F) : F :=
  even + alpha * odd

/-- Fold an entire layer.
    Uses iterative construction to avoid stack overflow.
-/
def foldLayer {F : Type} [FRIField F] [Add F] [Mul F] [Inhabited F]
    (layer : Array F) (alpha : F) : Array F :=
  let n := layer.size / 2
  Array.range n |>.map fun i =>
    let even := layer.get! (2 * i)
    let odd := layer.get! (2 * i + 1)
    foldPair even odd alpha

/-! ## Part 3: Commit Phase (Iterative) -/

/-- Single round of the commit phase.
    1. Build Merkle tree of current layer
    2. Absorb commitment into transcript
    3. Squeeze challenge α
    4. Fold layer using α
    5. Return updated state

    Returns: (newState, commitment, challenge)
-/
def commitRound {F : Type} [FRIField F] [CryptoHash F] [Inhabited F] [BEq F]
    (state : ProverState F) (transcript : TranscriptState F) :
    Option (ProverState F × TranscriptState F × F × F) := do
  -- 1. Build Merkle tree
  let tree ← buildTree state.currentLayer merkleHashFn

  -- 2. Get commitment (root)
  let commitment := tree.root

  -- 3. Absorb commitment
  let t1 := absorbCommitment transcript commitment

  -- 4. Squeeze challenge
  let result := squeeze t1
  let alpha := result.output
  let t2 := result.state

  -- 5. Fold layer
  let foldedLayer := foldLayer state.currentLayer alpha

  -- 6. Update state
  let newState : ProverState F := {
    currentLayer := foldedLayer
    domainSize := foldedLayer.size
    round := state.round + 1
    commitments := state.commitments ++ [commitment]
    challenges := state.challenges ++ [alpha]
    layerData := state.layerData ++ [foldedLayer]
  }

  return (newState, t2, commitment, alpha)

/-- Execute all commit rounds iteratively.
    Stops when domain size reaches finalDegree * blowup or after maxRounds.
-/
def commitPhase {F : Type} [FRIField F] [CryptoHash F] [Inhabited F] [BEq F]
    (evaluations : Array F) (config : FRIConfig) :
    IO (Option (ProverState F × TranscriptState F)) := do
  let mut state := ProverState.init evaluations
  let mut transcript : TranscriptState F := TranscriptState.forFRI

  let targetSize := config.finalDegree * config.blowupFactor
  let maxRounds := config.numRounds

  for round in [:maxRounds] do
    if state.domainSize <= targetSize then
      break

    match commitRound state transcript with
    | none =>
      IO.eprintln s!"[Prover] Commit round {round} failed (Merkle tree construction)"
      return none
    | some (newState, newTranscript, commitment, alpha) =>
      state := newState
      transcript := newTranscript

  return some (state, transcript)

/-! ## Part 4: Query Phase -/

/-- Derive query positions from transcript.
    Uses squeeze to get pseudo-random positions.
-/
def deriveQueryPositions {F : Type} [FRIField F] [CryptoHash F]
    (transcript : TranscriptState F) (domainSize : Nat) (numQueries : Nat) :
    List Nat × TranscriptState F := Id.run do
  let mut positions : List Nat := []
  let mut t := transcript

  for _ in [:numQueries] do
    let result := squeeze t
    let posNat := FRIField.toNat result.output
    let pos := posNat % domainSize
    positions := positions ++ [pos]
    t := result.state

  pure (positions, t)

/-- Generate a single layer query with Merkle proofs.
    Helper for generateQueryPath.
-/
def generateLayerQuery {F : Type} [FRIField F] [CryptoHash F] [Inhabited F] [BEq F]
    (layer : Array F) (pos : Nat) : Option (LayerQuery F × Nat) := do
  let nextLayerPos := pos / 2
  let evenPos := nextLayerPos * 2
  let oddPos := evenPos + 1

  -- Get values
  let evenValue := layer.get! evenPos
  let oddValue := layer.get! oddPos

  -- Build Merkle tree for this layer to get proofs
  let tree ← buildTree layer merkleHashFn
  let evenProof ← generateProof tree evenPos
  let oddProof ← generateProof tree oddPos

  let query : LayerQuery F := {
    position := nextLayerPos
    evenValue := evenValue
    oddValue := oddValue
    evenProof := evenProof
    oddProof := oddProof
  }
  pure (query, nextLayerPos)

/-- Generate query for a single position through all layers.
    Returns the LayerQuery structures for each round.
-/
def generateQueryPath {F : Type} [FRIField F] [CryptoHash F] [Inhabited F] [BEq F]
    (state : ProverState F) (initialPos : Nat) :
    Option (QueryPath F) := Id.run do
  let mut layerQueries : List (LayerQuery F) := []
  let mut pos := initialPos
  let mut failed := false

  -- For each layer (except the last which is the final constant)
  for (layerIdx, layerData) in state.layerData.enum do
    if failed then break
    if layerIdx >= state.layerData.length - 1 then
      break  -- Skip final layer

    match generateLayerQuery layerData pos with
    | none =>
      failed := true
    | some (query, nextPos) =>
      layerQueries := layerQueries ++ [query]
      pos := nextPos

  if failed then
    none
  else
    some {
      initialPosition := initialPos
      layerQueries := layerQueries
    }

/-- Generate all query paths -/
def queryPhase {F : Type} [FRIField F] [CryptoHash F] [Inhabited F] [BEq F]
    (state : ProverState F) (transcript : TranscriptState F) (config : FRIConfig) :
    IO (Option (List (QueryPath F))) := do
  -- Derive query positions
  let initialDomainSize := config.initialDomainSize
  let (positions, _) := deriveQueryPositions transcript initialDomainSize config.numQueries

  -- Generate query path for each position
  let mut queryPaths : List (QueryPath F) := []
  for (idx, pos) in positions.enum do
    match generateQueryPath state pos with
    | none =>
      IO.eprintln s!"[Prover] Failed to generate query path {idx} at position {pos}"
      return none
    | some path =>
      queryPaths := queryPaths ++ [path]

  return some queryPaths

/-! ## Part 5: Complete Prover -/

/-- Generate a complete FRI proof.

    Algorithm (iterative, no deep recursion):
    1. Commit Phase: For each round, commit → absorb → squeeze → fold
    2. Query Phase: Derive positions, generate authentication paths

    Returns: FRIProof or error message
-/
def prove {F : Type} [FRIField F] [CryptoHash F] [Inhabited F] [BEq F]
    (evaluations : Array F) (config : FRIConfig) :
    IO (Except String (FRIProof F)) := do
  -- Validate input
  if evaluations.size != config.initialDomainSize then
    return .error s!"Input size {evaluations.size} != expected {config.initialDomainSize}"

  -- Check power of 2
  let n := evaluations.size
  if n &&& (n - 1) != 0 then
    return .error s!"Input size {n} is not a power of 2"

  IO.println s!"[Prover] Starting FRI proof generation"
  IO.println s!"[Prover]   Domain size: {config.initialDomainSize}"
  IO.println s!"[Prover]   Target rounds: {config.numRounds}"
  IO.println s!"[Prover]   Queries: {config.numQueries}"

  -- Commit phase
  IO.println s!"[Prover] Running commit phase..."
  match ← commitPhase evaluations config with
  | none =>
    return .error "Commit phase failed"
  | some (state, transcript) =>
    IO.println s!"[Prover] Commit phase complete: {state.commitments.length} rounds"

    -- Query phase
    IO.println s!"[Prover] Running query phase..."
    match ← queryPhase state transcript config with
    | none =>
      return .error "Query phase failed"
    | some queryPaths =>
      IO.println s!"[Prover] Query phase complete: {queryPaths.length} queries"

      -- Construct proof
      let proof : FRIProof F := {
        config := config
        commitments := state.commitments
        challenges := state.challenges
        queryPaths := queryPaths
        finalLayer := state.currentLayer.toList
      }

      IO.println s!"[Prover] Proof generation complete"
      return .ok proof

/-! ## Part 6: Convenience Functions -/

/-- Create a simple FRI config for testing -/
def testConfig (degree : Nat) : FRIConfig :=
  { initialDegree := degree
    blowupFactor := 2
    numQueries := 4  -- Few queries for testing
    finalDegree := 1 }

/-- Create a production FRI config -/
def productionConfig (degree : Nat) (numQueries : Nat := 30) : FRIConfig :=
  { initialDegree := degree
    blowupFactor := 2
    numQueries := numQueries
    finalDegree := 1 }

/-! ## Part 7: Summary -/

def proverSummary : String :=
  "FRI Prover Module (Phase 3)
   ==========================

   1. Iterative Design:
      - Uses `for` loops instead of recursion
      - No stack overflow on large polynomials (2^20+)
      - State machine: ProverState transitions

   2. Commit Phase:
      - For each round: commit → absorb → squeeze → fold
      - Stores all layer data for query phase
      - Returns commitments and challenges

   3. Query Phase:
      - Derives positions from transcript (Fiat-Shamir)
      - Generates Merkle proofs for each query
      - Returns complete QueryPath structures

   4. Output:
      - FRIProof contains: commitments, challenges, queryPaths, finalLayer
      - All data needed for verification

   Performance:
   - Use compiled executable for degree > 64
   - #eval! tests should use small degrees

   Usage:
     let config := testConfig 16  -- degree=16
     let proof ← prove evaluations config"

#eval IO.println proverSummary

end AmoLean.FRI.Prover
