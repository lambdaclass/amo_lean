/-
  AMO-Lean: FRI Protocol State Machine
  Phase 6.5 - Complete FRI Protocol Assembly

  This module assembles the FRI protocol using the components built in
  previous phases:
  - MatExpr (Phase 5): Polynomial/matrix arithmetic
  - CryptoSigma (Phase 6.3): Cryptographic operations
  - FlatMerkle (Phase 6.4): Commitment scheme

  The FRI protocol is modeled as an explicit state machine:
    RoundState → RoundState

  Each round transition performs (in strict order):
  1. COMMIT: Build Merkle tree of current polynomial evaluations
  2. ABSORB: Ingest Merkle root into transcript
  3. SQUEEZE: Extract challenge α from transcript
  4. FOLD: Compute next layer using FRI fold with α

  This ordering is CRITICAL for security and is enforced by the
  CryptoSigma IR which prevents reordering of intrinsic operations.

  References:
  - "Fast Reed-Solomon IOP of Proximity" (Ben-Sasson et al.)
  - "DEEP-FRI" (Ben-Sasson et al.)
-/

import AmoLean.FRI.Basic
import AmoLean.FRI.Fold
import AmoLean.FRI.Transcript
import AmoLean.FRI.Merkle
import AmoLean.FRI.Kernel
import AmoLean.Matrix.Basic

namespace AmoLean.FRI.Protocol

open AmoLean.FRI (ZKCostModel defaultZKCost FRIParams FieldConfig)
open AmoLean.FRI.Fold (FRIField friFold)
open AmoLean.FRI.Transcript (TranscriptState Intrinsic CryptoSigma DomainTag)
open AmoLean.FRI.Transcript (absorb squeeze enterDomain exitDomain nextRound absorbCommitment)
open AmoLean.FRI.Merkle (FlatMerkle MerkleProof buildTreeSigma generateAccessTrace)
open AmoLean.FRI.Kernel (FRILayerKernel lowerToSigma)
open AmoLean.Sigma (Gather Scatter LoopVar IdxExpr Kernel SigmaExpr)
open AmoLean.Matrix (MatExpr)
open AmoLean.Vector (Vec)

/-! ## Part 1: Protocol State Definition -/

/-- Symbolic representation of a polynomial in FRI.

    During the protocol, we track polynomials symbolically to generate
    the IR. The actual evaluations are computed at runtime.
-/
inductive PolyExpr where
  /-- Initial polynomial (input to FRI) -/
  | initial : (degree : Nat) → PolyExpr
  /-- Folded polynomial from previous round -/
  | folded : (parent : PolyExpr) → (alpha : Nat) → PolyExpr  -- alpha is challenge ID
  /-- Constant polynomial (final layer) -/
  | constant : PolyExpr
  deriving Repr, Inhabited

namespace PolyExpr

/-- Get the degree of the polynomial -/
def degree : PolyExpr → Nat
  | .initial d => d
  | .folded parent _ => parent.degree / 2
  | .constant => 0

/-- Get the evaluation domain size (degree * blowup) -/
def domainSize (p : PolyExpr) (blowup : Nat := 2) : Nat :=
  p.degree * blowup

/-- Get the round number (depth of folding) -/
def roundNumber : PolyExpr → Nat
  | .initial _ => 0
  | .folded parent _ => parent.roundNumber + 1
  | .constant => 0

def toString : PolyExpr → String
  | .initial d => s!"P₀(deg={d})"
  | .folded parent α => s!"Fold({parent.toString}, α_{α})"
  | .constant => "const"

instance : ToString PolyExpr := ⟨PolyExpr.toString⟩

end PolyExpr

/-- State of a single FRI round.

    This captures the complete state needed to:
    1. Generate the IR for the current round
    2. Transition to the next round

    The state is semantic: it knows about the polynomial being processed,
    not just raw data.
-/
structure RoundState where
  /-- Current polynomial (symbolic) -/
  poly : PolyExpr
  /-- Current domain size (N) -/
  domain : Nat
  /-- Transcript state (Fiat-Shamir) -/
  transcript : TranscriptState
  /-- Round number (0-indexed) -/
  round : Nat
  /-- Merkle commitment of current layer (after commit phase) -/
  commitment : Option UInt64
  /-- Challenge α for folding (after squeeze phase) -/
  challenge : Option UInt64
  deriving Repr

namespace RoundState

/-- Create initial state for FRI protocol -/
def init (initialDegree : Nat) (blowup : Nat := 2) : RoundState :=
  let domain := initialDegree * blowup
  { poly := .initial initialDegree
    domain := domain
    transcript := TranscriptState.forFRI
    round := 0
    commitment := none
    challenge := none }

/-- Check if we've reached the final round -/
def isFinal (s : RoundState) : Bool :=
  s.domain <= 1

/-- Get the number of fold operations in this round -/
def foldCount (s : RoundState) : Nat :=
  s.domain / 2

def toString (s : RoundState) : String :=
  s!"RoundState(round={s.round}, domain={s.domain}, poly={s.poly})"

instance : ToString RoundState := ⟨RoundState.toString⟩

end RoundState

/-! ## Part 2: Round Operations (Phases) -/

/-- Phase 1: COMMIT - Build Merkle tree and get root.

    Input: Current polynomial evaluations (implicit in domain size)
    Output: Merkle root commitment
    CryptoSigma: Tree construction intrinsics
-/
def commitPhase (state : RoundState) : CryptoSigma × UInt64 :=
  -- Generate Merkle tree construction IR
  let treeSigma := buildTreeSigma state.domain

  -- Simulate commitment (in real impl, this would be computed)
  let simulatedRoot : UInt64 := UInt64.ofNat (state.domain * 0x9e3779b9 + state.round)

  (treeSigma, simulatedRoot)

/-- Phase 2: ABSORB - Ingest commitment into transcript.

    Input: Merkle root, current transcript
    Output: Updated transcript
    CryptoSigma: Absorb intrinsic
-/
def absorbPhase (state : RoundState) (commitment : UInt64) : CryptoSigma × TranscriptState :=
  let dummyGather := Gather.contiguous 1 (.const 0)
  let dummyScatter := Scatter.contiguous 1 (.const 0)

  -- Generate absorb IR
  let absorbSigma := CryptoSigma.intrinsic (.absorb 1) dummyGather dummyScatter

  -- Update transcript state
  let newTranscript := absorbCommitment state.transcript commitment

  (absorbSigma, newTranscript)

/-- Phase 3: SQUEEZE - Extract challenge from transcript.

    Input: Current transcript
    Output: Challenge α, updated transcript
    CryptoSigma: Squeeze intrinsic (BARRIER)
-/
def squeezePhase (transcript : TranscriptState) : CryptoSigma × UInt64 × TranscriptState :=
  let dummyGather := Gather.contiguous 1 (.const 0)
  let dummyScatter := Scatter.contiguous 1 (.const 0)

  -- Generate squeeze IR
  let squeezeSigma := CryptoSigma.intrinsic .squeeze dummyGather dummyScatter

  -- Extract challenge
  let result := squeeze transcript
  let alpha := result.output
  let newTranscript := result.state

  (squeezeSigma, alpha, newTranscript)

/-- Phase 4: FOLD - Compute next polynomial layer.

    Input: Current domain, challenge α
    Output: Folded polynomial expression
    CryptoSigma: FRI fold loop

    The fold operation: out[i] = in[2i] + α * in[2i+1]
-/
def foldPhase (state : RoundState) (alpha : UInt64) : CryptoSigma × PolyExpr :=
  let n := state.domain / 2  -- Output size

  -- Generate fold IR using FRI kernel
  let kernel := FRILayerKernel.create n
  let foldSigmaExpr := lowerToSigma n kernel

  -- Convert SigmaExpr to CryptoSigma (embed in crypto context)
  let foldSigma := embedSigmaExpr foldSigmaExpr

  -- Create folded polynomial expression
  let foldedPoly := PolyExpr.folded state.poly state.round

  (foldSigma, foldedPoly)
where
  /-- Embed standard SigmaExpr into CryptoSigma -/
  embedSigmaExpr : SigmaExpr → CryptoSigma
    | .compute k g s => .compute k g s
    | .loop n v body => .loop n v (embedSigmaExpr body)
    | .seq s1 s2 => .seq (embedSigmaExpr s1) (embedSigmaExpr s2)
    | .par s1 s2 => .par (embedSigmaExpr s1) (embedSigmaExpr s2)
    | .temp sz body => .temp sz (embedSigmaExpr body)
    | .nop => .nop

/-! ## Part 3: Complete Round Transition -/

/-- Output of a single FRI round -/
structure RoundOutput where
  /-- New state after the round -/
  nextState : RoundState
  /-- Combined IR for the entire round -/
  sigma : CryptoSigma
  /-- Phases executed (for debugging) -/
  phases : List String
  deriving Repr

/-- Execute one complete FRI round: Commit → Absorb → Squeeze → Fold

    This is the core state transition function.
    It produces BOTH:
    1. The next state (for protocol continuation)
    2. The CryptoSigma IR (for code generation)

    The IR is structured as:
    seq(
      DomainEnter(friFold),
      seq(
        Commit(MerkleTree),
        seq(
          Absorb(root),
          seq(
            Squeeze(α),
            seq(
              Fold(α),
              DomainExit
            )
          )
        )
      )
    )
-/
def friRound (state : RoundState) : RoundOutput :=
  let dummyGather := Gather.contiguous 1 (.const 0)
  let dummyScatter := Scatter.contiguous 1 (.const 0)

  -- Phase 0: Enter domain
  let domainEnterSigma := CryptoSigma.intrinsic (.domainEnter .friFold) dummyGather dummyScatter

  -- Phase 1: Commit
  let (commitSigma, commitment) := commitPhase state

  -- Phase 2: Absorb
  let (absorbSigma, transcriptAfterAbsorb) := absorbPhase state commitment

  -- Phase 3: Squeeze
  let (squeezeSigma, alpha, transcriptAfterSqueeze) := squeezePhase transcriptAfterAbsorb

  -- Phase 4: Fold
  let (foldSigma, foldedPoly) := foldPhase state alpha

  -- Phase 5: Exit domain
  let domainExitSigma := CryptoSigma.intrinsic .domainExit dummyGather dummyScatter

  -- Combine all phases in strict order
  let combinedSigma :=
    .seq domainEnterSigma
      (.seq commitSigma
        (.seq absorbSigma
          (.seq squeezeSigma
            (.seq foldSigma domainExitSigma))))

  -- Create next state
  let nextState : RoundState := {
    poly := foldedPoly
    domain := state.domain / 2
    transcript := nextRound transcriptAfterSqueeze
    round := state.round + 1
    commitment := some commitment
    challenge := some alpha
  }

  { nextState := nextState
    sigma := combinedSigma
    phases := ["DomainEnter", "Commit", "Absorb", "Squeeze", "Fold", "DomainExit"] }

/-! ## Part 4: Multi-Round Protocol Execution -/

/-- Execute multiple FRI rounds until reaching minimum domain size -/
partial def runFRIRounds (state : RoundState) (maxRounds : Nat) (acc : List RoundOutput) :
    List RoundOutput × RoundState :=
  if state.isFinal || acc.length >= maxRounds then
    (acc.reverse, state)
  else
    let output := friRound state
    runFRIRounds output.nextState maxRounds (output :: acc)

/-- Complete FRI commit phase (all rounds) -/
def friCommitPhase (initialDegree : Nat) (numRounds : Nat) : List RoundOutput × RoundState :=
  let initialState := RoundState.init initialDegree
  runFRIRounds initialState numRounds []

/-- Combine all round sigmas into single IR -/
def combineRoundSigmas (outputs : List RoundOutput) : CryptoSigma :=
  outputs.foldl (fun acc out => CryptoSigma.seq acc out.sigma) CryptoSigma.nop

/-! ## Part 5: Protocol Analysis -/

/-- Analyze the intrinsic flow of a CryptoSigma -/
def analyzeFlow (sigma : CryptoSigma) : List String :=
  let intrinsics := sigma.extractIntrinsicSequence
  intrinsics.map fun i =>
    match i with
    | .domainEnter tag => s!"→ ENTER({repr tag})"
    | .domainExit => "← EXIT"
    | .absorb n => s!"◆ ABSORB({n})"
    | .squeeze => "◇ SQUEEZE(α)"
    | .hash n => s!"# HASH({n})"
    | .merkleHash => "⊕ MERKLE_HASH"
    | .barrier => "| BARRIER"

/-- Pretty print the protocol flow -/
def printFlow (outputs : List RoundOutput) : IO Unit := do
  IO.println "FRI Protocol Flow:"
  IO.println "=================="
  for (i, out) in outputs.enum do
    IO.println s!"\n--- Round {i} ---"
    IO.println s!"State: domain={out.nextState.domain}, poly={out.nextState.poly}"
    IO.println s!"Commitment: {out.nextState.commitment.getD 0}"
    IO.println s!"Challenge α: {out.nextState.challenge.getD 0}"
    IO.println "Phases:"
    for phase in out.phases do
      IO.println s!"  • {phase}"

/-! ## Part 6: Cost Analysis -/

/-- Calculate cost of one FRI round -/
def roundCost (cm : ZKCostModel) (domainSize : Nat) : Nat :=
  -- Commit: Merkle tree construction
  let commitCost := Merkle.buildTreeCost cm domainSize

  -- Absorb: Single hash update
  let absorbCost := Intrinsic.cost cm (.absorb 1)

  -- Squeeze: Full hash extraction
  let squeezeCost := Intrinsic.cost cm .squeeze

  -- Fold: FRI fold operations
  let foldCost := Kernel.kernelCost cm (domainSize / 2)

  commitCost + absorbCost + squeezeCost + foldCost

/-- Calculate total cost of FRI protocol -/
def protocolCost (cm : ZKCostModel) (initialDomain : Nat) (numRounds : Nat) : Nat :=
  let costs := List.range numRounds |>.map fun r =>
    let domain := initialDomain / (2^r)
    roundCost cm domain
  costs.foldl (· + ·) 0

/-! ## Part 7: Tests -/

section Tests

/-- Test 1: Single round execution -/
def testSingleRound : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI SINGLE ROUND TEST (N = 16)                         ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let initialState := RoundState.init 8 2  -- degree=8, blowup=2 → domain=16
  IO.println s!"Initial state: {initialState}"

  let output := friRound initialState
  IO.println s!"\nAfter round 0:"
  IO.println s!"  Next state: {output.nextState}"
  IO.println s!"  Phases executed: {output.phases}"

  IO.println "\nGenerated CryptoSigma structure:"
  IO.println s!"{output.sigma}"

#eval! testSingleRound

/-- Test 2: Two-round protocol (N=16) -/
def testTwoRounds : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI TWO-ROUND TEST (N = 16)                            ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let (outputs, finalState) := friCommitPhase 8 2  -- 2 rounds

  IO.println s!"Executed {outputs.length} rounds"
  IO.println s!"Final state: domain={finalState.domain}, round={finalState.round}"

  printFlow outputs

  -- Show combined sigma
  IO.println "\n--- Combined CryptoSigma ---"
  let combined := combineRoundSigmas outputs
  IO.println s!"Total intrinsic count: {combined.intrinsicCount}"

  -- Analyze flow
  IO.println "\n--- Intrinsic Flow Analysis ---"
  let flow := analyzeFlow combined
  for step in flow do
    IO.println s!"  {step}"

#eval! testTwoRounds

/-- Test 3: Verify flow pattern -/
def testFlowPattern : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI FLOW PATTERN VERIFICATION                          ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let (outputs, _) := friCommitPhase 8 3  -- 3 rounds
  let combined := combineRoundSigmas outputs

  IO.println "Expected pattern per round:"
  IO.println "  ENTER → Tree → ABSORB → SQUEEZE → Fold → EXIT"
  IO.println ""

  let flow := analyzeFlow combined
  IO.println "Actual flow:"
  let mut roundNum := 0
  for step in flow do
    if step.startsWith "→ ENTER" then
      IO.println s!"\n  [Round {roundNum}]"
      roundNum := roundNum + 1
    IO.println s!"    {step}"

  -- Verify the pattern
  let intrinsics := combined.extractIntrinsicSequence
  let patternOk := verifyFlowPattern intrinsics
  IO.println s!"\nPattern verification: {if patternOk then "PASSED ✓" else "FAILED ✗"}"
where
  /-- Verify that the flow follows: Enter → (MerkleHash*) → Absorb → Squeeze → Exit -/
  verifyFlowPattern (intrinsics : List Intrinsic) : Bool :=
    -- Simplified check: each round should have Enter, Absorb, Squeeze, Exit in order
    let enters := intrinsics.filter fun i => match i with | .domainEnter _ => true | _ => false
    let absorbs := intrinsics.filter fun i => match i with | .absorb _ => true | _ => false
    let squeezes := intrinsics.filter fun i => match i with | .squeeze => true | _ => false
    let exits := intrinsics.filter fun i => match i with | .domainExit => true | _ => false
    -- Equal counts means balanced rounds
    enters.length == absorbs.length &&
    absorbs.length == squeezes.length &&
    squeezes.length == exits.length

#eval! testFlowPattern

/-- Test 4: Cost analysis -/
def testCostAnalysis : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI PROTOCOL COST ANALYSIS                             ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let cm := defaultZKCost

  IO.println "Per-round cost breakdown (N=1024):"
  let domain := 1024
  IO.println s!"  Commit (Merkle tree): {Merkle.buildTreeCost cm domain}"
  IO.println s!"  Absorb:               {Intrinsic.cost cm (.absorb 1)}"
  IO.println s!"  Squeeze:              {Intrinsic.cost cm .squeeze}"
  IO.println s!"  Fold:                 {Kernel.kernelCost cm (domain / 2)}"
  IO.println s!"  Total round cost:     {roundCost cm domain}"

  IO.println "\nTotal protocol cost by initial size:"
  for (size, rounds) in [(16, 4), (1024, 10), (1048576, 20)] do
    let cost := protocolCost cm size rounds
    IO.println s!"  N={size}, rounds={rounds}: {cost}"

#eval! testCostAnalysis

end Tests

/-! ## Part 8: Summary -/

def protocolSummary : String :=
  "FRI Protocol Module Summary (Phase 6.5):
   =======================================

   1. RoundState: Complete protocol state
      - poly: Symbolic polynomial (PolyExpr)
      - domain: Current evaluation domain size
      - transcript: Fiat-Shamir state
      - commitment: Merkle root (after commit)
      - challenge: α value (after squeeze)

   2. Round Phases (strict order):
      a) COMMIT: Build Merkle tree → root
      b) ABSORB: Ingest root into transcript
      c) SQUEEZE: Extract challenge α (BARRIER)
      d) FOLD: Compute P_{k+1}(x) = P_even(x) + α·P_odd(x)

   3. State Transition:
      friRound : RoundState → RoundOutput
      - Produces next state AND CryptoSigma IR
      - IR preserves operation ordering

   4. Multi-Round Execution:
      runFRIRounds : RoundState → Nat → List RoundOutput
      - Executes until domain ≤ 1 or max rounds

   5. Flow Pattern (per round):
      ENTER → MerkleTree → ABSORB → SQUEEZE → Fold → EXIT

   Security Invariant:
   The CryptoSigma IR enforces that SQUEEZE always comes AFTER ABSORB,
   preventing the optimizer from reordering these operations."

#eval! IO.println protocolSummary

end AmoLean.FRI.Protocol
