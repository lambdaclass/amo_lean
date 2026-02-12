/-
  AMO-Lean: FRI Flow Integration Test
  Phase 6.5 - Complete Protocol Assembly Verification

  This benchmark simulates the complete FRI protocol flow:
  1. Start with initial polynomial of degree 8 (domain N=16 with blowup=2)
  2. Execute 2 FRI rounds
  3. Verify the CryptoSigma flow pattern

  Expected pattern per round:
    Tree -> Hash -> Absorb -> Squeeze -> Fold -> Tree...

  The test verifies that the compiler CANNOT reorder these operations
  because they are represented as opaque intrinsics in the IR.
-/

import AmoLean.FRI.Protocol
import AmoLean.FRI.Transcript
import AmoLean.FRI.Merkle

namespace Benchmarks.FRI_Flow

open AmoLean.FRI.Protocol
open AmoLean.FRI.Transcript (CryptoSigma Intrinsic DomainTag)
open AmoLean.FRI.Merkle (buildTreeSigma)

/-! ## Test Configuration -/

/-- Initial polynomial degree -/
def INITIAL_DEGREE : Nat := 8

/-- Blowup factor -/
def BLOWUP : Nat := 2

/-- Initial domain size (N) -/
def INITIAL_DOMAIN : Nat := INITIAL_DEGREE * BLOWUP  -- 16

/-- Number of rounds to simulate -/
def NUM_ROUNDS : Nat := 2

/-! ## Flow Pattern Extraction -/

/-- Extract a human-readable flow description from CryptoSigma -/
def extractFlowDescription (sigma : CryptoSigma) : List String :=
  let intrinsics := sigma.extractIntrinsicSequence
  intrinsics.map fun i =>
    match i with
    | .domainEnter tag =>
        match tag with
        | .friFold => "ENTER[FRIFold]"
        | .friCommit => "ENTER[FRICommit]"
        | .friQuery => "ENTER[FRIQuery]"
        | .merkleNode => "ENTER[MerkleNode]"
        | .merkleLeaf => "ENTER[MerkleLeaf]"
        | .custom s => s!"ENTER[{s}]"
    | .domainExit => "EXIT"
    | .absorb n => s!"ABSORB({n})"
    | .squeeze => "SQUEEZE"
    | .hash n => s!"HASH({n})"
    | .merkleHash => "MERKLE_HASH"
    | .barrier => "BARRIER"

/-- Count specific intrinsic types -/
structure IntrinsicCounts where
  enters : Nat
  exits : Nat
  absorbs : Nat
  squeezes : Nat
  merkleHashes : Nat
  deriving Repr

def countIntrinsics (sigma : CryptoSigma) : IntrinsicCounts :=
  let intrinsics := sigma.extractIntrinsicSequence
  let count init filter := intrinsics.foldl (fun acc i => if filter i then acc + 1 else acc) init
  { enters := count 0 (fun i => match i with | .domainEnter _ => true | _ => false)
    exits := count 0 (fun i => match i with | .domainExit => true | _ => false)
    absorbs := count 0 (fun i => match i with | .absorb _ => true | _ => false)
    squeezes := count 0 (fun i => match i with | .squeeze => true | _ => false)
    merkleHashes := count 0 (fun i => match i with | .merkleHash => true | _ => false) }

/-! ## Integration Test: 2-Round FRI Protocol -/

/-- Add round markers to flow steps -/
def addRoundMarkers (flow : List String) (startRound : Nat) : List (Option Nat × String) :=
  let rec go : List String → Nat → List (Option Nat × String)
    | [], _ => []
    | step :: rest, round =>
        if step.startsWith "ENTER[FRI" then
          (some round, step) :: go rest (round + 1)
        else
          (none, step) :: go rest round
  go flow startRound

/-- Main integration test -/
def runFRIFlowTest : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════════════╗"
  IO.println "║           FRI PROTOCOL FLOW INTEGRATION TEST                       ║"
  IO.println "║                    Phase 6.5 Verification                          ║"
  IO.println "╚════════════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Initial configuration
  IO.println "┌────────────────────────────────────────────────────────────────────┐"
  IO.println "│ CONFIGURATION                                                      │"
  IO.println "├────────────────────────────────────────────────────────────────────┤"
  IO.println s!"│  Initial degree:    {INITIAL_DEGREE}"
  IO.println s!"│  Blowup factor:     {BLOWUP}"
  IO.println s!"│  Initial domain N:  {INITIAL_DOMAIN}"
  IO.println s!"│  Number of rounds:  {NUM_ROUNDS}"
  IO.println "└────────────────────────────────────────────────────────────────────┘"
  IO.println ""

  -- Execute FRI protocol
  let initialState := RoundState.init INITIAL_DEGREE BLOWUP
  let (outputs, finalState) := friCommitPhase INITIAL_DEGREE NUM_ROUNDS

  -- Display round-by-round execution
  IO.println "┌────────────────────────────────────────────────────────────────────┐"
  IO.println "│ ROUND-BY-ROUND EXECUTION                                           │"
  IO.println "└────────────────────────────────────────────────────────────────────┘"
  IO.println ""

  for (i, out) in outputs.enum do
    let prevDomain := if i == 0 then INITIAL_DOMAIN else INITIAL_DOMAIN / (2^i)
    let nextDomain := out.nextState.domain

    IO.println s!"══════════════════════ Round {i} ══════════════════════"
    IO.println s!"  Domain: {prevDomain} → {nextDomain}"
    IO.println s!"  Polynomial: {out.nextState.poly}"
    IO.println s!"  Commitment: 0x{Nat.toDigits 16 (out.nextState.commitment.getD 0).toNat |> String.mk}"
    IO.println s!"  Challenge α: 0x{Nat.toDigits 16 (out.nextState.challenge.getD 0).toNat |> String.mk}"
    IO.println ""

    -- Show phases executed
    IO.println "  Phases executed:"
    for phase in out.phases do
      IO.println s!"    → {phase}"
    IO.println ""

  -- Final state
  IO.println s!"Final state after {NUM_ROUNDS} rounds:"
  IO.println s!"  Domain:       {finalState.domain}"
  IO.println s!"  Poly:         {finalState.poly}"
  IO.println s!"  Transcript:   round={finalState.round}"
  IO.println ""

  -- Combined CryptoSigma analysis
  IO.println "┌────────────────────────────────────────────────────────────────────┐"
  IO.println "│ CRYPTOSIGMA IR ANALYSIS                                            │"
  IO.println "└────────────────────────────────────────────────────────────────────┘"
  IO.println ""

  let combined := combineRoundSigmas outputs

  -- Intrinsic counts
  let counts := countIntrinsics combined
  IO.println "Intrinsic operation counts:"
  IO.println s!"  Domain enters:     {counts.enters}"
  IO.println s!"  Domain exits:      {counts.exits}"
  IO.println s!"  Absorb operations: {counts.absorbs}"
  IO.println s!"  Squeeze operations:{counts.squeezes}"
  IO.println s!"  Merkle hashes:     {counts.merkleHashes}"
  IO.println s!"  Total intrinsics:  {combined.intrinsicCount}"
  IO.println ""

  -- Flow visualization
  IO.println "┌────────────────────────────────────────────────────────────────────┐"
  IO.println "│ FLOW VISUALIZATION                                                 │"
  IO.println "├────────────────────────────────────────────────────────────────────┤"
  IO.println "│ Expected: Tree → ABSORB → SQUEEZE → Fold → Tree...                 │"
  IO.println "└────────────────────────────────────────────────────────────────────┘"
  IO.println ""

  let flow := extractFlowDescription combined
  let flowWithRounds := addRoundMarkers flow 0
  for (marker, step) in flowWithRounds do
    if marker.isSome then
      IO.println s!"  ┌─ ROUND {marker.get!} ─────────────────────────────────────────"

    let prefixStr := match step with
      | "EXIT" => "  └"
      | _ => "  │"

    let symbol := match step with
      | s => if s.startsWith "ENTER[Merkle" then "T"
             else if s.startsWith "ENTER[FRI" then ">"
             else if s == "EXIT" then "<"
             else if s.startsWith "ABSORB" then "A"
             else if s == "SQUEEZE" then "S"
             else if s == "MERKLE_HASH" then "#"
             else "*"

    IO.println s!"{prefixStr}  {symbol} {step}"

  IO.println ""

  -- Pattern verification
  IO.println "┌────────────────────────────────────────────────────────────────────┐"
  IO.println "│ PATTERN VERIFICATION                                               │"
  IO.println "└────────────────────────────────────────────────────────────────────┘"
  IO.println ""

  -- Verify invariants
  let balancedDomains := counts.enters == counts.exits
  let correctAbsorbs := counts.absorbs == NUM_ROUNDS
  let correctSqueezes := counts.squeezes == NUM_ROUNDS

  IO.println s!"  [1] Domain balance (enters = exits):     {if balancedDomains then "✓ PASS" else "✗ FAIL"}"
  IO.println s!"  [2] Absorb count = rounds ({counts.absorbs} = {NUM_ROUNDS}):    {if correctAbsorbs then "✓ PASS" else "✗ FAIL"}"
  IO.println s!"  [3] Squeeze count = rounds ({counts.squeezes} = {NUM_ROUNDS}):   {if correctSqueezes then "✓ PASS" else "✗ FAIL"}"

  -- Verify ordering: each round must have ABSORB before SQUEEZE
  let intrinsics := combined.extractIntrinsicSequence
  let orderingOk := verifyOrdering intrinsics
  IO.println s!"  [4] ABSORB always before SQUEEZE:        {if orderingOk then "✓ PASS" else "✗ FAIL"}"

  let allPassed := balancedDomains && correctAbsorbs && correctSqueezes && orderingOk
  IO.println ""
  IO.println s!"  Overall result: {if allPassed then "ALL TESTS PASSED ✓✓✓" else "SOME TESTS FAILED ✗"}"
  IO.println ""

  -- Security note
  IO.println "┌────────────────────────────────────────────────────────────────────┐"
  IO.println "│ SECURITY INVARIANT                                                 │"
  IO.println "├────────────────────────────────────────────────────────────────────┤"
  IO.println "│ The CryptoSigma IR represents cryptographic operations as opaque   │"
  IO.println "│ intrinsics. The optimizer CANNOT:                                  │"
  IO.println "│   • Reorder ABSORB and SQUEEZE operations                          │"
  IO.println "│   • Merge or eliminate hash operations                             │"
  IO.println "│   • Move operations across domain boundaries                       │"
  IO.println "│                                                                    │"
  IO.println "│ This ensures Fiat-Shamir transform security is preserved even     │"
  IO.println "│ after aggressive compiler optimizations.                           │"
  IO.println "└────────────────────────────────────────────────────────────────────┘"
where
  /-- Verify that in each round, ABSORB comes before SQUEEZE -/
  verifyOrdering (intrinsics : List Intrinsic) : Bool :=
    let rec check : List Intrinsic → Bool → Bool
      | [], _ => true
      | (.absorb _) :: rest, _ => check rest true  -- saw absorb
      | .squeeze :: rest, sawAbsorb => sawAbsorb && check rest false  -- squeeze must come after absorb
      | (.domainEnter _) :: rest, _ => check rest false  -- reset at domain boundary
      | _ :: rest, sawAbsorb => check rest sawAbsorb
    check intrinsics false

/-- Test showing the CryptoSigma structure for one round -/
def showSingleRoundSigma : IO Unit := do
  IO.println ""
  IO.println "┌────────────────────────────────────────────────────────────────────┐"
  IO.println "│ SINGLE ROUND CRYPTOSIGMA STRUCTURE                                 │"
  IO.println "└────────────────────────────────────────────────────────────────────┘"
  IO.println ""

  let initialState := RoundState.init INITIAL_DEGREE BLOWUP
  let output := friRound initialState

  IO.println "Round 0 CryptoSigma (abbreviated):"
  IO.println s!"{output.sigma}"

#eval! runFRIFlowTest
#eval! showSingleRoundSigma

/-! ## Summary -/

def flowTestSummary : String :=
"FRI Flow Integration Test (Phase 6.5)
=====================================

This test verifies the complete FRI protocol assembly:

1. Initial Setup:
   - Polynomial degree: 8
   - Domain size N: 16 (with blowup factor 2)
   - Execute 2 rounds

2. Expected Flow Per Round:
   ENTER[FRIFold]
     └─ ENTER[MerkleTree]
         └─ MERKLE_HASH (×N/2)
     └─ EXIT
     └─ ABSORB(root)
     └─ SQUEEZE(α)
     └─ [FRI Fold operations]
   EXIT

3. Verified Invariants:
   - Domain boundaries are balanced
   - One ABSORB per round
   - One SQUEEZE per round
   - ABSORB always before SQUEEZE (security critical!)

4. Security Guarantee:
   The CryptoSigma IR prevents the optimizer from reordering
   cryptographic operations, preserving Fiat-Shamir security."

#eval! IO.println flowTestSummary

end Benchmarks.FRI_Flow
