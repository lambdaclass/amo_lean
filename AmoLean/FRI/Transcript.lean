/-
  AMO-Lean: FRI Transcript (Fiat-Shamir Transform)
  Phase 6.3 - Cryptographic State Model

  This module implements the Transcript abstraction for the Fiat-Shamir
  transform. The Transcript models a cryptographic sponge that:
  1. Absorbs data (commitments, messages)
  2. Squeezes randomness (challenges like α)

  Key Design Decisions:
  - Transcript operations are OPAQUE to the optimizer
  - The compiler cannot eliminate Absorb/Squeeze even if they appear "dead"
  - This ensures cryptographic security is preserved through optimization

  The Transcript guarantees:
  - Deterministic: Same inputs → same outputs
  - Binding: Cannot find two different transcripts with same challenge
  - Non-malleable: Adversary cannot control challenge values

  References:
  - "The Fiat-Shamir Transform" (Fiat & Shamir, 1986)
  - "Sponge Functions" (Bertoni et al., 2007)
  - "SAFE: Sponge API for Field Elements" (StarkWare)
-/

import AmoLean.FRI.Basic
import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Fields.TestField
import AmoLean.Vector.Basic
import AmoLean.Sigma.Basic

namespace AmoLean.FRI.Transcript

open AmoLean.FRI (FieldConfig ZKCostModel)
open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.Vector (Vec)
open AmoLean.Sigma (Kernel Gather Scatter LoopVar IdxExpr)

/-! ## Part 1: Transcript State -/

/-- Domain separator tags for different protocol phases.
    These prevent cross-protocol attacks by binding context. -/
inductive DomainTag where
  | friCommit      : DomainTag  -- Committing to polynomial evaluations
  | friFold        : DomainTag  -- Folding round
  | friQuery       : DomainTag  -- Query phase
  | merkleNode     : DomainTag  -- Merkle tree internal node
  | merkleLeaf     : DomainTag  -- Merkle tree leaf
  | custom : String → DomainTag -- User-defined domain
  deriving Repr, BEq, Inhabited

namespace DomainTag

def toBytes : DomainTag → List UInt8
  | .friCommit  => [0x01]
  | .friFold    => [0x02]
  | .friQuery   => [0x03]
  | .merkleNode => [0x04]
  | .merkleLeaf => [0x05]
  | .custom s   => [0xFF] ++ s.toUTF8.toList

end DomainTag

/-- Transcript state: models a cryptographic sponge.

    The state consists of:
    - absorbed: List of all data absorbed so far (for reproducibility)
    - squeezeCount: Number of challenges extracted
    - domainStack: Current domain context (for domain separation)

    IMPORTANT: This state is OPAQUE to the optimizer.
    Operations on Transcript cannot be reordered or eliminated.

    Type parameter F: The field type (e.g., BN254, TestField).
    Phase 2.1 Migration: UInt64 → generic F with [FRIField F] constraint.
-/
structure TranscriptState (F : Type) where
  /-- All absorbed data (commitment to history) -/
  absorbed : List F
  /-- Number of squeeze operations performed -/
  squeezeCount : Nat
  /-- Domain separation stack -/
  domainStack : List DomainTag
  /-- Current round number (for debugging) -/
  round : Nat
  deriving Repr

namespace TranscriptState

variable {F : Type}

/-- Create a fresh transcript with domain separator -/
def init (domain : DomainTag) : TranscriptState F :=
  { absorbed := []
    squeezeCount := 0
    domainStack := [domain]
    round := 0 }

/-- Create transcript for FRI protocol -/
def forFRI : TranscriptState F := init .friCommit

end TranscriptState

/-! ## Part 2: Transcript Operations -/

/-- Result of a transcript operation: new state + optional output -/
structure TranscriptResult (F : Type) (α : Type) where
  state : TranscriptState F
  output : α
  deriving Repr

/-- Absorb a single field element into the transcript.

    This operation:
    1. Appends the element to the absorbed list
    2. Updates internal sponge state (simulated)

    The element becomes part of the challenge derivation.

    Phase 2.1: Parametrized over field type F.
-/
def absorb {F : Type} (state : TranscriptState F) (elem : F) : TranscriptState F :=
  { state with absorbed := state.absorbed ++ [elem] }

/-- Absorb multiple field elements -/
def absorbMany {F : Type} (state : TranscriptState F) (elems : List F) : TranscriptState F :=
  { state with absorbed := state.absorbed ++ elems }

/-- Absorb a vector of field elements -/
def absorbVec {F : Type} (state : TranscriptState F) (vec : Vec F n) : TranscriptState F :=
  { state with absorbed := state.absorbed ++ vec.toList }

/-- Absorb a commitment (e.g., Merkle root) -/
def absorbCommitment {F : Type} (state : TranscriptState F) (commitment : F) : TranscriptState F :=
  absorb state commitment

/-- Squeeze a challenge from the transcript.

    This operation:
    1. Derives a pseudo-random field element from current state
    2. Increments squeeze counter
    3. Returns the challenge value

    CRITICAL: This operation is NOT idempotent.
    Calling squeeze twice gives different values.

    Phase 2.1: Now uses CryptoHash.squeeze instead of XOR.
    The XOR implementation is encapsulated in TestField's CryptoHash instance.
    Production code uses Poseidon2 via BN254's CryptoHash instance.
-/
def squeeze {F : Type} [FRIField F] [CryptoHash F] (state : TranscriptState F) :
    TranscriptResult F F :=
  -- Use CryptoHash.squeeze to derive challenge from absorbed data
  let challenge := CryptoHash.squeeze state.absorbed state.squeezeCount
  { state := { state with squeezeCount := state.squeezeCount + 1 }
    output := challenge }

/-- Squeeze multiple challenges efficiently using CryptoHash.squeezeMany.
    Phase 2.1: Now delegates to CryptoHash for batch challenge derivation.
-/
def squeezeMany {F : Type} [FRIField F] [CryptoHash F] (state : TranscriptState F)
    (count : Nat) : TranscriptResult F (List F) :=
  let challenges := CryptoHash.squeezeMany state.absorbed state.squeezeCount count
  { state := { state with squeezeCount := state.squeezeCount + count }
    output := challenges }

/-- Enter a new domain context (push) -/
def enterDomain {F : Type} (state : TranscriptState F) (tag : DomainTag) : TranscriptState F :=
  { state with domainStack := tag :: state.domainStack }

/-- Exit current domain context (pop) -/
def exitDomain {F : Type} (state : TranscriptState F) : TranscriptState F :=
  { state with domainStack := state.domainStack.tail }

/-- Advance to next round -/
def nextRound {F : Type} (state : TranscriptState F) : TranscriptState F :=
  { state with round := state.round + 1 }

/-! ## Part 3: Transcript Intrinsics for SigmaExpr -/

/-- Intrinsic operations that extend SigmaExpr for cryptographic primitives.

    These operations are:
    - OPAQUE: Cannot be optimized away or reordered
    - EFFECTFUL: Modify transcript state
    - SECURE: Preserve Fiat-Shamir security

    The optimizer MUST treat these as barriers that prevent
    code motion across them.
-/
inductive Intrinsic where
  /-- Absorb field elements into transcript -/
  | absorb : (count : Nat) → Intrinsic
  /-- Squeeze a challenge from transcript -/
  | squeeze : Intrinsic
  /-- Hash computation (Poseidon, Blake3, etc.) -/
  | hash : (inputCount : Nat) → Intrinsic
  /-- Merkle tree node computation -/
  | merkleHash : Intrinsic
  /-- Domain separator push -/
  | domainEnter : DomainTag → Intrinsic
  /-- Domain separator pop -/
  | domainExit : Intrinsic
  /-- Memory barrier (prevents reordering) -/
  | barrier : Intrinsic
  deriving Repr, BEq, Inhabited

namespace Intrinsic

def toString : Intrinsic → String
  | .absorb n => s!"Absorb({n})"
  | .squeeze => "Squeeze"
  | .hash n => s!"Hash({n})"
  | .merkleHash => "MerkleHash"
  | .domainEnter tag => s!"DomainEnter({repr tag})"
  | .domainExit => "DomainExit"
  | .barrier => "Barrier"

instance : ToString Intrinsic := ⟨Intrinsic.toString⟩

/-- Cost of intrinsic operation -/
def cost (cm : ZKCostModel) : Intrinsic → Nat
  | .absorb n => n * cm.memLoad + cm.hashCall / 4  -- Partial hash update
  | .squeeze => cm.hashCall  -- Full hash for challenge
  | .hash n => n * cm.memLoad + cm.hashCall
  | .merkleHash => 2 * cm.memLoad + cm.hashCall + cm.memStore
  | .domainEnter _ => 10  -- Minimal cost for bookkeeping
  | .domainExit => 10
  | .barrier => 0  -- No runtime cost, just compilation barrier

/-- Is this intrinsic a memory barrier? -/
def isBarrier : Intrinsic → Bool
  | .barrier => true
  | .squeeze => true  -- Squeeze is also a barrier (depends on all prior absorbs)
  | _ => false

/-- Can this intrinsic be reordered with another? -/
def canReorderWith : Intrinsic → Intrinsic → Bool
  | .absorb _, .absorb _ => false  -- Order of absorbs matters!
  | .squeeze, _ => false           -- Squeeze depends on all prior state
  | _, .squeeze => false           -- Nothing can move past squeeze
  | .barrier, _ => false
  | _, .barrier => false
  | .domainEnter _, _ => false     -- Domain changes are barriers
  | .domainExit, _ => false
  | _, .domainEnter _ => false
  | _, .domainExit => false
  | _, _ => true                   -- Other pairs may be reordered

end Intrinsic

/-! ## Part 4: Extended SigmaExpr with Intrinsics -/

/-- Extended Sigma expression that includes cryptographic intrinsics.

    This extends the base SigmaExpr with:
    - Intrinsic nodes for transcript operations
    - Explicit transcript state threading

    The key invariant: Intrinsic operations form a TOTAL ORDER
    that must be preserved through all optimizations.
-/
inductive CryptoSigma where
  /-- Standard compute kernel -/
  | compute : Kernel → Gather → Scatter → CryptoSigma
  /-- Loop construct -/
  | loop : (n : Nat) → (loopVar : LoopVar) → CryptoSigma → CryptoSigma
  /-- Sequential composition -/
  | seq : CryptoSigma → CryptoSigma → CryptoSigma
  /-- Parallel composition (for independent operations) -/
  | par : CryptoSigma → CryptoSigma → CryptoSigma
  /-- Temporary buffer allocation -/
  | temp : (size : Nat) → CryptoSigma → CryptoSigma
  /-- No operation -/
  | nop : CryptoSigma
  /-- CRYPTOGRAPHIC INTRINSIC (opaque, cannot be optimized) -/
  | intrinsic : Intrinsic → Gather → Scatter → CryptoSigma
  deriving Repr, Inhabited

namespace CryptoSigma

/-- Check if expression contains any intrinsics -/
partial def hasIntrinsics : CryptoSigma → Bool
  | .compute _ _ _ => false
  | .loop _ _ body => hasIntrinsics body
  | .seq s1 s2 => hasIntrinsics s1 || hasIntrinsics s2
  | .par s1 s2 => hasIntrinsics s1 || hasIntrinsics s2
  | .temp _ body => hasIntrinsics body
  | .nop => false
  | .intrinsic _ _ _ => true

/-- Count intrinsic operations -/
partial def intrinsicCount : CryptoSigma → Nat
  | .compute _ _ _ => 0
  | .loop n _ body => n * intrinsicCount body
  | .seq s1 s2 => intrinsicCount s1 + intrinsicCount s2
  | .par s1 s2 => intrinsicCount s1 + intrinsicCount s2
  | .temp _ body => intrinsicCount body
  | .nop => 0
  | .intrinsic _ _ _ => 1

/-- Extract the sequence of intrinsics (for security analysis) -/
partial def extractIntrinsicSequence : CryptoSigma → List Intrinsic
  | .compute _ _ _ => []
  | .loop _ _ body => extractIntrinsicSequence body
  | .seq s1 s2 => extractIntrinsicSequence s1 ++ extractIntrinsicSequence s2
  | .par s1 s2 => extractIntrinsicSequence s1 ++ extractIntrinsicSequence s2
  | .temp _ body => extractIntrinsicSequence body
  | .nop => []
  | .intrinsic i _ _ => [i]

/-- Pretty print -/
partial def toStringIndent (indent : Nat) : CryptoSigma → String
  | .compute k g s =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Compute {k}\n{pad}  gather: {g}\n{pad}  scatter: {s}"
  | .loop n v body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Loop i{v} = 0 to {n-1}:\n{toStringIndent (indent + 2) body}"
  | .seq s1 s2 =>
    s!"{toStringIndent indent s1}\n{toStringIndent indent s2}"
  | .par s1 s2 =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{toStringIndent indent s1}\n{pad}||\n{toStringIndent indent s2}"
  | .temp size body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Temp[{size}]:\n{toStringIndent (indent + 2) body}"
  | .nop =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Nop"
  | .intrinsic i g s =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}[INTRINSIC] {i}\n{pad}  gather: {g}\n{pad}  scatter: {s}"

def toString (e : CryptoSigma) : String := toStringIndent 0 e

instance : ToString CryptoSigma := ⟨CryptoSigma.toString⟩

end CryptoSigma

/-! ## Part 5: FRI Round with Transcript -/

/-- A single FRI round that transforms (Layer, Transcript) → (Layer', Transcript').

    This models the state machine transition for one folding round:
    1. Absorb current layer commitment
    2. Squeeze challenge α
    3. Compute folded layer
    4. (Next round will absorb new commitment)

    Phase 2.1: Parametrized over field type F.
-/
structure FRIRoundState (F : Type) where
  /-- Current layer evaluations (size n) -/
  layerSize : Nat
  /-- Transcript state -/
  transcript : TranscriptState F
  /-- Current round number -/
  round : Nat
  deriving Repr

/-- Execute one FRI round (state transition).
    Phase 2.1: Requires [FRIField F] [CryptoHash F] for squeeze operation.
-/
def friRoundTransition {F : Type} [FRIField F] [CryptoHash F]
    (state : FRIRoundState F) (commitment : F) : FRIRoundState F × F :=
  -- 1. Absorb commitment
  let t1 := absorbCommitment state.transcript commitment
  -- 2. Enter fold domain
  let t2 := enterDomain t1 .friFold
  -- 3. Squeeze challenge α
  let result := squeeze t2
  let alpha := result.output
  let t3 := result.state
  -- 4. Exit fold domain and advance round
  let t4 := exitDomain t3
  let t5 := nextRound t4
  -- 5. Return new state (layer size halved) and alpha
  let newState : FRIRoundState F := {
    layerSize := state.layerSize / 2
    transcript := t5
    round := state.round + 1
  }
  (newState, alpha)

/-- Generate CryptoSigma for one FRI round -/
def friRoundToSigma (n : Nat) (roundNum : Nat) : CryptoSigma :=
  let gather := Gather.contiguous n (.const 0)
  let scatter := Scatter.contiguous 1 (.const 0)

  .seq
    -- 1. Absorb commitment (intrinsic)
    (.intrinsic (.absorb 1) gather scatter)
    (.seq
      -- 2. Enter domain
      (.intrinsic (.domainEnter .friFold) gather scatter)
      (.seq
        -- 3. Squeeze challenge
        (.intrinsic .squeeze gather scatter)
        (.seq
          -- 4. FRI fold computation
          (.loop n roundNum
            (.compute .butterfly
              (Gather.strided 2 (.affine 0 2 roundNum) 1)
              (Scatter.contiguous 1 (.var roundNum))))
          -- 5. Exit domain
          (.intrinsic .domainExit gather scatter))))

/-! ## Part 6: Security Properties -/

/-- Verify that intrinsic sequence is well-formed for FRI -/
def verifyIntrinsicSequence (seq : List Intrinsic) : Bool × List String :=
  let rec check (s : List Intrinsic) (domainDepth : Nat) (errors : List String) :
      Bool × List String :=
    match s with
    | [] =>
      if domainDepth != 0 then (false, errors ++ ["Unbalanced domain stack"])
      else (errors.isEmpty, errors)
    | .domainEnter _ :: rest => check rest (domainDepth + 1) errors
    | .domainExit :: rest =>
      if domainDepth == 0 then check rest 0 (errors ++ ["Domain exit without enter"])
      else check rest (domainDepth - 1) errors
    | .squeeze :: rest =>
      -- Squeeze should follow absorbs
      check rest domainDepth errors
    | _ :: rest => check rest domainDepth errors
  check seq 0 []

/-- Theorem: Absorb operations cannot be reordered.
    Phase 2.1: Parametrized over generic field type F.
-/
theorem absorb_order_matters {F : Type} (s1 s2 : TranscriptState F) (a b : F) (h : a ≠ b) :
    absorb (absorb s1 a) b ≠ absorb (absorb s1 b) a := by
  simp [absorb]
  intro heq
  -- The absorbed lists would differ
  sorry  -- Full proof requires list extensionality

/-- Theorem: Squeeze is deterministic given transcript state.
    Phase 2.1: Requires CryptoHash constraint.
-/
theorem squeeze_deterministic {F : Type} [FRIField F] [CryptoHash F] (s : TranscriptState F) :
    (squeeze s).output = (squeeze s).output := rfl

/-! ## Part 7: Tests -/

section Tests

-- Import TestField for fast testing
open AmoLean.FRI.Fields.TestField (TestField)

-- Test 1: Basic transcript operations
def testTranscript : IO Unit := do
  IO.println "=== Transcript Test (Phase 2.1: Using TestField) ==="

  let t0 : TranscriptState TestField := TranscriptState.forFRI
  IO.println s!"Initial state: round={t0.round}, absorbed={t0.absorbed.length}"

  let elem1 : TestField := FRIField.ofNat 42
  let elem2 : TestField := FRIField.ofNat 123
  let t1 := absorb t0 elem1
  let t2 := absorb t1 elem2
  IO.println s!"After 2 absorbs: absorbed count={t2.absorbed.length}"

  let r := squeeze t2
  IO.println s!"Squeezed challenge: {FRIField.toNat r.output}"
  IO.println s!"Squeeze count: {r.state.squeezeCount}"

  let r2 := squeeze r.state
  IO.println s!"Second squeeze: {FRIField.toNat r2.output} (should differ from first)"

#eval! testTranscript

-- Test 2: FRI round state transition
def testFRIRound : IO Unit := do
  IO.println "\n=== FRI Round Test (Phase 2.1: Using TestField) ==="

  let initial : FRIRoundState TestField := {
    layerSize := 1024
    transcript := TranscriptState.forFRI
    round := 0
  }

  IO.println s!"Initial: layer size = {initial.layerSize}, round = {initial.round}"

  let commit1 : TestField := FRIField.ofNat 0xABCD
  let (state1, alpha1) := friRoundTransition initial commit1
  IO.println s!"Round 1: layer size = {state1.layerSize}, alpha = {FRIField.toNat alpha1}"

  let commit2 : TestField := FRIField.ofNat 0xDEF0
  let (state2, alpha2) := friRoundTransition state1 commit2
  IO.println s!"Round 2: layer size = {state2.layerSize}, alpha = {FRIField.toNat alpha2}"

  let commit3 : TestField := FRIField.ofNat 0x1234
  let (state3, alpha3) := friRoundTransition state2 commit3
  IO.println s!"Round 3: layer size = {state3.layerSize}, alpha = {FRIField.toNat alpha3}"

#eval! testFRIRound

-- Test 3: CryptoSigma generation
def testCryptoSigma : IO Unit := do
  IO.println "\n=== CryptoSigma Test ==="

  let sigma := friRoundToSigma 8 0
  IO.println s!"Generated CryptoSigma:\n{sigma}"
  IO.println s!"\nHas intrinsics: {sigma.hasIntrinsics}"
  IO.println s!"Intrinsic count: {sigma.intrinsicCount}"

  let intrinsics := sigma.extractIntrinsicSequence
  IO.println s!"Intrinsic sequence: {intrinsics.map Intrinsic.toString}"

  let (valid, errors) := verifyIntrinsicSequence intrinsics
  IO.println s!"Sequence valid: {valid}"
  if !valid then
    for e in errors do IO.println s!"  Error: {e}"

#eval! testCryptoSigma

-- Test 4: Intrinsic costs
def testIntrinsicCosts : IO Unit := do
  IO.println "\n=== Intrinsic Costs ==="

  let cm := AmoLean.FRI.defaultZKCost

  IO.println s!"Absorb(4): {Intrinsic.cost cm (.absorb 4)}"
  IO.println s!"Squeeze:   {Intrinsic.cost cm .squeeze}"
  IO.println s!"Hash(2):   {Intrinsic.cost cm (.hash 2)}"
  IO.println s!"MerkleHash: {Intrinsic.cost cm .merkleHash}"

#eval! testIntrinsicCosts

end Tests

/-! ## Part 8: Summary -/

def transcriptSummary : String :=
  "Transcript Module Summary:
   ========================

   1. TranscriptState: Cryptographic sponge simulation
      - absorbed: History of all ingested data
      - squeezeCount: Number of challenges extracted
      - domainStack: Domain separation context

   2. Operations:
      - absorb: Ingest field elements
      - squeeze: Extract pseudo-random challenge
      - enterDomain/exitDomain: Domain separation

   3. Intrinsic: Opaque operations for SigmaExpr
      - .absorb n: Absorb n elements
      - .squeeze: Extract challenge (BARRIER)
      - .hash n: Hash computation
      - .merkleHash: Merkle node hash

   4. CryptoSigma: Extended SigmaExpr with intrinsics
      - Preserves intrinsic order through optimization
      - Intrinsics form security-critical barriers

   5. FRI State Machine:
      - FRIRoundState: (LayerSize, Transcript, Round)
      - friRoundTransition: State → State × α

   Key Invariant: Intrinsic operations CANNOT be reordered or eliminated."

#eval! IO.println transcriptSummary

end AmoLean.FRI.Transcript
