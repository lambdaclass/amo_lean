/-
  AMO-Lean: FRI Cryptographic Hash Abstraction
  Phase 1 of Step 5.3 Migration

  This module defines the CryptoHash typeclass that abstracts cryptographic
  hash operations needed by FRI. It enables:
  1. Different fields to use different hash implementations
  2. Production (Poseidon2) vs testing (XOR) hash functions
  3. Domain separation for security

  Design Decisions:
  - Separate from FRIField: Hash algorithm is orthogonal to field arithmetic
  - Domain separation built-in: Prevents cross-protocol attacks
  - Uses DomainTag from Poseidon.DomainSeparation for unified tags

  Reference: docs/poseidon/ADR-009-step53-generic-field-migration.md
-/

import AmoLean.FRI.Fold
import AmoLean.Protocols.Poseidon.DomainSeparation

namespace AmoLean.FRI.Hash

open AmoLean.FRI.Fold (FRIField)
open AmoLean.Protocols.Poseidon.DomainSeparation (DomainTag)

/-! ## Part 1: CryptoHash Typeclass -/

/-- Typeclass for cryptographic hash operations used by FRI.

    This abstracts the hash function so that:
    - Production code can use Poseidon2 (cryptographically secure)
    - Tests can use XOR-based hash (fast, deterministic)

    Functions that need cryptographic hashing add `[CryptoHash F]` constraint.
-/
class CryptoHash (F : Type) where
  /-- 2-to-1 hash for Merkle tree nodes.
      hash2to1(left, right) produces a single field element.
  -/
  hash2to1 : F → F → F

  /-- Hash with domain separation tag.
      Prevents cross-protocol attacks by making different uses of the
      same hash function produce different outputs.
  -/
  hashWithDomain : DomainTag → F → F → F

  /-- Squeeze challenge from absorbed elements.
      Used by Fiat-Shamir transcript to derive pseudo-random challenges.
      `count` is the squeeze counter for multiple challenges.
  -/
  squeeze : List F → Nat → F

  /-- Multi-squeeze for deriving multiple challenges.
      More efficient than calling squeeze repeatedly.
      Returns `count` pseudo-random field elements.
  -/
  squeezeMany : List F → Nat → Nat → List F

  /-- Hash many elements into one (sponge construction).
      Default implementation uses foldl over hash2to1.
      Requires at least 2 elements (returns first element for singletons).
  -/
  hashMany : List F → Option F := fun xs =>
    match xs with
    | [] => none  -- Cannot hash empty list
    | [x] => some x  -- Single element: identity
    | x :: y :: rest => some (rest.foldl (fun acc elem => hash2to1 acc elem) (hash2to1 x y))

/-! ## Part 2: Convenience Functions -/

namespace CryptoHash

variable {F : Type} [CryptoHash F]

/-- Merkle tree hash with standard domain separation -/
def merkleHash (left right : F) : F :=
  hashWithDomain DomainTag.merkleTree2to1 left right

/-- FRI fold challenge derivation -/
def friFoldChallenge (commitment previousState : F) : F :=
  hashWithDomain DomainTag.friFold commitment previousState

/-- FRI query index derivation -/
def friQueryHash (seed index : F) : F :=
  hashWithDomain DomainTag.friQuery seed index

/-- FRI commitment hash -/
def friCommitHash (left right : F) : F :=
  hashWithDomain DomainTag.friCommit left right

end CryptoHash

/-! ## Part 3: Summary -/

def hashSummary : String :=
  "CryptoHash Typeclass (Step 5.3 Phase 1)
   ======================================

   1. Core Operations:
      - hash2to1: Merkle tree internal nodes
      - hashWithDomain: Domain-separated hashing
      - squeeze: Fiat-Shamir challenge derivation
      - squeezeMany: Multiple challenges efficiently

   2. Convenience Functions:
      - merkleHash: Standard Merkle with DomainTag.merkleTree2to1
      - friFoldChallenge: Fold challenge with DomainTag.friFold
      - friQueryHash: Query index with DomainTag.friQuery
      - friCommitHash: Commitment with DomainTag.friCommit

   3. Implementation Instances:
      - BN254: Uses Poseidon2 (cryptographically secure)
      - TestField: Uses XOR (fast, NOT secure)

   Usage: Functions needing crypto add [CryptoHash F] constraint:
   def buildMerkleTree [FRIField F] [CryptoHash F] (leaves : List F) : F"

#eval IO.println hashSummary

end AmoLean.FRI.Hash
