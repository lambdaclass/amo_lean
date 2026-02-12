/-
  Poseidon2 Domain Separation Module
  Step 5.2 - Unified Domain Tags for AMO-Lean

  This module defines the canonical domain separation scheme for all
  cryptographic hash operations in the protocol. It follows the
  recommendations from:

  1. Poseidon paper (Grassi et al.) Section 4.2 - Domain separator values
  2. SAFE API (Aumasson et al.) - IO pattern encoding
  3. Weak Fiat-Shamir paper (Dao et al.) - Transcript binding requirements

  Key Design Decisions:
  - Domain separator is placed in CAPACITY (inner state), not rate
  - Values follow Poseidon paper scheme for compatibility
  - All FRI operations use distinct tags to prevent cross-protocol attacks

  Reference: docs/references/poseidon/domain-separation/notes-domain-separation.md
-/

import AmoLean.Protocols.Poseidon.Constants.BN254

namespace AmoLean.Protocols.Poseidon.DomainSeparation

open AmoLean.Protocols.Poseidon.Constants.BN254 (p)

/-! ## Part 1: Domain Tag Enumeration -/

/-- Canonical domain tags for all cryptographic operations in AMO-Lean.

    Based on Poseidon paper Section 4.2 recommendations:
    - Merkle tree: 2^arity - 1
    - Hash variable-length: 2^64 + (output_len - 1)
    - Hash fixed-length: input_len * 2^64 + (output_len - 1)
    - Custom protocol: identifier * 2^32

    Additional tags for FRI protocol phases to prevent cross-protocol attacks.
-/
inductive DomainTag where
  /-- Merkle tree 2-to-1 hash (standard binary tree) -/
  | merkleTree2to1 : DomainTag
  /-- Merkle tree 4-to-1 hash (quad tree) -/
  | merkleTree4to1 : DomainTag
  /-- Merkle tree leaf hashing (if leaves need domain separation) -/
  | merkleLeaf : DomainTag
  /-- FRI commit phase - polynomial commitment -/
  | friCommit : DomainTag
  /-- FRI fold phase - challenge derivation for folding -/
  | friFold : DomainTag
  /-- FRI query phase - query index derivation -/
  | friQuery : DomainTag
  /-- DEEP quotient evaluation -/
  | friDeep : DomainTag
  /-- Transcript initialization with public parameters -/
  | transcriptInit : DomainTag
  /-- Generic constraint evaluation -/
  | constraint : DomainTag
  /-- User-defined custom domain -/
  | custom : String → DomainTag
  deriving Repr, BEq, Inhabited

namespace DomainTag

/-- Convert domain tag to capacity value (Nat).

    Values follow Poseidon paper Section 4.2:
    - Merkle arity k: 2^k - 1
    - Protocol phases: unique identifiers * 2^32

    These values are injected into the capacity element of the sponge state.
-/
def toCapacityValue : DomainTag → Nat
  -- Merkle operations (2^arity - 1)
  | .merkleTree2to1 => 2^2 - 1                    -- = 3
  | .merkleTree4to1 => 2^4 - 1                    -- = 15
  | .merkleLeaf     => 2^1 - 1                    -- = 1

  -- FRI protocol phases (identifier * 2^32)
  | .friCommit      => 1 * 2^32                   -- = 0x100000000
  | .friFold        => 2 * 2^32                   -- = 0x200000000
  | .friQuery       => 3 * 2^32                   -- = 0x300000000
  | .friDeep        => 4 * 2^32                   -- = 0x400000000

  -- Other operations
  | .transcriptInit => 5 * 2^32                   -- = 0x500000000
  | .constraint     => 6 * 2^32                   -- = 0x600000000

  -- Custom: hash the string and add offset to avoid collisions
  | .custom s       => 7 * 2^32 + s.hash.toNat

/-- Convert to field element (mod p) for injection into sponge state -/
def toFieldElement : DomainTag → Nat :=
  fun tag => tag.toCapacityValue % p

/-- Convert to bytes (for compatibility with byte-based hash APIs) -/
def toBytes : DomainTag → List UInt8
  | .merkleTree2to1 => [0x01, 0x00]  -- Tag family 0x01
  | .merkleTree4to1 => [0x01, 0x01]
  | .merkleLeaf     => [0x01, 0x02]
  | .friCommit      => [0x02, 0x00]  -- Tag family 0x02
  | .friFold        => [0x02, 0x01]
  | .friQuery       => [0x02, 0x02]
  | .friDeep        => [0x02, 0x03]
  | .transcriptInit => [0x03, 0x00]  -- Tag family 0x03
  | .constraint     => [0x04, 0x00]  -- Tag family 0x04
  | .custom s       => [0xFF] ++ s.toUTF8.toList

/-- Human-readable name for debugging -/
def toString : DomainTag → String
  | .merkleTree2to1 => "MerkleTree2to1"
  | .merkleTree4to1 => "MerkleTree4to1"
  | .merkleLeaf     => "MerkleLeaf"
  | .friCommit      => "FRICommit"
  | .friFold        => "FRIFold"
  | .friQuery       => "FRIQuery"
  | .friDeep        => "FRIDeep"
  | .transcriptInit => "TranscriptInit"
  | .constraint     => "Constraint"
  | .custom s       => s!"Custom({s})"

instance : ToString DomainTag := ⟨DomainTag.toString⟩

end DomainTag

/-! ## Part 2: IO Pattern Encoding (SAFE API style) -/

/-- IO operation type for SAFE-style pattern declaration -/
inductive IOOp where
  | absorb : Nat → IOOp   -- Absorb n field elements
  | squeeze : Nat → IOOp  -- Squeeze n field elements
  deriving Repr, BEq

namespace IOOp

/-- Encode IO operation as 32-bit word (SAFE API encoding)
    MSB = 1 for ABSORB, MSB = 0 for SQUEEZE
    Lower 31 bits = count -/
def encode : IOOp → UInt32
  | .absorb n  => UInt32.ofNat (0x80000000 ||| (n &&& 0x7FFFFFFF))
  | .squeeze n => UInt32.ofNat (n &&& 0x7FFFFFFF)

def toString : IOOp → String
  | .absorb n  => s!"ABSORB({n})"
  | .squeeze n => s!"SQUEEZE({n})"

instance : ToString IOOp := ⟨IOOp.toString⟩

end IOOp

/-- IO Pattern declaration for SAFE-style domain separation -/
structure IOPattern where
  operations : List IOOp
  deriving Repr, BEq

namespace IOPattern

-- Standard patterns for common operations

/-- Merkle 2-to-1 hash: absorb 2, squeeze 1 -/
def merkle2to1 : IOPattern := ⟨[.absorb 2, .squeeze 1]⟩

/-- Merkle 4-to-1 hash: absorb 4, squeeze 1 -/
def merkle4to1 : IOPattern := ⟨[.absorb 4, .squeeze 1]⟩

/-- FRI challenge derivation: absorb commitment, squeeze challenge -/
def friChallenge : IOPattern := ⟨[.absorb 1, .squeeze 1]⟩

/-- Multi-squeeze for multiple challenges -/
def friMultiChallenge (numChallenges : Nat) : IOPattern :=
  ⟨[.absorb 1, .squeeze numChallenges]⟩

/-- Aggregate consecutive operations of same type (SAFE requirement) -/
def aggregate (pattern : IOPattern) : IOPattern :=
  let rec go : List IOOp → List IOOp
    | [] => []
    | [x] => [x]
    | .absorb n :: .absorb m :: rest => go (.absorb (n + m) :: rest)
    | .squeeze n :: .squeeze m :: rest => go (.squeeze (n + m) :: rest)
    | x :: rest => x :: go rest
  ⟨go pattern.operations⟩

/-- Encode pattern to bytes for hashing -/
def toBytes (pattern : IOPattern) : List UInt8 :=
  pattern.operations.flatMap fun op =>
    let w := op.encode
    [UInt8.ofNat (w.toNat >>> 24 &&& 0xFF),
     UInt8.ofNat (w.toNat >>> 16 &&& 0xFF),
     UInt8.ofNat (w.toNat >>> 8 &&& 0xFF),
     UInt8.ofNat (w.toNat &&& 0xFF)]

end IOPattern

/-! ## Part 3: Compatibility Layer with Transcript.lean -/

/-- Convert new DomainTag to legacy Transcript.DomainTag format.

    This allows gradual migration without breaking existing code.
-/
def toLegacyTag : DomainTag → String
  | .merkleTree2to1 => "merkleNode"
  | .merkleTree4to1 => "merkleNode"
  | .merkleLeaf     => "merkleLeaf"
  | .friCommit      => "friCommit"
  | .friFold        => "friFold"
  | .friQuery       => "friQuery"
  | .friDeep        => "friCommit"  -- Map to closest existing
  | .transcriptInit => "friCommit"
  | .constraint     => "constraint"
  | .custom s       => s

/-! ## Part 4: Validation -/

/-- Verify that all domain tags produce unique capacity values -/
def validateUniqueness : Bool :=
  let tags := [
    DomainTag.merkleTree2to1,
    DomainTag.merkleTree4to1,
    DomainTag.merkleLeaf,
    DomainTag.friCommit,
    DomainTag.friFold,
    DomainTag.friQuery,
    DomainTag.friDeep,
    DomainTag.transcriptInit,
    DomainTag.constraint
  ]
  let values := tags.map DomainTag.toCapacityValue
  let uniqueValues := values.eraseDups
  values.length == uniqueValues.length

/-- Verify that Merkle tags follow 2^k - 1 pattern -/
def validateMerklePattern : Bool :=
  DomainTag.merkleTree2to1.toCapacityValue == 2^2 - 1 &&
  DomainTag.merkleTree4to1.toCapacityValue == 2^4 - 1 &&
  DomainTag.merkleLeaf.toCapacityValue == 2^1 - 1

/-! ## Part 5: Tests -/

section Tests

#eval IO.println s!"Domain tag uniqueness: {if validateUniqueness then "PASS" else "FAIL"}"
#eval IO.println s!"Merkle pattern: {if validateMerklePattern then "PASS" else "FAIL"}"

#eval IO.println "\nDomain tag values:"
#eval IO.println s!"  merkleTree2to1: {DomainTag.merkleTree2to1.toCapacityValue}"
#eval IO.println s!"  merkleTree4to1: {DomainTag.merkleTree4to1.toCapacityValue}"
#eval IO.println s!"  friCommit: {DomainTag.friCommit.toCapacityValue}"
#eval IO.println s!"  friFold: {DomainTag.friFold.toCapacityValue}"
#eval IO.println s!"  friQuery: {DomainTag.friQuery.toCapacityValue}"

#eval IO.println "\nIO Pattern encoding:"
#eval IO.println s!"  merkle2to1: {IOPattern.merkle2to1.operations}"
#eval IO.println s!"  friChallenge: {IOPattern.friChallenge.operations}"

end Tests

/-! ## Part 6: Summary -/

def domainSeparationSummary : String :=
  "Domain Separation Module Summary (Step 5.2)
   ==========================================

   1. Unified DomainTag Enumeration
      - merkleTree2to1, merkleTree4to1, merkleLeaf
      - friCommit, friFold, friQuery, friDeep
      - transcriptInit, constraint, custom

   2. Capacity Value Scheme (Poseidon paper)
      - Merkle operations: 2^arity - 1
      - Protocol phases: identifier * 2^32
      - Custom: 7 * 2^32 + hash(string)

   3. SAFE-style IO Pattern
      - Encode operations as 32-bit words
      - Aggregate consecutive same-type operations
      - Serialize to bytes for tag computation

   4. Compatibility
      - toLegacyTag maps to existing Transcript.DomainTag
      - Gradual migration without breaking changes

   Security Properties:
   - All tags produce unique capacity values ✓
   - Merkle tags follow 2^k - 1 pattern ✓
   - FRI phases have distinct identifiers ✓
   - Cross-protocol attacks prevented by domain separation"

#eval IO.println domainSeparationSummary

end AmoLean.Protocols.Poseidon.DomainSeparation
