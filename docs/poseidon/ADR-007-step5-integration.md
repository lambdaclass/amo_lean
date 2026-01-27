# ADR-007: Step 5 Integration Strategy

**Status**: Accepted
**Date**: 2026-01-27
**Context**: Step 5 - Connecting Poseidon2 with FRI Infrastructure

---

## Problem Statement

With Poseidon2 formally verified (Step 4 complete), we need to integrate it with the existing FRI infrastructure for production use. The initial assumption was that MerkleTree, Transcript, and Protocol modules needed to be implemented from scratch. **This assumption was incorrect.**

## Key Discovery: Infrastructure Already Exists

After examining the codebase, we found complete implementations:

| Module | File | Status | Gap |
|--------|------|--------|-----|
| MerkleTree | `AmoLean/FRI/Merkle.lean` | Complete (608 lines) | Uses placeholder hash |
| Transcript | `AmoLean/FRI/Transcript.lean` | Complete (~538 lines) | Uses XOR-based squeeze |
| Protocol | `AmoLean/FRI/Protocol.lean` | Complete (~538 lines) | Already integrated |

### Current Placeholder Hashes

**Merkle.lean (line 221-222)**:
```lean
/-- Simulated hash function for testing (XOR-based, NOT cryptographic!) -/
def testHash (a b : UInt64) : UInt64 :=
  (a ^^^ b) + 0x9e3779b97f4a7c15  -- Golden ratio constant for mixing
```

**Transcript.lean (squeeze function)**:
```lean
let hash := state.absorbed.foldl (fun acc x => acc ^^^ x.toNat) state.squeezeCount
```

### Existing Abstractions Ready for Poseidon2

**Generic HashFn interface** (Merkle.lean line 225):
```lean
abbrev HashFn (F : Type) := F → F → F
```

**buildTree accepts hashFn** (line 237):
```lean
def buildTree [FRIField F] [Inhabited F] (leaves : Array F) (hashFn : HashFn F) :
    Option (FlatMerkle F leaves.size)
```

**Domain separation already implemented** (Transcript.lean):
```lean
inductive DomainTag where
  | merkleNode | friChallenge | friCommit | fieldElement | constraint | custom
```

---

## Analysis of Original Step 5 Proposal

### Sub-step 5.1: MerkleTree Implementation
**Original Proposal**: Implement from scratch
**Reality**: Already exists with leaves-first flat layout optimized for SIMD
**Actual Work**: Create Poseidon2 adapter for `HashFn` type

### Sub-step 5.2: Fiat-Shamir Implementation
**Original Proposal**: Implement hash-based transcript
**Reality**: Complete transcript with DomainTag and absorb/squeeze API
**Actual Work**: Replace XOR-based squeeze with Poseidon2 sponge

### Sub-step 5.3: Domain Separation
**Original Proposal**: Add domain tags for security
**Reality**: DomainTag enum already defined with 6 variants
**Actual Work**: Verify coverage is complete (may need to add custom tags)

### Sub-step 5.4: FRI Integration
**Original Proposal**: Connect with FRI
**Reality**: Protocol.lean already orchestrates Merkle + Transcript
**Actual Work**: End-to-end tests only

---

## Refined Step 5 Plan

```
Step 5 Refinado:
├── 5.1: Hash Adapter (INTEGRATION, not implementation)
│   ├── Create poseidon2Hash : Nat → Nat → Nat for Merkle HashFn
│   ├── Create poseidon2Squeeze : TranscriptState → Nat for Transcript
│   └── Validate against Spec.lean semantics
│
├── 5.2: Security Audit (VERIFICATION, not implementation)
│   ├── Verify all FRI challenges use transcript (no raw randomness)
│   ├── Verify domain separation covers all contexts
│   └── Document any gaps or missing tags
│
└── 5.3: End-to-End Tests (VALIDATION)
    ├── Run FRI protocol with Poseidon2 hashes
    ├── Verify Merkle proofs with real cryptographic hash
    └── Benchmark full FRI commit vs testHash baseline
```

---

## Technical Design

### 5.1.1: Poseidon2 Merkle Adapter

The current `testHash` signature:
```lean
def testHash (a b : UInt64) : UInt64
```

Poseidon2 hash-to-one from Spec.lean:
```lean
def poseidon2Hash2to1 (params : Params) (a b : Nat) : Nat :=
  let state := #[a % params.prime, b % params.prime, 0]
  let result := poseidon2Permutation params state
  result.get! 0
```

**Adapter**:
```lean
def poseidon2HashFn (params : Params) : HashFn Nat :=
  fun a b => poseidon2Hash2to1 params a b
```

### 5.1.2: Poseidon2 Transcript Squeeze

Current XOR-based squeeze:
```lean
let hash := state.absorbed.foldl (fun acc x => acc ^^^ x.toNat) state.squeezeCount
```

**Poseidon2-based squeeze**:
```lean
def poseidon2Squeeze (params : Params) (state : TranscriptState) : Nat :=
  -- Sponge construction: absorb all elements, then squeeze
  let paddedInput := state.absorbed ++ (List.replicate (params.stateSize - state.absorbed.length % params.stateSize) 0)
  let chunks := paddedInput.toChunks params.stateSize
  let finalState := chunks.foldl (fun s chunk =>
    poseidon2Permutation params (zipAdd s chunk)
  ) (Array.mkArray params.stateSize 0)
  finalState.get! 0
```

### 5.2: Domain Separation Audit

Current tags in `DomainTag`:
```lean
inductive DomainTag where
  | merkleNode      -- Merkle tree internal nodes
  | friChallenge    -- FRI folding challenges
  | friCommit       -- FRI commitment phase
  | fieldElement    -- Field element hashing
  | constraint      -- Constraint evaluation
  | custom : String → DomainTag
```

**Completeness check**:
- [x] Merkle nodes (`.merkleNode`)
- [x] FRI challenges (`.friChallenge`)
- [x] FRI commits (`.friCommit`)
- [ ] Query phase responses (may need new tag)
- [ ] Proof finalization (may need new tag)

### 5.3: Test Plan

| Test | Description | Oracle |
|------|-------------|--------|
| E2E-1 | Merkle tree with Poseidon2, verify proof | Self-consistency |
| E2E-2 | FRI commit phase with Poseidon2 transcript | Protocol correctness |
| E2E-3 | FRI query phase with Poseidon2 challenges | Round-trip equality |
| E2E-4 | Full FRI protocol benchmark | testHash baseline |

---

## Risk Analysis

### Low Risk
- Hash adapter is straightforward function wrapping
- Existing infrastructure is well-tested with testHash

### Medium Risk
- Sponge construction for transcript may need careful implementation
- Performance may differ significantly from XOR-based testHash

### Mitigation
- Extensive differential testing against Spec.lean
- Benchmark comparison to ensure acceptable performance

---

## Success Criteria

1. **Functional**: FRI protocol runs to completion with Poseidon2 hashes
2. **Correct**: All Merkle proofs verify correctly
3. **Secure**: Domain separation covers all transcript contexts
4. **Documented**: Integration documented with code comments
5. **Tested**: End-to-end tests pass

---

## References

- `AmoLean/FRI/Merkle.lean` - Existing Merkle tree implementation
- `AmoLean/FRI/Transcript.lean` - Existing transcript implementation
- `AmoLean/FRI/Protocol.lean` - Existing FRI protocol orchestration
- `AmoLean/Protocols/Poseidon/Spec.lean` - Poseidon2 specification
- ADR-006 - Formal verification strategy (completed)

---

*Last updated: 2026-01-27*
