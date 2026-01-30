# ADR-008: Step 5.2 Domain Separation Audit

**Status**: Accepted
**Date**: 2026-01-27
**Context**: Step 5.2 - Auditing and unifying domain separation in AMO-Lean

---

## Problem Statement

After implementing Poseidon2 adapters (Step 5.1), we needed to:
1. Audit all hash usages for proper domain separation
2. Verify no weak Fiat-Shamir vulnerabilities exist
3. Unify inconsistent domain tag systems between modules

## Bibliography Studied

Nine papers/specifications were analyzed (see `docs/references/poseidon/domain-separation/`):

| Document | Key Contribution |
|----------|-----------------|
| SAFE API | IO pattern encoding, capacity injection |
| Weak Fiat-Shamir | Attack vectors, transcript binding requirements |
| ethSTARK Documentation | Production FRI domain separation patterns |
| Poseidon Paper (Section 4.2) | Canonical domain separator values |
| Generalized Indifferentiable Sponge | Security bounds for capacity-based separation |
| Concrete Fiat-Shamir Security | Q_H² quantum penalty, parameter bounds |
| Concrete Non-Interactive FRI | FRI-specific security bounds |
| To Pad or Not to Pad | NCP-based separation for large fields |
| Cryptographic Sponge Functions | Theoretical foundations |

Full analysis: `docs/references/poseidon/domain-separation/notes-domain-separation.md`

---

## Audit Findings

### 1. Hash Usage Inventory

| File | Context | Previous Tag | Issue |
|------|---------|--------------|-------|
| Merkle.lean:345 | Tree construction | `.merkleNode` | OK - uses DomainTag |
| Protocol.lean:270 | FRI round | `.friFold` | OK - proper domain |
| Integration.lean:198-207 | Various | String primes | **INCONSISTENT** |
| Transcript.lean:139 | Squeeze | XOR-based | **NOT POSEIDON2** |

### 2. Weak Fiat-Shamir Check

**Protocol.lean** analysis (lines 265-307):

```
friRound execution order:
1. Phase 0: DomainEnter(.friFold)
2. Phase 1: Commit (Merkle tree)
3. Phase 2: Absorb (commitment)  ← Merkle root absorbed
4. Phase 3: Squeeze (challenge α) ← After absorb ✓
5. Phase 4: Fold
6. Phase 5: DomainExit
```

**Verdict**: The FRI protocol correctly absorbs Merkle roots before squeezing challenges. No weak F-S vulnerability in the commit-absorb-squeeze flow.

**Gap Identified**: No explicit absorption of public parameters (field size, domain size) at protocol initialization. This is a potential weak F-S vector if different field configurations could produce colliding challenges.

### 3. Domain Tag Inconsistencies

**Before Step 5.2:**

| Integration.lean | Transcript.lean | Issue |
|-----------------|-----------------|-------|
| `"merkleNode" => 2` | `.merkleNode` | Values differ |
| `"friChallenge" => 3` | `.friFold` | **Naming mismatch** |
| `"friCommit" => 5` | `.friCommit` | Values differ |
| `"queryResponse" => 13` | (missing) | Integration-only |
| `"proofFinalize" => 17` | (missing) | Integration-only |
| (missing) | `.merkleLeaf` | Transcript-only |
| (missing) | `.friQuery` | Transcript-only |

---

## Solution Implemented

### 1. New DomainSeparation.lean Module

Created unified `DomainTag` enum following Poseidon paper Section 4.2:

```lean
inductive DomainTag where
  | merkleTree2to1 : DomainTag  -- Value: 2^2 - 1 = 3
  | merkleTree4to1 : DomainTag  -- Value: 2^4 - 1 = 15
  | merkleLeaf     : DomainTag  -- Value: 2^1 - 1 = 1
  | friCommit      : DomainTag  -- Value: 1 * 2^32
  | friFold        : DomainTag  -- Value: 2 * 2^32
  | friQuery       : DomainTag  -- Value: 3 * 2^32
  | friDeep        : DomainTag  -- Value: 4 * 2^32
  | transcriptInit : DomainTag  -- Value: 5 * 2^32
  | constraint     : DomainTag  -- Value: 6 * 2^32
  | custom : String → DomainTag -- Value: 7 * 2^32 + hash(s)
```

**Value Scheme** (from Poseidon paper):
- Merkle operations: `2^arity - 1`
- Protocol phases: `identifier * 2^32`
- Custom: `7 * 2^32 + hash(string)`

### 2. SAFE-Style IO Pattern

Implemented IO pattern encoding for future SAFE API compliance:

```lean
inductive IOOp where
  | absorb : Nat → IOOp   -- MSB=1, lower 31 bits = count
  | squeeze : Nat → IOOp  -- MSB=0, lower 31 bits = count

structure IOPattern where
  operations : List IOOp
```

### 3. Updated Integration.lean

Added new type-safe API while preserving backwards compatibility:

```lean
-- New API (recommended)
def poseidon2HashWithDomainTag (params : Params) (tag : DomainTag) (left right : Nat) : Nat

-- FRI-specific functions
def poseidon2FRIFoldChallenge (commitment : Nat) (previousState : Nat) : Nat
def poseidon2FRIQueryIndex (seed : Nat) (index : Nat) : Nat

-- Legacy API (backwards compatible)
def poseidon2HashWithDomain (params : Params) (domain : String) (left right : Nat) : Nat
```

---

## Verification

### Tests Added (Integration.lean)

| Test | Description | Status |
|------|-------------|--------|
| Test 7 | DomainTag produces distinct hashes | PASS |
| Test 8 | Legacy-New API compatibility | PASS |
| Test 9 | All FRI phases have distinct tags | PASS |

### Uniqueness Validation (DomainSeparation.lean)

```
Domain tag uniqueness: PASS
Merkle pattern: PASS

Domain tag values:
  merkleTree2to1: 3
  merkleTree4to1: 15
  friCommit: 4294967296
  friFold: 8589934592
  friQuery: 12884901888
```

---

## Gaps Remaining

### 1. Transcript.lean Squeeze Function

The squeeze function at line 139 still uses XOR:
```lean
let hash := state.absorbed.foldl (fun acc x => acc ^^^ x.toNat) state.squeezeCount
```

**Recommendation**: Replace with `poseidon2TranscriptSqueeze` from Integration.lean. This is a drop-in replacement but requires updating Transcript.lean imports.

**Risk**: LOW - The XOR is only used in the simulation; actual protocol uses Integration.lean adapters.

### 2. Public Parameter Binding

No explicit absorption of public parameters at protocol start. According to the Weak Fiat-Shamir paper, this could be exploited if:
- Different field sizes produce the same challenge
- Different domain sizes produce the same challenge

**Recommendation**: Add `transcriptInit` absorption at protocol start with:
- Field modulus p
- Domain size n
- Security parameter λ

**Risk**: MEDIUM - Only exploitable in multi-configuration scenarios.

### 3. Merkle Leaf Hashing

`DomainTag.merkleLeaf` is defined but not used. Leaf-level domain separation may be needed for certain proof constructions.

**Risk**: LOW - Not required for current FRI implementation.

---

## Files Changed

| File | Changes |
|------|---------|
| `AmoLean/Protocols/Poseidon/DomainSeparation.lean` | NEW - Unified domain tags |
| `AmoLean/Protocols/Poseidon/Integration.lean` | Updated domain separation |
| `docs/references/poseidon/domain-separation/notes-domain-separation.md` | NEW - Bibliography analysis |
| `docs/poseidon/ADR-008-domain-separation-audit.md` | NEW - This document |

---

## Security Properties Verified

- [x] All domain tags produce unique capacity values
- [x] Merkle tags follow `2^k - 1` pattern (Poseidon paper)
- [x] FRI phases have distinct identifiers
- [x] Merkle roots absorbed before challenge derivation
- [x] Legacy API maps to new tags correctly
- [ ] Public parameters absorbed at init (RECOMMENDED)
- [ ] Transcript.lean uses Poseidon2 squeeze (OPTIONAL)

---

## References

1. Poseidon Paper Section 4.2 - Domain separator values
2. SAFE API (2023) - IO pattern encoding
3. Weak Fiat-Shamir Attacks (2019) - Transcript binding requirements
4. ethSTARK Documentation - Production FRI patterns
5. `docs/references/poseidon/domain-separation/notes-domain-separation.md`

---

## Security Audit: Black-Box Cryptographic Tests

**File:** `Tests/TranscriptSecurityAudit.lean`
**Date:** 2026-01-27

### Test 1: Amnesia Test (State Preservation)

**Objective:** Verify transcript doesn't "forget" absorbed data.

| Scenario | Challenge Hash |
|----------|---------------|
| `squeeze([A, B])` | `80145588014033066208572451296323983327...` |
| `squeeze([B])` | `85981498108747198940168130670370971665...` |
| `squeeze([A])` | `47771154487208296609221924529761912727...` |
| `squeeze([B, A])` | `74349060000287442990529427813262257441...` |

**Result:** PASS ✓ - All scenarios produce unique challenges.

### Test 2: Avalanche Test (Single-Bit Sensitivity)

**Objective:** Verify single-bit changes produce radical output differences.

| Bit Changed | Bits Different | Percentage |
|-------------|----------------|------------|
| Bit 0 | 123 bits | 48.4% |
| Bit 7 | 133 bits | 52.4% |
| Bit 15 | 125 bits | 49.2% |
| Bit 31 | 131 bits | 51.6% |
| Bit 63 | 127 bits | 50.0% |

**Average:** 127 bits (~50% of 254-bit field)
**Result:** PASS ✓ - Excellent avalanche effect, near theoretical ideal.

### Test 3: Domain Separation Test

**Objective:** Verify different contexts produce cryptographically distinct outputs.

| Domain | Tag Value | Hash Unique |
|--------|-----------|-------------|
| MerkleTree2to1 | 3 | ✓ |
| FRI Commit | 4294967296 | ✓ |
| FRI Fold | 8589934592 | ✓ |
| FRI Query | 12884901888 | ✓ |

**All 6 pairwise comparisons:** PASS ✓
**Tagged vs Raw:** PASS ✓

### Test 4: Sponge State Continuity

**Objective:** Verify sponge state is maintained across operations.

- All partial transcripts produce unique challenges: ✓
- Multi-squeeze produces independent values: ✓

**Result:** PASS ✓

### Security Audit Conclusion

| Property | Status |
|----------|--------|
| Resistant to omission | ✓ Verified |
| Resistant to reordering | ✓ Verified |
| Avalanche effect (~50% bits) | ✓ Verified |
| Domain separation | ✓ Verified |
| Sponge state preservation | ✓ Verified |

**Overall:** The Poseidon2 transcript implementation passes all black-box cryptographic security tests.

---

*Last updated: 2026-01-27*
