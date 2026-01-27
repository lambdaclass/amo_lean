# ADR-009: Step 5.3 - Generic Field Migration for FRI Protocol

**Status**: Accepted
**Date**: 2026-01-27
**Context**: Step 5.3 - End-to-End FRI Tests with Poseidon2

---

## Executive Summary

After completing Steps 5.1 (Integration Adapters) and 5.2 (Domain Separation Audit), we analyzed options for Step 5.3 (End-to-End FRI Tests). The critical finding was that the current FRI implementation uses `UInt64` hardcoded throughout, which:

1. **Cannot use Poseidon2 correctly** - BN254 field has 254 bits, truncating to 64 bits reduces collision resistance from 127 bits to 32 bits (attackable in ~4 seconds on GPU)
2. **Prevents multi-field support** - Cannot switch between BN254 and Goldilocks
3. **Creates security debt** - Any truncation-based "smoke test" risks being confused with production code

**Decision**: Implement Option 4 - Complete migration to generic field type `F` with `FRIField` and `CryptoHash` typeclasses.

---

## Problem Statement

### Current Architecture (UInt64 Hardcoded)

```
┌─────────────────────────────────────────────────────────────┐
│                        FRI Protocol                          │
├─────────────────────────────────────────────────────────────┤
│  Protocol.lean ──→ Transcript.lean ──→ Merkle.lean          │
│       │                  │                  │                │
│    UInt64             UInt64            UInt64               │
│       │                  │                  │                │
│       └──────────────────┴──────────────────┘                │
│                          │                                   │
│                      testHash (XOR)                          │
│                    [NO SEGURIDAD]                            │
└─────────────────────────────────────────────────────────────┘
```

### Key Issues

| File | Line | Issue |
|------|------|-------|
| Transcript.lean | 73 | `absorbed : List UInt64` |
| Transcript.lean | 137-142 | `squeeze` returns `UInt64` via XOR |
| Protocol.lean | 109 | `commitment : Option UInt64` |
| Protocol.lean | 111 | `challenge : Option UInt64` |
| Merkle.lean | 221-222 | `testHash` uses `UInt64` |

---

## Options Evaluated

### Option 1: UInt64 Truncation (Smoke Test)

```lean
def poseidon2MerkleHashU64 (a b : UInt64) : UInt64 :=
  UInt64.ofNat (poseidon2MerkleHash a.toNat b.toNat % 2^64)
```

**Security Impact**:
- Collision resistance: 127 bits → **32 bits**
- Attack cost: Infeasible → **~4 seconds on GPU**

**Verdict**: Unacceptable. Creates dangerous code that looks secure ("uses Poseidon2") but isn't.

### Option 2: Use Goldilocks Instead of BN254

Goldilocks field (p = 2^64 - 2^32 + 1) fits in UInt64.

**Issues**:
- We don't have Poseidon2 parameters for Goldilocks
- Goldilocks requires α=7, t=12 (different from BN254's α=5, t=3)
- Would need to generate/obtain round constants

**Verdict**: Partial solution. Doesn't address multi-field requirement.

### Option 3: Parallel Implementation

Create FRI_Nat.lean alongside existing FRI code.

**Issues**:
- Code duplication (~2000 lines)
- Maintenance burden (changes needed in two places)
- No path to unification

**Verdict**: Wasteful. Creates tech debt.

### Option 4: Generic Field Migration (SELECTED)

Parametrize all FRI types by generic field `F`:

```lean
structure TranscriptState (F : Type) where
  absorbed : List F
  ...

structure RoundState (F : Type) where
  transcript : TranscriptState F
  commitment : Option F
  challenge : Option F
  ...
```

**Benefits**:
- **Full security**: Each field gets proper Poseidon2 parameters
- **Modularity**: Same code works with BN254, Goldilocks, TestField
- **No debt**: Clean architecture, no truncation hacks
- **Extensibility**: Easy to add new fields (Mersenne31, BabyBear, etc.)

**Verdict**: Best long-term solution. Accepted.

---

## Target Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    FRI Protocol [F : Field]                  │
├─────────────────────────────────────────────────────────────┤
│  Protocol F ────→ Transcript F ────→ Merkle F               │
│       │                  │                  │                │
│   generic F          generic F          generic F            │
│       │                  │                  │                │
│       └──────────────────┴──────────────────┘                │
│                          │                                   │
│              ┌───────────┴───────────┐                       │
│              ▼                       ▼                       │
│     ┌─────────────────┐     ┌─────────────────┐             │
│     │   BN254 Field   │     │ Goldilocks Field│             │
│     │   (254 bits)    │     │   (64 bits)     │             │
│     ├─────────────────┤     ├─────────────────┤             │
│     │ Poseidon2 BN254 │     │Poseidon2 Goldil.│             │
│     │ t=3, RF=8, RP=56│     │t=12, RF=8, RP=22│             │
│     │ [127-bit sec]   │     │ [64-bit sec]    │             │
│     └─────────────────┘     └─────────────────┘             │
└─────────────────────────────────────────────────────────────┘
```

---

## Implementation Plan

### Phase 1: Infrastructure (New Files)

| File | Purpose |
|------|---------|
| `AmoLean/FRI/Hash.lean` | `CryptoHash` typeclass |
| `AmoLean/FRI/Fields/BN254.lean` | BN254 field + Poseidon2 instance |
| `AmoLean/FRI/Fields/TestField.lean` | Fast XOR-based field for testing |
| `AmoLean/FRI/Fields/Goldilocks.lean` | Placeholder (needs Poseidon2 params) |

### Phase 2: Migration (Modify Existing)

| File | Changes |
|------|---------|
| `AmoLean/FRI/Fold.lean` | Extend `FRIField` typeclass |
| `AmoLean/FRI/Transcript.lean` | Parametrize `TranscriptState` by `F` |
| `AmoLean/FRI/Protocol.lean` | Parametrize `RoundState` by `F` |
| `AmoLean/FRI/Merkle.lean` | Already generic, verify compatibility |

### Phase 3: Tests

| File | Purpose |
|------|---------|
| `Tests/FRIGenericTests.lean` | End-to-end tests with multiple fields |
| `Tests/FRIPoseidon2E2E.lean` | BN254 Poseidon2 integration tests |

### Phase 4: Documentation

| File | Purpose |
|------|---------|
| `docs/poseidon/ADR-009-*.md` | This document |
| `docs/poseidon/PROGRESS.md` | Updated with Step 5.3 status |
| `docs/poseidon/migration/` | Migration notes and decisions |

---

## New Typeclasses

### Extended FRIField

```lean
class FRIField (F : Type) extends Add F, Sub F, Mul F, Neg F, Inhabited F where
  zero : F
  one : F
  fdiv : F → F → F
  ofNat : Nat → F
  toNat : F → Nat           -- NEW: inverse conversion
  modulus : Nat             -- NEW: field modulus
```

### CryptoHash

```lean
class CryptoHash (F : Type) where
  /-- 2-to-1 hash for Merkle tree nodes -/
  hash2to1 : F → F → F

  /-- Hash with domain separation tag -/
  hashWithDomain : DomainTag → F → F → F

  /-- Squeeze challenge from absorbed elements -/
  squeeze : List F → Nat → F
```

---

## Security Properties After Migration

| Aspect | Pre-Migration | Post-Migration (BN254) |
|--------|---------------|------------------------|
| Collision resistance | 0 bits (XOR) | **127 bits** |
| Preimage resistance | ~64 bits | **254 bits** |
| Domain separation | Manual strings | **Typed DomainTag** |
| Field overflow | Silent wrap | **Impossible (dependent types)** |

---

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Type parameter propagation complexity | Use `variable {F : Type} [FRIField F] [CryptoHash F]` |
| Goldilocks lacks Poseidon2 params | Implement BN254 first; Goldilocks is future work |
| Performance of dependent types | Use `Subtype` with efficient `decide` |
| Existing tests use UInt64 | Migrate to `TestField` (XOR-based, fast) |

---

## File Organization

### Where to Save Migration Work

```
docs/poseidon/
├── ADR-009-step53-generic-field-migration.md  <- This document
├── migration/
│   ├── PLAN.md                <- Detailed migration plan
│   ├── PHASE1-NOTES.md        <- Phase 1 progress notes
│   ├── PHASE2-NOTES.md        <- Phase 2 progress notes
│   └── DECISIONS.md           <- Incremental decisions during migration
└── ...

AmoLean/FRI/
├── Hash.lean                  <- NEW: CryptoHash typeclass
├── Fields/
│   ├── BN254.lean            <- NEW: BN254 field instance
│   ├── TestField.lean        <- NEW: Fast test field (XOR)
│   └── Goldilocks.lean       <- NEW: Placeholder for future
└── ... (existing files to modify)

Tests/
├── FRIGenericTests.lean      <- NEW: Generic field tests
└── FRIPoseidon2E2E.lean      <- NEW: BN254 E2E tests
```

### What NOT to Modify (Safeguarded)

The following completed work is committed and should not be modified during migration:

- `AmoLean/Protocols/Poseidon/Spec.lean` - Poseidon2 specification
- `AmoLean/Protocols/Poseidon/Constants/BN254.lean` - BN254 constants
- `AmoLean/Protocols/Poseidon/DomainSeparation.lean` - Domain tags
- `Tests/TranscriptSecurityAudit.lean` - Security audit tests
- All Step 4 verification work

---

## Success Criteria

1. **Functional**: FRI protocol executes with BN254 field
2. **Secure**: Full 127-bit collision resistance
3. **Generic**: Same code works with TestField (fast) and BN254 (secure)
4. **Tested**: End-to-end tests pass with Poseidon2 hashing
5. **Documented**: All decisions captured in migration/ directory

---

## References

1. Poseidon Paper Section 4.2 - Domain separator values
2. ADR-008 - Domain Separation Audit (Step 5.2)
3. `docs/references/poseidon/domain-separation/notes-domain-separation.md`
4. FRI Protocol Analysis - `AmoLean/FRI/Protocol.lean`

---

*Last updated: 2026-01-27*
*Decision: Option 4 (Generic Field Migration) selected*
