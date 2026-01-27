# Step 5.3 Migration Plan: Generic Field Type

**Status**: In Progress
**Started**: 2026-01-27
**Reference**: [ADR-009](../ADR-009-step53-generic-field-migration.md)

---

## Overview

This document tracks the detailed migration plan for converting FRI from `UInt64` to generic field type `F`.

---

## Phase 1: Infrastructure (NEW FILES)

### 1.1 Extend FRIField Typeclass

**File**: `AmoLean/FRI/Fold.lean`
**Status**: [ ] Not Started

Changes:
```lean
class FRIField (F : Type) extends Add F, Sub F, Mul F, Neg F, Inhabited F where
  zero : F
  one : F
  fdiv : F → F → F
  ofNat : Nat → F
  toNat : F → Nat      -- ADD
  modulus : Nat        -- ADD
```

### 1.2 Create CryptoHash Typeclass

**File**: `AmoLean/FRI/Hash.lean` (NEW)
**Status**: [ ] Not Started

```lean
class CryptoHash (F : Type) where
  hash2to1 : F → F → F
  hashWithDomain : DomainTag → F → F → F
  squeeze : List F → Nat → F
  squeezeMany : List F → Nat → Nat → List F
```

### 1.3 Create BN254 Field Instance

**File**: `AmoLean/FRI/Fields/BN254.lean` (NEW)
**Status**: [ ] Not Started

- Define `BN254` structure
- Implement `FRIField BN254`
- Implement `CryptoHash BN254` (uses Poseidon2)

### 1.4 Create TestField Instance

**File**: `AmoLean/FRI/Fields/TestField.lean` (NEW)
**Status**: [ ] Not Started

- Define `TestField` (wraps `Nat` with small modulus)
- Implement `FRIField TestField`
- Implement `CryptoHash TestField` (uses XOR for speed)

---

## Phase 2: Migration (MODIFY EXISTING)

### 2.1 Transcript.lean

**File**: `AmoLean/FRI/Transcript.lean`
**Status**: [ ] Not Started
**Lines affected**: ~200

Key changes:
1. `TranscriptState` → `TranscriptState (F : Type)`
2. `absorbed : List UInt64` → `absorbed : List F`
3. `squeeze` uses `CryptoHash.squeeze`
4. All functions get `[FRIField F] [CryptoHash F]` constraints

### 2.2 Protocol.lean

**File**: `AmoLean/FRI/Protocol.lean`
**Status**: [ ] Not Started
**Lines affected**: ~150

Key changes:
1. `RoundState` → `RoundState (F : Type)`
2. `commitment : Option UInt64` → `commitment : Option F`
3. `challenge : Option UInt64` → `challenge : Option F`
4. All functions get type constraints

### 2.3 Merkle.lean

**File**: `AmoLean/FRI/Merkle.lean`
**Status**: [ ] Not Started
**Lines affected**: ~50

Already mostly generic. Changes:
1. Verify `FlatMerkle F` works with new constraints
2. Update `buildTree` to use `CryptoHash.hash2to1`
3. Remove `testHash` (moved to TestField)

---

## Phase 3: Tests

### 3.1 Generic Field Tests

**File**: `Tests/FRIGenericTests.lean` (NEW)
**Status**: [ ] Not Started

- Test FRI with TestField (fast, for CI)
- Test FRI with BN254 (secure, for validation)

### 3.2 End-to-End Poseidon2 Tests

**File**: `Tests/FRIPoseidon2E2E.lean` (NEW)
**Status**: [ ] Not Started

- Single round test with BN254
- Multi-round test with BN254
- Determinism verification
- Challenge uniqueness verification

---

## Phase 4: Documentation

- [ ] Update `docs/poseidon/PROGRESS.md`
- [ ] Update `docs/poseidon/README.md`
- [ ] Create `docs/poseidon/migration/PHASE1-NOTES.md`
- [ ] Create `docs/poseidon/migration/PHASE2-NOTES.md`
- [ ] Create `docs/poseidon/migration/DECISIONS.md`

---

## Verification Checklist

### Phase 1 Complete When:
- [ ] `lake build` succeeds with new files
- [ ] BN254 field arithmetic correct (basic tests)
- [ ] TestField arithmetic correct (basic tests)
- [ ] CryptoHash instances work in isolation

### Phase 2 Complete When:
- [ ] Transcript compiles with generic F
- [ ] Protocol compiles with generic F
- [ ] Merkle compiles with generic F
- [ ] Existing tests pass (after migration to TestField)

### Phase 3 Complete When:
- [ ] Single FRI round works with BN254
- [ ] Multi-round FRI works with BN254
- [ ] All security properties verified
- [ ] Performance acceptable

---

## Rollback Plan

If migration fails at any phase:

1. **Phase 1 failure**: Simply delete new files, no existing code modified
2. **Phase 2 failure**: Use `git checkout` to restore original FRI files
3. **Phase 3 failure**: Tests don't affect production code

All commits are incremental. Each phase can be reverted independently.

---

## Notes

- **DO NOT MODIFY** completed Poseidon2 implementation (Spec.lean, Constants/)
- **DO NOT MODIFY** domain separation work (DomainSeparation.lean)
- All migration work happens in FRI/ directory
- Document every decision in `DECISIONS.md`

---

*Last updated: 2026-01-27*
