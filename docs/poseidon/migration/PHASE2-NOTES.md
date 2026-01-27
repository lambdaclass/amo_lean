# Phase 2: Migration - Progress Notes

**Status**: Not Started
**Depends On**: Phase 1 Complete
**Reference**: [PLAN.md](PLAN.md)

---

## Objective

Modify existing FRI files to use generic field type `F` instead of `UInt64`.

---

## Files to Modify

### 1. `AmoLean/FRI/Transcript.lean`

**Status**: [ ] Not Started
**Lines affected**: ~200

Key changes needed:
1. `TranscriptState` → `TranscriptState (F : Type)`
2. `absorbed : List UInt64` → `absorbed : List F`
3. `squeeze` implementation → use `CryptoHash.squeeze`
4. Add `[FRIField F] [CryptoHash F]` constraints to all functions

### 2. `AmoLean/FRI/Protocol.lean`

**Status**: [ ] Not Started
**Lines affected**: ~150

Key changes needed:
1. `RoundState` → `RoundState (F : Type)`
2. `commitment : Option UInt64` → `commitment : Option F`
3. `challenge : Option UInt64` → `challenge : Option F`
4. Update `friRound`, `commitPhase`, `squeezePhase`, etc.

### 3. `AmoLean/FRI/Merkle.lean`

**Status**: [ ] Not Started
**Lines affected**: ~50

Already mostly generic. Changes needed:
1. Verify `FlatMerkle F` works with new `FRIField` constraints
2. Remove `testHash` (moved to TestField module)
3. Update `buildTree` signature for `CryptoHash` constraint

---

## Migration Order

**Important**: Migrate in this order to minimize breakage:

1. **Transcript.lean** first (most isolated)
2. **Protocol.lean** second (depends on Transcript)
3. **Merkle.lean** last (verify compatibility)

---

## Verification Tests

After each file migration:
- [ ] `lake build` succeeds
- [ ] Existing tests can be adapted to use `TestField`
- [ ] No runtime errors with test inputs

---

## Progress Log

(Add entries as work progresses)

| Date | Work Done | Issues |
|------|-----------|--------|
| - | Not started | - |

---

*Last updated: 2026-01-27*
