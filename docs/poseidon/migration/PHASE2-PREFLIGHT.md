# Phase 2.1 Pre-Flight Analysis: Transcript.lean

**Date**: 2026-01-28
**Status**: ✅ MIGRATION COMPLETE
**Target File**: `AmoLean/FRI/Transcript.lean` (~538 lines)

---

## 1. UInt64 References (Must Migrate)

| Line | Code | Migration Action |
|------|------|------------------|
| 73 | `absorbed : List UInt64` | → `absorbed : List F` |
| 112 | `absorb (elem : UInt64)` | → `absorb (elem : F)` |
| 116 | `absorbMany (elems : List UInt64)` | → `absorbMany (elems : List F)` |
| 120 | `absorbVec (vec : Vec UInt64 n)` | → `absorbVec (vec : Vec F n)` |
| 124 | `absorbCommitment (commitment : UInt64)` | → `absorbCommitment (commitment : F)` |
| 137 | `squeeze : TranscriptResult UInt64` | → Use `CryptoHash.squeeze` |
| 145 | `squeezeMany : TranscriptResult (List UInt64)` | → Use `CryptoHash.squeezeMany` |
| 347-348 | `friRoundTransition (commitment : UInt64)` | → `(commitment : F)` |
| 412 | theorem with `UInt64` | → Update or mark as legacy |

---

## 2. Bitwise Operations (Must Encapsulate)

| Line | Code | Risk | Solution |
|------|------|------|----------|
| 139 | `acc ^^^ x.toNat` | HIGH | Replace entire squeeze with `CryptoHash.squeeze` |

**Decision**: The XOR-based hash in `squeeze` will be completely replaced by `CryptoHash.squeeze`. The XOR implementation lives in `TestField`'s `CryptoHash` instance, not in the protocol code.

---

## 3. Numeric Literals (Safe vs Risky)

### Safe (Nat, not F):
- Line 87: `squeezeCount := 0` - Counter, stays Nat
- Line 89: `round := 0` - Counter, stays Nat
- Line 141: `squeezeCount + 1` - Counter arithmetic
- Line 163: `round + 1` - Counter arithmetic
- Lines 305, 321, 371, etc. - Loop indices, string formatting

### Risky (Need attention):
- Line 140: `UInt64.ofNat (hash % (2^64 - 1))` - REMOVED (replaced by CryptoHash)

**Conclusion**: Most numeric literals are for counters/indices (Nat), not field elements. Low risk.

---

## 4. Dependency Map

```
Level 0 (Only [FRIField F] needed):
├── TranscriptState (structure)
├── init
├── forFRI
├── absorb
├── absorbMany
├── absorbVec
├── absorbCommitment
├── enterDomain
├── exitDomain
└── nextRound

Level 1 (Needs [FRIField F] [CryptoHash F]):
├── squeeze         ← Uses CryptoHash.squeeze
└── squeezeMany     ← Uses squeeze

Level 2 (Inherits constraints from Level 1):
├── FRIRoundState (structure)
├── friRoundTransition  ← Uses absorb, squeeze, etc.
└── friRoundToSigma     ← Uses CryptoSigma (no F)

No Migration Needed:
├── DomainTag (enum)
├── Intrinsic (enum)
├── CryptoSigma (inductive, uses Intrinsic)
├── verifyIntrinsicSequence (operates on Intrinsic)
└── All Intrinsic/CryptoSigma helper functions
```

---

## 5. Migration Order

```
Step 1: Parametrize TranscriptState with F
        - Add (F : Type) parameter
        - Change absorbed : List UInt64 → List F
        - Keep squeezeCount, domainStack, round as-is (Nat/List DomainTag)

Step 2: Parametrize TranscriptResult
        - Already has (α : Type), will use with F

Step 3: Update Level 0 functions
        - Add {F : Type} [FRIField F] to signatures
        - Change UInt64 parameters to F
        - No implementation changes needed

Step 4: Update Level 1 functions (squeeze, squeezeMany)
        - Add {F : Type} [FRIField F] [CryptoHash F]
        - Replace XOR implementation with CryptoHash.squeeze
        - This is the critical change

Step 5: Update Level 2 (FRIRoundState, friRoundTransition)
        - Constraints propagate from Level 1
        - Parametrize FRIRoundState with F

Step 6: Update tests section
        - Use TestField for quick tests
        - Verify with BN254 for production validation
```

---

## 6. Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Type inference failures | High | Medium | Explicit type annotations |
| Constraint propagation errors | Medium | High | Bottom-up migration order |
| Broken tests | High | Low | Tests updated to use TestField |
| Performance regression | Low | Medium | Accept for now, optimize later |

---

## 7. Verification Checklist (Post-Migration)

- [x] `lake build AmoLean.FRI.Transcript` succeeds ✅
- [x] No new `sorry` introduced (existing theorem sorry preserved) ✅
- [x] Tests run with TestField ✅
- [ ] Tests run with BN254 (to be added)
- [x] Squeeze produces different output for different inputs ✅
- [x] Squeeze is deterministic (same input → same output) ✅

### Migration Results (2026-01-28)

**Test Output:**
```
=== Transcript Test (Phase 2.1: Using TestField) ===
Initial state: round=0, absorbed=0
After 2 absorbs: absorbed count=2
Squeezed challenge: 175
Squeeze count: 1
Second squeeze: 174 (should differ from first)

=== FRI Round Test (Phase 2.1: Using TestField) ===
Initial: layer size = 1024, round = 0
Round 1: layer size = 512, alpha = 2177342782468466662
Round 2: layer size = 256, alpha = 31974
Round 3: layer size = 128, alpha = 2177342782468453040
```

**Key Changes Made:**
1. `TranscriptState` now takes `(F : Type)` parameter
2. `absorbed : List F` instead of `List UInt64`
3. `squeeze` uses `CryptoHash.squeeze` instead of XOR
4. All functions have `{F : Type}` with appropriate constraints
5. Tests use `TestField` for fast verification

---

## 8. Files That Import Transcript.lean

```
AmoLean/FRI/Protocol.lean  ← Will need update in Phase 2.2
AmoLean/FRI/CodeGen.lean   ← Uses CryptoSigma, likely OK
AmoLean.lean               ← Root import, OK
```

---

*Analysis completed: 2026-01-28*
*Ready to proceed with migration*
