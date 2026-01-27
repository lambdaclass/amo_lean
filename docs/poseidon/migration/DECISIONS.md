# Migration Decisions Log

This document captures incremental decisions made during the Step 5.3 migration.

---

## Decision 1: Reject UInt64 Truncation

**Date**: 2026-01-27
**Context**: Initial approach considered truncating Poseidon2 output to 64 bits

**Decision**: REJECTED

**Rationale**:
- Truncating 254-bit output to 64 bits reduces collision resistance from 127 bits to 32 bits
- 32-bit collision resistance is attackable in ~4 seconds on modern GPU
- Creates "security theater" - code appears to use Poseidon2 but is insecure
- Risk of truncated code being used in production accidentally

**Consequences**:
- Must migrate FRI to generic field type
- More upfront work, but no security debt

---

## Decision 2: Use Typeclasses for Field and Hash

**Date**: 2026-01-27
**Context**: How to abstract field and hash operations

**Decision**: Two separate typeclasses

```lean
class FRIField (F : Type) where ...
class CryptoHash (F : Type) where ...
```

**Rationale**:
- Separation of concerns: field arithmetic vs cryptographic operations
- Different fields may use same hash (theoretical)
- Same field may use different hash implementations (testing vs production)
- Follows Lean 4 best practices

**Consequences**:
- Functions need both constraints: `[FRIField F] [CryptoHash F]`
- More flexible but slightly more verbose

---

## Decision 3: TestField for Fast Testing

**Date**: 2026-01-27
**Context**: Existing tests use UInt64 with XOR hash - very fast

**Decision**: Create `TestField` type with XOR-based `CryptoHash`

**Rationale**:
- Maintains fast test execution for CI
- XOR is deterministic - tests are reproducible
- Clearly marked as non-cryptographic
- Same code path as production, just different instance

**Consequences**:
- Tests run fast with TestField
- Can also run (slower) tests with BN254 for full validation

---

## Decision 4: BN254 First, Goldilocks Later

**Date**: 2026-01-27
**Context**: We have Poseidon2 parameters for BN254 but not Goldilocks

**Decision**: Implement BN254 fully; Goldilocks is placeholder

**Rationale**:
- BN254 parameters are complete and tested (Step 4)
- Goldilocks requires different Poseidon2 parameters (t=12, α=7)
- Can add Goldilocks later without changing architecture
- Migration success doesn't depend on Goldilocks

**Consequences**:
- Goldilocks.lean will have `sorry` until parameters obtained
- Multi-field testing deferred

---

## Decision 5: Phase-by-Phase Commits

**Date**: 2026-01-27
**Context**: Migration touches many files

**Decision**: Commit after each phase, not at the end

**Rationale**:
- Each phase is independently revertible
- Progress is visible in git history
- Failures are isolated
- Easier to review

**Consequences**:
- Multiple commits for Step 5.3
- Clear commit messages per phase

---

## Future Decisions

(To be added as migration progresses)

### Pending Questions:
1. Should `FRIField` include `inv` (multiplicative inverse)?
2. How to handle Goldilocks' different Poseidon2 parameters?
3. Should we support fields that don't fit in 256 bits?

---

*Last updated: 2026-01-27*
