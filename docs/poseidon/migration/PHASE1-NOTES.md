# Phase 1: Infrastructure - Progress Notes

**Status**: Not Started
**Reference**: [PLAN.md](PLAN.md)

---

## Objective

Create the foundational typeclasses and field instances needed for generic FRI.

---

## Files to Create

### 1. `AmoLean/FRI/Hash.lean`

**Status**: [ ] Not Started

**Design**:
```lean
import AmoLean.FRI.Transcript (DomainTag)

namespace AmoLean.FRI.Hash

class CryptoHash (F : Type) where
  /-- 2-to-1 hash for Merkle tree nodes -/
  hash2to1 : F → F → F

  /-- Hash with domain separation tag -/
  hashWithDomain : DomainTag → F → F → F

  /-- Squeeze challenge from absorbed elements -/
  squeeze : List F → Nat → F

  /-- Multi-squeeze for multiple challenges -/
  squeezeMany : List F → Nat → Nat → List F

  /-- Optional: hash many elements (sponge construction) -/
  hashMany : List F → F := fun xs =>
    xs.foldl hash2to1 (hash2to1 xs.head! xs.head!)

end AmoLean.FRI.Hash
```

**Notes**:
- Import DomainTag from Transcript or DomainSeparation
- Consider making DomainTag a parameter of CryptoHash

---

### 2. `AmoLean/FRI/Fields/BN254.lean`

**Status**: [ ] Not Started

**Design**:
```lean
import AmoLean.FRI.Fold (FRIField)
import AmoLean.FRI.Hash (CryptoHash)
import AmoLean.Protocols.Poseidon.Integration

namespace AmoLean.FRI.Fields.BN254

-- Re-export p from Poseidon constants
open AmoLean.Protocols.Poseidon.Constants.BN254 (p)

/-- BN254 scalar field element -/
structure BN254 where
  val : Nat
  deriving Repr, BEq, Inhabited

namespace BN254

def ofNat (n : Nat) : BN254 := ⟨n % p⟩
def toNat (x : BN254) : Nat := x.val

-- Arithmetic operations (mod p)
def add (a b : BN254) : BN254 := ofNat (a.val + b.val)
def sub (a b : BN254) : BN254 := ofNat (p + a.val - b.val)
def mul (a b : BN254) : BN254 := ofNat (a.val * b.val)
def neg (a : BN254) : BN254 := ofNat (p - a.val)
-- ... etc

end BN254

instance : FRIField BN254 where
  zero := ⟨0⟩
  one := ⟨1⟩
  add := BN254.add
  sub := BN254.sub
  mul := BN254.mul
  neg := BN254.neg
  fdiv := ... -- Uses modular inverse
  ofNat := BN254.ofNat
  toNat := BN254.toNat
  modulus := p

instance : CryptoHash BN254 where
  hash2to1 := fun a b => BN254.ofNat (poseidon2Hash2to1 bn254Params a.toNat b.toNat)
  hashWithDomain := fun tag a b =>
    BN254.ofNat (poseidon2HashWithDomainTag bn254Params tag a.toNat b.toNat)
  squeeze := fun xs count =>
    BN254.ofNat (poseidon2Squeeze bn254Params (xs.map BN254.toNat) count)
  squeezeMany := ...

end AmoLean.FRI.Fields.BN254
```

**Notes**:
- Reuse existing Poseidon2 implementation from Integration.lean
- Need to handle modular inverse for `fdiv`

---

### 3. `AmoLean/FRI/Fields/TestField.lean`

**Status**: [ ] Not Started

**Design**:
```lean
namespace AmoLean.FRI.Fields.TestField

/-- Small test field for fast testing (NOT cryptographically secure) -/
def testPrime : Nat := 2^61 - 1  -- Mersenne prime, fits in UInt64

structure TestField where
  val : Nat
  deriving Repr, BEq, Inhabited

instance : FRIField TestField where
  -- Similar to BN254 but with testPrime
  ...

instance : CryptoHash TestField where
  hash2to1 := fun a b => ⟨(a.val ^^^ b.val + 0x9e3779b97f4a7c15) % testPrime⟩
  -- XOR-based, fast, NOT secure
  ...

end AmoLean.FRI.Fields.TestField
```

**Notes**:
- Uses XOR for speed (same as current testHash)
- Clearly documented as non-cryptographic

---

### 4. Extend `AmoLean/FRI/Fold.lean`

**Status**: [ ] Not Started

**Changes needed**:
```lean
-- Add to FRIField typeclass:
  toNat : F → Nat
  modulus : Nat
```

---

## Verification Tests

Before proceeding to Phase 2, verify:

```lean
-- Test BN254 arithmetic
#eval BN254.add ⟨5⟩ ⟨7⟩  -- Should be ⟨12⟩
#eval BN254.mul ⟨3⟩ ⟨4⟩  -- Should be ⟨12⟩

-- Test CryptoHash
#eval (CryptoHash.hash2to1 (⟨1⟩ : BN254) ⟨2⟩).val
-- Should match poseidon2Hash2to1 bn254Params 1 2

-- Test TestField
#eval (CryptoHash.hash2to1 (⟨1⟩ : TestField) ⟨2⟩).val
-- Should be XOR-based result
```

---

## Questions to Resolve

1. **DomainTag import**: From Transcript.lean or DomainSeparation.lean?
   - Answer: TBD in implementation

2. **Modular inverse**: Implement or use existing?
   - Answer: TBD

3. **BN254 vs ZMod**: Use structure or Lean's ZMod?
   - Answer: TBD (structure gives more control)

---

## Progress Log

(Add entries as work progresses)

| Date | Work Done | Issues |
|------|-----------|--------|
| 2026-01-27 | Created placeholder | None |

---

*Last updated: 2026-01-27*
