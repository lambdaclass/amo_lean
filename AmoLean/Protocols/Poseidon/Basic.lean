/-
  Poseidon2 Hash Implementation for AMO-Lean

  Priority: #1 (Critical)

  Poseidon2 is a ZK-friendly hash designed for efficient arithmetic circuits.
  Required for:
  - Proof recursion in zkVMs
  - Merkle trees in zero-knowledge proofs
  - State commitments

  Key challenge: Poseidon combines linear and non-linear operations
    Poseidon_round(state) = MDS × (state + round_constants)^α

  Where:
  - MDS matrix: LINEAR (compatible with current Kronecker optimization)
  - S-box (x^α): NON-LINEAR (requires extending MatExpr with elemwise)

  Implementation Status:
  - [x] Paso 0.5: Pure specification (Spec.lean)
  - [x] Paso 0.5: BN254 parameters (Params/BN254.lean)
  - [ ] Paso 1: Extend MatExpr with elemwise
  - [ ] Paso 2: CodeGen for S-box
  - [ ] Paso 3: Poseidon2 in MatExpr
  - [ ] Paso 4: Verification
  - [ ] Paso 5: Integration

  See: docs/poseidon/ for ADRs and detailed documentation
-/

import AmoLean.Protocols.Poseidon.Spec
import AmoLean.Protocols.Poseidon.Params.BN254

namespace AmoLean.Protocols.Poseidon

-- Re-export key definitions for convenience
export Spec (Params State poseidon2Permutation poseidon2Hash sbox5 sboxOpt)
export Params.BN254 (prime alpha fullRounds partialRounds stateSize mdsMatrix)

/-! ## Implementation Roadmap

### Paso 1: Extend MatExpr (ADR-001)
Add `elemwise` constructor to MatExpr for element-wise non-linear operations.
See: docs/poseidon/ADR-001-elemwise.md

### Paso 2: CodeGen (ADR-003)
Generate optimized C/SIMD code for S-box.
- Square chain for x^5 (3 multiplications)
- SIMD blend for partial rounds
See: docs/poseidon/ADR-003-codegen-simd.md

### Paso 3: Poseidon2 in MatExpr (ADR-002)
Express Poseidon2 using extended MatExpr.
- Full rounds: add → elemwise → mul
- Partial rounds: split → elemwise → concat → mul
See: docs/poseidon/ADR-002-partial-rounds.md
-/

-- TODO: Paso 1 - Extend MatExpr
-- inductive ElemOp where
--   | pow : Nat → ElemOp
--   | custom : String → ElemOp

-- TODO: Paso 2 - CodeGen for elemwise
-- def generateSboxC : ElemOp → String

-- TODO: Paso 3 - Poseidon2 in MatExpr
-- def poseidon2MatExpr : Params p t → MatExpr (ZMod p) t 1 → MatExpr (ZMod p) t 1

end AmoLean.Protocols.Poseidon
