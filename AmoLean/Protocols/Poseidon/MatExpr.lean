/-
  AMO-Lean: Poseidon2 MatExpr Integration
  Phase 3: Complete Hash Construction

  This module provides the MatExpr-level representation of Poseidon2.
  Key design decisions (from Phase 3 planning):

  1. **Symbolic Constant References**: MDS matrices and round constants are NOT
     embedded as literals in the expression tree. Instead, we use typed
     references (`ConstRef`) that the CodeGen translates to array accesses.

  2. **MDS as Opaque Operation**: The MDS multiplication is a single node,
     not expanded into scalar operations. This prevents graph explosion.

  3. **Round Functions as Combinators**: `fullRound` and `partialRound` are
     functions that compose MatExpr nodes, not giant expression trees.

  4. **Loop in CodeGen Only**: The 64 rounds are NOT unrolled in MatExpr.
     The `PoseidonConfig` structure provides metadata for CodeGen to emit loops.

  References:
  - ADR-004: Layered CodeGen Strategy
  - Phase 3 Design Discussion: Graph explosion prevention
-/

import AmoLean.Matrix.Basic

namespace AmoLean.Protocols.Poseidon.MatExpr

open AmoLean.Matrix (MatExpr ElemOp)

/-! ## Part 1: Symbolic Constant References

Constants (MDS matrix, round constants) are referenced symbolically,
not embedded as literal values. This prevents:
- Bloated expression trees
- Slow E-Graph equality checks
- Huge generated Lean files
-/

/-- Typed reference to external constants.
    Shape information is preserved for type safety.
    CodeGen translates these to `extern const` array accesses. -/
inductive ConstRef where
  /-- MDS matrix reference: t×t matrix -/
  | mds (t : Nat) : ConstRef
  /-- MDS internal matrix (for Poseidon2 optimization) -/
  | mdsInternal (t : Nat) : ConstRef
  /-- MDS external matrix (for Poseidon2 optimization) -/
  | mdsExternal (t : Nat) : ConstRef
  /-- Round constants for a specific round -/
  | roundConst (round : Nat) (t : Nat) : ConstRef
  deriving Repr, BEq, Hashable, Inhabited

namespace ConstRef

/-- Get the state size (t) from a ConstRef -/
def stateSize : ConstRef → Nat
  | mds t => t
  | mdsInternal t => t
  | mdsExternal t => t
  | roundConst _ t => t

/-- Check if this is an MDS reference -/
def isMDS : ConstRef → Bool
  | mds _ => true
  | mdsInternal _ => true
  | mdsExternal _ => true
  | roundConst _ _ => false

/-- Generate C identifier for this constant -/
def toCIdent : ConstRef → String
  | mds t => s!"POSEIDON_MDS_{t}"
  | mdsInternal t => s!"POSEIDON_MDS_INTERNAL_{t}"
  | mdsExternal t => s!"POSEIDON_MDS_EXTERNAL_{t}"
  | roundConst r t => s!"POSEIDON_RC_{t}[{r}]"

/-- Generate C type declaration -/
def toCType : ConstRef → String
  | mds t => s!"const uint64_t {toCIdent (mds t)}[{t}][{t}][4]"
  | mdsInternal t => s!"const uint64_t {toCIdent (mdsInternal t)}[{t}][{t}][4]"
  | mdsExternal t => s!"const uint64_t {toCIdent (mdsExternal t)}[{t}][{t}][4]"
  | roundConst _ t => s!"const uint64_t POSEIDON_RC_{t}[][{t}][4]"

end ConstRef

/-! ## Part 2: Poseidon Operation Types

These represent the high-level operations in Poseidon2 rounds.
They are designed to be:
- Opaque to E-Graph (no distribution rules)
- Compact in representation
- Clear for CodeGen
-/

/-- Poseidon-specific operations that act on state vectors.
    These are NOT MatExpr constructors - they're semantic markers
    that guide CodeGen. -/
inductive PoseidonOp where
  /-- Add round constants: state + RC[round] -/
  | addRC (round : Nat)
  /-- MDS matrix multiplication: MDS × state -/
  | mdsApply
  /-- MDS internal (Poseidon2): M_I × state -/
  | mdsInternal
  /-- MDS external (Poseidon2): M_E × state -/
  | mdsExternal
  /-- Full S-box: apply x^α to all elements -/
  | sboxFull (alpha : Nat)
  /-- Partial S-box: apply x^α only to element 0 -/
  | sboxPartial (alpha : Nat)
  deriving Repr, BEq, Hashable, Inhabited

namespace PoseidonOp

/-- Estimate multiplication count for this operation -/
def mulCount (t : Nat) : PoseidonOp → Nat
  | addRC _ => 0  -- Additions only
  | mdsApply => t * t  -- Dense matrix
  | mdsInternal => t + 1  -- Diagonal + rank-1 (Poseidon2 structure)
  | mdsExternal => t * t  -- Dense matrix
  | sboxFull α => t * (if α == 5 then 3 else α)  -- Square chain
  | sboxPartial α => if α == 5 then 3 else α  -- Single element

end PoseidonOp

/-! ## Part 3: Poseidon Configuration

This structure captures the full configuration of a Poseidon2 instance.
It is NOT an expression tree - it's metadata that guides CodeGen.
-/

/-- Field type for Poseidon implementation -/
inductive PoseidonField where
  | BN254      -- 254-bit, α=5
  | Goldilocks -- 64-bit, α=7
  | Generic (prime : Nat) (alpha : Nat)
  deriving Repr, BEq, Inhabited

namespace PoseidonField

/-- Get the S-box exponent for this field -/
def alpha : PoseidonField → Nat
  | BN254 => 5
  | Goldilocks => 7
  | Generic _ α => α

/-- Get limb count for this field -/
def limbCount : PoseidonField → Nat
  | BN254 => 4
  | Goldilocks => 1
  | Generic _ _ => 4  -- Conservative default

end PoseidonField

/-- Complete Poseidon2 configuration.
    This drives CodeGen to emit the correct loop structure. -/
structure PoseidonConfig where
  /-- Field type -/
  field : PoseidonField
  /-- State size (t) -/
  stateSize : Nat
  /-- Number of full rounds (RF) -/
  fullRounds : Nat
  /-- Number of partial rounds (RP) -/
  partialRounds : Nat
  /-- Use Poseidon2 MDS optimization (M = M_E · M_I) -/
  usePoseidon2MDS : Bool := true
  deriving Repr, Inhabited

namespace PoseidonConfig

/-- BN254 standard configuration (t=3) -/
def bn254_t3 : PoseidonConfig := {
  field := .BN254
  stateSize := 3
  fullRounds := 8
  partialRounds := 56
}

/-- BN254 configuration for Merkle trees (t=5) -/
def bn254_t5 : PoseidonConfig := {
  field := .BN254
  stateSize := 5
  fullRounds := 8
  partialRounds := 56
}

/-- Goldilocks configuration (t=12, common for STARK) -/
def goldilocks_t12 : PoseidonConfig := {
  field := .Goldilocks
  stateSize := 12
  fullRounds := 8
  partialRounds := 22
}

/-- Total number of rounds -/
def totalRounds (c : PoseidonConfig) : Nat :=
  c.fullRounds + c.partialRounds

/-- Half of full rounds (for split structure) -/
def halfFullRounds (c : PoseidonConfig) : Nat :=
  c.fullRounds / 2

/-- Get S-box exponent -/
def alpha (c : PoseidonConfig) : Nat :=
  c.field.alpha

end PoseidonConfig

/-! ## Part 4: Round Representation

Instead of building giant MatExpr trees, we represent rounds as
operations on an abstract state. The CodeGen generates loops.
-/

/-- A single Poseidon round operation sequence.
    Represents: AddRC → S-box → MDS -/
structure RoundSpec where
  /-- Round index (for round constant lookup) -/
  roundIdx : Nat
  /-- Is this a full round (S-box on all elements)? -/
  isFullRound : Bool
  /-- Use internal MDS (for partial rounds in Poseidon2)? -/
  useInternalMDS : Bool := false
  deriving Repr, BEq, Inhabited

/-- Sequence of rounds (for a phase of the permutation) -/
abbrev RoundSequence := Array RoundSpec

/-- Complete permutation structure -/
structure PermutationSpec where
  /-- Configuration -/
  config : PoseidonConfig
  /-- First half of full rounds -/
  firstFullRounds : RoundSequence
  /-- Partial rounds -/
  partialRounds : RoundSequence
  /-- Second half of full rounds -/
  lastFullRounds : RoundSequence
  deriving Repr, Inhabited

namespace PermutationSpec

/-- Build permutation spec from config -/
def fromConfig (c : PoseidonConfig) : PermutationSpec :=
  let halfFull := c.halfFullRounds
  let firstFull := Array.range halfFull |>.map fun i => {
    roundIdx := i
    isFullRound := true
    useInternalMDS := false
  }
  let partialRnds := Array.range c.partialRounds |>.map fun i => {
    roundIdx := halfFull + i
    isFullRound := false
    useInternalMDS := c.usePoseidon2MDS
  }
  let lastFull := Array.range halfFull |>.map fun i => {
    roundIdx := halfFull + c.partialRounds + i
    isFullRound := true
    useInternalMDS := false
  }
  { config := c, firstFullRounds := firstFull, partialRounds := partialRnds, lastFullRounds := lastFull }

/-- Total multiplication count estimate -/
def estimateMulCount (p : PermutationSpec) : Nat :=
  let t := p.config.stateSize
  let α := p.config.alpha
  let fullRoundMuls := t * t + t * (if α == 5 then 3 else α)  -- MDS + S-box
  let partialRoundMuls :=
    (if p.config.usePoseidon2MDS then t + 1 else t * t) +  -- MDS internal/full
    (if α == 5 then 3 else α)  -- Single S-box
  p.firstFullRounds.size * fullRoundMuls +
  p.partialRounds.size * partialRoundMuls +
  p.lastFullRounds.size * fullRoundMuls

end PermutationSpec

/-! ## Part 5: MatExpr Integration

These functions create MatExpr nodes for individual Poseidon operations.
They use the existing MatExpr constructors where possible.
-/

/-- Create MatExpr for full S-box (all elements) -/
def mkFullSbox (α : Nat) (state : MatExpr β t 1) : MatExpr β t 1 :=
  MatExpr.elemwise (ElemOp.pow α) state

/-- Create MatExpr for partial S-box (element 0 only) -/
def mkPartialSbox (α : Nat) (state : MatExpr β t 1) : MatExpr β t 1 :=
  MatExpr.partialElemwise 0 (ElemOp.pow α) state

/-! ## Part 6: Code Generation Helpers

These produce C code fragments for Poseidon operations.
They are designed to work with the existing CodeGen infrastructure.
-/

/-- Left brace for C code -/
def lbrace : String := "{"
/-- Right brace for C code -/
def rbrace : String := "}"

/-- Generate C code for round constant addition -/
def genAddRC (t : Nat) (roundVar : String) : String :=
  s!"    // Add round constants
    for (int i = 0; i < {t}; i++) {lbrace}
        field_add(state->elem[i], state->elem[i], POSEIDON_RC[{roundVar}][i], p);
    {rbrace}"

/-- Generate C code for MDS multiplication (full matrix) -/
def genMDSApply (t : Nat) : String :=
  s!"    // MDS matrix multiplication
    poseidon_state_{t} tmp;
    for (int i = 0; i < {t}; i++) {lbrace}
        field_zero(tmp.elem[i]);
        for (int j = 0; j < {t}; j++) {lbrace}
            uint64_t prod[4];
            field_mul(prod, POSEIDON_MDS[i][j], state->elem[j], p);
            field_add(tmp.elem[i], tmp.elem[i], prod, p);
        {rbrace}
    {rbrace}
    memcpy(state, &tmp, sizeof(tmp));"

/-- Generate C code for MDS internal (Poseidon2 optimization) -/
def genMDSInternal (t : Nat) : String :=
  s!"    // MDS internal (Poseidon2: diagonal + low-rank)
    // Sum all elements
    uint64_t sum[4];
    field_zero(sum);
    for (int i = 0; i < {t}; i++) {lbrace}
        field_add(sum, sum, state->elem[i], p);
    {rbrace}
    // Apply: state[i] = state[i] * diag[i] + sum
    for (int i = 0; i < {t}; i++) {lbrace}
        uint64_t scaled[4];
        field_mul(scaled, state->elem[i], POSEIDON_MDS_DIAG[i], p);
        field_add(state->elem[i], scaled, sum, p);
    {rbrace}"

/-- Generate C code for full round -/
def genFullRound (config : PoseidonConfig) (roundVar : String) : String :=
  let t := config.stateSize
  let α := config.alpha
  s!"static inline void poseidon_full_round(
    poseidon_state_{t} *state,
    int round,
    const field_params *p
) {lbrace}
{genAddRC t roundVar}

    // S-box on all elements
    for (int i = 0; i < {t}; i++) {lbrace}
        sbox{α}(state->elem[i], state->elem[i], p);
    {rbrace}

{genMDSApply t}
{rbrace}"

/-- Generate C code for partial round -/
def genPartialRound (config : PoseidonConfig) (roundVar : String) : String :=
  let t := config.stateSize
  let α := config.alpha
  let mdsCode := if config.usePoseidon2MDS then genMDSInternal t else genMDSApply t
  s!"static inline void poseidon_partial_round(
    poseidon_state_{t} *state,
    int round,
    const field_params *p
) {lbrace}
{genAddRC t roundVar}

    // S-box on element 0 only
    sbox{α}(state->elem[0], state->elem[0], p);

{mdsCode}
{rbrace}"

/-- Generate C code for complete permutation -/
def genPermutation (config : PoseidonConfig) : String :=
  let t := config.stateSize
  let rf := config.fullRounds
  let rp := config.partialRounds
  let halfRf := rf / 2

  s!"/**
 * Poseidon2 Permutation
 * Field: {repr config.field}
 * State size: {t}
 * Rounds: RF={rf}, RP={rp}
 *
 * Structure: [RF/2 full] → [RP partial] → [RF/2 full]
 */
void poseidon2_permutation(
    poseidon_state_{t} *state,
    const field_params *p
) {lbrace}
    int round = 0;

    // First RF/2 full rounds
    for (int r = 0; r < {halfRf}; r++) {lbrace}
        poseidon_full_round(state, round++, p);
    {rbrace}

    // RP partial rounds
    for (int r = 0; r < {rp}; r++) {lbrace}
        poseidon_partial_round(state, round++, p);
    {rbrace}

    // Last RF/2 full rounds
    for (int r = 0; r < {halfRf}; r++) {lbrace}
        poseidon_full_round(state, round++, p);
    {rbrace}
{rbrace}"

/-- Generate complete Poseidon2 header file -/
def genPoseidon2Header (config : PoseidonConfig) : String :=
  let t := config.stateSize
  let α := config.alpha

  s!"/**
 * Poseidon2 Complete Implementation
 * Generated by AMO-Lean Phase 3
 *
 * Configuration:
 *   Field: {repr config.field}
 *   State size: t={t}
 *   S-box: x^{α}
 *   Rounds: RF={config.fullRounds}, RP={config.partialRounds}
 *   MDS optimization: {config.usePoseidon2MDS}
 *
 * Estimated multiplications per hash:
 *   {(PermutationSpec.fromConfig config).estimateMulCount}
 */

#ifndef POSEIDON2_H
#define POSEIDON2_H

#include <stdint.h>
#include <string.h>

#ifdef __cplusplus
extern \"C\" {lbrace}
#endif

/* ============================================================================
 * Type Definitions
 * ============================================================================ */

typedef struct {lbrace}
    uint64_t elem[{t}][4];
{rbrace} poseidon_state_{t};

typedef struct {lbrace}
    uint64_t modulus[4];
    uint64_t r2[4];
    uint64_t inv;
{rbrace} field_params;

/* ============================================================================
 * External Constants (defined in poseidon_constants.c)
 * ============================================================================ */

extern const uint64_t POSEIDON_MDS[{t}][{t}][4];
extern const uint64_t POSEIDON_MDS_DIAG[{t}][4];
extern const uint64_t POSEIDON_RC[{config.totalRounds}][{t}][4];

/* ============================================================================
 * Field Operations (defined in field_ops.c)
 * ============================================================================ */

extern void field_add(uint64_t *out, const uint64_t *a, const uint64_t *b,
                      const field_params *p);
extern void field_mul(uint64_t *out, const uint64_t *a, const uint64_t *b,
                      const field_params *p);
extern void field_zero(uint64_t *out);

/* ============================================================================
 * S-box Implementation
 * ============================================================================ */

static inline void sbox{α}(
    uint64_t *out,
    const uint64_t *x,
    const field_params *p
) {lbrace}
    uint64_t x2[4], x4[4];
    field_mul(x2, x, x, p);      // x^2
    field_mul(x4, x2, x2, p);    // x^4
    field_mul(out, x, x4, p);    // x^5
{rbrace}

/* ============================================================================
 * Round Functions
 * ============================================================================ */

{genFullRound config "round"}

{genPartialRound config "round"}

/* ============================================================================
 * Permutation
 * ============================================================================ */

{genPermutation config}

/* ============================================================================
 * Hash Function (Sponge Construction)
 * ============================================================================ */

/**
 * Hash two field elements (for Merkle tree)
 */
static inline void poseidon2_hash_2to1(
    uint64_t out[4],
    const uint64_t left[4],
    const uint64_t right[4],
    const field_params *p
) {lbrace}
    poseidon_state_{t} state;
    memset(&state, 0, sizeof(state));

    // Absorb left and right
    memcpy(state.elem[0], left, 32);
    memcpy(state.elem[1], right, 32);

    // Permute
    poseidon2_permutation(&state, p);

    // Squeeze first element
    memcpy(out, state.elem[0], 32);
{rbrace}

#ifdef __cplusplus
{rbrace}
#endif

#endif // POSEIDON2_H
"

/-! ## Part 7: Tests -/

section Tests

def testConstRef : IO Unit := do
  IO.println "=== Test: ConstRef identifiers ==="
  let refs := [
    ConstRef.mds 3,
    ConstRef.mdsInternal 3,
    ConstRef.mdsExternal 3,
    ConstRef.roundConst 0 3,
    ConstRef.roundConst 63 3
  ]
  for r in refs do
    IO.println s!"  {repr r} → {r.toCIdent}"
  IO.println ""

def testPoseidonConfig : IO Unit := do
  IO.println "=== Test: PoseidonConfig ==="
  let configs := [
    ("BN254 t=3", PoseidonConfig.bn254_t3),
    ("BN254 t=5", PoseidonConfig.bn254_t5),
    ("Goldilocks t=12", PoseidonConfig.goldilocks_t12)
  ]
  for (name, c) in configs do
    let spec := PermutationSpec.fromConfig c
    IO.println s!"  {name}:"
    IO.println s!"    Rounds: RF={c.fullRounds}, RP={c.partialRounds}, total={c.totalRounds}"
    IO.println s!"    Estimated muls: {spec.estimateMulCount}"
  IO.println ""

def testCodeGen : IO Unit := do
  IO.println "=== Test: Code Generation (BN254 t=3) ==="
  let config := PoseidonConfig.bn254_t3
  let code := genPoseidon2Header config
  -- Only print first 2000 chars to avoid flooding output
  IO.println (code.take 2000)
  IO.println "... (truncated)"
  IO.println ""

#eval! do
  testConstRef
  testPoseidonConfig
  -- Uncomment to see full generated code:
  -- testCodeGen

end Tests

end AmoLean.Protocols.Poseidon.MatExpr
