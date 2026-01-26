/-
  Poseidon2 Pure Specification

  This is an executable reference implementation of Poseidon2 in pure Lean.
  It does NOT use MatExpr or any IR - it's a direct implementation for:
  1. Understanding the algorithm
  2. Generating test vectors
  3. Differential fuzzing against generated C code

  The implementation follows the Poseidon2 paper (eprint.iacr.org/2023/323).

  Structure:
  - Poseidon2 permutation: [RF/2 full rounds] → [RP partial rounds] → [RF/2 full rounds]
  - Full round: AddRoundConstants → S-box(all) → MDS
  - Partial round: AddRoundConstants → S-box(first only) → MDS
-/

import Mathlib.Data.ZMod.Basic

namespace AmoLean.Protocols.Poseidon.Spec

/-! ## Field Arithmetic

We work over ZMod p for a prime p. For BN254:
p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
-/

/-- Generic Poseidon2 parameters structure -/
structure Params (p : Nat) (t : Nat) where
  /-- S-box exponent (typically 5) -/
  alpha : Nat
  /-- Number of full rounds -/
  fullRounds : Nat
  /-- Number of partial rounds -/
  partialRounds : Nat
  /-- MDS matrix as a function (i, j) → coefficient -/
  mds : Fin t → Fin t → ZMod p
  /-- Round constants: round index → state position → constant -/
  roundConstants : Nat → Fin t → ZMod p
  deriving Repr

/-! ## S-box Implementation

The S-box is x^α. For α=5, we use the square chain:
x^5 = x * (x^2)^2 = x * x^4

This requires only 3 multiplications instead of 4.
-/

/-- Square chain for x^5: x → x² → x⁴ → x⁵ (3 multiplications) -/
def sbox5 (x : ZMod p) : ZMod p :=
  let x2 := x * x      -- x²
  let x4 := x2 * x2    -- x⁴
  x * x4               -- x⁵

/-- General S-box for any exponent (uses binary exponentiation) -/
def sbox (alpha : Nat) (x : ZMod p) : ZMod p :=
  x ^ alpha

/-- Optimized S-box that uses square chain for α=5 -/
def sboxOpt (alpha : Nat) (x : ZMod p) : ZMod p :=
  if alpha == 5 then sbox5 x
  else x ^ alpha

/-! ## MDS Matrix Multiplication

For t=3, the MDS matrix is:
  [2, 1, 1]
  [1, 2, 1]
  [1, 1, 3]

We represent state as a function Fin t → ZMod p for generality.
-/

/-- State type: a vector of t field elements -/
abbrev State (p : Nat) (t : Nat) := Fin t → ZMod p

/-- Matrix-vector multiplication: result[i] = Σⱼ M[i,j] * v[j] -/
def mdsMultiply (M : Fin t → Fin t → ZMod p) (v : State p t) : State p t :=
  fun i => Finset.univ.sum fun j => M i j * v j

/-! ## Round Functions -/

/-- Add round constants to state -/
def addRoundConstants (rc : Fin t → ZMod p) (state : State p t) : State p t :=
  fun i => state i + rc i

/-- Apply S-box to ALL elements (full round) -/
def sboxFull (alpha : Nat) (state : State p t) : State p t :=
  fun i => sboxOpt alpha (state i)

/-- Apply S-box only to element 0 (partial round) -/
def sboxPartial (alpha : Nat) (state : State p t) : State p t :=
  fun i =>
    if i.val == 0 then sboxOpt alpha (state i)
    else state i

/-- One full round: AddRC → S-box(all) → MDS -/
def fullRound (params : Params p t) (roundIdx : Nat) (state : State p t) : State p t :=
  let withRC := addRoundConstants (params.roundConstants roundIdx) state
  let afterSbox := sboxFull params.alpha withRC
  mdsMultiply params.mds afterSbox

/-- One partial round: AddRC → S-box(first) → MDS -/
def partialRound (params : Params p t) (roundIdx : Nat) (state : State p t) : State p t :=
  let withRC := addRoundConstants (params.roundConstants roundIdx) state
  let afterSbox := sboxPartial params.alpha withRC
  mdsMultiply params.mds afterSbox

/-! ## Poseidon2 Permutation

Structure: [RF/2 full] → [RP partial] → [RF/2 full]
-/

/-- Apply n rounds of a given round function starting at roundIdx -/
def applyRounds (roundFn : Nat → State p t → State p t)
    (startIdx : Nat) (numRounds : Nat) (state : State p t) : State p t :=
  (List.range numRounds).foldl
    (fun s i => roundFn (startIdx + i) s)
    state

/-- Poseidon2 permutation -/
def poseidon2Permutation (params : Params p t) (input : State p t) : State p t :=
  let halfFull := params.fullRounds / 2

  -- First RF/2 full rounds
  let state := applyRounds (fullRound params) 0 halfFull input

  -- RP partial rounds
  let state := applyRounds (partialRound params) halfFull params.partialRounds state

  -- Final RF/2 full rounds
  let state := applyRounds (fullRound params) (halfFull + params.partialRounds) halfFull state

  state

/-! ## Sponge Construction (for variable-length hashing)

Poseidon2 hash uses a sponge construction:
- Rate r = t - 1 (absorb r elements at a time)
- Capacity c = 1 (one element reserved for security)
-/

/-- Initialize sponge state (all zeros) -/
def initState : State p t := fun _ => 0

/-- Absorb one block of r elements into state -/
def absorbBlock (params : Params p t) (block : Fin (t-1) → ZMod p) (state : State p t) : State p t :=
  -- XOR block into first r positions of state
  let state' : State p t := fun i =>
    if h : i.val < t - 1 then
      state i + block ⟨i.val, h⟩
    else
      state i
  -- Apply permutation
  poseidon2Permutation params state'

/-- Squeeze: return first element of state -/
def squeeze (state : State p t) : ZMod p :=
  state ⟨0, by omega⟩

/-- Hash a list of field elements (simplified, assumes input fits in one block) -/
def poseidon2Hash (params : Params p t) (input : List (ZMod p)) : ZMod p :=
  -- Pad input to r elements
  let padded := input ++ List.replicate (t - 1 - input.length) 0
  -- Create block function
  let block : Fin (t-1) → ZMod p := fun i =>
    padded.getD i.val 0
  -- Absorb and squeeze
  let state := absorbBlock params block initState
  squeeze state

/-! ## Concrete Parameters for BN254 t=3

For testing and validation.
-/

/-- BN254 scalar field prime -/
def bn254Prime : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- MDS matrix for t=3: [[2,1,1], [1,2,1], [1,1,3]] -/
def mds3 : Fin 3 → Fin 3 → ZMod bn254Prime
  | ⟨0, _⟩, ⟨0, _⟩ => 2
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, ⟨2, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 2
  | ⟨1, _⟩, ⟨2, _⟩ => 1
  | ⟨2, _⟩, ⟨0, _⟩ => 1
  | ⟨2, _⟩, ⟨1, _⟩ => 1
  | ⟨2, _⟩, ⟨2, _⟩ => 3
  | ⟨n+3, h⟩, _ => absurd h (by omega)
  | _, ⟨n+3, h⟩ => absurd h (by omega)

/-- Placeholder round constants (for testing structure, not security) -/
def testRoundConstants : Nat → Fin 3 → ZMod bn254Prime :=
  fun round i => (round * 3 + i.val + 1 : Nat)

/-- Test parameters for BN254 t=3 -/
def testParams : Params bn254Prime 3 := {
  alpha := 5
  fullRounds := 8
  partialRounds := 56
  mds := mds3
  roundConstants := testRoundConstants
}

/-! ## Test Execution

These tests verify the structure of the implementation.
For production, replace testRoundConstants with actual constants from the reference.
-/

/-- Test: S-box of 2 should equal 2^5 = 32 -/
#eval (sbox5 (2 : ZMod bn254Prime))  -- Should be 32

/-- Test: MDS multiply with simple input -/
#eval mdsMultiply mds3 (fun i => (i.val + 1 : ZMod bn254Prime))
-- Input: [1, 2, 3]
-- Expected: [2*1+1*2+1*3, 1*1+2*2+1*3, 1*1+1*2+3*3] = [7, 8, 12]

/-- Test: One full round -/
#eval fullRound testParams 0 (fun _ => (1 : ZMod bn254Prime))

/-- Test: Full permutation -/
#eval poseidon2Permutation testParams (fun i => (i.val + 1 : ZMod bn254Prime))

end AmoLean.Protocols.Poseidon.Spec
