/-
  Poseidon2 Pure Specification

  This is an executable reference implementation of Poseidon2 in pure Lean.
  It does NOT use MatExpr or any IR - it's a direct implementation for:
  1. Understanding the algorithm
  2. Generating test vectors
  3. Differential fuzzing against generated C code

  NOTE: We use simple Nat arithmetic with explicit modulo operations
  instead of Mathlib's ZMod to avoid heavy compilation times.

  The implementation follows the Poseidon2 paper (eprint.iacr.org/2023/323).
-/

namespace AmoLean.Protocols.Poseidon.Spec

/-! ## Field Arithmetic

Simple modular arithmetic using Nat. All operations take the prime as parameter.
-/

/-- Modular addition -/
def modAdd (p : Nat) (a b : Nat) : Nat :=
  (a + b) % p

/-- Modular subtraction -/
def modSub (p : Nat) (a b : Nat) : Nat :=
  (a + p - b % p) % p

/-- Modular multiplication -/
def modMul (p : Nat) (a b : Nat) : Nat :=
  (a * b) % p

/-- Modular exponentiation (square-and-multiply) -/
def modPow (p : Nat) (base : Nat) : Nat → Nat
  | 0 => 1
  | 1 => base % p
  | n + 2 =>
    let half := modPow p base ((n + 2) / 2)
    let squared := modMul p half half
    if (n + 2) % 2 == 0 then squared
    else modMul p squared base
termination_by n => n

/-! ## S-box Implementation

The S-box is x^α. For α=5, we use the square chain:
x^5 = x * (x^2)^2 = x * x^4

This requires only 3 multiplications instead of 4.
-/

/-- Square chain for x^5: x → x² → x⁴ → x⁵ (3 multiplications) -/
def sbox5 (p : Nat) (x : Nat) : Nat :=
  let x2 := modMul p x x      -- x²
  let x4 := modMul p x2 x2    -- x⁴
  modMul p x x4               -- x⁵

/-- General S-box for any exponent -/
def sbox (p : Nat) (alpha : Nat) (x : Nat) : Nat :=
  if alpha == 5 then sbox5 p x
  else modPow p x alpha

/-! ## State and Matrix Types

State is represented as an Array of Nat values.
-/

/-- State type: array of field elements -/
abbrev State := Array Nat

/-- Create zero state of size t -/
def zeroState (t : Nat) : State :=
  Array.mkArray t 0

/-! ## MDS Matrix Operations

Poseidon2 uses TWO different MDS operations:
1. External MDS (for full rounds): state[i] += sum(state)
2. Internal MDS (for partial rounds): uses diagonal multiplication

For t=3, the external MDS is: state[i] = state[i] + sum
The internal MDS for t=3 uses diagonal [1, 1, 2]:
  state[0] += sum
  state[1] += sum
  state[2] = 2*state[2] + sum

Reference: HorizenLabs/poseidon2 implementation
-/

/-- MDS matrix as nested array (for reference, not used directly in Poseidon2) -/
def mds3 : Array (Array Nat) := #[
  #[2, 1, 1],
  #[1, 2, 1],
  #[1, 1, 3]
]

/-- Matrix-vector multiplication: result[i] = Σⱼ M[i,j] * v[j] -/
def mdsMultiply (p : Nat) (M : Array (Array Nat)) (v : State) : State :=
  M.map fun row =>
    row.zipWith v (modMul p) |>.foldl (modAdd p) 0

/-- External MDS for Poseidon2 (used in full rounds)
    state[i] = state[i] + sum(state) for all i -/
def mdsExternal (p : Nat) (state : State) : State :=
  let sum := state.foldl (modAdd p) 0
  state.map (modAdd p sum)

/-- Internal MDS for Poseidon2 t=3 (used in partial rounds)
    Uses diagonal [1, 1, 2]:
    state[0] += sum
    state[1] += sum
    state[2] = 2*state[2] + sum -/
def mdsInternal3 (p : Nat) (state : State) : State :=
  if state.size != 3 then state else
  let s0 := state.get! 0
  let s1 := state.get! 1
  let s2 := state.get! 2
  let sum := modAdd p (modAdd p s0 s1) s2
  #[modAdd p s0 sum,
    modAdd p s1 sum,
    modAdd p (modAdd p s2 s2) sum]  -- 2*s2 + sum

/-! ## Poseidon2 Parameters -/

/-- Generic Poseidon2 parameters structure -/
structure Params where
  /-- Field prime -/
  prime : Nat
  /-- State size -/
  t : Nat
  /-- S-box exponent (typically 5) -/
  alpha : Nat
  /-- Number of full rounds -/
  fullRounds : Nat
  /-- Number of partial rounds -/
  partialRounds : Nat
  /-- MDS matrix -/
  mds : Array (Array Nat)
  /-- Round constants: array of arrays (one per round, each of size t) -/
  roundConstants : Array (Array Nat)
  deriving Repr

/-! ## Round Functions -/

/-- Add round constants to state -/
def addRoundConstants (p : Nat) (rc : Array Nat) (state : State) : State :=
  state.zipWith rc (modAdd p)

/-- Apply S-box to ALL elements (full round) -/
def sboxFull (p : Nat) (alpha : Nat) (state : State) : State :=
  state.map (sbox p alpha)

/-- Apply S-box only to element 0 (partial round) -/
def sboxPartial (p : Nat) (alpha : Nat) (state : State) : State :=
  if state.size > 0 then
    state.set! 0 (sbox p alpha (state.get! 0))
  else
    state

/-- One full round: AddRC → S-box(all) → External MDS -/
def fullRound (params : Params) (roundIdx : Nat) (state : State) : State :=
  let rc := params.roundConstants.getD roundIdx #[]
  let withRC := addRoundConstants params.prime rc state
  let afterSbox := sboxFull params.prime params.alpha withRC
  mdsExternal params.prime afterSbox

/-- One partial round: AddRC → S-box(first) → Internal MDS -/
def partialRound (params : Params) (roundIdx : Nat) (state : State) : State :=
  let rc := params.roundConstants.getD roundIdx #[]
  let withRC := addRoundConstants params.prime rc state
  let afterSbox := sboxPartial params.prime params.alpha withRC
  mdsInternal3 params.prime afterSbox

/-! ## Poseidon2 Permutation

Structure: [RF/2 full] → [RP partial] → [RF/2 full]
-/

/-- Apply n rounds starting at roundIdx -/
def applyRounds (roundFn : Nat → State → State)
    (startIdx : Nat) (numRounds : Nat) (state : State) : State :=
  (List.range numRounds).foldl
    (fun s i => roundFn (startIdx + i) s)
    state

/-- Poseidon2 permutation
    Structure: Initial MDS → [RF/2 full] → [RP partial] → [RF/2 full] -/
def poseidon2Permutation (params : Params) (input : State) : State :=
  let halfFull := params.fullRounds / 2

  -- Initial linear layer (external MDS before first round)
  let state := mdsExternal params.prime input

  -- First RF/2 full rounds
  let state := applyRounds (fullRound params) 0 halfFull state

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

/-- Absorb one block into state (XOR into first r positions) -/
def absorbBlock (params : Params) (block : Array Nat) (state : State) : State :=
  let state' := state.mapIdx fun i v =>
    if i < block.size then modAdd params.prime v (block.getD i 0)
    else v
  poseidon2Permutation params state'

/-- Squeeze: return first element of state -/
def squeeze (state : State) : Nat :=
  state.getD 0 0

/-- Hash a list of field elements (simplified, single block) -/
def poseidon2Hash (params : Params) (input : Array Nat) : Nat :=
  let state := zeroState params.t
  let state := absorbBlock params input state
  squeeze state

/-! ## Test Parameters -/

/-- Small test prime for fast testing -/
def testPrime : Nat := 17

/-- Generate simple round constants for testing -/
def makeTestRoundConstants (p : Nat) (t : Nat) (numRounds : Nat) : Array (Array Nat) :=
  Array.range numRounds |>.map fun r =>
    Array.range t |>.map fun i => (r * t + i + 1) % p

/-- Test parameters with small prime -/
def testParams : Params := {
  prime := testPrime
  t := 3
  alpha := 5
  fullRounds := 8
  partialRounds := 56
  mds := mds3
  roundConstants := makeTestRoundConstants testPrime 3 64
}

/-! ## BN254 Parameters -/

/-- BN254 scalar field prime -/
def bn254Prime : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BN254 parameters for t=3 -/
def bn254Params : Params := {
  prime := bn254Prime
  t := 3
  alpha := 5
  fullRounds := 8
  partialRounds := 56
  mds := mds3
  roundConstants := makeTestRoundConstants bn254Prime 3 64  -- Placeholder
}

/-! ## Test Execution -/

-- Test with small prime (fast)
#eval sbox5 testPrime 2  -- 2^5 = 32 mod 17 = 15

#eval mdsMultiply testPrime mds3 #[1, 2, 3]
-- [2*1+1*2+1*3, 1*1+2*2+1*3, 1*1+1*2+3*3] = [7, 8, 12]

#eval fullRound testParams 0 #[1, 1, 1]

#eval poseidon2Permutation testParams #[1, 2, 3]

#eval poseidon2Hash testParams #[1, 2]

end AmoLean.Protocols.Poseidon.Spec
