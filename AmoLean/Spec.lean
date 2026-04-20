/-
  AmoLean Spec — Unified input language for the trzk compiler.

  Users write specs using this type. The compiler dispatches to
  the appropriate backend (NTT optimized pipeline, Poseidon codegen,
  or Sigma-SPL matrix path) based on the spec structure.
-/

namespace AmoLean.Spec

/-- Supported finite fields. -/
inductive Field where
  | babybear    -- p = 2^31 - 2^27 + 1 = 2013265921
  | koalabear   -- p = 2^31 - 2^24 + 1 = 2130706433
  | mersenne31  -- p = 2^31 - 1 = 2147483647
  | goldilocks  -- p = 2^64 - 2^32 + 1
  deriving Repr, BEq, Inhabited

/-- Hardware targets for optimization. -/
inductive Hardware where
  | scalar  -- Generic scalar (ARM Cortex-A76 cost model)
  | neon    -- ARM NEON SIMD (4 lanes)
  | avx2    -- x86 AVX2 SIMD (8 lanes)
  deriving Repr, BEq, Inhabited

/-- The unified spec type. -/
inductive Spec where
  /-- NTT over a finite field. Size must be a power of 2. -/
  | ntt (field : Field) (size : Nat)
  /-- Poseidon2 S-box (x^exp) for a field with given state size. -/
  | poseidon2Sbox (field : Field) (stateSize : Nat) (exp : Nat := 5)
  /-- DFT (Walsh-Hadamard) matrix of size n. -/
  | dft (n : Nat)
  /-- Identity matrix of size n. -/
  | identity (n : Nat)
  /-- Kronecker product of two specs. -/
  | kron (a b : Spec)
  /-- Matrix composition (apply b first, then a). -/
  | compose (a b : Spec)
  deriving Repr, Inhabited

/-- Compute the dimensions of a spec. Returns none on dimension mismatch. -/
def Spec.dims : Spec → Option (Nat × Nat)
  | .ntt _ size => some (size, size)
  | .poseidon2Sbox _ stateSize _ => some (stateSize, stateSize)
  | .dft n => some (n, n)
  | .identity n => some (n, n)
  | .kron a b => do
    let (m1, n1) ← a.dims
    let (m2, n2) ← b.dims
    some (m1 * m2, n1 * n2)
  | .compose a b => do
    let (m1, k1) ← a.dims
    let (k2, n2) ← b.dims
    if k1 = k2 then some (m1, n2) else none

/-- Check if a spec is a named algorithm (routes to optimized pipeline). -/
def Spec.isNamedAlgorithm : Spec → Bool
  | .ntt .. => true
  | .poseidon2Sbox .. => true
  | _ => false

/-- Check if a spec is a composable matrix operation. -/
def Spec.isMatrix : Spec → Bool
  | .dft .. => true
  | .identity .. => true
  | .kron .. => true
  | .compose .. => true
  | _ => false

end AmoLean.Spec

-- Re-export at top level for user convenience
open AmoLean.Spec in
def ntt := Spec.ntt
open AmoLean.Spec in
def poseidon2Sbox := Spec.poseidon2Sbox
open AmoLean.Spec in
def dft := Spec.dft
open AmoLean.Spec in
def identity' := Spec.identity  -- identity conflicts with Lean's prelude
open AmoLean.Spec in
def kron := Spec.kron
open AmoLean.Spec in
def compose := Spec.compose
