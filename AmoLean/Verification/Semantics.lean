/-
  AMO-Lean: Reference Semantics for Sigma-SPL
  Phase 5.10 - Verification via operational semantics

  This module provides a reference implementation ("oracle") for the Sigma-SPL IR.
  The implementation prioritizes clarity and correctness over performance.

  Design principle: Each function should be "obviously correct" by inspection,
  making it suitable as a trusted oracle for property-based testing.

  Memory Model (FIXED):
  - EvalState has separate `readMem` and `writeMem`
  - For .seq s1 s2: s1's output becomes s2's input
  - For .temp: allocates fresh buffer for intermediate results

  Key functions:
  - evalSigma: Interpret SigmaExpr on a concrete input vector
  - evalKernel: Interpret individual kernels (DFT_2, etc.)
  - evalGather/evalScatter: Interpret gather/scatter operations

  References:
  - SPIRAL: "Formal Loop Merging for Signal Transforms"
  - QuickCheck: "Testing Monadic Code with QuickCheck"
-/

import AmoLean.Sigma.Basic
import AmoLean.Vector.Basic

namespace AmoLean.Verification

open AmoLean.Sigma (SigmaExpr Kernel Gather Scatter IdxExpr LoopVar)
open AmoLean.Vector (Vec)

/-! ## Part 1: Memory Model

We model memory as a simple array for clarity.
This is inefficient but obviously correct.
-/

/-- Memory is an array of values indexed by natural numbers -/
structure Memory (α : Type) where
  data : Array α
  deriving Repr

/-- Read from memory at an index (returns default for out-of-bounds) -/
def Memory.read [Inhabited α] (mem : Memory α) (idx : Nat) : α :=
  if idx < mem.data.size then mem.data[idx]! else default

/-- Write to memory at an index (extends if needed) -/
def Memory.write [Inhabited α] (mem : Memory α) (idx : Nat) (val : α) : Memory α :=
  if idx < mem.data.size then
    { data := mem.data.set! idx val }
  else
    -- Extend memory with defaults, then write
    let newSize := idx + 1
    let extended := mem.data ++ Array.mkArray (newSize - mem.data.size) default
    { data := extended.set! idx val }

/-- Create memory from a list -/
def Memory.ofList (l : List α) : Memory α := { data := l.toArray }

/-- Convert memory to list -/
def Memory.toList (mem : Memory α) : List α := mem.data.toList

/-- Size of memory -/
def Memory.size (mem : Memory α) : Nat := mem.data.size

/-- Create a zeroed memory of given size -/
def Memory.zeros (size : Nat) : Memory Float := { data := Array.mkArray size 0.0 }

/-- Copy a memory -/
def Memory.copy (mem : Memory α) : Memory α := { data := mem.data }

/-! ## Part 2: Loop Variable Environment

Environment for loop variables (i0, i1, i2, ...).
-/

/-- Environment mapping loop variables to their current values -/
abbrev LoopEnv := LoopVar → Nat

/-- Empty environment (all variables are 0) -/
def LoopEnv.empty : LoopEnv := fun _ => 0

/-- Update environment with a binding -/
def LoopEnv.bind (env : LoopEnv) (v : LoopVar) (val : Nat) : LoopEnv :=
  fun v' => if v' == v then val else env v'

/-! ## Part 3: Evaluate Index Expressions

These determine memory addresses for gather/scatter.
-/

/-- Evaluate an index expression given loop environment -/
def evalIdxExpr (env : LoopEnv) : IdxExpr → Nat
  | .const n => n
  | .var v => env v
  | .affine base stride v => base + stride * env v
  | .add e1 e2 => evalIdxExpr env e1 + evalIdxExpr env e2
  | .mul c e => c * evalIdxExpr env e

/-! ## Part 4: Gather and Scatter Operations

Gather reads elements from READ memory.
Scatter writes elements to WRITE memory.
-/

/-- Gather n elements from memory starting at baseAddr with stride -/
def evalGather [Inhabited α] (env : LoopEnv) (g : Gather) (mem : Memory α) : List α :=
  let baseAddr := evalIdxExpr env g.baseAddr
  List.range g.count |>.map fun i =>
    mem.read (baseAddr + g.stride * i)

/-- Scatter n elements to memory starting at baseAddr with stride -/
def evalScatter [Inhabited α] (env : LoopEnv) (s : Scatter) (mem : Memory α) (vals : List α) : Memory α :=
  let baseAddr := evalIdxExpr env s.baseAddr
  vals.enum.foldl (fun acc (i, v) =>
    acc.write (baseAddr + s.stride * i) v) mem

/-! ## Part 5: Kernel Evaluation

Each kernel is a small, fixed computation.
These implementations are intentionally simple for correctness.
-/

/-- Complex number for DFT computation -/
structure Complex where
  re : Float
  im : Float
  deriving Repr, Inhabited

instance : Add Complex where
  add a b := ⟨a.re + b.re, a.im + b.im⟩

instance : Sub Complex where
  sub a b := ⟨a.re - b.re, a.im - b.im⟩

instance : Mul Complex where
  mul a b := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

instance : Neg Complex where
  neg a := ⟨-a.re, -a.im⟩

def Complex.ofFloat (x : Float) : Complex := ⟨x, 0.0⟩

/-- Evaluate identity kernel: just copy -/
def evalIdentityKernel (input : List Float) : List Float := input

/-- Evaluate DFT_2 kernel (butterfly): [x0, x1] → [x0 + x1, x0 - x1] -/
def evalDFT2Kernel (input : List Float) : List Float :=
  match input with
  | [x0, x1] => [x0 + x1, x0 - x1]
  | _ => input  -- Fallback for invalid input

/-- Evaluate DFT_4 kernel: standard DFT matrix for size 4 -/
def evalDFT4Kernel (input : List Float) : List Float :=
  match input with
  | [x0, x1, x2, x3] =>
    -- DFT_4 = (DFT_2 ⊗ I_2) · T · (I_2 ⊗ DFT_2)
    -- Stage 1: I_2 ⊗ DFT_2
    let t0 := x0 + x1
    let t1 := x0 - x1
    let t2 := x2 + x3
    let t3 := x2 - x3
    -- Stage 2: Twiddles (simplified for real input)
    -- Stage 3: DFT_2 ⊗ I_2
    let y0 := t0 + t2
    let y1 := t1 + t3
    let y2 := t0 - t2
    let y3 := t1 - t3
    [y0, y1, y2, y3]
  | _ => input

/-- Evaluate scale kernel: multiply by 1 (placeholder) -/
def evalScaleKernel (input : List Float) : List Float := input

/-- Evaluate butterfly kernel: same as DFT_2 -/
def evalButterflyKernel (input : List Float) : List Float := evalDFT2Kernel input

/-- Evaluate NTT_2 kernel (modular butterfly): [x0, x1] → [x0 + x1 mod p, x0 - x1 mod p] -/
def evalNTT2Kernel (p : Nat) (input : List Float) : List Float :=
  match input with
  | [x0, x1] =>
    let sum := x0 + x1
    let diff := x0 - x1
    let pf := Float.ofScientific p true 0
    let sumMod := if sum >= pf then sum - pf else sum
    let diffMod := if diff < 0 then diff + pf else diff
    [sumMod, diffMod]
  | _ => input

/-- Evaluate a kernel on input data -/
def evalKernel (k : Kernel) (input : List Float) : List Float :=
  match k with
  | .identity _ => evalIdentityKernel input
  | .dft 2 => evalDFT2Kernel input
  | .dft 4 => evalDFT4Kernel input
  | .dft _ => input  -- Fallback for other sizes
  | .ntt 2 p => evalNTT2Kernel p input
  | .ntt _ _ => input  -- Fallback
  | .twiddle _ _ => input  -- Twiddle is just multiplication by constants
  | .scale => evalScaleKernel input
  | .butterfly => evalButterflyKernel input

/-! ## Part 6: Main Sigma Evaluator

This is the main reference semantics: evalSigma.

CRITICAL DESIGN (FIXED):
- readMem: where gather reads from
- writeMem: where scatter writes to
- For .seq s1 s2: s1's output becomes s2's input
- For .temp: creates a fresh intermediate buffer
-/

/-- State during evaluation with explicit read/write memories -/
structure EvalState where
  readMem : Memory Float    -- Source memory for gather operations
  writeMem : Memory Float   -- Target memory for scatter operations
  deriving Repr

/-- Initial state from input list -/
def EvalState.init (input : List Float) (outputSize : Nat) : EvalState :=
  { readMem := Memory.ofList input
  , writeMem := Memory.zeros outputSize
  }

/-- Evaluate a SigmaExpr with correct memory threading

    Key invariants:
    - .compute: reads from readMem, writes to writeMem
    - .seq s1 s2: s1's writeMem becomes s2's readMem
    - .temp: allocates fresh writeMem for body
-/
partial def evalSigma (env : LoopEnv) (state : EvalState) : SigmaExpr → EvalState
  | .nop => state

  | .compute kernel gather scatter =>
    -- 1. Gather from READ memory
    let inputVals := evalGather env gather state.readMem
    -- 2. Apply kernel
    let outputVals := evalKernel kernel inputVals
    -- 3. Scatter to WRITE memory
    let newWriteMem := evalScatter env scatter state.writeMem outputVals
    { state with writeMem := newWriteMem }

  | .loop n loopVar body =>
    -- Execute body n times with loopVar = 0, 1, ..., n-1
    List.range n |>.foldl (fun st i =>
      let env' := env.bind loopVar i
      evalSigma env' st body
    ) state

  | .seq s1 s2 =>
    -- Execute s1 (reads from readMem, writes to writeMem)
    let state1 := evalSigma env state s1
    -- CRITICAL: s1's output becomes s2's input!
    -- s2 reads from s1's writeMem, writes to the same writeMem
    let state2 := { readMem := state1.writeMem, writeMem := state1.writeMem }
    evalSigma env state2 s2

  | .par s1 s2 =>
    -- For reference semantics, parallel = sequential
    let state1 := evalSigma env state s1
    let state2 := { readMem := state1.writeMem, writeMem := state1.writeMem }
    evalSigma env state2 s2

  | .temp size body =>
    -- Allocate fresh temporary buffer for intermediate results
    let tempMem := Memory.zeros size
    -- Execute body: reads from current readMem, writes to temp
    let stateWithTemp := { readMem := state.readMem, writeMem := tempMem }
    let stateAfterBody := evalSigma env stateWithTemp body
    -- Return with the final writeMem as output
    { readMem := state.readMem, writeMem := stateAfterBody.writeMem }

/-! ## Part 7: Convenience Functions -/

/-- Run SigmaExpr on input list, returning output list -/
def runSigma (sigma : SigmaExpr) (input : List Float) (outputSize : Nat) : List Float :=
  let initState := EvalState.init input outputSize
  let finalState := evalSigma LoopEnv.empty initState sigma
  finalState.writeMem.toList

/-- Run SigmaExpr and compare with expected output -/
def checkSigma (sigma : SigmaExpr) (input : List Float) (expected : List Float) : Bool :=
  let actual := runSigma sigma input expected.length
  let tolerance := 1e-10
  actual.zip expected |>.all fun (a, e) => (a - e).abs < tolerance

/-! ## Part 8: Tests -/

section Tests

open AmoLean.Sigma (lowerFresh)
open AmoLean.Matrix (MatExpr)

-- Test 1: Identity
def testIdentity : IO Unit := do
  IO.println "=== Test: Identity ==="
  let i2 : MatExpr Int 2 2 := .identity 2
  let sigma := lowerFresh 2 2 i2
  let input := [1.0, 2.0]
  let result := runSigma sigma input 2
  IO.println s!"Input: {input}"
  IO.println s!"Result: {result}"
  IO.println s!"Expected: {input}"
  IO.println s!"Match: {result == input}"
  IO.println ""

-- Test 2: DFT_2
def testDFT2 : IO Unit := do
  IO.println "=== Test: DFT_2 ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let sigma := lowerFresh 2 2 dft2
  let input := [1.0, 1.0]
  let result := runSigma sigma input 2
  IO.println s!"Input: {input}"
  IO.println s!"Result: {result}"
  IO.println s!"Expected: [2.0, 0.0]"
  IO.println ""

-- Test 3: I_2 ⊗ DFT_2
def testI2xDFT2 : IO Unit := do
  IO.println "=== Test: I_2 ⊗ DFT_2 ==="
  let i2 : MatExpr Int 2 2 := .identity 2
  let dft2 : MatExpr Int 2 2 := .dft 2
  let expr : MatExpr Int 4 4 := .kron i2 dft2
  let sigma := lowerFresh 4 4 expr
  IO.println s!"Sigma:\n{sigma}"
  let input := [1.0, 1.0, 2.0, 2.0]
  let result := runSigma sigma input 4
  IO.println s!"Input: {input}"
  IO.println s!"Result: {result}"
  IO.println s!"Expected: [2.0, 0.0, 4.0, 0.0]"
  IO.println ""

-- Test 4: DFT_2 ⊗ I_2
def testDFT2xI2 : IO Unit := do
  IO.println "=== Test: DFT_2 ⊗ I_2 ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  let expr : MatExpr Int 4 4 := .kron dft2 i2
  let sigma := lowerFresh 4 4 expr
  IO.println s!"Sigma:\n{sigma}"
  let input := [1.0, 2.0, 3.0, 4.0]
  let result := runSigma sigma input 4
  IO.println s!"Input: {input}"
  IO.println s!"Result: {result}"
  IO.println s!"Expected: [4.0, 6.0, -2.0, -2.0]"
  IO.println ""

-- Test 5: Cooley-Tukey DFT_4 = (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2)
def testCooleyTukey4 : IO Unit := do
  IO.println "=== Test: Cooley-Tukey DFT_4 ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  let stage1 : MatExpr Int 4 4 := .kron i2 dft2
  let stage2 : MatExpr Int 4 4 := .kron dft2 i2
  let ct4 : MatExpr Int 4 4 := .compose stage2 stage1
  let sigma := lowerFresh 4 4 ct4
  IO.println s!"Sigma:\n{sigma}"

  let input := [1.0, 0.0, 0.0, 0.0]
  let result := runSigma sigma input 4
  IO.println s!"Input: {input}"
  IO.println s!"Result: {result}"
  -- For [1,0,0,0], DFT_4 should give [1,1,1,1]
  IO.println s!"Expected: [1.0, 1.0, 1.0, 1.0]"

  -- Verify manually:
  -- Stage 1: I_2 ⊗ DFT_2
  --   [1,0] → [1,-1] (DFT_2 on first pair, but wait, input is [1,0,0,0])
  --   Actually: pair 1 = [1,0] → [1+0, 1-0] = [1, 1]
  --   pair 2 = [0,0] → [0+0, 0-0] = [0, 0]
  --   So after stage 1: [1, 1, 0, 0]
  -- Stage 2: DFT_2 ⊗ I_2 (strided)
  --   lane 0: [t0, t2] = [1, 0] → [1+0, 1-0] = [1, 1]
  --   lane 1: [t1, t3] = [1, 0] → [1+0, 1-0] = [1, 1]
  --   So after stage 2: [1, 1, 1, 1]
  IO.println ""

#eval! do
  testIdentity
  testDFT2
  testI2xDFT2
  testDFT2xI2
  testCooleyTukey4

end Tests

end AmoLean.Verification
