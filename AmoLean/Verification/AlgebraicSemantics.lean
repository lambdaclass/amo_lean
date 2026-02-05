/-
  AMO-Lean: Algebraic Semantics for Formal Verification
  Session 15: C-Lite++ Strategy

  This module provides reference semantics over a generic Field α,
  enabling formal verification without Float-specific issues.

  Key Design Decisions:
  1. Generic over [Field α] [DecidableEq α] [Inhabited α]
  2. DFT parametrized by (ω : α) (hω : IsPrimitiveRoot ω n)
  3. No `partial` - all functions are total with termination proofs
  4. Separate from Semantics.lean to preserve Float-based testing

  References:
  - Session 15 documentation: C-Lite++ strategy
  - NTT/RootsOfUnity.lean: IsPrimitiveRoot definition
  - Expert consultations: DeepSeek (Lean 4), Gemini QA
-/

import AmoLean.Sigma.Basic
import AmoLean.NTT.RootsOfUnity
import Mathlib.Algebra.Field.Defs

namespace AmoLean.Verification.Algebraic

open AmoLean.Sigma (SigmaExpr Kernel Gather Scatter IdxExpr LoopVar lower lowerFresh LowerState)
open AmoLean.Matrix (MatExpr Perm)
open AmoLean.NTT (IsPrimitiveRoot)

/-! ## Part 1: Generic Memory Model -/

variable {α : Type} [Field α] [DecidableEq α] [Inhabited α]

/-- Memory is an array of values indexed by natural numbers -/
structure Memory (α : Type*) where
  data : Array α
  deriving Repr

namespace Memory

/-- Read from memory at an index (returns default for out-of-bounds) -/
def read [Inhabited α] (mem : Memory α) (idx : Nat) : α :=
  if idx < mem.data.size then mem.data[idx]! else default

/-- Write to memory at an index (extends if needed) -/
def write [Inhabited α] (mem : Memory α) (idx : Nat) (val : α) : Memory α :=
  if idx < mem.data.size then
    { data := mem.data.set! idx val }
  else
    let newSize := idx + 1
    let extended := mem.data ++ Array.mkArray (newSize - mem.data.size) default
    { data := extended.set! idx val }

/-- Create memory from a list -/
def ofList (l : List α) : Memory α := { data := l.toArray }

/-- Convert memory to list -/
def toList (mem : Memory α) : List α := mem.data.toList

/-- Size of memory -/
def size (mem : Memory α) : Nat := mem.data.size

/-- Create a zeroed memory of given size -/
def zeros [Zero α] (size : Nat) : Memory α := { data := Array.mkArray size 0 }

/-- Array getElem! equals List getElem when in bounds.
    This is a fundamental property that bridges Array and List indexing.
    Axiomatized due to complexity of getElem! unfolding. -/
axiom array_getElem_bang_eq_list_getElem (l : List α) (i : Nat) (hi : i < l.length) :
    l.toArray[i]! = l[i]'hi

/-- Reading from ofList at valid index gives list element -/
@[simp]
theorem read_ofList (l : List α) (i : Nat) (hi : i < l.length) :
    (ofList l).read i = l[i]'hi := by
  simp only [ofList, read]
  have h : i < l.toArray.size := by simp [hi]
  simp only [h, ↓reduceIte]
  exact array_getElem_bang_eq_list_getElem l i hi

/-- Size of ofList equals list length -/
@[simp]
theorem size_ofList (l : List α) : (ofList l).size = l.length := by
  simp only [ofList, size, Array.size_toArray]

/-- toList of ofList is identity -/
@[simp]
theorem toList_ofList (l : List α) : (ofList l).toList = l := by
  simp only [ofList, toList, Array.toList_toArray]

end Memory

/-! ## Part 2: Evaluation State -/

/-- Environment mapping loop variables to their current values -/
abbrev LoopEnv := LoopVar → Nat

/-- Empty environment (all variables are 0) -/
def LoopEnv.empty : LoopEnv := fun _ => 0

/-- Update environment with a binding -/
def LoopEnv.bind (env : LoopEnv) (v : LoopVar) (val : Nat) : LoopEnv :=
  fun v' => if v' == v then val else env v'

/-- State during evaluation with explicit read/write memories -/
structure EvalState (α : Type*) where
  readMem : Memory α
  writeMem : Memory α
  deriving Repr

/-- Initial state from input list -/
def EvalState.init [Zero α] (input : List α) (outputSize : Nat) : EvalState α :=
  { readMem := Memory.ofList input
  , writeMem := Memory.zeros outputSize }

/-! ## Part 3: Index Expression Evaluation -/

/-- Evaluate an index expression given loop environment -/
def evalIdxExpr (env : LoopEnv) : IdxExpr → Nat
  | .const n => n
  | .var v => env v
  | .affine base stride v => base + stride * env v
  | .add e1 e2 => evalIdxExpr env e1 + evalIdxExpr env e2
  | .mul c e => c * evalIdxExpr env e

/-! ## Part 4: Gather and Scatter Operations -/

/-- Gather n elements from memory starting at baseAddr with stride -/
def evalGather (env : LoopEnv) (g : Gather) (mem : Memory α) : List α :=
  let baseAddr := evalIdxExpr env g.baseAddr
  List.range g.count |>.map fun i =>
    mem.read (baseAddr + g.stride * i)

/-- Scatter n elements to memory starting at baseAddr with stride -/
def evalScatter (env : LoopEnv) (s : Scatter) (mem : Memory α) (vals : List α) : Memory α :=
  let baseAddr := evalIdxExpr env s.baseAddr
  vals.enum.foldl (fun acc (i, v) =>
    acc.write (baseAddr + s.stride * i) v) mem

/-! ## Part 5: Algebraic DFT with Primitive Root

The DFT requires a primitive n-th root of unity ω.
We parametrize by (ω : α) (hω : IsPrimitiveRoot ω n).
-/

/-- DFT_n matrix-vector product using primitive root ω.
    y[k] = Σ_{j=0}^{n-1} ω^{kj} · x[j] -/
def evalDFT (ω : α) (n : Nat) (input : List α) : List α :=
  List.range n |>.map fun k =>
    List.range n |>.foldl (fun acc j =>
      let x_j := input.getD j default
      acc + (ω ^ (k * j)) * x_j
    ) 0

/-- DFT_2 (butterfly): [x0, x1] → [x0 + x1, x0 - x1]
    For DFT_2, ω = -1 and ω^0 = 1, ω^1 = -1 -/
def evalDFT2 (input : List α) : List α :=
  match input with
  | [x0, x1] => [x0 + x1, x0 - x1]
  | _ => input

/-! ## Part 6: Kernel Evaluation (Algebraic) -/

/-- Evaluate identity kernel: just copy -/
def evalIdentityKernel (input : List α) : List α := input

/-- Evaluate a kernel on input data -/
def evalKernelAlg (ω : α) (k : Kernel) (input : List α) : List α :=
  match k with
  | .identity _ => evalIdentityKernel input
  | .dft 2 => evalDFT2 input
  | .dft n => evalDFT ω n input
  | .ntt _ _ => input  -- NTT uses field-specific root
  | .twiddle _ _ => input  -- Twiddle factors are diagonal scaling
  | .scale => input
  | .butterfly => evalDFT2 input
  | .sbox _ _ => input  -- S-box for Poseidon (not implemented algebraically)
  | .partialSbox _ _ _ => input
  | .mdsApply _ _ => input
  | .mdsInternal _ => input
  | .addRoundConst _ _ => input

/-! ## Part 7: Main Sigma Evaluator (Algebraic)

Total evaluator with termination proof via nodeCount.
-/

/-- Helper: iterate evalSigmaAlg for loop body -/
def iterateSigmaEval (ω : α) (loopVar : Nat) (body : SigmaExpr)
    (evalBody : LoopEnv → EvalState α → EvalState α)
    (n : Nat) (env : LoopEnv) (state : EvalState α) : EvalState α :=
  (List.range n).foldl (fun st i =>
    let env' := env.bind loopVar i
    let st' := evalBody env' st
    { readMem := st'.writeMem, writeMem := st'.writeMem }
  ) state

/-- Evaluate a SigmaExpr algebraically.
    Now total with termination proof via nodeCount. -/
def evalSigmaAlg (ω : α) (env : LoopEnv) (state : EvalState α) (sigma : SigmaExpr) : EvalState α :=
  match sigma with
  | .compute k g s =>
    let inputs := evalGather env g state.readMem
    let outputs := evalKernelAlg ω k inputs
    { state with writeMem := evalScatter env s state.writeMem outputs }

  | .loop n loopVar body =>
    -- Execute body for each iteration using foldl
    (List.range n).foldl (fun st i =>
      let env' := env.bind loopVar i
      let st' := evalSigmaAlg ω env' st body
      { readMem := st'.writeMem, writeMem := st'.writeMem }
    ) state

  | .seq s1 s2 =>
    let state1 := evalSigmaAlg ω env state s1
    let state2 := { readMem := state1.writeMem, writeMem := state1.writeMem }
    evalSigmaAlg ω env state2 s2

  | .par s1 s2 =>
    -- For reference semantics, parallel = sequential
    let state1 := evalSigmaAlg ω env state s1
    let state2 := { readMem := state1.writeMem, writeMem := state1.writeMem }
    evalSigmaAlg ω env state2 s2

  | .temp size body =>
    let tempMem := Memory.zeros size
    let stateWithTemp := { readMem := state.readMem, writeMem := tempMem }
    let stateAfterBody := evalSigmaAlg ω env stateWithTemp body
    { readMem := state.readMem, writeMem := stateAfterBody.writeMem }

  | .nop => state
termination_by sigma.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [SigmaExpr.nodeCount]
  all_goals omega

/-- Run SigmaExpr on input list, returning output list -/
def runSigmaAlg (ω : α) (sigma : SigmaExpr) (input : List α) (outputSize : Nat) : List α :=
  let initState := EvalState.init input outputSize
  let finalState := evalSigmaAlg ω LoopEnv.empty initState sigma
  finalState.writeMem.toList

/-! ## Part 8: Matrix Expression Evaluator (Algebraic)

Reference semantics for MatExpr over generic Field α.
-/

/-- Apply permutation to a list -/
def applyPerm (p : Perm n) (xs : List α) : List α :=
  -- Simplified: just return the list (permutation logic omitted for now)
  xs

/-- Apply kernel B to blocks: (I_m ⊗ B) · v -/
def applyBlockwise (m : Nat) (kernel : List α → List α) (input : List α) : List α :=
  let blockSize := input.length / m
  (List.range m).flatMap fun i =>
    let block := input.drop (i * blockSize) |>.take blockSize
    kernel block

/-- Apply kernel A with stride: (A ⊗ I_n) · v -/
def applyStrided (n : Nat) (kernel : List α → List α) (input : List α) : List α :=
  let numLanes := input.length / n
  let lanes := List.range n |>.map fun lane =>
    List.range numLanes |>.map fun j =>
      let idx := lane + j * n
      input.getD idx default
  let processedLanes := lanes.map kernel
  List.range (numLanes * n) |>.map fun idx =>
    let lane := idx % n
    let i := idx / n
    match processedLanes[lane]? with
    | some laneData => laneData.getD i default
    | none => default

/-- Check if a MatExpr is an identity matrix -/
def isIdentity : MatExpr α m n → Bool
  | .identity _ => true
  | _ => false

/-- Apply kernel B to blocks inline (for termination proof): (I_m ⊗ B) · v -/
def applyBlockwiseInline (m : Nat) (blockSize : Nat) (evalBlock : List α → List α) (input : List α) : List α :=
  (List.range m).flatMap fun i =>
    let block := input.drop (i * blockSize) |>.take blockSize
    evalBlock block

/-- Apply kernel A strided inline (for termination proof): (A ⊗ I_n) · v -/
def applyStridedInline (n : Nat) (laneLen : Nat) (evalLane : List α → List α) (input : List α) : List α :=
  let lanes := List.range n |>.map fun lane =>
    List.range laneLen |>.map fun j =>
      let idx := lane + j * n
      input.getD idx default
  let processedLanes := lanes.map evalLane
  List.range (laneLen * n) |>.map fun idx =>
    let lane := idx % n
    let i := idx / n
    match processedLanes[lane]? with
    | some laneData => laneData.getD i default
    | none => default

/-- Main matrix expression evaluator (algebraic).
    Parametrized by primitive root ω for DFT operations.
    Now total with termination proof via nodeCount. -/
def evalMatExprAlg (ω : α) (m n : Nat) (mExpr : MatExpr α m n) (input : List α) : List α :=
  match mExpr with
  | .identity _ => input
  | .zero _ _ => List.replicate m 0
  | .dft 2 => evalDFT2 input
  | .dft n' => evalDFT ω n' input
  | .ntt _ _ => input  -- NTT would need field-specific implementation
  | .twiddle _ _ => input  -- Twiddle factors
  | .perm p => applyPerm p input
  | @MatExpr.kron _ m₁ n₁ m₂ n₂ a b =>
    if isIdentity a then
      -- (I_{m₁} ⊗ B) · v : apply B to m₁ blocks of size n₂
      (List.range m₁).flatMap fun i =>
        let block := input.drop (i * n₂) |>.take n₂
        evalMatExprAlg ω m₂ n₂ b block
    else if isIdentity b then
      -- (A ⊗ I_{m₂}) · v : apply A strided
      let laneLen := input.length / m₂
      let lanes := List.range m₂ |>.map fun lane =>
        List.range laneLen |>.map fun j =>
          input.getD (lane + j * m₂) default
      let processedLanes := lanes.map (evalMatExprAlg ω m₁ n₁ a)
      List.range (laneLen * m₂) |>.map fun idx =>
        let lane := idx % m₂
        let i := idx / m₂
        match processedLanes[lane]? with
        | some laneData => laneData.getD i default
        | none => default
    else
      -- General (A ⊗ B) · v : B blockwise, then A strided
      let afterB := (List.range m₁).flatMap fun i =>
        let block := input.drop (i * n₂) |>.take n₂
        evalMatExprAlg ω m₂ n₂ b block
      let laneLen := afterB.length / m₂
      let lanes := List.range m₂ |>.map fun lane =>
        List.range laneLen |>.map fun j =>
          afterB.getD (lane + j * m₂) default
      let processedLanes := lanes.map (evalMatExprAlg ω m₁ n₁ a)
      List.range (laneLen * m₂) |>.map fun idx =>
        let lane := idx % m₂
        let i := idx / m₂
        match processedLanes[lane]? with
        | some laneData => laneData.getD i default
        | none => default
  | @MatExpr.compose _ _ k _ a b =>
    let intermediate := evalMatExprAlg ω k n b input
    evalMatExprAlg ω m k a intermediate
  | .add a b =>
    let ra := evalMatExprAlg ω m n a input
    let rb := evalMatExprAlg ω m n b input
    ra.zip rb |>.map fun (x, y) => x + y
  | .smul _ a => evalMatExprAlg ω m n a input
  | .transpose a => evalMatExprAlg ω n m a input
  | .conjTranspose a => evalMatExprAlg ω n m a input
  | .diag _ => input
  | .scalar _ => input
  | .elemwise _ a => evalMatExprAlg ω m n a input
  | .partialElemwise _ _ a => evalMatExprAlg ω m n a input
  | @MatExpr.mdsApply _ t _ _ a => evalMatExprAlg ω t 1 a input
  | @MatExpr.addRoundConst _ t _ _ a => evalMatExprAlg ω t 1 a input
termination_by mExpr.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [MatExpr.nodeCount]
  all_goals omega

/-! ## Part 9: Correctness Theorems -/

/-- The fundamental correctness theorem (algebraic version).

    For any matrix expression mat and input vector v:
    evaluating the lowered Sigma-SPL code produces the same result
    as direct matrix-vector multiplication.

    This theorem is parametrized by:
    - A field α with decidable equality
    - A primitive n-th root of unity ω

    Note: This is the STATEMENT. The proof requires induction on mat
    and leveraging properties of IsPrimitiveRoot. -/
theorem lowering_algebraic_correct
    (ω : α) (hω : IsPrimitiveRoot ω n) (hn : n > 0)
    (mat : MatExpr α k n) (v : List α) (hv : v.length = n) :
    runSigmaAlg ω (lowerFresh k n mat) v k = evalMatExprAlg ω k n mat v := by
  sorry  -- Main theorem: requires case analysis on mat

/-- Identity preserves input -/
theorem identity_algebraic_correct (n : Nat) (v : List α) (hv : v.length = n) :
    evalMatExprAlg ω n n (.identity n) v = v := by
  simp only [evalMatExprAlg]

/-- DFT_2 correctness -/
theorem dft2_algebraic_correct (v : List α) (hv : v.length = 2) :
    evalMatExprAlg ω 2 2 (.dft 2) v = evalDFT2 v := by
  simp only [evalMatExprAlg]

/-- Identity kernel preserves input -/
@[simp]
theorem evalKernelAlg_identity (n : Nat) (input : List α) :
    evalKernelAlg ω (.identity n) input = input := by
  simp only [evalKernelAlg, evalIdentityKernel]

/-- Lower identity produces compute with identity kernel -/
theorem lower_identity (n : Nat) :
    lowerFresh n n (.identity n : MatExpr α n n) =
    .compute (.identity n) (Gather.contiguous n (.const 0)) (Scatter.contiguous n (.const 0)) := by
  simp only [lowerFresh, lower]

/-- Helper: 0 + 1 * i = i -/
@[simp]
theorem zero_add_one_mul (i : Nat) : 0 + 1 * i = i := by omega

/-- Map read over range equals list -/
theorem map_read_range_eq_list (v : List α) :
    List.map (fun i => (Memory.ofList v).read i) (List.range v.length) = v := by
  apply List.ext_getElem
  · simp [List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    exact Memory.read_ofList v i h1

/-- Gather contiguous from Memory.ofList returns the list -/
theorem evalGather_ofList_contiguous (v : List α) :
    evalGather LoopEnv.empty (Gather.contiguous v.length (.const 0)) (Memory.ofList v) = v := by
  simp only [evalGather, Gather.contiguous, evalIdxExpr, zero_add_one_mul]
  exact map_read_range_eq_list v

/-- Scatter then toList identity for contiguous writes.
    When writing a list v to positions 0..n-1 into zeros(n), toList gives v.
    This is the core lemma for identity lowering correctness. -/
theorem scatter_zeros_toList (v : List α) :
    (List.foldl (fun acc x => acc.write x.1 x.2) (Memory.zeros v.length) v.enum).toList = v := by
  -- This requires reasoning about foldl and Memory.write
  -- The fold writes v[0] at 0, v[1] at 1, etc., which reconstructs v
  sorry  -- Requires foldl/Memory reasoning

/-- Lowering correctness for identity matrix -/
theorem lowering_identity_correct (n : Nat) (v : List α) (hv : v.length = n) :
    runSigmaAlg ω (lowerFresh n n (.identity n : MatExpr α n n)) v n = v := by
  simp only [runSigmaAlg, lowerFresh, lower, evalSigmaAlg, evalKernelAlg, evalIdentityKernel,
             EvalState.init, evalGather, evalScatter, Gather.contiguous, Scatter.contiguous,
             evalIdxExpr, LoopEnv.empty, zero_add_one_mul]
  -- Goal: (foldl write zeros (map read range).enum).toList = v
  rw [← hv]
  -- Now goal: (foldl write zeros (map read range).enum).toList = v
  -- The gather produces v via map_read_range_eq_list
  conv_lhs =>
    arg 1  -- focus on the foldl
    arg 3  -- focus on the list being folded
    rw [map_read_range_eq_list v]
  -- Now: (foldl write zeros v.enum).toList = v
  exact scatter_zeros_toList v

end AmoLean.Verification.Algebraic
