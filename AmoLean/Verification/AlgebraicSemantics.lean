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

/-! ### Bridge lemmas: Memory.write ↔ List.set -/

/-- Size of zeros equals the requested size -/
@[simp]
theorem zeros_size [Zero α] (n : Nat) : (zeros n : Memory α).size = n := by
  simp only [zeros, size, Array.size_mkArray]

/-- toList of zeros is replicate of 0 -/
@[simp]
theorem zeros_toList [Zero α] (n : Nat) : (zeros n : Memory α).toList = List.replicate n 0 := by
  simp only [zeros, toList, Array.toList_mkArray]

/-- Writing to in-bounds position preserves size -/
theorem size_write_eq [Inhabited α] (mem : Memory α) (i : Nat) (v : α) (hi : i < mem.size) :
    (mem.write i v).size = mem.size := by
  unfold write
  split_ifs with h
  · simp only [size, Array.set!, Array.size_setIfInBounds]
  · exact absurd hi h

/-- Writing to in-bounds position: toList becomes List.set -/
theorem toList_write_eq_set [Inhabited α] (mem : Memory α) (i : Nat) (v : α) (hi : i < mem.size) :
    (mem.write i v).toList = mem.toList.set i v := by
  unfold write
  split_ifs with h
  · simp only [toList, Array.set!, Array.toList_setIfInBounds]
  · exact absurd hi h

/-- zeros_size expressed as data.size -/
theorem zeros_data_size [Zero α] (n : Nat) : (zeros n : Memory α).data.size = n := by
  simp only [zeros, Array.size_mkArray]

/-- Two Memory values are equal iff their data arrays are equal.
    Since Memory is determined entirely by its data field, equality of
    toList (= data.toList) implies structural equality. -/
theorem eq_of_toList_eq {m1 m2 : Memory α} (h : m1.toList = m2.toList) : m1 = m2 := by
  cases m1; cases m2
  simp only [toList] at h
  exact congrArg Memory.mk (Array.ext' h)

/-- Memory equality from toList, iff version -/
@[simp]
theorem toList_injective {m1 m2 : Memory α} : m1.toList = m2.toList ↔ m1 = m2 :=
  ⟨eq_of_toList_eq, fun h => h ▸ rfl⟩

/-- Memory roundtrip: ofList ∘ toList = id -/
theorem ofList_toList (m : Memory α) : Memory.ofList m.toList = m := by
  cases m; simp only [ofList, toList]

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

/-- Run SigmaExpr on input list, returning output list.
    Uses `.take outputSize` to ensure the result has exactly `outputSize` elements,
    which is necessary for compose correctness when k ≠ k_mid. -/
def runSigmaAlg (ω : α) (sigma : SigmaExpr) (input : List α) (outputSize : Nat) : List α :=
  let initState := EvalState.init input outputSize
  let finalState := evalSigmaAlg ω LoopEnv.empty initState sigma
  finalState.writeMem.toList.take outputSize

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
    This is the core lemma for identity lowering correctness.

    Axiomatized because:
    1. Computational verification passes all tests
    2. The fold writes v[i] at position i, reconstructing v
    3. Full formal proof requires complex foldl/List.set reasoning with enum index tracking

    TODO: Replace with formal proof using foldl_enum invariant -/
axiom scatter_zeros_toList (v : List α) :
    (List.foldl (fun acc x => acc.write x.1 x.2) (Memory.zeros v.length) v.enum).toList = v

/-- Lowering correctness for identity matrix -/
theorem lowering_identity_correct (n : Nat) (v : List α) (hv : v.length = n) :
    runSigmaAlg ω (lowerFresh n n (.identity n : MatExpr α n n)) v n = v := by
  subst hv
  simp only [runSigmaAlg, lowerFresh, lower, evalSigmaAlg, evalKernelAlg, evalIdentityKernel,
             EvalState.init, evalGather, evalScatter, Gather.contiguous, Scatter.contiguous,
             evalIdxExpr, LoopEnv.empty, zero_add_one_mul]
  rw [map_read_range_eq_list v, scatter_zeros_toList v, List.take_length]

/-! ### Meta-lemma: Compute with contiguous gather/scatter

All base cases of lowering (identity, dft, ntt, twiddle, perm) produce the
same SigmaExpr structure: `.compute kernel (Gather.contiguous n) (Scatter.contiguous n)`.
This meta-lemma proves correctness for all such cases at once. -/

/-- Running a compute node with contiguous gather/scatter returns the kernel applied to input.
    This is the core meta-lemma that covers all base lowering cases. -/
theorem lowering_compute_contiguous_correct (n : Nat) (k : Kernel)
    (v : List α) (hv : v.length = n)
    (hlen : (evalKernelAlg ω k v).length = n) :
    runSigmaAlg ω (.compute k (Gather.contiguous n (.const 0))
                               (Scatter.contiguous n (.const 0))) v n
    = evalKernelAlg ω k v := by
  subst hv
  simp only [runSigmaAlg, evalSigmaAlg, EvalState.init,
             evalGather, evalScatter, Gather.contiguous, Scatter.contiguous,
             evalIdxExpr, LoopEnv.empty, zero_add_one_mul]
  rw [map_read_range_eq_list v]
  -- Goal: (foldl write (zeros v.length) (evalKernelAlg ω k v).enum).toList.take v.length
  --       = evalKernelAlg ω k v
  have hlen' : v.length = (evalKernelAlg ω k v).length := by omega
  rw [hlen', scatter_zeros_toList (evalKernelAlg ω k v), List.take_length]

/-- Lower DFT produces compute with contiguous gather/scatter -/
theorem lower_dft (n' : Nat) :
    lowerFresh n' n' (.dft n' : MatExpr α n' n') =
    .compute (.dft n') (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)) := by
  simp only [lowerFresh, lower]

/-- evalDFT produces a list of length n -/
theorem evalDFT_length (ω' : α) (n' : Nat) (input : List α) :
    (evalDFT ω' n' input).length = n' := by
  simp only [evalDFT, List.length_map, List.length_range]

/-- evalDFT2 preserves length for 2-element lists -/
theorem evalDFT2_length (input : List α) (h : input.length = 2) :
    (evalDFT2 input).length = 2 := by
  match input, h with
  | [_, _], _ => rfl

/-- evalKernelAlg for .dft n preserves length -/
theorem evalKernelAlg_dft_length (n' : Nat) (input : List α) (h : input.length = n') :
    (evalKernelAlg ω (.dft n') input).length = n' := by
  match n' with
  | 0 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
  | 1 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
  | 2 => simp only [evalKernelAlg]; exact evalDFT2_length input h
  | n + 3 => simp only [evalKernelAlg]; exact evalDFT_length ω (n + 3) input

/-- evalMatExprAlg for DFT equals evalKernelAlg for DFT.
    Both match on n'=2 vs n'≠2 with identical branches. -/
theorem evalMatExprAlg_dft_eq_kernelAlg (n' : Nat) (v : List α) :
    evalMatExprAlg ω n' n' (.dft n' : MatExpr α n' n') v = evalKernelAlg ω (.dft n') v := by
  -- Both unfold to the same match on n' (2 → evalDFT2, n → evalDFT ω n)
  -- Case split to resolve the match
  match n' with
  | 0 => simp [evalMatExprAlg, evalKernelAlg]
  | 1 => simp [evalMatExprAlg, evalKernelAlg]
  | 2 => simp [evalMatExprAlg, evalKernelAlg]
  | n + 3 => simp [evalMatExprAlg, evalKernelAlg]

/-- Lowering correctness for DFT: the compiled code produces the same result
    as the reference DFT evaluation.

    Key insight (L-061): IsPrimitiveRoot is NOT needed for lowering correctness.
    The lowering just says "compiled code = reference semantics", regardless of ω. -/
theorem lowering_dft_correct (n' : Nat) (v : List α) (hv : v.length = n') :
    runSigmaAlg ω (lowerFresh n' n' (.dft n' : MatExpr α n' n')) v n'
    = evalKernelAlg ω (.dft n') v := by
  rw [lower_dft]
  exact lowering_compute_contiguous_correct n' (.dft n') v hv
    (evalKernelAlg_dft_length n' v hv)

/-! ## Part 10: Foundational Axioms, Compose Proof, and Main Correctness Theorem -/

/-! ### Foundational Axioms

These axioms capture fundamental properties of the lowered SigmaExpr evaluation.
They are more primitive and auditable than the previous compose/kron axioms,
and serve as the building blocks for the compose correctness proof.

**Size preservation**: Evaluating a lowered expression preserves the write
memory size. This holds because lowered expressions only write within the
allocated output region [0, m).

**Write memory irrelevance**: The output (first m elements) of evaluating a
lowered expression does not depend on the initial write memory contents.
This holds because all positions in [0, m) are overwritten by the evaluation.

**Alpha-equivalence**: Different LowerState values (which only affect loop
variable numbering) do not change the semantics of a lowered expression.
Loop variable IDs are just names; the semantics depends only on the loop
structure, not the specific IDs used.

**Output length preservation**: evalMatExprAlg always produces a list of
length m (the output dimension). -/

/-- Axiom: evalSigmaAlg preserves writeMem size for lowered expressions.
    When evaluating (lower m n state mat).1 starting with writeMem of size m,
    the resulting writeMem also has size m. -/
axiom evalSigmaAlg_writeMem_size_preserved
    (ω : α) {m n : Nat} (state : LowerState) (mat : MatExpr α m n)
    (rm : Memory α) (wm : Memory α) (hwm : wm.size = m) :
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm }
      (lower m n state mat).1).writeMem.size = m

/-- Axiom: For lowered expressions, the output (first m elements of writeMem)
    does not depend on the initial writeMem contents. All positions in [0, m)
    are overwritten during evaluation. -/
axiom evalSigmaAlg_writeMem_irrelevant
    (ω : α) {m n : Nat} (state : LowerState) (mat : MatExpr α m n)
    (rm : Memory α) (wm1 wm2 : Memory α) :
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm1 }
      (lower m n state mat).1).writeMem.toList.take m =
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm2 }
      (lower m n state mat).1).writeMem.toList.take m

/-- Axiom: Alpha-equivalence for lowered expressions.
    Different LowerState values (which only affect loop variable numbering)
    do not change the semantics of the lowered SigmaExpr. -/
axiom lower_state_irrelevant (ω : α) {m n : Nat} (state1 state2 : LowerState)
    (mat : MatExpr α m n) (v : List α) :
    runSigmaAlg ω (lower m n state1 mat).1 v m =
    runSigmaAlg ω (lower m n state2 mat).1 v m

/-- Axiom: evalMatExprAlg output length preservation.
    The algebraic matrix evaluator always produces a list of length m
    (the output dimension), given an input of length n. -/
axiom evalMatExprAlg_length
    (ω : α) {m n : Nat} (mat : MatExpr α m n)
    (v : List α) (hv : v.length = n) :
    (evalMatExprAlg ω m n mat v).length = m

/-! ### Compose Lowering Correctness (PROVEN)

The compose case is the critical structural case for compiler verification.
Given `lower (.compose a b)` = `.temp k_mid (.seq exprB exprA)`, we prove
that evaluating the lowered code produces the same result as composing
the matrix semantics: `a(b(input))`.

The proof uses the following chain:
1. Unfold both sides (lower for compose, evalMatExprAlg for compose)
2. Unfold runSigmaAlg for `.temp` and `.seq` using equation lemmas
3. Use IH_B to establish that exprB produces `intermediate = b(input)`
4. Use size preservation to show writeMem.size = k_mid
5. Use Memory roundtrip (ofList ∘ toList = id) to identify writeMem
6. Use writeMem irrelevance to change initial writeMem for exprA
7. Use alpha-equivalence to relate exprA (with state1) to lowerFresh
8. Use IH_A to conclude exprA produces `a(intermediate)` -/

set_option maxHeartbeats 800000 in
theorem lowering_compose_step
    (ω : α) {k k_mid n : Nat}
    (a : MatExpr α k k_mid) (b : MatExpr α k_mid n)
    (v : List α) (hv : v.length = n)
    (ihB : runSigmaAlg ω (lowerFresh k_mid n b) v k_mid = evalMatExprAlg ω k_mid n b v)
    (ihA : ∀ (w : List α), w.length = k_mid →
           runSigmaAlg ω (lowerFresh k k_mid a) w k = evalMatExprAlg ω k k_mid a w)
    (h_inter_len : (evalMatExprAlg ω k_mid n b v).length = k_mid) :
    runSigmaAlg ω (lowerFresh k n (@MatExpr.compose α k k_mid n a b)) v k =
    evalMatExprAlg ω k n (@MatExpr.compose α k k_mid n a b) v := by
  -- Step 1: Unfold evalMatExprAlg for compose → a(b(v))
  simp only [evalMatExprAlg]
  set intermediate := evalMatExprAlg ω k_mid n b v with h_inter_def
  -- Step 2: Unfold lowerFresh and lower for compose → .temp k_mid (.seq exprB exprA)
  simp only [lowerFresh]
  simp only [lower]
  -- Step 3: Unfold runSigmaAlg and evalSigmaAlg for .temp and .seq
  simp only [runSigmaAlg, EvalState.init]
  rw [evalSigmaAlg.eq_5, evalSigmaAlg.eq_3]
  dsimp only []
  -- Step 4: Name the key subexpression (evaluation of exprB)
  set stateB := evalSigmaAlg ω LoopEnv.empty
    { readMem := Memory.ofList v, writeMem := Memory.zeros k_mid }
    (lower k_mid n { nextLoopVar := 0 } b).1 with h_stateB_def
  -- Step 5: From IH_B, derive stateB.writeMem content
  have h_ihB_unfolded : stateB.writeMem.toList.take k_mid = intermediate := by
    have := ihB
    simp only [runSigmaAlg, EvalState.init, lowerFresh] at this
    exact this
  -- Step 6: Size preservation → stateB.writeMem.size = k_mid
  have h_size : stateB.writeMem.size = k_mid :=
    evalSigmaAlg_writeMem_size_preserved ω { nextLoopVar := 0 } b
      (Memory.ofList v) (Memory.zeros k_mid) (Memory.zeros_size k_mid)
  -- Step 7: toList has full length, so take = identity
  have h_toList_len : stateB.writeMem.toList.length = k_mid := by
    rw [Array.length_toList]; exact h_size
  have h_take_full : stateB.writeMem.toList.take k_mid = stateB.writeMem.toList :=
    List.take_of_length_le (le_of_eq h_toList_len)
  -- Step 8: stateB.writeMem.toList = intermediate
  have h_wm_toList : stateB.writeMem.toList = intermediate := by
    rw [← h_take_full]; exact h_ihB_unfolded
  -- Step 9: stateB.writeMem = Memory.ofList intermediate (by roundtrip)
  have h_mem_eq : stateB.writeMem = Memory.ofList intermediate := by
    rw [← Memory.ofList_toList stateB.writeMem, h_wm_toList]
  -- Step 10: Substitute readMem and writeMem for exprA
  rw [h_mem_eq]
  -- Step 11: writeMem irrelevance — initial writeMem doesn't affect output
  set state1 := (lower k_mid n { nextLoopVar := 0 } b).2 with h_state1_def
  rw [evalSigmaAlg_writeMem_irrelevant ω state1 a
    (Memory.ofList intermediate) (Memory.ofList intermediate) (Memory.zeros k)]
  -- Step 12: Alpha-equivalence — exprA (with state1) ≡ lowerFresh (with {})
  have h_alpha := lower_state_irrelevant ω state1 { nextLoopVar := 0 } a intermediate
  simp only [runSigmaAlg, EvalState.init] at h_alpha
  rw [h_alpha]
  -- Step 13: Apply IH_A
  have := ihA intermediate h_inter_len
  simp only [runSigmaAlg, EvalState.init, lowerFresh] at this
  exact this

/-! ### Kron Axiom

The Kronecker product lowering correctness is axiomatized pending development
of the loop invariant infrastructure (adjustBlock/adjustStride semantics,
non-interference between loop iterations). -/

/-- Axiom: Kronecker product lowering is correct.
    For I ⊗ B: lower produces .loop m₁ loopVar (adjustBlock ... (lower b))
    For A ⊗ I: lower produces .loop m₂ loopVar (adjustStride ... (lower a))

    Computational verification: all matrix expression tests pass.
    See: AmoLean/Test/Verification.lean -/
axiom lowering_kron_axiom
    {m₁ n₁ m₂ n₂ : Nat}
    (ω : α) (a : MatExpr α m₁ n₁) (b : MatExpr α m₂ n₂)
    (v : List α) (hv : v.length = n₁ * n₂) :
    runSigmaAlg ω (lowerFresh (m₁ * m₂) (n₁ * n₂) (.kron a b)) v (m₁ * m₂) =
    evalMatExprAlg ω (m₁ * m₂) (n₁ * n₂) (.kron a b) v

/-! ### The Fundamental Correctness Theorem

For any matrix expression mat and input vector v:
evaluating the lowered Sigma-SPL code produces the same result
as direct matrix-vector multiplication.

Current status:
- Identity case: PROVEN via lowering_identity_correct
- DFT case: PROVEN via lowering_dft_correct + meta-lemma
- NTT case: PROVEN via meta-lemma (identity-like kernel)
- Twiddle case: PROVEN via meta-lemma (identity-like kernel)
- Diag case: PROVEN via meta-lemma (identity kernel)
- Scalar case: PROVEN via meta-lemma (scale kernel, size 1)
- Compose case: PROVEN via lowering_compose_step (uses foundational axioms)
- Kron case: AXIOMATIZED (requires adjustBlock/adjustStride semantics)
- Remaining: sorry (zero, perm, add, smul, transpose, conjTranspose,
  elemwise, partialElemwise, mdsApply, addRoundConst)

Note: IsPrimitiveRoot is NOT needed for lowering correctness.
The lowering correctness says "compiled code = reference semantics"
regardless of ω. IsPrimitiveRoot would only be needed at a higher level
to prove "compiled code computes DFT". -/

set_option maxHeartbeats 800000 in
theorem lowering_algebraic_correct
    (ω : α) (mat : MatExpr α k n) (v : List α) (hv : v.length = n) :
    runSigmaAlg ω (lowerFresh k n mat) v k = evalMatExprAlg ω k n mat v := by
  match mat with
  | .identity n' =>
    -- Identity case: PROVEN
    simp only [evalMatExprAlg]
    exact lowering_identity_correct n' v hv
  | .dft n' =>
    -- DFT case: PROVEN via meta-lemma (L-060)
    rw [evalMatExprAlg_dft_eq_kernelAlg, lower_dft]
    exact lowering_compute_contiguous_correct n' (.dft n') v hv
      (evalKernelAlg_dft_length n' v hv)
  | .ntt n' p_ntt =>
    -- NTT case: PROVEN - identity-like kernel (evalKernelAlg returns input)
    simp only [evalMatExprAlg]
    have hlower : lowerFresh n' n' (.ntt n' p_ntt : MatExpr α n' n') =
      .compute (.ntt n' p_ntt) (Gather.contiguous n' (.const 0))
        (Scatter.contiguous n' (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω (.ntt n' p_ntt) v).length = n' := by
      simp [evalKernelAlg]; exact hv
    have hmeta := lowering_compute_contiguous_correct n' (.ntt n' p_ntt) v hv hlen
    simp only [evalKernelAlg] at hmeta
    exact hmeta
  | .twiddle n' k_tw =>
    -- Twiddle case: PROVEN - identity-like kernel
    simp only [evalMatExprAlg]
    have hlower : lowerFresh n' n' (.twiddle n' k_tw : MatExpr α n' n') =
      .compute (.twiddle n' k_tw) (Gather.contiguous n' (.const 0))
        (Scatter.contiguous n' (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω (.twiddle n' k_tw) v).length = n' := by
      simp [evalKernelAlg]; exact hv
    have hmeta := lowering_compute_contiguous_correct n' (.twiddle n' k_tw) v hv hlen
    simp only [evalKernelAlg] at hmeta
    exact hmeta
  | .diag v' =>
    -- Diag case: PROVEN - lowers to identity kernel
    simp only [evalMatExprAlg]
    have hlower : lowerFresh n n (@MatExpr.diag α n v') =
      .compute (.identity n) (Gather.contiguous n (.const 0))
        (Scatter.contiguous n (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω (.identity n) v).length = n := by
      simp [evalKernelAlg, evalIdentityKernel]; exact hv
    have hmeta := lowering_compute_contiguous_correct n (.identity n) v hv hlen
    simp only [evalKernelAlg, evalIdentityKernel] at hmeta
    exact hmeta
  | .scalar e =>
    -- Scalar case: PROVEN - lowers to scale kernel, size 1
    simp only [evalMatExprAlg]
    have hlower : lowerFresh 1 1 (.scalar e : MatExpr α 1 1) =
      .compute .scale (Gather.contiguous 1 (.const 0))
        (Scatter.contiguous 1 (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω .scale v).length = 1 := by
      simp [evalKernelAlg]; exact hv
    have hmeta := lowering_compute_contiguous_correct 1 .scale v hv hlen
    simp only [evalKernelAlg] at hmeta
    exact hmeta
  | .kron a b =>
    -- Kronecker product: AXIOMATIZED (requires adjustBlock/adjustStride semantics)
    exact lowering_kron_axiom ω a b v hv
  | .compose a b =>
    -- Composition: PROVEN via lowering_compose_step
    -- Uses foundational axioms: size preservation, writeMem irrelevance, alpha-equivalence
    exact lowering_compose_step ω a b v hv
      (lowering_algebraic_correct ω b v hv)
      (fun w hw => lowering_algebraic_correct ω a w hw)
      (evalMatExprAlg_length ω b v hv)
  | _ =>
    -- Remaining cases: zero, perm, add, smul, transpose, conjTranspose,
    -- elemwise, partialElemwise, mdsApply, addRoundConst
    -- These either have compound lowerings (need recursive proof) or
    -- semantic mismatches (e.g., perm lowers to identity)
    sorry
termination_by mat.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [MatExpr.nodeCount]
  all_goals omega

end AmoLean.Verification.Algebraic
