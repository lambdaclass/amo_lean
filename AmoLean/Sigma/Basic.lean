/-
  AMO-Lean: Sigma-SPL Intermediate Representation
  Phase 5.5 - Lowering from MatExpr to Loop IR

  This module implements the Σ-SPL (Sigma-SPL) intermediate representation
  from the SPIRAL project. Σ-SPL extends SPL with iterative sums, providing
  a bridge between high-level matrix formulas and low-level loop code.

  Key concepts from SPIRAL:
  - Σ_{i=0}^{n-1} (S_i · A_i · G_i) represents a loop
  - G_i = Gather: read from memory with stride/permutation
  - S_i = Scatter: write to memory with stride/permutation
  - A_i = Compute: the arithmetic kernel

  Lowering rules:
  - (I_n ⊗ A_m) → Σ_{i=0}^{n-1} (S_{i,m} · A · G_{i,m})
  - (A_m ⊗ I_n) → L^{mn}_n · (I_n ⊗ A_m) · L^{mn}_m
  - L^{mn}_n (stride permutation) → Gather with stride pattern

  References:
  - SPIRAL: "Efficient SIMD Vectorization of DSP Transforms"
  - "Formal Loop Merging for Signal Transforms" (Franchetti et al.)
-/

import AmoLean.Matrix.Basic
import AmoLean.Matrix.Perm

namespace AmoLean.Sigma

open AmoLean.Matrix (Perm MatExpr ElemOp strideIndex)

/-! ## Part 1: Index Expressions -/

/-- Loop variable identifier -/
abbrev LoopVar := Nat

/-- Index expression: affine expression for memory addressing -/
inductive IdxExpr where
  | const : Nat → IdxExpr
  | var : LoopVar → IdxExpr
  | affine : (base : Nat) → (stride : Nat) → LoopVar → IdxExpr
  | add : IdxExpr → IdxExpr → IdxExpr
  | mul : Nat → IdxExpr → IdxExpr
  deriving Repr, BEq, Inhabited

namespace IdxExpr

def eval (env : LoopVar → Nat) : IdxExpr → Nat
  | const n => n
  | var v => env v
  | affine base stride v => base + stride * env v
  | add e1 e2 => eval env e1 + eval env e2
  | mul c e => c * eval env e

def toString : IdxExpr → String
  | const n => s!"{n}"
  | var v => s!"i{v}"
  | affine base stride v =>
    if base == 0 then s!"{stride}*i{v}"
    else s!"{base} + {stride}*i{v}"
  | add e1 e2 => s!"({toString e1} + {toString e2})"
  | mul c e => s!"{c}*({toString e})"

instance : ToString IdxExpr := ⟨IdxExpr.toString⟩

end IdxExpr

/-! ## Part 2: Gather and Scatter -/

/-- Gather: read n elements from memory with stride pattern -/
structure Gather where
  count : Nat
  baseAddr : IdxExpr
  stride : Nat
  deriving Repr, Inhabited

namespace Gather

def contiguous (n : Nat) (base : IdxExpr) : Gather :=
  { count := n, baseAddr := base, stride := 1 }

def strided (n : Nat) (base : IdxExpr) (s : Nat) : Gather :=
  { count := n, baseAddr := base, stride := s }

def block (blockSize : Nat) (loopVar : LoopVar) : Gather :=
  { count := blockSize, baseAddr := .affine 0 blockSize loopVar, stride := 1 }

def toString (g : Gather) : String :=
  s!"Gather[{g.count}](base={g.baseAddr}, stride={g.stride})"

instance : ToString Gather := ⟨Gather.toString⟩

end Gather

/-- Scatter: write n elements to memory with stride pattern -/
structure Scatter where
  count : Nat
  baseAddr : IdxExpr
  stride : Nat
  deriving Repr, Inhabited

namespace Scatter

def contiguous (n : Nat) (base : IdxExpr) : Scatter :=
  { count := n, baseAddr := base, stride := 1 }

def block (blockSize : Nat) (loopVar : LoopVar) : Scatter :=
  { count := blockSize, baseAddr := .affine 0 blockSize loopVar, stride := 1 }

def toString (s : Scatter) : String :=
  s!"Scatter[{s.count}](base={s.baseAddr}, stride={s.stride})"

instance : ToString Scatter := ⟨Scatter.toString⟩

end Scatter

/-! ## Part 3: Kernel Operations -/

/-- Kernel: small fixed computation (DFT₂, etc.) -/
inductive Kernel where
  | identity : Nat → Kernel
  | dft : Nat → Kernel
  | ntt : Nat → Nat → Kernel
  | twiddle : Nat → Nat → Kernel
  | scale : Kernel
  | butterfly : Kernel
  | sbox : Nat → Nat → Kernel  -- S-box: size, exponent (for Poseidon2 x^α)
  deriving Repr, BEq, Inhabited

namespace Kernel

def inputSize : Kernel → Nat
  | identity n => n
  | dft n => n
  | ntt n _ => n
  | twiddle n _ => n
  | scale => 1
  | butterfly => 2
  | sbox n _ => n

def toString : Kernel → String
  | identity n => s!"I_{n}"
  | dft n => s!"DFT_{n}"
  | ntt n p => s!"NTT_{n}(mod {p})"
  | twiddle n k => s!"T^{n}_{k}"
  | scale => "Scale"
  | butterfly => "Butterfly"
  | sbox n α => s!"Sbox_{n}(x^{α})"

instance : ToString Kernel := ⟨Kernel.toString⟩

end Kernel

/-! ## Part 4: SigmaExpr (Loop IR) -/

/-- Sigma-SPL Expression: loop intermediate representation.
    Σ_{i=0}^{n-1} (Scatter · Kernel · Gather) -/
inductive SigmaExpr where
  | compute : Kernel → Gather → Scatter → SigmaExpr
  | loop : (n : Nat) → (loopVar : LoopVar) → SigmaExpr → SigmaExpr
  | seq : SigmaExpr → SigmaExpr → SigmaExpr
  | par : SigmaExpr → SigmaExpr → SigmaExpr
  | temp : (size : Nat) → SigmaExpr → SigmaExpr
  | nop : SigmaExpr
  deriving Repr, Inhabited

namespace SigmaExpr

def loopDepth : SigmaExpr → Nat
  | compute _ _ _ => 0
  | loop _ _ body => 1 + loopDepth body
  | seq s1 s2 => max (loopDepth s1) (loopDepth s2)
  | par s1 s2 => max (loopDepth s1) (loopDepth s2)
  | temp _ body => loopDepth body
  | nop => 0

def kernelCount : SigmaExpr → Nat
  | compute _ _ _ => 1
  | loop n _ body => n * kernelCount body
  | seq s1 s2 => kernelCount s1 + kernelCount s2
  | par s1 s2 => kernelCount s1 + kernelCount s2
  | temp _ body => kernelCount body
  | nop => 0

partial def toStringIndent (indent : Nat) : SigmaExpr → String
  | compute k g s =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Compute {k}\n{pad}  gather: {g}\n{pad}  scatter: {s}"
  | loop n v body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Loop i{v} = 0 to {n-1}:\n{toStringIndent (indent + 2) body}"
  | seq s1 s2 =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{toStringIndent indent s1}\n{pad};\n{toStringIndent indent s2}"
  | par s1 s2 =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{toStringIndent indent s1}\n{pad}||\n{toStringIndent indent s2}"
  | temp size body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Temp[{size}]:\n{toStringIndent (indent + 2) body}"
  | nop =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Nop"

def toString (s : SigmaExpr) : String := toStringIndent 0 s

instance : ToString SigmaExpr := ⟨SigmaExpr.toString⟩

end SigmaExpr

/-! ## Part 5: Lowering MatExpr → SigmaExpr -/

structure LowerState where
  nextLoopVar : LoopVar := 0
  deriving Repr, Inhabited

def freshLoopVar (s : LowerState) : (LoopVar × LowerState) :=
  (s.nextLoopVar, { s with nextLoopVar := s.nextLoopVar + 1 })

/-- Adjust gather/scatter for block access (I_n ⊗ A) -/
def adjustBlock (loopVar : LoopVar) (blockIn blockOut : Nat) : SigmaExpr → SigmaExpr
  | .compute k _ _ =>
    .compute k (Gather.block blockIn loopVar) (Scatter.block blockOut loopVar)
  | .loop n v body => .loop n v (adjustBlock loopVar blockIn blockOut body)
  | .seq s1 s2 => .seq (adjustBlock loopVar blockIn blockOut s1) (adjustBlock loopVar blockIn blockOut s2)
  | .par s1 s2 => .par (adjustBlock loopVar blockIn blockOut s1) (adjustBlock loopVar blockIn blockOut s2)
  | .temp sz body => .temp sz (adjustBlock loopVar blockIn blockOut body)
  | .nop => .nop

/-- Adjust for strided access (A ⊗ I_n) -/
def adjustStride (loopVar : LoopVar) (innerSize mSize nSize : Nat) : SigmaExpr → SigmaExpr
  | .compute k _ _ =>
    let g : Gather := { count := nSize, baseAddr := .var loopVar, stride := innerSize }
    let s : Scatter := { count := mSize, baseAddr := .var loopVar, stride := innerSize }
    .compute k g s
  | .loop n v body => .loop n v (adjustStride loopVar innerSize mSize nSize body)
  | .seq s1 s2 => .seq (adjustStride loopVar innerSize mSize nSize s1) (adjustStride loopVar innerSize mSize nSize s2)
  | .par s1 s2 => .par (adjustStride loopVar innerSize mSize nSize s1) (adjustStride loopVar innerSize mSize nSize s2)
  | .temp sz body => .temp sz (adjustStride loopVar innerSize mSize nSize body)
  | .nop => .nop

/-- Lower MatExpr to SigmaExpr -/
partial def lower (m n : Nat) (state : LowerState) : MatExpr α m n → (SigmaExpr × LowerState)
  | .identity n' =>
    (.compute (.identity n') (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)), state)

  | .zero _ _ => (.nop, state)

  | .dft n' =>
    (.compute (.dft n') (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)), state)

  | .ntt n' p =>
    (.compute (.ntt n' p) (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)), state)

  | .twiddle n' k =>
    (.compute (.twiddle n' k) (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)), state)

  | .perm _ =>
    (.compute (.identity n) (Gather.contiguous n (.const 0)) (Scatter.contiguous n (.const 0)), state)

  | @MatExpr.kron _ m₁ n₁ m₂ n₂ a b =>
    -- Check if a is identity
    let aIsIdentity := match a with | .identity _ => true | _ => false
    let bIsIdentity := match b with | .identity _ => true | _ => false

    if aIsIdentity then
      -- I_{m₁} ⊗ B → Loop over m₁ blocks of size m₂
      let (loopVar, state1) := freshLoopVar state
      let (bodyExpr, state2) := lower m₂ n₂ state1 b
      let body := adjustBlock loopVar n₂ m₂ bodyExpr
      (.loop m₁ loopVar body, state2)
    else if bIsIdentity then
      -- A ⊗ I_{m₂} → Strided access
      let (loopVar, state1) := freshLoopVar state
      let (bodyExpr, state2) := lower m₁ n₁ state1 a
      let body := adjustStride loopVar m₂ m₁ n₁ bodyExpr
      (.loop m₂ loopVar body, state2)
    else
      -- General A ⊗ B: nested structure
      let (loopVar, state1) := freshLoopVar state
      let (exprA, state2) := lower m₁ n₁ state1 a
      let (exprB, state3) := lower m₂ n₂ state2 b
      (.loop m₁ loopVar (.seq exprA (.loop m₂ (loopVar + 1) exprB)), state3)

  | @MatExpr.compose _ m' k n' a b =>
    let (exprB, state1) := lower k n' state b
    let (exprA, state2) := lower m' k state1 a
    (.temp k (.seq exprB exprA), state2)

  | .add a b =>
    let (exprA, state1) := lower m n state a
    let (exprB, state2) := lower m n state1 b
    (.par exprA exprB, state2)

  | .smul _ a =>
    let (exprA, state1) := lower m n state a
    (.seq exprA (.compute .scale (Gather.contiguous n (.const 0)) (Scatter.contiguous n (.const 0))), state1)

  | .transpose a =>
    lower n m state a

  | .conjTranspose a =>
    lower n m state a

  | .diag _ =>
    (.compute (.identity n) (Gather.contiguous n (.const 0)) (Scatter.contiguous n (.const 0)), state)

  | .scalar _ =>
    (.compute .scale (Gather.contiguous 1 (.const 0)) (Scatter.contiguous 1 (.const 0)), state)

  | @MatExpr.elemwise _ m' n' op a =>
    -- Lower the inner matrix first, then apply S-box
    let (innerExpr, state1) := lower m' n' state a
    -- Get the exponent from ElemOp
    let exp := match op with
      | ElemOp.pow α => α
      | ElemOp.custom _ => 1  -- Default to identity for custom ops
    -- Apply S-box to each element
    let sboxExpr : SigmaExpr := .compute (.sbox (m' * n') exp)
      (Gather.contiguous (m' * n') (.const 0))
      (Scatter.contiguous (m' * n') (.const 0))
    (.seq innerExpr sboxExpr, state1)

def lowerFresh (m n : Nat) (e : MatExpr α m n) : SigmaExpr :=
  (lower m n {} e).1

/-! ## Part 6: Tests -/

section Tests

-- Test 1: I_4
def test1 : IO Unit := do
  let i4 : MatExpr Int 4 4 := .identity 4
  let sigma := lowerFresh 4 4 i4
  IO.println "=== Test 1: I_4 ==="
  IO.println s!"Output:\n{sigma}"
  IO.println s!"Loop depth: {sigma.loopDepth}"
  IO.println s!"Kernel count: {sigma.kernelCount}\n"

-- Test 2: I_2 ⊗ I_2
def test2 : IO Unit := do
  let i2 : MatExpr Int 2 2 := .identity 2
  let expr : MatExpr Int 4 4 := .kron i2 i2
  let sigma := lowerFresh 4 4 expr
  IO.println "=== Test 2: I_2 ⊗ I_2 ==="
  IO.println s!"Output:\n{sigma}"
  IO.println s!"Loop depth: {sigma.loopDepth}"
  IO.println s!"Kernel count: {sigma.kernelCount}\n"

-- Test 3: I_2 ⊗ DFT_2
def test3 : IO Unit := do
  let i2 : MatExpr Int 2 2 := .identity 2
  let dft2 : MatExpr Int 2 2 := .dft 2
  let expr : MatExpr Int 4 4 := .kron i2 dft2
  let sigma := lowerFresh 4 4 expr
  IO.println "=== Test 3: I_2 ⊗ DFT_2 ==="
  IO.println s!"Output:\n{sigma}"
  IO.println s!"Loop depth: {sigma.loopDepth}"
  IO.println s!"Kernel count: {sigma.kernelCount}\n"

-- Test 4: DFT_2 ⊗ I_2
def test4 : IO Unit := do
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  let expr : MatExpr Int 4 4 := .kron dft2 i2
  let sigma := lowerFresh 4 4 expr
  IO.println "=== Test 4: DFT_2 ⊗ I_2 ==="
  IO.println s!"Output:\n{sigma}"
  IO.println s!"Loop depth: {sigma.loopDepth}"
  IO.println s!"Kernel count: {sigma.kernelCount}\n"

-- Test 5: (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2)
def test5 : IO Unit := do
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  let stage1 : MatExpr Int 4 4 := .kron i2 dft2
  let stage2 : MatExpr Int 4 4 := .kron dft2 i2
  let expr : MatExpr Int 4 4 := .compose stage2 stage1
  let sigma := lowerFresh 4 4 expr
  IO.println "=== Test 5: (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2) ==="
  IO.println s!"Output:\n{sigma}"
  IO.println s!"Loop depth: {sigma.loopDepth}"
  IO.println s!"Kernel count: {sigma.kernelCount}\n"

-- Run all tests
#eval! do
  test1
  test2
  test3
  test4
  test5

end Tests

end AmoLean.Sigma
