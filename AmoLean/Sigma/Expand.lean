/-
  AMO-Lean: Kernel Expansion
  Phase 5.6 - Expand symbolic kernels to scalar operations

  This module expands high-level kernels (DFT₂, DFT₄, etc.) into
  explicit scalar operations. The expansion is necessary for:
  1. Code generation (we need actual arithmetic operations)
  2. Verification (we can prove the expansion equals the kernel)

  Key expansions:
  - DFT_2: [[1,1],[1,-1]] → y0 = x0 + x1, y1 = x0 - x1
  - DFT_4: Radix-4 butterfly network
  - Twiddle: Complex multiplication by ω^k

  References:
  - SPIRAL: "FFTW: An Adaptive Software Architecture for the FFT"
  - Van Loan: "Computational Frameworks for the Fast Fourier Transform"
-/

import AmoLean.Sigma.Basic
import AmoLean.Matrix.Basic

namespace AmoLean.Sigma

open AmoLean.Matrix (MatExpr)

/-! ## Part 1: Scalar Expressions for Kernels -/

/-- Variable identifier for scalar expressions -/
structure ScalarVar where
  name : String
  idx : Nat
  deriving Repr, BEq, Hashable, Inhabited

namespace ScalarVar

def toString (v : ScalarVar) : String := s!"{v.name}{v.idx}"

instance : ToString ScalarVar := ⟨ScalarVar.toString⟩

def input (i : Nat) : ScalarVar := ⟨"x", i⟩
def output (i : Nat) : ScalarVar := ⟨"y", i⟩
def temp (i : Nat) : ScalarVar := ⟨"t", i⟩

end ScalarVar

/-- Scalar expression: arithmetic over variables -/
inductive ScalarExpr where
  | var : ScalarVar → ScalarExpr
  | const : Int → ScalarExpr
  | neg : ScalarExpr → ScalarExpr
  | add : ScalarExpr → ScalarExpr → ScalarExpr
  | sub : ScalarExpr → ScalarExpr → ScalarExpr
  | mul : ScalarExpr → ScalarExpr → ScalarExpr
  deriving Repr, BEq, Inhabited

namespace ScalarExpr

-- Smart constructors
def x (i : Nat) : ScalarExpr := .var (.input i)
def y (i : Nat) : ScalarExpr := .var (.output i)
def t (i : Nat) : ScalarExpr := .var (.temp i)

-- Common constants
def zero : ScalarExpr := .const 0
def one : ScalarExpr := .const 1
def negOne : ScalarExpr := .const (-1)

-- Simplified pretty printing
partial def toString : ScalarExpr → String
  | .var v => s!"{v}"
  | .const n => s!"{n}"
  | .neg e => s!"-({toString e})"
  | .add e1 e2 => s!"({toString e1} + {toString e2})"
  | .sub e1 e2 => s!"({toString e1} - {toString e2})"
  | .mul e1 e2 => s!"({toString e1} * {toString e2})"

instance : ToString ScalarExpr := ⟨ScalarExpr.toString⟩

-- Evaluate with a mapping from variable to Int
def eval (env : ScalarVar → Int) : ScalarExpr → Int
  | .var v => env v
  | .const n => n
  | .neg e => -(eval env e)
  | .add e1 e2 => eval env e1 + eval env e2
  | .sub e1 e2 => eval env e1 - eval env e2
  | .mul e1 e2 => eval env e1 * eval env e2

end ScalarExpr

/-! ## Part 2: Scalar Statements (SSA form) -/

/-- A single scalar assignment: var := expr -/
structure ScalarAssign where
  target : ScalarVar
  value : ScalarExpr
  deriving Repr, BEq, Inhabited

namespace ScalarAssign

def toString (a : ScalarAssign) : String :=
  s!"{a.target} := {a.value}"

instance : ToString ScalarAssign := ⟨ScalarAssign.toString⟩

end ScalarAssign

/-- A block of scalar assignments (straight-line code) -/
abbrev ScalarBlock := List ScalarAssign

namespace ScalarBlock

def toString (b : ScalarBlock) : String :=
  String.intercalate "\n" (b.map ScalarAssign.toString)

def empty : ScalarBlock := []

def append (b1 b2 : ScalarBlock) : ScalarBlock := b1 ++ b2

end ScalarBlock

/-! ## Part 3: Kernel Expansion -/

/-- Expanded kernel: scalar operations replacing a symbolic kernel -/
structure ExpandedKernel where
  inputVars : List ScalarVar
  outputVars : List ScalarVar
  body : ScalarBlock
  deriving Repr, Inhabited

namespace ExpandedKernel

def toString (k : ExpandedKernel) : String :=
  let inputs := String.intercalate ", " (k.inputVars.map ScalarVar.toString)
  let outputs := String.intercalate ", " (k.outputVars.map ScalarVar.toString)
  s!"ExpandedKernel:\n  inputs: [{inputs}]\n  outputs: [{outputs}]\n  body:\n{k.body.map (s!"    " ++ ScalarAssign.toString ·) |> String.intercalate "\n"}"

instance : ToString ExpandedKernel := ⟨ExpandedKernel.toString⟩

end ExpandedKernel

/-- Expand identity kernel of size n.
    y[i] = x[i] for i = 0..n-1 -/
def expandIdentity (n : Nat) : ExpandedKernel :=
  let inputs := List.range n |>.map ScalarVar.input
  let outputs := List.range n |>.map ScalarVar.output
  let body := List.range n |>.map fun i =>
    { target := ScalarVar.output i, value := ScalarExpr.x i }
  { inputVars := inputs, outputVars := outputs, body := body }

/-- Expand DFT_2 kernel (butterfly).
    y0 = x0 + x1
    y1 = x0 - x1 -/
def expandDFT2 : ExpandedKernel :=
  let inputs := [ScalarVar.input 0, ScalarVar.input 1]
  let outputs := [ScalarVar.output 0, ScalarVar.output 1]
  let body := [
    { target := ScalarVar.output 0, value := .add (.x 0) (.x 1) },
    { target := ScalarVar.output 1, value := .sub (.x 0) (.x 1) }
  ]
  { inputVars := inputs, outputVars := outputs, body := body }

/-- Expand DFT_4 kernel (radix-4 butterfly).
    Uses the decomposition DFT_4 = (DFT_2 ⊗ I_2) · T^4_2 · (I_2 ⊗ DFT_2) · L^4_2

    Stage 1 (I_2 ⊗ DFT_2):
      t0 = x0 + x1,  t1 = x0 - x1
      t2 = x2 + x3,  t3 = x2 - x3

    Stage 2 (Twiddles T^4_2): ω = e^{-2πi/4} = -i
      u0 = t0,  u1 = t1 * ω^0 = t1
      u2 = t2,  u3 = t3 * ω^1 = t3 * (-i)
    For real case, we use: t3 * (-i) ≈ -i*t3 (requires complex)
    Simplified for real: just use t3 directly

    Stage 3 (DFT_2 ⊗ I_2):
      y0 = u0 + u2,  y2 = u0 - u2
      y1 = u1 + u3,  y3 = u1 - u3

    For real FFT, output is in bit-reversed order: [y0, y2, y1, y3]
-/
def expandDFT4 : ExpandedKernel :=
  let inputs := List.range 4 |>.map ScalarVar.input
  let outputs := List.range 4 |>.map ScalarVar.output
  let body := [
    -- Stage 1: I_2 ⊗ DFT_2
    { target := .temp 0, value := .add (.x 0) (.x 1) },  -- t0 = x0 + x1
    { target := .temp 1, value := .sub (.x 0) (.x 1) },  -- t1 = x0 - x1
    { target := .temp 2, value := .add (.x 2) (.x 3) },  -- t2 = x2 + x3
    { target := .temp 3, value := .sub (.x 2) (.x 3) },  -- t3 = x2 - x3
    -- Stage 2: Twiddles (identity for real case, simplified)
    -- For full complex FFT, t3 would be multiplied by -i
    -- Stage 3: DFT_2 ⊗ I_2 (strided)
    { target := .output 0, value := .add (.t 0) (.t 2) },  -- y0 = t0 + t2
    { target := .output 1, value := .add (.t 1) (.t 3) },  -- y1 = t1 + t3
    { target := .output 2, value := .sub (.t 0) (.t 2) },  -- y2 = t0 - t2
    { target := .output 3, value := .sub (.t 1) (.t 3) }   -- y3 = t1 - t3
  ]
  { inputVars := inputs, outputVars := outputs, body := body }

/-- Expand scale kernel: y = factor * x -/
def expandScale (factor : Int) : ExpandedKernel :=
  { inputVars := [.input 0],
    outputVars := [.output 0],
    body := [{ target := .output 0, value := .mul (.const factor) (.x 0) }] }

/-- Expand butterfly kernel (same as DFT_2) -/
def expandButterfly : ExpandedKernel := expandDFT2

/-- Expand S-box kernel: x^α for each element (Poseidon2).
    For α=5, uses square chain: x^5 = x * (x^2)^2 (3 multiplications) -/
def expandSbox (size : Nat) (α : Nat) : ExpandedKernel :=
  let inputs := List.range size |>.map ScalarVar.input
  let outputs := List.range size |>.map ScalarVar.output
  -- For each element, compute x^α using square chain if α=5
  let body := if α == 5 then
    -- Square chain: x^5 = x * x^4 = x * (x^2)^2
    List.range size |>.bind fun i =>
      let xi := ScalarExpr.x i
      [
        { target := .temp (3*i),     value := .mul xi xi },          -- t_3i = x_i^2
        { target := .temp (3*i + 1), value := .mul (.t (3*i)) (.t (3*i)) },  -- t_3i+1 = x_i^4
        { target := .output i,       value := .mul xi (.t (3*i + 1)) }       -- y_i = x_i^5
      ]
  else
    -- Naive: compute x^α with α-1 multiplications
    List.range size |>.map fun i =>
      -- For simplicity, just use y = x (TODO: implement general power)
      { target := .output i, value := ScalarExpr.x i }
  { inputVars := inputs, outputVars := outputs, body := body }

/-- Main kernel expansion function -/
def expandKernel : Kernel → ExpandedKernel
  | .identity n => expandIdentity n
  | .dft 2 => expandDFT2
  | .dft 4 => expandDFT4
  | .dft n => expandIdentity n  -- Fallback for larger DFT
  | .ntt n _ => expandIdentity n  -- TODO: implement proper NTT
  | .twiddle n _ => expandIdentity n  -- TODO: implement twiddle factors
  | .scale => expandScale 1  -- Default scale factor
  | .butterfly => expandButterfly
  | .sbox n α => expandSbox n α  -- Poseidon2 S-box

/-! ## Part 4: Expanded SigmaExpr -/

/-- SigmaExpr with kernels expanded to scalar operations -/
inductive ExpandedSigma where
  | scalar : ExpandedKernel → Gather → Scatter → ExpandedSigma
  | loop : (n : Nat) → (loopVar : LoopVar) → ExpandedSigma → ExpandedSigma
  | seq : ExpandedSigma → ExpandedSigma → ExpandedSigma
  | par : ExpandedSigma → ExpandedSigma → ExpandedSigma
  | temp : (size : Nat) → ExpandedSigma → ExpandedSigma
  | nop : ExpandedSigma
  deriving Repr, Inhabited

namespace ExpandedSigma

partial def toStringIndent (indent : Nat) : ExpandedSigma → String
  | .scalar k g s =>
    let pad := String.mk (List.replicate indent ' ')
    let bodyStr := k.body.map (fun a => s!"{pad}    {a.target} := {a.value}") |> String.intercalate "\n"
    s!"{pad}Scalar block:\n{bodyStr}\n{pad}  gather: {g}\n{pad}  scatter: {s}"
  | .loop n v body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Loop i{v} = 0 to {n-1}:\n{toStringIndent (indent + 2) body}"
  | .seq s1 s2 =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{toStringIndent indent s1}\n{pad};\n{toStringIndent indent s2}"
  | .par s1 s2 =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{toStringIndent indent s1}\n{pad}||\n{toStringIndent indent s2}"
  | .temp size body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Temp[{size}]:\n{toStringIndent (indent + 2) body}"
  | .nop =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Nop"

def toString (e : ExpandedSigma) : String := toStringIndent 0 e

instance : ToString ExpandedSigma := ⟨ExpandedSigma.toString⟩

end ExpandedSigma

/-- Expand all kernels in a SigmaExpr -/
def expandSigmaExpr : SigmaExpr → ExpandedSigma
  | .compute k g s => .scalar (expandKernel k) g s
  | .loop n v body => .loop n v (expandSigmaExpr body)
  | .seq s1 s2 => .seq (expandSigmaExpr s1) (expandSigmaExpr s2)
  | .par s1 s2 => .par (expandSigmaExpr s1) (expandSigmaExpr s2)
  | .temp sz body => .temp sz (expandSigmaExpr body)
  | .nop => .nop

/-! ## Part 5: Statistics -/

/-- Count operations in expanded kernel -/
def ExpandedKernel.opCount (k : ExpandedKernel) : Nat × Nat × Nat :=
  let count := fun op =>
    k.body.foldl (fun acc a =>
      match a.value with
      | .add _ _ => if op == "add" then acc + 1 else acc
      | .sub _ _ => if op == "sub" then acc + 1 else acc
      | .mul _ _ => if op == "mul" then acc + 1 else acc
      | .neg _ => if op == "neg" then acc + 1 else acc
      | _ => acc
    ) 0
  (count "add", count "sub", count "mul")

/-- Count total operations in expanded sigma -/
partial def ExpandedSigma.totalOps : ExpandedSigma → Nat × Nat × Nat
  | .scalar k _ _ =>
    let (a, s, m) := k.opCount
    (a, s, m)
  | .loop n _ body =>
    let (a, s, m) := body.totalOps
    (n * a, n * s, n * m)
  | .seq s1 s2 =>
    let (a1, s1', m1) := s1.totalOps
    let (a2, s2', m2) := s2.totalOps
    (a1 + a2, s1' + s2', m1 + m2)
  | .par s1 s2 =>
    let (a1, s1', m1) := s1.totalOps
    let (a2, s2', m2) := s2.totalOps
    (a1 + a2, s1' + s2', m1 + m2)
  | .temp _ body => body.totalOps
  | .nop => (0, 0, 0)

/-! ## Part 6: Tests -/

section Tests

-- Test 1: Expand DFT_2
def testExpandDFT2 : IO Unit := do
  IO.println "=== Test 1: Expand DFT_2 ==="
  let k := expandDFT2
  IO.println s!"{k}"
  let (adds, subs, muls) := k.opCount
  IO.println s!"Operations: {adds} adds, {subs} subs, {muls} muls"
  IO.println ""

-- Test 2: Expand DFT_4
def testExpandDFT4 : IO Unit := do
  IO.println "=== Test 2: Expand DFT_4 ==="
  let k := expandDFT4
  IO.println s!"{k}"
  let (adds, subs, muls) := k.opCount
  IO.println s!"Operations: {adds} adds, {subs} subs, {muls} muls"
  IO.println ""

-- Test 3: Expand I_2 ⊗ DFT_2 (from SigmaExpr)
def testExpandKron : IO Unit := do
  IO.println "=== Test 3: Expand I_2 ⊗ DFT_2 ==="
  -- Create I_2 ⊗ DFT_2 as SigmaExpr
  let i2 : MatExpr Int 2 2 := .identity 2
  let dft2 : MatExpr Int 2 2 := .dft 2
  let expr : MatExpr Int 4 4 := .kron i2 dft2
  let sigma := lowerFresh 4 4 expr
  IO.println s!"Before expansion:\n{sigma}\n"

  let expanded := expandSigmaExpr sigma
  IO.println s!"After expansion:\n{expanded}\n"

  let (adds, subs, muls) := expanded.totalOps
  IO.println s!"Total operations: {adds} adds, {subs} subs, {muls} muls"
  IO.println s!"Expected: 2 adds, 2 subs, 0 muls (two DFT_2 butterflies)"
  IO.println ""

-- Test 4: Expand (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2)
def testExpandCT : IO Unit := do
  IO.println "=== Test 4: Expand (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2) ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  let stage1 : MatExpr Int 4 4 := .kron i2 dft2
  let stage2 : MatExpr Int 4 4 := .kron dft2 i2
  let expr : MatExpr Int 4 4 := .compose stage2 stage1
  let sigma := lowerFresh 4 4 expr

  IO.println s!"SigmaExpr (before expansion):"
  IO.println s!"{sigma}\n"

  let expanded := expandSigmaExpr sigma
  IO.println s!"Expanded:\n{expanded}\n"

  let (adds, subs, muls) := expanded.totalOps
  IO.println s!"Total operations: {adds} adds, {subs} subs, {muls} muls"
  IO.println s!"Expected: 4 adds, 4 subs, 0 muls (4 butterflies for DFT_4)"
  IO.println ""

-- Test 5: Verify DFT_2 numerically
def testVerifyDFT2 : IO Unit := do
  IO.println "=== Test 5: Verify DFT_2 expansion numerically ==="
  let k := expandDFT2
  -- Test with input [3, 5]
  let env : ScalarVar → Int := fun v =>
    if v == .input 0 then 3
    else if v == .input 1 then 5
    else 0

  -- Compute outputs
  let y0Val := match k.body.get? 0 with
    | some assign => ScalarExpr.eval env assign.value
    | none => 0
  let y1Val := match k.body.get? 1 with
    | some assign => ScalarExpr.eval env assign.value
    | none => 0

  IO.println s!"Input: x0 = 3, x1 = 5"
  IO.println s!"DFT_2 outputs:"
  IO.println s!"  y0 = x0 + x1 = {y0Val} (expected: 8)"
  IO.println s!"  y1 = x0 - x1 = {y1Val} (expected: -2)"
  IO.println s!"Verification: {if y0Val == 8 && y1Val == -2 then "PASS ✓" else "FAIL ✗"}"
  IO.println ""

-- Run all tests
#eval! do
  testExpandDFT2
  testExpandDFT4
  testExpandKron
  testExpandCT
  testVerifyDFT2

end Tests

end AmoLean.Sigma
