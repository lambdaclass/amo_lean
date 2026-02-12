/-
  AMO-Lean: Code Generation from Sigma-SPL
  Phase 5.7 - Generate C code from ExpandedSigma

  This module generates C code from the expanded Sigma-SPL IR.
  The generated code uses simple C with loops, making it suitable for
  further optimization by C compilers or for SIMD extension.

  Pipeline:
    MatExpr → SigmaExpr → ExpandedSigma → C code

  Code structure:
    - Function signature with double* input/output arrays
    - Loop nests for Σ iterations
    - Scalar operations for expanded kernels
    - Temporary arrays for intermediate results

  References:
  - SPIRAL: "Automatic Implementation of Signal Processing Algorithms"
  - Fiat-Crypto: "Simple High-Level Code For Cryptographic Arithmetic"
-/

import AmoLean.Sigma.Expand

namespace AmoLean.Sigma.CodeGen

open AmoLean.Sigma

/-! ## Part 1: Code Generation State -/

/-- State for code generation -/
structure CodeGenState where
  indent : Nat := 0
  nextTemp : Nat := 0
  deriving Repr, Inhabited

def CodeGenState.increaseIndent (s : CodeGenState) : CodeGenState :=
  { s with indent := s.indent + 1 }

def CodeGenState.freshTemp (s : CodeGenState) : (String × CodeGenState) :=
  (s!"temp_{s.nextTemp}", { s with nextTemp := s.nextTemp + 1 })

/-! ## Part 2: C Code Primitives -/

def indentStr (n : Nat) : String :=
  String.mk (List.replicate (n * 2) ' ')

def cType : String := "double"

/-- Generate C variable name from ScalarVar -/
def varToC (v : ScalarVar) (baseOffset : String := "") : String :=
  match v.name with
  | "x" => s!"in[{baseOffset}{if baseOffset.isEmpty then "" else " + "}{v.idx}]"
  | "y" => s!"out[{baseOffset}{if baseOffset.isEmpty then "" else " + "}{v.idx}]"
  | "t" => s!"t{v.idx}"
  | _ => s!"{v.name}{v.idx}"

/-- Generate C expression from ScalarExpr -/
partial def exprToC (e : ScalarExpr) (baseOffset : String := "") : String :=
  match e with
  | .var v => varToC v baseOffset
  | .const n => s!"{n}.0"
  | .neg e' => s!"-({exprToC e' baseOffset})"
  | .add e1 e2 => s!"({exprToC e1 baseOffset} + {exprToC e2 baseOffset})"
  | .sub e1 e2 => s!"({exprToC e1 baseOffset} - {exprToC e2 baseOffset})"
  | .mul e1 e2 => s!"({exprToC e1 baseOffset} * {exprToC e2 baseOffset})"

/-- Generate C assignment from ScalarAssign -/
def assignToC (a : ScalarAssign) (indent : Nat) (baseOffset : String := "") : String :=
  let pad := indentStr indent
  let lhs := varToC a.target baseOffset
  let rhs := exprToC a.value baseOffset
  match a.target.name with
  | "t" => s!"{pad}{cType} {lhs} = {rhs};"
  | _ => s!"{pad}{lhs} = {rhs};"

/-! ## Part 3: Generate C for Gather/Scatter with Offsets -/

/-- Compute base offset expression from IdxExpr -/
partial def idxExprToC : IdxExpr → String
  | .const n => s!"{n}"
  | .var v => s!"i{v}"
  | .affine base stride v =>
    if base == 0 then s!"{stride} * i{v}"
    else s!"{base} + {stride} * i{v}"
  | .add e1 e2 => s!"({idxExprToC e1} + {idxExprToC e2})"
  | .mul c e => s!"{c} * ({idxExprToC e})"

/-- Generate base offset for gather -/
def gatherOffset (g : Gather) : String := idxExprToC g.baseAddr

/-- Generate base offset for scatter -/
def scatterOffset (s : Scatter) : String := idxExprToC s.baseAddr

/-! ## Part 4: Main Code Generation -/

/-- Generate index expression with stride: base + stride * idx -/
def genIndexWithStride (base : String) (stride : Nat) (idx : Nat) : String :=
  if stride == 1 then
    if base.isEmpty then s!"{idx}"
    else s!"{base} + {idx}"
  else
    if base.isEmpty then s!"{stride} * {idx}"
    else s!"{base} + {stride} * {idx}"

/-- Generate C code for a scalar block with stride support -/
def scalarBlockToC (block : ScalarBlock) (indent : Nat) (g : Gather) (s : Scatter) : String :=
  let gatherBase := gatherOffset g
  let scatterBase := scatterOffset s
  let gatherStride := g.stride
  let scatterStride := s.stride
  let lines := block.map fun a =>
    let line := match a.target.name with
      | "y" =>
        let pad := indentStr indent
        let outIdx := genIndexWithStride scatterBase scatterStride a.target.idx
        let lhs := s!"out[{outIdx}]"
        let rhsStr := genRhsWithOffsets a.value gatherBase gatherStride
        s!"{pad}{lhs} = {rhsStr};"
      | "t" =>
        let pad := indentStr indent
        let lhs := s!"t{a.target.idx}"
        let rhsStr := genRhsWithOffsets a.value gatherBase gatherStride
        s!"{pad}{cType} {lhs} = {rhsStr};"
      | _ => assignToC a indent ""
    line
  String.intercalate "\n" lines
where
  genRhsWithOffsets (e : ScalarExpr) (gatherBase : String) (gatherStride : Nat) : String :=
    match e with
    | .var v =>
      match v.name with
      | "x" =>
        let inIdx := genIndexWithStride gatherBase gatherStride v.idx
        s!"in[{inIdx}]"
      | "t" => s!"t{v.idx}"
      | _ => varToC v ""
    | .const n => s!"{n}.0"
    | .neg e' => s!"-({genRhsWithOffsets e' gatherBase gatherStride})"
    | .add e1 e2 => s!"({genRhsWithOffsets e1 gatherBase gatherStride} + {genRhsWithOffsets e2 gatherBase gatherStride})"
    | .sub e1 e2 => s!"({genRhsWithOffsets e1 gatherBase gatherStride} - {genRhsWithOffsets e2 gatherBase gatherStride})"
    | .mul e1 e2 => s!"({genRhsWithOffsets e1 gatherBase gatherStride} * {genRhsWithOffsets e2 gatherBase gatherStride})"

/-- Generate C code for ExpandedSigma -/
partial def expandedSigmaToC (e : ExpandedSigma) (state : CodeGenState) : String :=
  let pad := indentStr state.indent
  match e with
  | .scalar k g s =>
    scalarBlockToC k.body state.indent g s

  | .loop n v body =>
    let loopVar := s!"i{v}"
    let lbrace := "{"
    let rbrace := "}"
    let header := s!"{pad}for (int {loopVar} = 0; {loopVar} < {n}; {loopVar}++) {lbrace}"
    let bodyCode := expandedSigmaToC body state.increaseIndent
    let footer := s!"{pad}{rbrace}"
    s!"{header}\n{bodyCode}\n{footer}"

  | .seq s1 s2 =>
    let code1 := expandedSigmaToC s1 state
    let code2 := expandedSigmaToC s2 state
    s!"{code1}\n{code2}"

  | .par s1 s2 =>
    -- For now, generate sequential code (parallel annotation as comment)
    let code1 := expandedSigmaToC s1 state
    let code2 := expandedSigmaToC s2 state
    s!"{pad}/* parallel region */\n{code1}\n{code2}"

  | .temp size body =>
    let (tempName, state') := state.freshTemp
    let decl := s!"{pad}{cType} {tempName}[{size}];"
    let bodyCode := expandedSigmaToC body state'
    s!"{decl}\n{bodyCode}"

  | .nop => s!"{pad}/* nop */"

/-! ## Part 5: Full Function Generation -/

/-- Generate a complete C function from ExpandedSigma -/
def generateFunction (name : String) (inputSize outputSize : Nat) (e : ExpandedSigma) : String :=
  let signature := s!"void {name}({cType}* restrict in, {cType}* restrict out)"
  let lbrace := "{"
  let rbrace := "}"
  let body := expandedSigmaToC e { indent := 1 }
  s!"{signature} {lbrace}\n{body}\n{rbrace}"

/-- Generate a complete C file with includes -/
def generateCFile (name : String) (inputSize outputSize : Nat) (e : ExpandedSigma) : String :=
  let header := "// Generated by AMO-Lean Sigma-SPL CodeGen\n// Phase 5.7\n"
  let includes := "#include <stddef.h>\n\n"
  let func := generateFunction name inputSize outputSize e
  s!"{header}{includes}{func}"

/-! ## Part 6: Pipeline Helpers -/

/-- Full pipeline: MatExpr → SigmaExpr → ExpandedSigma → C code -/
def matExprToC (name : String) (m n : Nat) (e : AmoLean.Matrix.MatExpr Int m n) : String :=
  let sigma := lowerFresh m n e
  let expanded := expandSigmaExpr sigma
  generateCFile name n m expanded

/-! ## Part 7: Tests -/

section Tests

open AmoLean.Matrix (MatExpr)

-- Test 1: Generate C for I_4
def testGenI4 : IO Unit := do
  IO.println "=== Test 1: Generate C for I_4 ==="
  let i4 : MatExpr Int 4 4 := .identity 4
  let sigma := lowerFresh 4 4 i4
  let expanded := expandSigmaExpr sigma
  let code := generateFunction "identity_4" 4 4 expanded
  IO.println code
  IO.println ""

-- Test 2: Generate C for DFT_2
def testGenDFT2 : IO Unit := do
  IO.println "=== Test 2: Generate C for DFT_2 ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let sigma := lowerFresh 2 2 dft2
  let expanded := expandSigmaExpr sigma
  let code := generateFunction "dft_2" 2 2 expanded
  IO.println code
  IO.println ""

-- Test 3: Generate C for I_2 ⊗ DFT_2
def testGenI2xDFT2 : IO Unit := do
  IO.println "=== Test 3: Generate C for I_2 ⊗ DFT_2 ==="
  let i2 : MatExpr Int 2 2 := .identity 2
  let dft2 : MatExpr Int 2 2 := .dft 2
  let expr : MatExpr Int 4 4 := .kron i2 dft2
  let sigma := lowerFresh 4 4 expr
  let expanded := expandSigmaExpr sigma
  let code := generateFunction "i2_kron_dft2" 4 4 expanded
  IO.println code
  IO.println ""

-- Test 4: Generate C for (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2) = DFT_4 via Cooley-Tukey
def testGenDFT4CT : IO Unit := do
  IO.println "=== Test 4: Generate C for DFT_4 via Cooley-Tukey ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  let stage1 : MatExpr Int 4 4 := .kron i2 dft2
  let stage2 : MatExpr Int 4 4 := .kron dft2 i2
  let expr : MatExpr Int 4 4 := .compose stage2 stage1
  let sigma := lowerFresh 4 4 expr
  let expanded := expandSigmaExpr sigma
  let code := generateFunction "dft_4_cooley_tukey" 4 4 expanded
  IO.println code
  IO.println ""

-- Test 5: Full C file generation
def testGenFullFile : IO Unit := do
  IO.println "=== Test 5: Full C file for DFT_2 ==="
  let dft2 : MatExpr Int 2 2 := .dft 2
  let code := matExprToC "dft2" 2 2 dft2
  IO.println code
  IO.println ""

-- Run all tests
#eval! do
  testGenI4
  testGenDFT2
  testGenI2xDFT2
  testGenDFT4CT
  testGenFullFile

end Tests

end AmoLean.Sigma.CodeGen
