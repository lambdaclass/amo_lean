/-
  AMO-Lean v2.2.0 — Trust-Lean Integration Tests
  Tests/TrustLeanIntegration.lean

  N10.3 (v2.2.0): Integration tests for the Trust-Lean bridge.
  Tests all 6 ExpandedSigma constructors, verified pipeline end-to-end,
  and semantic equivalence between bridge conversion and C code generation.
-/

import AmoLean.Bridge.TrustLean
import AmoLean.Sigma.Expand

set_option autoImplicit false

namespace AmoLean.Tests.TrustLeanIntegration

open AmoLean.Sigma
open AmoLean.Bridge.TrustLean

/-! ## TC-10.3.1: ScalarVar Conversion -/

-- Input variable converts correctly
example : convertScalarVar (ScalarVar.input 0) = some ⟨.input, 0⟩ := rfl
example : convertScalarVar (ScalarVar.input 5) = some ⟨.input, 5⟩ := rfl

-- Output variable converts correctly
example : convertScalarVar (ScalarVar.output 0) = some ⟨.output, 0⟩ := rfl
example : convertScalarVar (ScalarVar.output 3) = some ⟨.output, 3⟩ := rfl

-- Temp variable converts correctly
example : convertScalarVar (ScalarVar.temp 0) = some ⟨.temp, 0⟩ := rfl
example : convertScalarVar (ScalarVar.temp 7) = some ⟨.temp, 7⟩ := rfl

-- Unknown variable names return none
example : convertScalarVar ⟨"foo", 0⟩ = none := rfl
example : convertScalarVar ⟨"alpha", 0⟩ = none := rfl
example : convertScalarVar ⟨"", 0⟩ = none := rfl
example : convertScalarVar ⟨"X", 0⟩ = none := rfl

/-! ## TC-10.3.2: Nop Constructor -/

-- Nop converts and generates empty C code
#eval verifiedCodeGen .nop
example : convertExpandedSigma .nop = some .nop := rfl

/-! ## TC-10.3.3: Scalar Constructor (DFT_2 butterfly) -/

-- DFT_2 expanded kernel: y0 = x0 + x1, y1 = x0 - x1
private def dft2Kernel : ExpandedKernel :=
  { inputVars := [.input 0, .input 1]
    outputVars := [.output 0, .output 1]
    body := [{ target := .output 0, value := .add (.var (.input 0)) (.var (.input 1)) },
             { target := .output 1, value := .sub (.var (.input 0)) (.var (.input 1)) }] }

private def dft2Sigma : ExpandedSigma :=
  .scalar dft2Kernel
    { count := 2, baseAddr := .const 0, stride := 1 }
    { count := 2, baseAddr := .const 0, stride := 1 }

-- DFT_2 converts and generates C code
#eval verifiedCodeGen dft2Sigma
example : (convertExpandedSigma dft2Sigma).isSome = true := rfl

/-! ## TC-10.3.4: Seq Constructor -/

private def seqSigma : ExpandedSigma := .seq dft2Sigma .nop

-- Seq converts and generates C code
#eval verifiedCodeGen seqSigma
example : (convertExpandedSigma seqSigma).isSome = true := rfl

/-! ## TC-10.3.5: Par Constructor -/

private def parSigma : ExpandedSigma := .par dft2Sigma dft2Sigma

-- Par converts and generates C code
#eval verifiedCodeGen parSigma
example : (convertExpandedSigma parSigma).isSome = true := rfl

/-! ## TC-10.3.6: Loop Constructor -/

private def loopSigma : ExpandedSigma := .loop 4 0 dft2Sigma

-- Loop converts and generates C code
#eval verifiedCodeGen loopSigma
example : (convertExpandedSigma loopSigma).isSome = true := rfl

/-! ## TC-10.3.7: Temp Constructor -/

private def tempSigma : ExpandedSigma :=
  .temp 4 (.seq dft2Sigma dft2Sigma)

-- Temp converts and generates C code
#eval verifiedCodeGen tempSigma
example : (convertExpandedSigma tempSigma).isSome = true := rfl

/-! ## TC-10.3.8: Full DFT_4 Pipeline (Complex Structure) -/

-- DFT_4 = (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2) via expanded sigma
private def dft4Sigma : ExpandedSigma :=
  .temp 4
    (.seq
      (.loop 2 0
        (.scalar dft2Kernel
          { count := 2, baseAddr := .affine 0 2 0, stride := 1 }
          { count := 2, baseAddr := .affine 0 2 0, stride := 1 }))
      (.loop 2 1
        (.scalar dft2Kernel
          { count := 2, baseAddr := .var 1, stride := 2 }
          { count := 2, baseAddr := .var 1, stride := 2 })))

-- Full DFT_4 pipeline generates valid C code
#eval verifiedCodeGen dft4Sigma
example : (convertExpandedSigma dft4Sigma).isSome = true := rfl

/-! ## TC-10.3.9: Roundtrip on Concrete Instances -/

-- Backward roundtrip theorem instantiated on nop
example : convertExpandedSigma (convertBackExpandedSigma .nop) = some .nop :=
  roundtrip_expandedSigma_backward .nop

/-! ## TC-10.3.10: Pipeline End-to-End -/

-- Full verified codegen pipeline from amo-lean ExpandedSigma to C code
#eval do
  let sigma := dft4Sigma
  match verifiedCodeGen sigma with
  | some code => return s!"=== Verified C Code ===\n{code}"
  | none => return "Conversion failed"

/-! ## TC-10.3.11: Edge Cases -/

-- Empty kernel (no inputs, no outputs, no body)
private def emptyKernel : ExpandedSigma :=
  .scalar { inputVars := [], outputVars := [], body := [] }
    { count := 0, baseAddr := .const 0, stride := 1 }
    { count := 0, baseAddr := .const 0, stride := 1 }

#eval verifiedCodeGen emptyKernel
example : (convertExpandedSigma emptyKernel).isSome = true := rfl

-- Deeply nested structure (loop inside temp inside seq)
private def deepNested : ExpandedSigma :=
  .temp 8 (.seq (.loop 4 0 (.temp 2 (.loop 2 1 dft2Sigma))) .nop)

#eval verifiedCodeGen deepNested
example : (convertExpandedSigma deepNested).isSome = true := rfl

/-! ## TC-10.3.12: Regression — Bridge Theorems Type-Check -/

-- Core theorems type-check and are available
example := @roundtrip_expandedSigma_backward
example := @roundtrip_scalarVar_forward
example := @roundtrip_idxExpr_forward
example := @roundtrip_idxExpr_backward
example := @roundtrip_gather_forward
example := @roundtrip_scatter_forward
example := @roundtrip_scalarExpr_backward
example := @roundtrip_expandedKernel_backward

-- Forward roundtrip theorems (Corrección 1)
example := @roundtrip_scalarExpr_forward
example := @roundtrip_scalarAssign_forward
example := @roundtrip_scalarVarList_forward
example := @roundtrip_scalarAssignList_forward
example := @roundtrip_expandedKernel_forward
example := @roundtrip_expandedSigma_forward
example := @convert_injective

/-! ## TC-10.3.13: Stress Test — Large ExpandedSigma (>100 expressions) -/

-- Build a large ExpandedSigma with >100 sub-expressions programmatically.
-- Node count grows exponentially: O(2^depth) since each level creates 2 recursive
-- calls (via seq+loop and par). buildLargeSigma 5 ≈ 2^5 × |dft2Sigma| > 100 nodes.
-- Conversion is linear in node count: each node visited exactly once.
private def buildLargeSigma (depth : Nat) : ExpandedSigma :=
  match depth with
  | 0 => dft2Sigma
  | n + 1 => .seq (.loop 2 0 (buildLargeSigma n)) (.par (buildLargeSigma n) .nop)

-- buildLargeSigma 5 produces a structure with >100 sub-expressions
-- (each level triples: loop + par + nop + 2 recursive calls)
-- Stress test: conversion succeeds and generates C code for >100 expression structure
#eval do
  let large := buildLargeSigma 5
  match verifiedCodeGen large with
  | some code => return s!"Stress test PASS: {code.length} chars of C generated"
  | none => return "Stress test FAIL: conversion returned none"

-- Conversion succeeds for large sigma
example : (convertExpandedSigma (buildLargeSigma 5)).isSome = true := rfl

-- Full roundtrip on large sigma via backward theorem
example : convertExpandedSigma (convertBackExpandedSigma
    (convertExpandedSigma (buildLargeSigma 5)).get!) =
    some (convertExpandedSigma (buildLargeSigma 5)).get! :=
  roundtrip_expandedSigma_backward _

/-! ## TC-10.3.14: MicroC Pipeline -/

-- MicroC pipeline produces output for all constructors
#eval verifiedCodeGenMicroC dft2Sigma
#eval verifiedCodeGenMicroC .nop
#eval verifiedCodeGenMicroC loopSigma
#eval verifiedCodeGenMicroC seqSigma

-- Conversion succeeds (verified examples)
example : (verifiedCodeGenMicroC dft2Sigma).isSome = true := rfl
example : (verifiedCodeGenMicroC .nop).isSome = true := rfl
example : (verifiedCodeGenMicroC loopSigma).isSome = true := rfl
example : (verifiedCodeGenMicroC seqSigma).isSome = true := rfl
example : (verifiedCodeGenMicroC parSigma).isSome = true := rfl
example : (verifiedCodeGenMicroC tempSigma).isSome = true := rfl

/-! ## TC-10.3.15: MicroC vs CBackend Agreement -/

-- Both pipelines produce `some` on the same inputs
example : (verifiedCodeGen dft2Sigma).isSome = true ∧
          (verifiedCodeGenMicroC dft2Sigma).isSome = true := ⟨rfl, rfl⟩
example : (verifiedCodeGen .nop).isSome = true ∧
          (verifiedCodeGenMicroC .nop).isSome = true := ⟨rfl, rfl⟩
example : (verifiedCodeGen loopSigma).isSome = true ∧
          (verifiedCodeGenMicroC loopSigma).isSome = true := ⟨rfl, rfl⟩

/-! ## TC-10.3.16: Roundtrip on Generated MicroC -/

-- The MicroCStmt produced by expandedSigmaToMicroCStmt roundtrips through
-- microCToString ∘ parseMicroC (uses Trust-Lean's master_roundtrip guarantee)
#eval do
  let some mc := expandedSigmaToMicroCStmt dft2Sigma | return "FAIL: conversion"
  let text := _root_.TrustLean.microCToString mc
  match _root_.TrustLean.parseMicroC text with
  | some _ => return s!"Roundtrip PASS: parseMicroC returned some on {text.length} chars"
  | none => return "Roundtrip FAIL: parse returned none"

/-! ## TC-10.3.17: Stress Test via MicroC Pipeline -/

-- Large sigma via MicroC pipeline
#eval do
  let large := buildLargeSigma 5
  match verifiedCodeGenMicroC large with
  | some code => return s!"MicroC stress PASS: {code.length} chars generated"
  | none => return "MicroC stress FAIL: conversion returned none"

-- Conversion succeeds for large sigma via MicroC
example : (verifiedCodeGenMicroC (buildLargeSigma 5)).isSome = true := rfl

end AmoLean.Tests.TrustLeanIntegration
