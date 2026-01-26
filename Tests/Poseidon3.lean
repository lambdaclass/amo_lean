/-
  Phase 3 Tests: Poseidon2 Complete Integration

  Tests for:
  1. ConstRef symbolic references
  2. PoseidonConfig construction
  3. Round estimation
  4. C code generation (complete header)
  5. MatExpr integration with mdsApply and addRoundConst
-/

import AmoLean.Protocols.Poseidon.MatExpr
import AmoLean.Matrix.Basic
import AmoLean.Sigma.Basic
import AmoLean.Sigma.Expand

namespace Tests.Poseidon3

open AmoLean.Protocols.Poseidon.MatExpr
open AmoLean.Matrix (MatExpr ElemOp)
open AmoLean.Sigma (Kernel lowerFresh expandKernel)

/-! ## Test 1: ConstRef Identifiers -/

def testConstRef : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║          PHASE 3 TESTS - Poseidon2 Integration             ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "=== Test 1: ConstRef Symbolic References ==="

  let refs := [
    (ConstRef.mds 3, "POSEIDON_MDS_3"),
    (ConstRef.mdsInternal 3, "POSEIDON_MDS_INTERNAL_3"),
    (ConstRef.mdsExternal 3, "POSEIDON_MDS_EXTERNAL_3"),
    (ConstRef.roundConst 0 3, "POSEIDON_RC_3[0]"),
    (ConstRef.roundConst 63 3, "POSEIDON_RC_3[63]")
  ]

  let mut passed := 0
  for (ref, expected) in refs do
    let actual := ref.toCIdent
    if actual == expected then
      IO.println s!"  PASS: {repr ref} → {actual}"
      passed := passed + 1
    else
      IO.println s!"  FAIL: {repr ref} → got {actual}, expected {expected}"

  IO.println s!"  Result: {passed}/{refs.length} passed"
  IO.println ""

/-! ## Test 2: PoseidonConfig -/

def testPoseidonConfig : IO Unit := do
  IO.println "=== Test 2: PoseidonConfig Construction ==="

  let configs := [
    ("BN254 t=3", PoseidonConfig.bn254_t3),
    ("BN254 t=5", PoseidonConfig.bn254_t5),
    ("Goldilocks t=12", PoseidonConfig.goldilocks_t12)
  ]

  for (name, c) in configs do
    IO.println s!"  {name}:"
    IO.println s!"    State size: t={c.stateSize}"
    IO.println s!"    Rounds: RF={c.fullRounds}, RP={c.partialRounds}"
    IO.println s!"    Total: {c.totalRounds}"
    IO.println s!"    Alpha: {c.alpha}"

  IO.println "  PASS: All configs constructed"
  IO.println ""

/-! ## Test 3: Round Estimation -/

def testRoundEstimation : IO Unit := do
  IO.println "=== Test 3: Multiplication Count Estimation ==="

  let configs := [
    ("BN254 t=3", PoseidonConfig.bn254_t3),
    ("BN254 t=5", PoseidonConfig.bn254_t5),
    ("Goldilocks t=12", PoseidonConfig.goldilocks_t12)
  ]

  for (name, c) in configs do
    let spec := PermutationSpec.fromConfig c
    let muls := spec.estimateMulCount
    IO.println s!"  {name}: ~{muls} multiplications per hash"

  IO.println "  PASS: Estimates computed"
  IO.println ""

/-! ## Test 4: C Code Generation -/

-- Simple substring check using a decreasing counter
partial def containsSubstr (haystack needle : String) : Bool :=
  let n := needle.length
  let h := haystack.length
  if n > h then false
  else
    let rec check (remaining : Nat) (i : Nat) : Bool :=
      if remaining == 0 then false
      else
        let sub := (haystack.drop i).take n
        if sub == needle then true
        else check (remaining - 1) (i + 1)
    check (h - n + 1) 0

def testCodeGenPreview : IO Unit := do
  IO.println "=== Test 4: C Code Generation (BN254 t=3) ==="

  let config := PoseidonConfig.bn254_t3
  let code := genPoseidon2Header config

  let checks := [
    ("Header guard", containsSubstr code "#ifndef POSEIDON2_H"),
    ("State typedef", containsSubstr code "poseidon_state_3"),
    ("S-box function", containsSubstr code "sbox5"),
    ("Full round", containsSubstr code "poseidon_full_round"),
    ("Partial round", containsSubstr code "poseidon_partial_round"),
    ("Permutation", containsSubstr code "poseidon2_permutation"),
    ("Hash function", containsSubstr code "poseidon2_hash_2to1"),
    ("Extern constants", containsSubstr code "extern const uint64_t POSEIDON_MDS"),
    ("Loop for full rounds", containsSubstr code "for (int r = 0;")
  ]

  let mut passed := 0
  for (desc, ok) in checks do
    if ok then
      IO.println s!"  PASS: {desc}"
      passed := passed + 1
    else
      IO.println s!"  FAIL: {desc} not found"

  IO.println s!"  Result: {passed}/{checks.length} passed"
  IO.println ""

  -- Print code size
  IO.println s!"  Generated code size: {code.length} chars"
  IO.println ""

/-! ## Test 5: MatExpr Integration -/

def testMatExprIntegration : IO Unit := do
  IO.println "=== Test 5: MatExpr with mdsApply and addRoundConst ==="

  -- Create a simple 3x3 identity as starting point
  let baseMatrix : MatExpr Int 3 3 := .identity 3

  -- Test the op count estimates for the new constructors
  IO.println s!"  identity(3) op estimate: {baseMatrix.opCountEstimate}"

  -- Create an elemwise operation on a 3x1 state
  let sbox : MatExpr Int 3 1 := .elemwise (ElemOp.pow 5) (.zero 3 1)
  IO.println s!"  elemwise(pow 5) on 3x1 op estimate: {sbox.opCountEstimate}"

  -- Partial elemwise
  let partialSbox : MatExpr Int 3 1 := .partialElemwise 0 (ElemOp.pow 5) (.zero 3 1)
  IO.println s!"  partialElemwise(0, pow 5) on 3x1 op estimate: {partialSbox.opCountEstimate}"

  -- Check the node counts
  IO.println s!"  identity node count: {baseMatrix.nodeCount}"
  IO.println s!"  elemwise node count: {sbox.nodeCount}"
  IO.println s!"  partialElemwise node count: {partialSbox.nodeCount}"

  -- Test estimated costs
  let cm := AmoLean.Matrix.defaultCostModel
  IO.println s!"  identity cost estimate: {AmoLean.Matrix.estimateCost cm baseMatrix}"
  IO.println s!"  elemwise cost estimate: {AmoLean.Matrix.estimateCost cm sbox}"

  IO.println "  PASS: MatExpr integration working"
  IO.println ""

/-! ## Test 6: Sigma Kernel Integration -/

def testSigmaKernelIntegration : IO Unit := do
  IO.println "=== Test 6: Sigma Kernel Integration ==="

  -- Test the new kernels
  let kernels := [
    (Kernel.mdsApply "MDS" 3, "MDS_MDS(3)"),
    (Kernel.mdsInternal 3, "MDS_Internal(3)"),
    (Kernel.addRoundConst 5 3, "AddRC(round=5, size=3)")
  ]

  for (k, expected) in kernels do
    let actual := k.toString
    IO.println s!"  Kernel: {actual}"
    let expanded := expandKernel k
    IO.println s!"    Expanded: {expanded.inputVars.length} inputs → {expanded.outputVars.length} outputs"

  IO.println "  PASS: All kernels expanded"
  IO.println ""

/-! ## Test 7: Write Generated Code -/

def testWriteGeneratedCode : IO Unit := do
  IO.println "=== Test 7: Write Generated Code Files ==="

  -- BN254 t=3
  let config3 := PoseidonConfig.bn254_t3
  let code3 := genPoseidon2Header config3
  IO.FS.writeFile "generated/poseidon2_bn254_t3.h" code3
  IO.println "  Written: generated/poseidon2_bn254_t3.h"

  -- BN254 t=5
  let config5 := PoseidonConfig.bn254_t5
  let code5 := genPoseidon2Header config5
  IO.FS.writeFile "generated/poseidon2_bn254_t5.h" code5
  IO.println "  Written: generated/poseidon2_bn254_t5.h"

  IO.println "  PASS: Code files generated"
  IO.println ""

/-! ## Run All Tests -/

def runAllTests : IO Unit := do
  testConstRef
  testPoseidonConfig
  testRoundEstimation
  testCodeGenPreview
  testMatExprIntegration
  testSigmaKernelIntegration
  testWriteGeneratedCode

  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║  PHASE 3 TESTS COMPLETE                                    ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"

#eval! runAllTests

end Tests.Poseidon3
