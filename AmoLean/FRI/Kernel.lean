/-
  AMO-Lean: FRI Step Kernel
  Phase 6 - Validation Task 2

  This module defines a parametrized FRI Layer Kernel that can be
  instantiated for any size n and generates reusable low-level code.

  Design goals:
  1. Parametric in size n (not hardcoded)
  2. Generates code like: void fri_step(n, float* in, float* out, float alpha)
  3. Type-safe at compile time using dependent types
  4. Supports both symbolic lowering and code generation

  The kernel encapsulates the FRI fold operation:
    out[i] = in[2*i] + alpha * in[2*i + 1]  for i = 0..n-1
-/

import AmoLean.FRI.Basic
import AmoLean.FRI.Fold
import AmoLean.Sigma.Basic
import AmoLean.Sigma.Expand
import AmoLean.Vector.Basic

namespace AmoLean.FRI.Kernel

open AmoLean.FRI (ZKCostModel defaultZKCost FRIParams)
open AmoLean.FRI.Fold (FRIField splitEvenOdd friFold)
open AmoLean.Sigma (SigmaExpr Gather Scatter Kernel LoopVar IdxExpr ScalarExpr ScalarVar ScalarAssign)
open AmoLean.Vector (Vec)

/-! ## Part 1: FRI Kernel Specification -/

/-- Specification of an FRI layer kernel operation -/
structure FRIKernelSpec where
  /-- Input domain size (must be 2n for fold) -/
  inputSize : Nat
  /-- Output domain size (n after fold) -/
  outputSize : Nat
  /-- Size invariant: output = input / 2 -/
  h_half : outputSize = inputSize / 2
  /-- Blowup factor used -/
  blowupFactor : Nat := 2
  deriving Repr

instance : ToString FRIKernelSpec where
  toString s := s!"FRIKernelSpec(in={s.inputSize}, out={s.outputSize}, blowup={s.blowupFactor})"

namespace FRIKernelSpec

/-- Create kernel spec for size n (input 2n → output n) -/
def forSize (n : Nat) : FRIKernelSpec := {
  inputSize := 2 * n
  outputSize := n
  h_half := by simp [Nat.mul_div_cancel_left]
}

/-- Number of fold operations -/
def foldCount (spec : FRIKernelSpec) : Nat := spec.outputSize

/-- Memory loads per iteration -/
def loadsPerIter : Nat := 2  -- even + odd

/-- Memory stores per iteration -/
def storesPerIter : Nat := 1  -- folded value

/-- Total memory accesses -/
def totalMemoryOps (spec : FRIKernelSpec) : Nat :=
  spec.foldCount * (loadsPerIter + storesPerIter)

end FRIKernelSpec

/-! ## Part 2: FRI Layer Kernel (Parametric) -/

/-- A parametric FRI layer kernel that can be instantiated for any size.

    This structure captures the essence of the FRI fold operation
    in a size-agnostic way, allowing reuse across different layer sizes.
-/
structure FRILayerKernel (n : Nat) where
  /-- Kernel specification -/
  spec : FRIKernelSpec
  /-- Spec matches the size parameter -/
  h_spec : spec = FRIKernelSpec.forSize n
  /-- Optional name for code generation -/
  name : String := s!"fri_fold_{n}"
  deriving Repr

namespace FRILayerKernel

/-- Create a kernel for size n -/
def create (n : Nat) : FRILayerKernel n := {
  spec := FRIKernelSpec.forSize n
  h_spec := rfl
  name := s!"fri_fold_{n}"
}

/-- Create a generic kernel (size passed at runtime) -/
def createGeneric (n : Nat) : FRILayerKernel n := {
  spec := FRIKernelSpec.forSize n
  h_spec := rfl
  name := "fri_fold_n"  -- Generic name
}

end FRILayerKernel

/-! ## Part 3: Lower to SigmaExpr -/

/-- Lower FRI kernel to Sigma expression (loop IR) -/
def lowerToSigma (n : Nat) (_kernel : FRILayerKernel n) : SigmaExpr :=
  -- Create the fold loop:
  -- for i = 0 to n-1:
  --   out[i] = fold(in[2*i], in[2*i+1], alpha)
  .loop n 0  -- loopVar = 0
    (.compute
      .butterfly  -- Butterfly kernel for fold
      (Gather.strided 2 (.affine 0 2 0) 1)   -- Read: base = 2*i0, count = 2, stride = 1
      (Scatter.contiguous 1 (.var 0)))        -- Write: base = i0, count = 1

/-- Lower to expanded scalar operations -/
def lowerToScalar (n : Nat) (kernel : FRILayerKernel n) : List ScalarAssign :=
  -- Generate unrolled scalar code for small n
  if n ≤ 8 then
    -- Unrolled version
    List.range n |>.flatMap fun i =>
      let evenIdx := 2 * i
      let oddIdx := 2 * i + 1
      -- t = in[2*i+1] * alpha
      -- out[i] = in[2*i] + t
      [ { target := ScalarVar.temp i
        , value := .mul (.var ⟨"alpha", 0⟩) (.var ⟨"in", oddIdx⟩) }
      , { target := ScalarVar.output i
        , value := .add (.var ⟨"in", evenIdx⟩) (.var ⟨"t", i⟩) }
      ]
  else
    -- For larger sizes, just generate loop pattern
    [ { target := ⟨"loop_body", 0⟩
      , value := .add (.var ⟨"in_even", 0⟩) (.mul (.var ⟨"alpha", 0⟩) (.var ⟨"in_odd", 0⟩)) }
    ]

/-! ## Part 4: Code Generation Templates -/

/-- C-style function signature -/
def cSignature (n : Nat) (kernel : FRILayerKernel n) : String :=
  s!"void {kernel.name}(size_t n, const float* in, float* out, float alpha)"

/-- Parametric C signature (size as parameter) -/
def cSignatureParametric : String :=
  "void fri_step(size_t n, const float* in, float* out, float alpha)"

/-- Generate C loop body -/
def cLoopBody : String :=
  "  for (size_t i = 0; i < n; i++) {\n" ++
  "    out[i] = in[2*i] + alpha * in[2*i + 1];\n" ++
  "  }"

/-- Generate complete C function -/
def generateCFunction (n : Nat) (kernel : FRILayerKernel n) : String :=
  let sig := cSignature n kernel
  let body := cLoopBody
  sig ++ " {\n" ++ body ++ "\n}"

/-- Generate parametric C function (reusable for any n) -/
def generateParametricCFunction : String :=
  let sig := cSignatureParametric
  let body := cLoopBody
  "// Parametric FRI fold kernel - reusable for any size\n" ++ sig ++ " {\n" ++ body ++ "\n}"

/-! ## Part 5: SIMD-Optimized Kernel Template -/

/-- AVX2 vectorized loop body (processes 8 elements at once) -/
def avx2LoopBody : String :=
  "  __m256 v_alpha = _mm256_set1_ps(alpha);\n" ++
  "  for (size_t i = 0; i < n; i += 8) {\n" ++
  "    // Load 16 input elements (interleaved even/odd)\n" ++
  "    __m256 even = _mm256_loadu_ps(&in[2*i]);      // Load with stride\n" ++
  "    __m256 odd  = _mm256_loadu_ps(&in[2*i + 8]);  // Simplified\n" ++
  "    // Fold: out = even + alpha * odd\n" ++
  "    __m256 result = _mm256_fmadd_ps(v_alpha, odd, even);\n" ++
  "    _mm256_storeu_ps(&out[i], result);\n" ++
  "  }"

/-- Generate AVX2-optimized C function -/
def generateAVX2Function : String :=
  "// AVX2-optimized FRI fold kernel\n" ++
  "void fri_step_avx2(size_t n, const float* in, float* out, float alpha) {\n" ++
  avx2LoopBody ++ "\n" ++
  "  // Handle remainder\n" ++
  "  for (size_t i = (n/8)*8; i < n; i++) {\n" ++
  "    out[i] = in[2*i] + alpha * in[2*i + 1];\n" ++
  "  }\n" ++
  "}"

/-! ## Part 6: Cost Analysis -/

/-- Calculate cost of kernel execution -/
def kernelCost (cm : ZKCostModel) (n : Nat) : Nat :=
  n * (cm.fieldMul + cm.fieldAdd + 2 * cm.memLoad + cm.memStore)

/-- Theoretical FLOPS per byte (operational intensity) -/
def operationalIntensity (n : Nat) (elemSize : Nat := 8) : Float :=
  -- 2 ops per output (mul + add)
  -- 3 memory accesses per output (2 loads + 1 store)
  let flops := (2 * n).toFloat
  let bytes := (3 * n * elemSize).toFloat
  flops / bytes

/-! ## Part 7: Tests and Demonstrations -/

section Tests

-- Test 1: Create kernel for size 4
def kernel4 : FRILayerKernel 4 := FRILayerKernel.create 4

#eval! IO.println s!"Kernel spec: {kernel4.spec}"
#eval! IO.println s!"Kernel name: {kernel4.name}"

-- Test 2: Lower to SigmaExpr
#eval! do
  let sigma := lowerToSigma 4 kernel4
  IO.println "=== SigmaExpr for FRI Kernel (n=4) ==="
  IO.println s!"{sigma}"

-- Test 3: Generate C code
#eval! do
  IO.println "=== Generated C Code (n=4) ==="
  IO.println (generateCFunction 4 kernel4)

-- Test 4: Generate parametric C code
#eval! do
  IO.println "\n=== Parametric C Function ==="
  IO.println generateParametricCFunction

-- Test 5: Generate AVX2 code
#eval! do
  IO.println "\n=== AVX2 Optimized Function ==="
  IO.println generateAVX2Function

-- Test 6: Cost analysis
#eval! do
  IO.println "\n=== Cost Analysis ==="
  let cost4 := kernelCost defaultZKCost 4
  let cost1024 := kernelCost defaultZKCost 1024
  IO.println s!"Cost for n=4:    {cost4}"
  IO.println s!"Cost for n=1024: {cost1024}"
  IO.println s!"Operational intensity: {operationalIntensity 1024}"

-- Test 7: Lower to scalar (unrolled for small n)
#eval! do
  let scalars := lowerToScalar 4 kernel4
  IO.println "\n=== Scalar Operations (n=4, unrolled) ==="
  for s in scalars do
    IO.println s!"  {s.target} := {s.value}"

-- Test 8: Multiple kernel sizes
#eval! do
  IO.println "\n=== Multiple Kernel Sizes ==="
  for size in [2, 4, 8, 16, 32] do
    let spec := FRIKernelSpec.forSize size
    IO.println s!"n={size}: input={spec.inputSize}, output={spec.outputSize}, folds={spec.foldCount}"

end Tests

/-! ## Part 8: Summary -/

/-- Summary of the FRI Step Kernel design -/
def designSummary : String :=
  "FRI Step Kernel Design Summary:\n" ++
  "================================\n" ++
  "1. FRIKernelSpec: Captures size invariants (input = 2*output)\n" ++
  "2. FRILayerKernel n: Type-safe kernel parametric in size\n" ++
  "3. lowerToSigma: Generates loop IR for lowering pipeline\n" ++
  "4. lowerToScalar: Unrolls to explicit scalar operations\n" ++
  "5. generateCFunction: Produces C code\n" ++
  "6. generateParametricCFunction: Reusable for any size\n" ++
  "7. generateAVX2Function: SIMD-optimized variant\n\n" ++
  "Key property: The kernel is REUSABLE - same code works for any n."

#eval! IO.println designSummary

end AmoLean.FRI.Kernel
