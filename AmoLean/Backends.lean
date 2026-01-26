/-
  AMO-Lean Backends Module

  Code generators for different target platforms:
  - C_AVX2: Current stable backend (SIMD via AVX2)
  - C_AVX512: [FUTURE] Extended SIMD with thermal awareness
  - CUDA: [FUTURE] GPU backend with memory hierarchy modeling

  Each backend transforms MatExpr/GPUExpr to target code.
-/

-- Current stable backend (AVX2)
import AmoLean.CodeGen
import AmoLean.Sigma.CodeGen

-- Future backends will be imported here:
-- import AmoLean.Backends.C_AVX512
-- import AmoLean.Backends.CUDA
