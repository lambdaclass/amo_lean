/-
  AMO-Lean: SIMD Code Generation
  Phase 5.8 - Generate AVX/AVX2 intrinsics from ExpandedSigma

  This module generates SIMD code using Intel AVX intrinsics.
  The key insight from SPIRAL is that A ⊗ I_ν (where ν is SIMD width)
  naturally vectorizes: each scalar operation becomes a SIMD operation.

  SIMD vectorization strategy:
  - ν = 4 for AVX (256-bit, 4 doubles)
  - ν = 8 for AVX-512 (512-bit, 8 doubles)
  - I_n ⊗ A with n ≥ ν → outer loop + SIMD inner
  - A ⊗ I_ν → pure SIMD (vectorized trivially)

  Key AVX intrinsics:
  - _mm256_load_pd: load 4 aligned doubles
  - _mm256_store_pd: store 4 aligned doubles
  - _mm256_add_pd: SIMD add
  - _mm256_sub_pd: SIMD sub
  - _mm256_mul_pd: SIMD mul
  - _mm256_unpacklo_pd, _mm256_unpackhi_pd: interleaving

  References:
  - SPIRAL: "Efficient SIMD Vectorization for Hashing in OpenSSL"
  - Intel Intrinsics Guide: https://intel.com/intrinsics
-/

import AmoLean.Sigma.Expand
import AmoLean.Sigma.CodeGen

namespace AmoLean.Sigma.SIMD

open AmoLean.Sigma
open AmoLean.Sigma.CodeGen (indentStr cType)

/-! ## Part 1: SIMD Configuration -/

/-- SIMD configuration for different instruction sets -/
structure SIMDConfig where
  name : String           -- e.g., "AVX", "AVX512"
  width : Nat             -- vector width in elements (4 for AVX, 8 for AVX512)
  vectorType : String     -- e.g., "__m256d", "__m512d"
  loadIntrinsic : String  -- e.g., "_mm256_load_pd"
  storeIntrinsic : String -- e.g., "_mm256_store_pd"
  addIntrinsic : String   -- e.g., "_mm256_add_pd"
  subIntrinsic : String   -- e.g., "_mm256_sub_pd"
  mulIntrinsic : String   -- e.g., "_mm256_mul_pd"
  deriving Repr, Inhabited

def avxConfig : SIMDConfig := {
  name := "AVX"
  width := 4
  vectorType := "__m256d"
  loadIntrinsic := "_mm256_load_pd"
  storeIntrinsic := "_mm256_store_pd"
  addIntrinsic := "_mm256_add_pd"
  subIntrinsic := "_mm256_sub_pd"
  mulIntrinsic := "_mm256_mul_pd"
}

def avx512Config : SIMDConfig := {
  name := "AVX-512"
  width := 8
  vectorType := "__m512d"
  loadIntrinsic := "_mm512_load_pd"
  storeIntrinsic := "_mm512_store_pd"
  addIntrinsic := "_mm512_add_pd"
  subIntrinsic := "_mm512_sub_pd"
  mulIntrinsic := "_mm512_mul_pd"
}

/-! ## Part 2: SIMD Code Generation State -/

/-- State for SIMD code generation -/
structure SIMDGenState where
  config : SIMDConfig := avxConfig
  indent : Nat := 0
  nextVecReg : Nat := 0
  deriving Repr, Inhabited

def SIMDGenState.freshVecReg (s : SIMDGenState) : (String × SIMDGenState) :=
  (s!"v{s.nextVecReg}", { s with nextVecReg := s.nextVecReg + 1 })

def SIMDGenState.increaseIndent (s : SIMDGenState) : SIMDGenState :=
  { s with indent := s.indent + 1 }

/-! ## Part 3: SIMD Expression Generation -/

/-- Generate SIMD load instruction -/
def genLoad (cfg : SIMDConfig) (indent : Nat) (destReg : String) (arrayName : String) (offset : String) : String :=
  let pad := indentStr indent
  s!"{pad}{cfg.vectorType} {destReg} = {cfg.loadIntrinsic}(&{arrayName}[{offset}]);"

/-- Generate SIMD store instruction -/
def genStore (cfg : SIMDConfig) (indent : Nat) (arrayName : String) (offset : String) (srcReg : String) : String :=
  let pad := indentStr indent
  s!"{pad}{cfg.storeIntrinsic}(&{arrayName}[{offset}], {srcReg});"

/-- Generate SIMD binary operation -/
def genBinaryOp (cfg : SIMDConfig) (op : String) (dest src1 src2 : String) : String :=
  let intrinsic := match op with
    | "add" => cfg.addIntrinsic
    | "sub" => cfg.subIntrinsic
    | "mul" => cfg.mulIntrinsic
    | _ => "UNKNOWN_OP"
  s!"{cfg.vectorType} {dest} = {intrinsic}({src1}, {src2});"

/-! ## Part 4: Vectorize Expanded Kernels -/

/-- Check if a kernel can be vectorized with given SIMD width -/
def canVectorize (k : ExpandedKernel) (simdWidth : Nat) : Bool :=
  -- For now, only vectorize if kernel size matches SIMD width
  k.inputVars.length == simdWidth

/-- Generate SIMD code for DFT_2 (vectorized butterfly) -/
def genDFT2SIMD (cfg : SIMDConfig) (indent : Nat) (inReg0 inReg1 : String) : String × String × String :=
  let pad := indentStr indent
  let outReg0 := s!"t_add"
  let outReg1 := s!"t_sub"
  let code := s!"{pad}{cfg.vectorType} {outReg0} = {cfg.addIntrinsic}({inReg0}, {inReg1});\n{pad}{cfg.vectorType} {outReg1} = {cfg.subIntrinsic}({inReg0}, {inReg1});"
  (code, outReg0, outReg1)

/-- Generate SIMD code for a single butterfly on SIMD registers -/
def genButterflySIMD (cfg : SIMDConfig) (indent : Nat) (state : SIMDGenState)
    (inReg0 inReg1 : String) : (String × String × String × SIMDGenState) :=
  let (outReg0, state1) := state.freshVecReg
  let (outReg1, state2) := state1.freshVecReg
  let pad := indentStr indent
  let code := s!"{pad}{cfg.vectorType} {outReg0} = {cfg.addIntrinsic}({inReg0}, {inReg1});\n{pad}{cfg.vectorType} {outReg1} = {cfg.subIntrinsic}({inReg0}, {inReg1});"
  (code, outReg0, outReg1, state2)

/-! ## Part 5: Generate SIMD for I_n ⊗ DFT_2 pattern -/

/-- Generate SIMD code for I_n ⊗ DFT_2 with n * 2 = SIMD_WIDTH

    For AVX (width=4), I_2 ⊗ DFT_2:
    - Load v0 = [x0, x1, x2, x3]
    - Shuffle to get v_even = [x0, x2, ?, ?], v_odd = [x1, x3, ?, ?]
    - Add: y0,y2 = v_even + v_odd
    - Sub: y1,y3 = v_even - v_odd
    - Shuffle and store
-/
def genI2xDFT2_AVX (indent : Nat) : String :=
  let pad := indentStr indent
  let cfg := avxConfig
  s!"{pad}// I_2 ⊗ DFT_2 vectorized (4 butterflies in parallel)\n" ++
  s!"{pad}{cfg.vectorType} v_in = {cfg.loadIntrinsic}(&in[0]);\n" ++
  s!"{pad}// Shuffle to separate even/odd pairs\n" ++
  s!"{pad}{cfg.vectorType} v_lo = _mm256_unpacklo_pd(v_in, v_in); // [x0,x0,x2,x2]\n" ++
  s!"{pad}{cfg.vectorType} v_hi = _mm256_unpackhi_pd(v_in, v_in); // [x1,x1,x3,x3]\n" ++
  s!"{pad}// Butterfly: add and subtract\n" ++
  s!"{pad}{cfg.vectorType} v_add = {cfg.addIntrinsic}(v_lo, v_hi);\n" ++
  s!"{pad}{cfg.vectorType} v_sub = {cfg.subIntrinsic}(v_lo, v_hi);\n" ++
  s!"{pad}// Interleave results\n" ++
  s!"{pad}{cfg.vectorType} v_out = _mm256_unpacklo_pd(v_add, v_sub);\n" ++
  s!"{pad}{cfg.storeIntrinsic}(&out[0], v_out);"

/-! ## Part 6: High-level SIMD Function Generation -/

/-- Generate SIMD version of DFT_4 -/
def genDFT4_SIMD (indent : Nat) : String :=
  let pad := indentStr indent
  let cfg := avxConfig
  -- DFT_4 = (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2)
  -- With AVX, we can do all 4 elements in one register
  s!"{pad}// DFT_4 fully vectorized with AVX\n" ++
  s!"{pad}{cfg.vectorType} v0 = {cfg.loadIntrinsic}(&in[0]);\n" ++
  s!"{pad}\n" ++
  s!"{pad}// Stage 1: I_2 ⊗ DFT_2 (two butterflies on adjacent pairs)\n" ++
  s!"{pad}// v0 = [x0, x1, x2, x3]\n" ++
  s!"{pad}// We need: t0=x0+x1, t1=x0-x1, t2=x2+x3, t3=x2-x3\n" ++
  s!"{pad}{cfg.vectorType} v_shuf = _mm256_permute_pd(v0, 0b0101); // [x1,x0,x3,x2]\n" ++
  s!"{pad}{cfg.vectorType} v_add1 = {cfg.addIntrinsic}(v0, v_shuf);\n" ++
  s!"{pad}{cfg.vectorType} v_sub1 = {cfg.subIntrinsic}(v0, v_shuf);\n" ++
  s!"{pad}// Blend to get [t0,t1,t2,t3]\n" ++
  s!"{pad}{cfg.vectorType} v1 = _mm256_blend_pd(v_add1, v_sub1, 0b1010);\n" ++
  s!"{pad}\n" ++
  s!"{pad}// Stage 2: DFT_2 ⊗ I_2 (strided butterflies)\n" ++
  s!"{pad}// Need: y0=t0+t2, y1=t1+t3, y2=t0-t2, y3=t1-t3\n" ++
  s!"{pad}{cfg.vectorType} v_hi128 = _mm256_permute2f128_pd(v1, v1, 0x01); // swap 128-bit lanes\n" ++
  s!"{pad}{cfg.vectorType} v_add2 = {cfg.addIntrinsic}(v1, v_hi128);\n" ++
  s!"{pad}{cfg.vectorType} v_sub2 = {cfg.subIntrinsic}(v1, v_hi128);\n" ++
  s!"{pad}// Blend to get [y0,y1,y2,y3]\n" ++
  s!"{pad}{cfg.vectorType} v_out = _mm256_blend_pd(v_add2, v_sub2, 0b1100);\n" ++
  s!"{pad}\n" ++
  s!"{pad}{cfg.storeIntrinsic}(&out[0], v_out);"

/-- Generate SIMD function wrapper -/
def genSIMDFunction (name : String) (n : Nat) (body : String) : String :=
  let lbrace := "{"
  let rbrace := "}"
  s!"void {name}(double* restrict in, double* restrict out) {lbrace}\n{body}\n{rbrace}"

/-- Generate SIMD header with includes -/
def genSIMDHeader : String :=
  "// Generated by AMO-Lean SIMD CodeGen\n" ++
  "// Phase 5.8 - AVX intrinsics\n" ++
  "#include <immintrin.h>\n" ++
  "#include <stddef.h>\n\n"

/-! ## Part 7: Full SIMD File Generation -/

/-- Generate complete SIMD C file for DFT_4 -/
def genDFT4File : String :=
  genSIMDHeader ++
  genSIMDFunction "dft4_avx" 4 (genDFT4_SIMD 1)

/-- Generate complete SIMD C file for DFT_8 -/
def genDFT8_SIMD (indent : Nat) : String :=
  let pad := indentStr indent
  let cfg := avxConfig
  -- DFT_8 = (DFT_2 ⊗ I_4) · T · (I_2 ⊗ DFT_4) · L
  s!"{pad}// DFT_8 with AVX\n" ++
  s!"{pad}// Load two vectors (8 doubles = 2 x 4)\n" ++
  s!"{pad}{cfg.vectorType} v0 = {cfg.loadIntrinsic}(&in[0]);\n" ++
  s!"{pad}{cfg.vectorType} v1 = {cfg.loadIntrinsic}(&in[4]);\n" ++
  s!"{pad}\n" ++
  s!"{pad}// Stage 1: DFT_2 ⊗ I_4 (4 butterflies in parallel)\n" ++
  s!"{pad}{cfg.vectorType} t0 = {cfg.addIntrinsic}(v0, v1);\n" ++
  s!"{pad}{cfg.vectorType} t1 = {cfg.subIntrinsic}(v0, v1);\n" ++
  s!"{pad}\n" ++
  s!"{pad}// TODO: Twiddle factors would go here\n" ++
  s!"{pad}// t1 = t1 * twiddles;\n" ++
  s!"{pad}\n" ++
  s!"{pad}// Stage 2: I_2 ⊗ DFT_4 (two DFT_4 in parallel)\n" ++
  s!"{pad}// Each DFT_4 operates on one AVX register\n" ++
  s!"{pad}// ... (DFT_4 code for t0 and t1)\n" ++
  s!"{pad}\n" ++
  s!"{pad}{cfg.storeIntrinsic}(&out[0], t0);\n" ++
  s!"{pad}{cfg.storeIntrinsic}(&out[4], t1);"

/-! ## Part 8: Tests -/

section Tests

-- Test 1: DFT_4 SIMD
def testDFT4SIMD : IO Unit := do
  IO.println "=== Test 1: DFT_4 SIMD (AVX) ==="
  IO.println genDFT4File
  IO.println ""

-- Test 2: DFT_8 SIMD outline
def testDFT8SIMD : IO Unit := do
  IO.println "=== Test 2: DFT_8 SIMD (AVX) outline ==="
  IO.println genSIMDHeader
  IO.println (genSIMDFunction "dft8_avx" 8 (genDFT8_SIMD 1))
  IO.println ""

-- Test 3: I_2 ⊗ DFT_2 vectorized
def testI2xDFT2SIMD : IO Unit := do
  IO.println "=== Test 3: I_2 ⊗ DFT_2 vectorized ==="
  IO.println genSIMDHeader
  IO.println (genSIMDFunction "i2_kron_dft2_avx" 4 (genI2xDFT2_AVX 1))
  IO.println ""

-- Run all tests
#eval! do
  testDFT4SIMD
  testDFT8SIMD
  testI2xDFT2SIMD

end Tests

end AmoLean.Sigma.SIMD
