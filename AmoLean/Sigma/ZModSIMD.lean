/-
  AMO-Lean: SIMD Modular Arithmetic
  Phase 5.9 - FMA-based modular operations for NTT

  This module implements SIMD modular arithmetic using the FMA (Fused Multiply-Add)
  approach from "High-performance SIMD modular arithmetic for polynomial evaluation"
  by Fortin et al.

  Key insight: For primes p ≤ 50 bits, use floating-point with FMA:
    1. Compute h = x * y (product)
    2. Compute l = fma(x, y, -h) (low bits via error-free transformation)
    3. Compute q = floor(h / p) (quotient estimate)
    4. Compute r = fma(-q, p, h) + l (remainder)

  This avoids expensive integer division and enables SIMD vectorization.

  Speedups reported by Fortin et al.:
  - 3.7x on AVX2 (4-wide)
  - 7.2x on AVX-512 (8-wide)

  References:
  - Fortin et al. "High-performance SIMD modular arithmetic" (2024)
  - Granlund & Montgomery "Division by Invariant Integers using Multiplication"
-/

import AmoLean.Sigma.SIMD

namespace AmoLean.Sigma.ZModSIMD

open AmoLean.Sigma.SIMD (avxConfig SIMDConfig genSIMDHeader)
open AmoLean.Sigma.CodeGen (indentStr)

/-! ## Part 1: Modular Arithmetic Configuration -/

/-- Configuration for a specific prime field -/
structure FieldConfig where
  prime : Nat
  primeFloat : String      -- p as double literal
  invPrime : String        -- 1/p as double literal (precomputed)
  primitiveRoot : Nat      -- Primitive root for NTT
  deriving Repr, Inhabited

/-- Goldilocks prime: 2^64 - 2^32 + 1 (popular in ZK proofs) -/
def goldilocksConfig : FieldConfig := {
  prime := 18446744069414584321
  primeFloat := "18446744069414584321.0"
  invPrime := "5.421010862427522e-20"  -- 1/p
  primitiveRoot := 7
}

/-- Baby bear prime: 2^31 - 2^27 + 1 (RISC Zero) -/
def babyBearConfig : FieldConfig := {
  prime := 2013265921
  primeFloat := "2013265921.0"
  invPrime := "4.967053722587597e-10"  -- 1/p
  primitiveRoot := 31
}

/-- A small test prime: 17 -/
def testPrimeConfig : FieldConfig := {
  prime := 17
  primeFloat := "17.0"
  invPrime := "0.058823529411764705"  -- 1/17
  primitiveRoot := 3
}

/-! ## Part 2: Scalar Modular Operations -/

/-- Generate modular addition: (a + b) mod p -/
def genModAdd (cfg : FieldConfig) (indent : Nat) (dest a b : String) : String :=
  let pad := indentStr indent
  -- Simple approach: add, then conditionally subtract p
  s!"{pad}double {dest}_tmp = {a} + {b};\n" ++
  s!"{pad}double {dest} = {dest}_tmp >= {cfg.primeFloat} ? {dest}_tmp - {cfg.primeFloat} : {dest}_tmp;"

/-- Generate modular subtraction: (a - b) mod p -/
def genModSub (cfg : FieldConfig) (indent : Nat) (dest a b : String) : String :=
  let pad := indentStr indent
  -- Subtract, then add p if negative
  s!"{pad}double {dest}_tmp = {a} - {b};\n" ++
  s!"{pad}double {dest} = {dest}_tmp < 0 ? {dest}_tmp + {cfg.primeFloat} : {dest}_tmp;"

/-- Generate modular multiplication using FMA: (a * b) mod p

    Algorithm from Fortin et al.:
    h = a * b           // high part
    l = fma(a, b, -h)   // low part (error-free transformation)
    q = floor(h * inv_p) // quotient estimate
    r = fma(-q, p, h) + l // remainder
-/
def genModMulFMA (cfg : FieldConfig) (indent : Nat) (dest a b : String) : String :=
  let pad := indentStr indent
  let p := cfg.primeFloat
  let invP := cfg.invPrime
  s!"{pad}// Modular multiplication via FMA\n" ++
  s!"{pad}double h_{dest} = {a} * {b};\n" ++
  s!"{pad}double l_{dest} = fma({a}, {b}, -h_{dest});\n" ++
  s!"{pad}double q_{dest} = floor(h_{dest} * {invP});\n" ++
  s!"{pad}double {dest} = fma(-q_{dest}, {p}, h_{dest}) + l_{dest};"

/-! ## Part 3: SIMD Modular Operations -/

/-- Generate SIMD modular addition (AVX) -/
def genSIMDModAdd (cfg : FieldConfig) (simd : SIMDConfig) (indent : Nat) (dest a b : String) : String :=
  let pad := indentStr indent
  let vecP := s!"v_prime"
  s!"{pad}// SIMD modular add\n" ++
  s!"{pad}{simd.vectorType} {dest}_tmp = {simd.addIntrinsic}({a}, {b});\n" ++
  s!"{pad}{simd.vectorType} {dest}_cmp = _mm256_cmp_pd({dest}_tmp, {vecP}, _CMP_GE_OQ);\n" ++
  s!"{pad}{simd.vectorType} {dest}_sub = {simd.subIntrinsic}({dest}_tmp, {vecP});\n" ++
  s!"{pad}{simd.vectorType} {dest} = _mm256_blendv_pd({dest}_tmp, {dest}_sub, {dest}_cmp);"

/-- Generate SIMD modular subtraction (AVX) -/
def genSIMDModSub (cfg : FieldConfig) (simd : SIMDConfig) (indent : Nat) (dest a b : String) : String :=
  let pad := indentStr indent
  let vecP := s!"v_prime"
  s!"{pad}// SIMD modular sub\n" ++
  s!"{pad}{simd.vectorType} {dest}_tmp = {simd.subIntrinsic}({a}, {b});\n" ++
  s!"{pad}{simd.vectorType} v_zero = _mm256_setzero_pd();\n" ++
  s!"{pad}{simd.vectorType} {dest}_cmp = _mm256_cmp_pd({dest}_tmp, v_zero, _CMP_LT_OQ);\n" ++
  s!"{pad}{simd.vectorType} {dest}_add = {simd.addIntrinsic}({dest}_tmp, {vecP});\n" ++
  s!"{pad}{simd.vectorType} {dest} = _mm256_blendv_pd({dest}_tmp, {dest}_add, {dest}_cmp);"

/-- Generate SIMD modular multiplication via FMA (AVX) -/
def genSIMDModMulFMA (cfg : FieldConfig) (simd : SIMDConfig) (indent : Nat) (dest a b : String) : String :=
  let pad := indentStr indent
  let vecP := s!"v_prime"
  let vecInvP := s!"v_inv_prime"
  s!"{pad}// SIMD modular mul via FMA\n" ++
  s!"{pad}{simd.vectorType} h_{dest} = {simd.mulIntrinsic}({a}, {b});\n" ++
  s!"{pad}{simd.vectorType} l_{dest} = _mm256_fmsub_pd({a}, {b}, h_{dest});\n" ++
  s!"{pad}{simd.vectorType} q_{dest} = _mm256_floor_pd({simd.mulIntrinsic}(h_{dest}, {vecInvP}));\n" ++
  s!"{pad}{simd.vectorType} r_{dest} = _mm256_fnmadd_pd(q_{dest}, {vecP}, h_{dest});\n" ++
  s!"{pad}{simd.vectorType} {dest} = {simd.addIntrinsic}(r_{dest}, l_{dest});"

/-! ## Part 4: NTT Butterfly with Modular Arithmetic -/

/-- Generate modular butterfly: (a + b*w, a - b*w) mod p -/
def genModButterfly (cfg : FieldConfig) (indent : Nat) (out0 out1 a b twiddle : String) : String :=
  let pad := indentStr indent
  s!"{pad}// Modular butterfly\n" ++
  genModMulFMA cfg indent "bw" b twiddle ++ "\n" ++
  genModAdd cfg indent out0 a "bw" ++ "\n" ++
  genModSub cfg indent out1 a "bw"

/-- Generate SIMD modular butterfly -/
def genSIMDModButterfly (cfg : FieldConfig) (simd : SIMDConfig) (indent : Nat)
    (out0 out1 a b twiddle : String) : String :=
  let pad := indentStr indent
  s!"{pad}// SIMD modular butterfly\n" ++
  genSIMDModMulFMA cfg simd indent "bw" b twiddle ++ "\n" ++
  genSIMDModAdd cfg simd indent out0 a "bw" ++ "\n" ++
  genSIMDModSub cfg simd indent out1 a "bw"

/-! ## Part 5: Complete NTT Function Generation -/

/-- Generate constants for prime field -/
def genFieldConstants (cfg : FieldConfig) (simd : SIMDConfig) (indent : Nat) : String :=
  let pad := indentStr indent
  s!"{pad}// Prime field constants\n" ++
  s!"{pad}{simd.vectorType} v_prime = _mm256_set1_pd({cfg.primeFloat});\n" ++
  s!"{pad}{simd.vectorType} v_inv_prime = _mm256_set1_pd({cfg.invPrime});"

/-- Generate NTT_4 with modular arithmetic -/
def genNTT4 (cfg : FieldConfig) (indent : Nat) : String :=
  let pad := indentStr indent
  let simd := avxConfig
  s!"{pad}// NTT_4 over Z/{cfg.prime}Z\n" ++
  genFieldConstants cfg simd indent ++ "\n\n" ++
  s!"{pad}// Load inputs\n" ++
  s!"{pad}{simd.vectorType} v_in = {simd.loadIntrinsic}(&in[0]);\n\n" ++
  s!"{pad}// Stage 1: Butterflies on pairs [0,1] and [2,3]\n" ++
  s!"{pad}// For NTT, we need twiddle factors ω^k\n" ++
  s!"{pad}{simd.vectorType} v_one = _mm256_set1_pd(1.0);\n" ++
  s!"{pad}{simd.vectorType} v_omega = _mm256_set_pd(1.0, 1.0, 1.0, 1.0); // ω^0 for first stage\n\n" ++
  s!"{pad}// Shuffle and butterfly\n" ++
  s!"{pad}{simd.vectorType} v_shuf = _mm256_permute_pd(v_in, 0b0101);\n" ++
  genSIMDModAdd cfg simd indent "v_add1" "v_in" "v_shuf" ++ "\n" ++
  genSIMDModSub cfg simd indent "v_sub1" "v_in" "v_shuf" ++ "\n\n" ++
  s!"{pad}// Blend results\n" ++
  s!"{pad}{simd.vectorType} v1 = _mm256_blend_pd(v_add1, v_sub1, 0b1010);\n\n" ++
  s!"{pad}// Stage 2: Cross butterflies with twiddles\n" ++
  s!"{pad}{simd.vectorType} v_hi128 = _mm256_permute2f128_pd(v1, v1, 0x01);\n" ++
  genSIMDModAdd cfg simd indent "v_add2" "v1" "v_hi128" ++ "\n" ++
  genSIMDModSub cfg simd indent "v_sub2" "v1" "v_hi128" ++ "\n\n" ++
  s!"{pad}{simd.vectorType} v_out = _mm256_blend_pd(v_add2, v_sub2, 0b1100);\n" ++
  s!"{pad}{simd.storeIntrinsic}(&out[0], v_out);"

/-- Generate complete NTT function -/
def genNTTFunction (name : String) (cfg : FieldConfig) (n : Nat) (body : String) : String :=
  let lbrace := "{"
  let rbrace := "}"
  s!"// NTT over Z/{cfg.prime}Z\n" ++
  s!"void {name}(double* restrict in, double* restrict out) {lbrace}\n{body}\n{rbrace}"

/-! ## Part 6: Full File Generation -/

def genZModSIMDHeader : String :=
  "// Generated by AMO-Lean ZMod SIMD CodeGen\n" ++
  "// Phase 5.9 - FMA-based modular arithmetic\n" ++
  "#include <immintrin.h>\n" ++
  "#include <math.h>\n" ++
  "#include <stddef.h>\n\n"

def genNTT4File (cfg : FieldConfig) : String :=
  genZModSIMDHeader ++
  genNTTFunction s!"ntt4_p{cfg.prime}" cfg 4 (genNTT4 cfg 1)

/-! ## Part 7: Tests -/

section Tests

-- Test 1: Scalar modular operations
def testScalarModOps : IO Unit := do
  IO.println "=== Test 1: Scalar Modular Operations (p=17) ==="
  let cfg := testPrimeConfig
  IO.println "// Modular addition:"
  IO.println (genModAdd cfg 0 "result" "a" "b")
  IO.println ""
  IO.println "// Modular multiplication via FMA:"
  IO.println (genModMulFMA cfg 0 "result" "a" "b")
  IO.println ""

-- Test 2: SIMD modular operations
def testSIMDModOps : IO Unit := do
  IO.println "=== Test 2: SIMD Modular Operations (AVX) ==="
  let cfg := testPrimeConfig
  let simd := avxConfig
  IO.println "// SIMD modular add:"
  IO.println (genSIMDModAdd cfg simd 0 "v_result" "v_a" "v_b")
  IO.println ""
  IO.println "// SIMD modular mul via FMA:"
  IO.println (genSIMDModMulFMA cfg simd 0 "v_result" "v_a" "v_b")
  IO.println ""

-- Test 3: NTT_4 with small prime
def testNTT4Small : IO Unit := do
  IO.println "=== Test 3: NTT_4 with p=17 ==="
  IO.println (genNTT4File testPrimeConfig)
  IO.println ""

-- Test 4: NTT_4 with Goldilocks prime
def testNTT4Goldilocks : IO Unit := do
  IO.println "=== Test 4: NTT_4 with Goldilocks prime ==="
  IO.println (genNTT4File goldilocksConfig)
  IO.println ""

-- Run all tests
#eval! do
  testScalarModOps
  testSIMDModOps
  testNTT4Small

end Tests

end AmoLean.Sigma.ZModSIMD
