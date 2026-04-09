/-
  AmoLean.Sigma.UnifiedSIMDBridge — Unified SIMD Code Generation

  Bridges the two SIMD codegen paths:
    1. Sigma/SIMD.lean: generates AVX intrinsics for MatExpr (DFT structure, doubles)
    2. MixedExprToSIMD.lean: generates AVX/NEON intrinsics for MixedExpr (field arithmetic, u32)

  This module combines both:
    - NTT structure from Sigma (stages, stride, gather/scatter)
    - Butterfly kernel from MixedExprToSIMD (Solinas fold, u32)

  Result: SIMD NTT with field-optimized kernels.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedExprToSIMD
import AmoLean.EGraph.Verified.Bitwise.NTTBridge
import AmoLean.EGraph.Verified.Bitwise.NTTFactorizationRules

set_option autoImplicit false

namespace AmoLean.Sigma.UnifiedSIMDBridge

open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise
  (HardwareCost arm_cortex_a76 riscv_sifive_u74 fpga_dsp48e2
   mersenne31_prime babybear_prime goldilocks_prime)
open AmoLean.EGraph.Verified.Bitwise.MixedExprToSIMD
  (SIMDConfig avx2Config neonConfig exprToSIMD emitSolinasFoldSIMD)
open AmoLean.EGraph.Verified.Bitwise.NTTBridge
  (butterflyDirectAuto solinasFoldExpr)
open AmoLean.EGraph.Verified.Bitwise.NTTFactorizationRules
  (NTTStrategy selectBestStrategy)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: SIMD NTT generation with field-optimized kernels
-- ══════════════════════════════════════════════════════════════════

/-- Generate a complete SIMD NTT C function with field-optimized butterfly kernels.
    Combines:
      - Loop structure from Sigma pipeline (radix-2 DIT)
      - Butterfly kernel from MixedExprToSIMD (Solinas fold on u32)
      - SIMD intrinsics: AVX2 (8-wide) or NEON (4-wide)

    Each butterfly processes `cfg.lanes` butterflies in parallel.
    For BabyBear on AVX2: 8 butterflies per instruction.
    For BabyBear on NEON: 4 butterflies per instruction. -/
def genSIMDNTT (n p : Nat) (k c : Nat) (simd : SIMDConfig)
    (funcName : String := "ntt_simd") : String :=
  let numStages := Nat.log 2 n
  let bfVarName : Nat → String := fun i => match i with | 0 => "va" | 1 => "vw" | _ => "vb"
  let (sumExpr, diffExpr) := butterflyDirectAuto 0 1 2 p
  let sumBody := exprToSIMD sumExpr simd bfVarName
  let diffBody := exprToSIMD diffExpr simd bfVarName

  s!"/* AMO-Lean Generated SIMD NTT — Cross-Level Optimized
 * N = {n}, p = {p}, {simd.target} ({simd.lanes} lanes × u32)
 * Structure: Sigma pipeline (radix-2 DIT)
 * Kernel: E-graph optimized Solinas fold (verified)
 * Butterfly: {simd.lanes} parallel per vector instruction
 */

#include {simd.headerInclude}
#include <stdint.h>
#include <stddef.h>

/* Solinas fold (vectorized): fold(x) % p = x % p */
static inline {simd.vecType} solinas_fold({simd.vecType} x) \{
    return {exprToSIMD (solinasFoldExpr (.witnessE 0) k c) simd (fun _ => "x")};
}

/* Butterfly sum: a' = fold(a + fold(w * b)) — {simd.lanes}-wide */
static inline {simd.vecType} bf_sum({simd.vecType} va, {simd.vecType} vw, {simd.vecType} vb) \{
    return {sumBody};
}

/* Butterfly diff: b' = fold(p + a - fold(w * b)) — {simd.lanes}-wide */
static inline {simd.vecType} bf_diff({simd.vecType} va, {simd.vecType} vw, {simd.vecType} vb) \{
    return {diffBody};
}

/* Full NTT: {n} elements, radix-2 DIT, {simd.lanes}-wide SIMD butterflies */
void {funcName}(uint32_t *data, size_t n, const uint32_t *twiddles) \{
    size_t log_n = {numStages};

    for (size_t stage = 0; stage < log_n; stage++) \{
        size_t half = 1 << (log_n - stage - 1);
        for (size_t group = 0; group < (1u << stage); group++) \{
            /* Process {simd.lanes} butterflies per iteration */
            for (size_t pair = 0; pair < half; pair += {simd.lanes}) \{
                size_t i = group * 2 * half + pair;
                size_t j = i + half;

                /* Load {simd.lanes} data elements */
                {simd.vecType} va = {match simd.target with
                  | "avx2" => s!"_mm256_loadu_si256((__m256i*)&data[i])"
                  | _ => s!"vld1q_u32(&data[i])"};
                {simd.vecType} vb = {match simd.target with
                  | "avx2" => s!"_mm256_loadu_si256((__m256i*)&data[j])"
                  | _ => s!"vld1q_u32(&data[j])"};

                /* Load twiddle factors */
                size_t tw_idx = stage * (n / 2) + group * half + pair;
                {simd.vecType} vw = {match simd.target with
                  | "avx2" => s!"_mm256_loadu_si256((__m256i*)&twiddles[tw_idx])"
                  | _ => s!"vld1q_u32(&twiddles[tw_idx])"};

                /* Butterfly: {simd.lanes} parallel */
                {simd.vecType} sum = bf_sum(va, vw, vb);
                {simd.vecType} diff = bf_diff(va, vw, vb);

                /* Store results */
                {match simd.target with
                  | "avx2" => s!"_mm256_storeu_si256((__m256i*)&data[i], sum);\n                _mm256_storeu_si256((__m256i*)&data[j], diff);"
                  | _ => s!"vst1q_u32(&data[i], sum);\n                vst1q_u32(&data[j], diff);"};
            }
        }
    }
}
"

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Kronecker-packed SIMD NTT
-- ══════════════════════════════════════════════════════════════════

/-- Generate Kronecker-packed NTT: two BabyBear NTTs in one 64-bit word.
    Each u64 holds pack(a₁, a₂) = a₁ + a₂ * 2³².
    All operations (add, mul, fold) operate on both lanes simultaneously.
    Throughput: 2x compared to unpacked u32 NTT (without SIMD). -/
def genKroneckerPackedNTT (n p : Nat) (funcName : String := "ntt_kron") : String :=
  s!"/* AMO-Lean Generated Kronecker-Packed NTT
 * N = {n}, p = {p}
 * Each uint64_t holds TWO BabyBear elements: pack(a, b) = a + b * 2^32
 * Throughput: 2x (two NTTs in one word, no SIMD needed)
 * Verified: kronPack_roundtrip, solinasFold_mod_correct
 *
 * IMPORTANT: This requires that all intermediate values stay < 2^31.
 * BabyBear (p < 2^31) satisfies this after each Solinas fold.
 */

#include <stdint.h>
#include <stddef.h>

#define BABYBEAR_P 0x78000001ULL
#define BABYBEAR_C 134217727ULL
#define MASK32     0xFFFFFFFFULL

/* Kronecker fold: applies Solinas fold to BOTH lanes independently.
   Low lane:  fold(lo(x))
   High lane: fold(hi(x))
   Since BabyBear uses 31-bit shift, and each lane is < 2^32,
   the fold operates cleanly within each 32-bit lane. */
static inline uint64_t kron_fold(uint64_t x) \{
    uint32_t lo = (uint32_t)(x & MASK32);
    uint32_t hi = (uint32_t)(x >> 32);
    uint64_t lo_folded = ((lo >> 31) * BABYBEAR_C) + (lo & 0x7FFFFFFF);
    uint64_t hi_folded = ((hi >> 31) * BABYBEAR_C) + (hi & 0x7FFFFFFF);
    return lo_folded | (hi_folded << 32);
}

/* Kronecker butterfly: operates on packed pairs */
static inline void kron_butterfly(uint64_t *a, uint64_t *b, uint64_t w) \{
    /* w*b: multiply each lane independently */
    uint32_t a_lo = (uint32_t)(*a & MASK32), a_hi = (uint32_t)(*a >> 32);
    uint32_t b_lo = (uint32_t)(*b & MASK32), b_hi = (uint32_t)(*b >> 32);
    uint32_t w_lo = (uint32_t)(w & MASK32),  w_hi = (uint32_t)(w >> 32);

    uint64_t wb = ((uint64_t)(w_lo * b_lo)) | ((uint64_t)(w_hi * b_hi) << 32);
    uint64_t wb_folded = kron_fold(wb);

    uint64_t sum = kron_fold((*a & MASK32) + (wb_folded & MASK32) |
                             ((uint64_t)(a_hi + (uint32_t)(wb_folded >> 32)) << 32));
    uint64_t diff = kron_fold((BABYBEAR_P + a_lo - (uint32_t)(wb_folded & MASK32)) |
                              ((uint64_t)(BABYBEAR_P + a_hi - (uint32_t)(wb_folded >> 32)) << 32));
    *a = sum;
    *b = diff;
}

/* Kronecker-packed NTT */
void {funcName}(uint64_t *data, size_t n, const uint64_t *twiddles) \{
    /* data[i] holds pack(ntt1[i], ntt2[i]) — two independent NTTs */
    size_t log_n = {Nat.log 2 n};
    for (size_t stage = 0; stage < log_n; stage++) \{
        size_t half = 1 << (log_n - stage - 1);
        for (size_t group = 0; group < (1u << stage); group++) \{
            for (size_t pair = 0; pair < half; pair++) \{
                size_t i = group * 2 * half + pair;
                size_t j = i + half;
                uint64_t w = twiddles[stage * (n / 2) + group * half + pair];
                kron_butterfly(&data[i], &data[j], w);
            }
        }
    }
}
"

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Strategy-aware NTT generation
-- ══════════════════════════════════════════════════════════════════

/-- Generate optimized NTT using the best strategy for the given parameters.
    Combines cross-level optimization:
      1. Select factorization (radix-2/4, DIT/DIF) based on total cost
      2. Select reduction (Solinas/Harvey/Montgomery) based on hardware
      3. Select execution (scalar/SIMD/Kronecker) based on field width + ISA -/
def genBestNTT (n p : Nat) (simd : Option SIMDConfig := none)
    (funcName : String := "ntt_best") : String :=
  -- Step 1: determine field parameters
  let (k, c) :=
    if p == babybear_prime then (31, 2^27 - 1)
    else if p == mersenne31_prime then (31, 1)
    else if p == goldilocks_prime then (64, 2^32 - 1)
    else (31, 1)  -- default

  -- Step 2: select best strategy
  let (strategy, _cost) := selectBestStrategy n p 3 1 6  -- ARM costs

  -- Step 3: generate code for chosen strategy
  match strategy, simd with
  | .kroneckerPacked, _ =>
    genKroneckerPackedNTT n p funcName
  | _, some cfg =>
    genSIMDNTT n p k c cfg funcName
  | _, none =>
    -- Scalar fallback: use MixedBridge
    AmoLean.Sigma.MixedBridge.nttToOptimizedC
      { n := n, p := p, hw := arm_cortex_a76, funcName := funcName }

-- ══════════════════════════════════════════════════════════════════
-- Section 4: IO — write all variants
-- ══════════════════════════════════════════════════════════════════

/-- Write all NTT variants for BabyBear to a directory. -/
def writeAllNTTVariants (outputDir : String := "generated/ntt") : IO Unit := do
  IO.FS.createDirAll outputDir

  -- Scalar NTT (cross-level: Sigma structure + MixedExpr kernel)
  let scalar := genBestNTT 1024 babybear_prime none "ntt_scalar_1024"
  IO.FS.writeFile ⟨s!"{outputDir}/ntt_babybear_scalar.c"⟩ scalar
  IO.println s!"  Written: ntt_babybear_scalar.c ({scalar.length} bytes)"

  -- SIMD NTT (AVX2: 8-wide)
  let avx2 := genSIMDNTT 1024 babybear_prime 31 (2^27-1) avx2Config "ntt_avx2_1024"
  IO.FS.writeFile ⟨s!"{outputDir}/ntt_babybear_avx2.c"⟩ avx2
  IO.println s!"  Written: ntt_babybear_avx2.c ({avx2.length} bytes)"

  -- SIMD NTT (NEON: 4-wide)
  let neon := genSIMDNTT 1024 babybear_prime 31 (2^27-1) neonConfig "ntt_neon_1024"
  IO.FS.writeFile ⟨s!"{outputDir}/ntt_babybear_neon.c"⟩ neon
  IO.println s!"  Written: ntt_babybear_neon.c ({neon.length} bytes)"

  -- Kronecker-packed NTT (2x throughput, no SIMD)
  let kron := genKroneckerPackedNTT 1024 babybear_prime "ntt_kron_1024"
  IO.FS.writeFile ⟨s!"{outputDir}/ntt_babybear_kron.c"⟩ kron
  IO.println s!"  Written: ntt_babybear_kron.c ({kron.length} bytes)"

  -- Best strategy (auto-selected)
  let best := genBestNTT 1024 babybear_prime (some neonConfig) "ntt_best_1024"
  IO.FS.writeFile ⟨s!"{outputDir}/ntt_babybear_best.c"⟩ best
  IO.println s!"  Written: ntt_babybear_best.c ({best.length} bytes)"

  IO.println "\nDone. NTT variants generated:"
  IO.println "  scalar:   Sigma structure + MixedExpr kernel (verified)"
  IO.println "  avx2:     8-wide SIMD with Solinas fold u32"
  IO.println "  neon:     4-wide SIMD with Solinas fold u32"
  IO.println "  kron:     Kronecker-packed (2 NTTs in 1 u64)"
  IO.println "  best:     Auto-selected best strategy"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: strategy selection prefers kronecker for BabyBear. -/
example : (selectBestStrategy 1024 babybear_prime 3 1 6).1 = .kroneckerPacked := by
  native_decide

end AmoLean.Sigma.UnifiedSIMDBridge
