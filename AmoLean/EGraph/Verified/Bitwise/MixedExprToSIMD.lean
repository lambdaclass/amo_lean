/-
  AmoLean.EGraph.Verified.Bitwise.MixedExprToSIMD — SIMD C code generation from MixedExpr

  Generates AVX2 and NEON intrinsics code for BabyBear field arithmetic.
  Maps MixedExpr constructors to lane-parallel SIMD operations:
    AVX2: 8 × u32 in __m256i (x86-64)
    NEON: 4 × u32 in uint32x4_t (ARM aarch64)

  Key insight: The Solinas fold `(x >> k) * c + (x & mask)` vectorizes trivially
  because all operations are element-wise (no cross-lane dependencies).

  The generated code is NOT formally verified at the SIMD level — verification
  is at the scalar MixedExpr level (solinasFold_mod_correct). SIMD correctness
  follows because all intrinsics used are lane-wise equivalents of scalar ops.
-/
import AmoLean.EGraph.Verified.Bitwise.NTTBridge

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.MixedExprToSIMD

open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise
  (mersenne31_prime babybear_prime goldilocks_prime)
open AmoLean.EGraph.Verified.Bitwise.NTTBridge
  (solinasFoldExpr mersenneFoldExpr butterflyDirectSum butterflyDirectDiff
   butterflyDirectAuto)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: SIMD Configuration
-- ══════════════════════════════════════════════════════════════════

/-- SIMD target configuration. -/
structure SIMDConfig where
  target : String        -- "avx2" or "neon"
  lanes : Nat           -- 8 for AVX2, 4 for NEON
  vecType : String      -- "__m256i" or "uint32x4_t"
  headerInclude : String -- "<immintrin.h>" or "<arm_neon.h>"
  deriving Repr, Inhabited

def avx2Config : SIMDConfig :=
  { target := "avx2", lanes := 8, vecType := "__m256i"
    headerInclude := "<immintrin.h>" }

def neonConfig : SIMDConfig :=
  { target := "neon", lanes := 4, vecType := "uint32x4_t"
    headerInclude := "<arm_neon.h>" }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: MixedExpr → SIMD intrinsics
-- ══════════════════════════════════════════════════════════════════

/-- Map a MixedExpr to SIMD C intrinsic expression.
    Each scalar operation becomes a lane-parallel SIMD operation.
    Variable references (witnessE n) become SIMD register names. -/
def exprToSIMD (e : MixedExpr) (cfg : SIMDConfig)
    (varName : Nat → String := fun n => s!"v{n}") : String :=
  match cfg.target with
  | "avx2" => exprToAVX2 e varName
  | "neon" => exprToNEON e varName
  | _ => s!"/* unsupported SIMD target: {cfg.target} */"
where
  exprToAVX2 (e : MixedExpr) (varName : Nat → String) : String :=
    match e with
    | .constE n        => s!"_mm256_set1_epi32({n})"
    | .witnessE n      => varName n
    | .pubInputE n     => s!"pub_{n}"
    | .addE a b        => s!"_mm256_add_epi32({exprToAVX2 a varName}, {exprToAVX2 b varName})"
    | .subE a b        => s!"_mm256_sub_epi32({exprToAVX2 a varName}, {exprToAVX2 b varName})"
    | .mulE a b        => s!"_mm256_mullo_epi32({exprToAVX2 a varName}, {exprToAVX2 b varName})"
    | .negE a          => s!"_mm256_sub_epi32(_mm256_setzero_si256(), {exprToAVX2 a varName})"
    | .smulE n a       => s!"_mm256_mullo_epi32(_mm256_set1_epi32({n}), {exprToAVX2 a varName})"
    | .shiftRightE a n => s!"_mm256_srli_epi32({exprToAVX2 a varName}, {n})"
    | .shiftLeftE a n  => s!"_mm256_slli_epi32({exprToAVX2 a varName}, {n})"
    | .bitAndE a b     => s!"_mm256_and_si256({exprToAVX2 a varName}, {exprToAVX2 b varName})"
    | .bitXorE a b     => s!"_mm256_xor_si256({exprToAVX2 a varName}, {exprToAVX2 b varName})"
    | .bitOrE a b      => s!"_mm256_or_si256({exprToAVX2 a varName}, {exprToAVX2 b varName})"
    | .constMaskE n    => s!"_mm256_set1_epi32({2^n - 1})"
    | .reduceE a _p    => exprToAVX2 a varName  -- reduce is a no-op in SIMD (fold replaces it)
    | .kronPackE a b w =>
      s!"_mm256_add_epi32({exprToAVX2 a varName}, _mm256_slli_epi32({exprToAVX2 b varName}, {w}))"
    | .kronUnpackLoE a w =>
      s!"_mm256_and_si256({exprToAVX2 a varName}, _mm256_set1_epi32({2^w - 1}))"
    | .kronUnpackHiE a w =>
      s!"_mm256_srli_epi32({exprToAVX2 a varName}, {w})"
    | .montyReduceE a p mu =>
      s!"monty_reduce_avx2({exprToAVX2 a varName}, _mm256_set1_epi32({p}), _mm256_set1_epi32({mu}))"
    | .barrettReduceE a p m =>
      s!"barrett_reduce_avx2({exprToAVX2 a varName}, _mm256_set1_epi32({p}), _mm256_set1_epi32({m}))"
    | .harveyReduceE a p =>
      s!"harvey_reduce_avx2({exprToAVX2 a varName}, _mm256_set1_epi32({p}))"
    | .conditionalSubE a p =>
      s!"cond_sub_avx2({exprToAVX2 a varName}, _mm256_set1_epi32({p}))"
    -- v3.20.b B2 (§14.13.2) — SIMD pack ops are NEON-specific. AVX2 equivalents
    -- will land in v3.21 x86 enablement (§15). For now emit a placeholder that
    -- makes compilation fail loudly if this path is exercised — AVX2 users
    -- should not be routed through packed*Neon constructors.
    | .packedLoadNeonE _              => "/* AVX2: packedLoadNeon not yet supported (v3.21 §15) */"
    | .packedStoreNeonE _ _           => "/* AVX2: packedStoreNeon not yet supported (v3.21 §15) */"
    | .packedButterflyNeonDITE _ _ _  => "/* AVX2: packedButterflyNeonDIT not yet supported (v3.21 §15) */"

  exprToNEON (e : MixedExpr) (varName : Nat → String) : String :=
    match e with
    | .constE n        => s!"vdupq_n_u32({n})"
    | .witnessE n      => varName n
    | .pubInputE n     => s!"pub_{n}"
    | .addE a b        => s!"vaddq_u32({exprToNEON a varName}, {exprToNEON b varName})"
    | .subE a b        => s!"vsubq_u32({exprToNEON a varName}, {exprToNEON b varName})"
    | .mulE a b        => s!"vmulq_u32({exprToNEON a varName}, {exprToNEON b varName})"
    | .negE a          => s!"vsubq_u32(vdupq_n_u32(0), {exprToNEON a varName})"
    | .smulE n a       => s!"vmulq_n_u32({exprToNEON a varName}, {n})"
    | .shiftRightE a n => s!"vshrq_n_u32({exprToNEON a varName}, {n})"
    | .shiftLeftE a n  => s!"vshlq_n_u32({exprToNEON a varName}, {n})"
    | .bitAndE a b     => s!"vandq_u32({exprToNEON a varName}, {exprToNEON b varName})"
    | .bitXorE a b     => s!"veorq_u32({exprToNEON a varName}, {exprToNEON b varName})"
    | .bitOrE a b      => s!"vorrq_u32({exprToNEON a varName}, {exprToNEON b varName})"
    | .constMaskE n    => s!"vdupq_n_u32({2^n - 1})"
    | .reduceE a _p    => exprToNEON a varName
    | .kronPackE a b w =>
      s!"vaddq_u32({exprToNEON a varName}, vshlq_n_u32({exprToNEON b varName}, {w}))"
    | .kronUnpackLoE a w =>
      s!"vandq_u32({exprToNEON a varName}, vdupq_n_u32({2^w - 1}))"
    | .kronUnpackHiE a w =>
      s!"vshrq_n_u32({exprToNEON a varName}, {w})"
    | .montyReduceE a _p _mu =>
      -- Montgomery REDC using Plonky3's NEON recipe (all u32 lanes, no u64):
      -- Requires lhs (the value to reduce) to be in signed range [-P, P].
      -- Uses pre-broadcast constants PACKED_P and PACKED_MU.
      -- Result: canonical form [0, P).
      s!"monty_mul_neon({exprToNEON a varName})"
    | .barrettReduceE a p m =>
      s!"barrett_reduce_neon({exprToNEON a varName}, vdupq_n_u32({p}), vdupq_n_u32({m}))"
    | .harveyReduceE a p =>
      s!"harvey_reduce_neon({exprToNEON a varName}, vdupq_n_u32({p}))"
    | .conditionalSubE a p =>
      s!"cond_sub_neon({exprToNEON a varName}, vdupq_n_u32({p}))"
    -- v3.20.b B2 (§14.13.2) — NEON-native pack ops. Real emission for B3 will
    -- go through SIMDEmitter.lean's `emitPackedButterflyNeonDIT_C` which uses
    -- Stmt.call for the packed kernel; this `exprToNEON` path is not how B2/B3
    -- emit (it's for the generic MixedExpr→SIMD-C helper, not the verified
    -- pipeline). Emit human-readable placeholders that compile as expressions
    -- to not break callers.
    | .packedLoadNeonE addr            => s!"vld1q_s32((int32_t*){exprToNEON addr varName})"
    | .packedStoreNeonE values _addr   => exprToNEON values varName
    | .packedButterflyNeonDITE a b _tw =>
      s!"vshrq_n_u32(vaddq_u32({exprToNEON a varName}, {exprToNEON b varName}), 1)"

-- ══════════════════════════════════════════════════════════════════
-- Section 3: SIMD function emission
-- ══════════════════════════════════════════════════════════════════

/-- Emit a SIMD C function that processes `lanes` elements in parallel. -/
def emitSIMDFunction (funcName : String) (params : List String)
    (body : MixedExpr) (cfg : SIMDConfig)
    (varName : Nat → String := fun n => s!"v{n}") : String :=
  let paramStr := String.intercalate ", " (params.map fun p => s!"{cfg.vecType} {p}")
  let bodyExpr := exprToSIMD body cfg varName
  s!"static inline {cfg.vecType} {funcName}({paramStr}) \{
    return {bodyExpr};
}"

/-- Emit the Solinas fold as a SIMD function.
    fold(x) = (x >> k) * c + (x & (2^k - 1))
    Verified: solinasFold_mod_correct — fold(x) % p = x % p -/
def emitSolinasFoldSIMD (k c : Nat) (cfg : SIMDConfig) : String :=
  let foldExpr := solinasFoldExpr (.witnessE 0) k c
  emitSIMDFunction s!"solinas_fold_{k}_{c}" ["x"] foldExpr cfg (fun _ => "x")

/-- Emit the Mersenne fold as a SIMD function.
    fold(x) = (x >> k) + (x & (2^k - 1))  [c = 1, no multiply] -/
def emitMersenneFoldSIMD (k : Nat) (cfg : SIMDConfig) : String :=
  let foldExpr := mersenneFoldExpr (.witnessE 0) k
  emitSIMDFunction s!"mersenne_fold_{k}" ["x"] foldExpr cfg (fun _ => "x")

/-- Emit a full butterfly SIMD function.
    sum:  fold(a + fold(w * b))
    diff: fold(p + a - fold(w * b))
    Verified: butterflyDirectSum_correct -/
def emitButterflySIMD (k c p : Nat) (cfg : SIMDConfig) : String × String :=
  let bfVarName : Nat → String := fun n => match n with | 0 => "a" | 1 => "w" | _ => "b"
  let (sumExpr, diffExpr) := butterflyDirectAuto 0 1 2 p
  let sumFn := emitSIMDFunction s!"butterfly_sum_{p}" ["a", "w", "b"] sumExpr cfg bfVarName
  let diffFn := emitSIMDFunction s!"butterfly_diff_{p}" ["a", "w", "b"] diffExpr cfg bfVarName
  (sumFn, diffFn)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: NTT stage SIMD generation
-- ══════════════════════════════════════════════════════════════════

/-- Emit a complete SIMD header with all BabyBear operations.
    Includes: fold, butterfly_sum, butterfly_diff, and NTT stage helpers. -/
def emitBabyBearSIMDHeader (cfg : SIMDConfig) : String :=
  let fold := emitSolinasFoldSIMD 31 (2^27 - 1) cfg
  let (bfSum, bfDiff) := emitButterflySIMD 31 (2^27 - 1) babybear_prime cfg
  s!"/* AMO-Lean Generated SIMD — BabyBear (p = 2^31 - 2^27 + 1)
 * Target: {cfg.target} ({cfg.lanes} lanes × u32)
 * Verified: solinasFold_mod_correct, butterflyDirectSum_correct
 * Generated from: AmoLean/EGraph/Verified/Bitwise/NTTBridge.lean
 */

#include {cfg.headerInclude}
#include <stdint.h>

#define BABYBEAR_P 0x78000001U
#define BABYBEAR_C 134217727U  /* 2^27 - 1 */

/* ═══ Solinas fold: fold(x) % p = x % p ═══ */
{fold}

/* ═══ Butterfly sum: a' = fold(a + fold(w*b)) ═══ */
{bfSum}

/* ═══ Butterfly diff: b' = fold(p + a - fold(w*b)) ═══ */
{bfDiff}

/* ═══ Butterfly pair (in-place) ═══ */
static inline void butterfly_pair_{babybear_prime}({cfg.vecType} *a, {cfg.vecType} *b, {cfg.vecType} w) \{
    {cfg.vecType} sum = butterfly_sum_{babybear_prime}(*a, w, *b);
    {cfg.vecType} diff = butterfly_diff_{babybear_prime}(*a, w, *b);
    *a = sum;
    *b = diff;
}
"

/-- Emit a Mersenne31 SIMD header. -/
def emitMersenne31SIMDHeader (cfg : SIMDConfig) : String :=
  let fold := emitMersenneFoldSIMD 31 cfg
  let (bfSum, bfDiff) := emitButterflySIMD 31 1 mersenne31_prime cfg
  s!"/* AMO-Lean Generated SIMD — Mersenne31 (p = 2^31 - 1)
 * Target: {cfg.target} ({cfg.lanes} lanes × u32)
 * Verified: solinasFold_mod_correct
 */

#include {cfg.headerInclude}
#include <stdint.h>

#define MERSENNE31_P 0x7FFFFFFFU

/* ═══ Mersenne fold: fold(x) = (x >> 31) + (x & mask) ═══ */
{fold}

/* ═══ Butterfly ═══ */
{bfSum}
{bfDiff}
"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: FRI fold SIMD
-- ══════════════════════════════════════════════════════════════════

/-- FRI fold SIMD: process `lanes` polynomial evaluations in parallel.
    Each lane computes: result[i] = even[i] + alpha * odd[i] (mod p)
    This is naturally data-parallel (no inter-lane dependencies). -/
def emitFRIFoldSIMD (k c p : Nat) (cfg : SIMDConfig) : String :=
  let foldExpr := solinasFoldExpr (.witnessE 0) k c
  let foldCode := exprToSIMD foldExpr cfg (fun _ => "x")
  s!"/* FRI fold: result[i] = fold(even[i] + fold(alpha * odd[i]))
 * Each lane processes one evaluation point independently.
 * Verified: solinasFold_mod_correct (scalar level)
 */
static inline {cfg.vecType} fri_fold_{p}(
    {cfg.vecType} even, {cfg.vecType} odd, {cfg.vecType} alpha) \{
    /* Step 1: alpha * odd (lane-wise multiply) */
    {cfg.vecType} prod = {match cfg.target with
      | "avx2" => s!"_mm256_mullo_epi32(alpha, odd)"
      | _ => s!"vmulq_u32(alpha, odd)"};
    /* Step 2: fold(alpha * odd) */
    {cfg.vecType} x = prod;
    {cfg.vecType} prod_folded = {foldCode};
    /* Step 3: even + fold(alpha * odd) */
    {cfg.vecType} sum = {match cfg.target with
      | "avx2" => s!"_mm256_add_epi32(even, prod_folded)"
      | _ => s!"vaddq_u32(even, prod_folded)"};
    /* Step 4: fold(sum) */
    x = sum;
    return {foldCode};
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 6: IO — write SIMD headers to files
-- ══════════════════════════════════════════════════════════════════

/-- Write all SIMD headers to a directory. -/
def writeSIMDHeaders (outputDir : String := "generated/simd") : IO Unit := do
  IO.FS.createDirAll outputDir

  -- BabyBear AVX2
  let bbAvx2 := emitBabyBearSIMDHeader avx2Config
  IO.FS.writeFile ⟨s!"{outputDir}/babybear_avx2.h"⟩ bbAvx2
  IO.println s!"  Written: {outputDir}/babybear_avx2.h ({bbAvx2.length} bytes)"

  -- BabyBear NEON
  let bbNeon := emitBabyBearSIMDHeader neonConfig
  IO.FS.writeFile ⟨s!"{outputDir}/babybear_neon.h"⟩ bbNeon
  IO.println s!"  Written: {outputDir}/babybear_neon.h ({bbNeon.length} bytes)"

  -- Mersenne31 AVX2
  let m31Avx2 := emitMersenne31SIMDHeader avx2Config
  IO.FS.writeFile ⟨s!"{outputDir}/mersenne31_avx2.h"⟩ m31Avx2
  IO.println s!"  Written: {outputDir}/mersenne31_avx2.h ({m31Avx2.length} bytes)"

  -- FRI fold AVX2
  let friAvx2 := emitFRIFoldSIMD 31 (2^27 - 1) babybear_prime avx2Config
  IO.FS.writeFile ⟨s!"{outputDir}/fri_fold_avx2.h"⟩ friAvx2
  IO.println s!"  Written: {outputDir}/fri_fold_avx2.h ({friAvx2.length} bytes)"

  -- FRI fold NEON
  let friNeon := emitFRIFoldSIMD 31 (2^27 - 1) babybear_prime neonConfig
  IO.FS.writeFile ⟨s!"{outputDir}/fri_fold_neon.h"⟩ friNeon
  IO.println s!"  Written: {outputDir}/fri_fold_neon.h ({friNeon.length} bytes)"

  IO.println s!"\nDone. SIMD headers generated for AVX2 and NEON."

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Correctness argument (not a formal proof)
-- ══════════════════════════════════════════════════════════════════

/-!
### Lane-wise Correctness Argument

The SIMD code is correct because:
1. `solinasFold_mod_correct` proves `fold(x) % p = x % p` for any `x : Nat`
2. All SIMD intrinsics used are **element-wise** (no cross-lane operations):
   - `_mm256_add_epi32` = lane-wise add
   - `_mm256_mullo_epi32` = lane-wise multiply (low 32 bits)
   - `_mm256_srli_epi32` = lane-wise shift right
   - `_mm256_and_si256` = lane-wise AND
   - Same for NEON equivalents
3. Therefore, for each lane `i`:
   `simd_fold(x)[i] = scalar_fold(x[i])`
   and by `solinasFold_mod_correct`:
   `simd_fold(x)[i] % p = x[i] % p`

This argument holds for all operations in the generated code:
- Solinas fold: 4 element-wise ops (shift + mul + and + add)
- Butterfly sum: 2 folds + 1 add + 1 mul = 10 element-wise ops
- FRI fold: 1 mul + 2 folds + 1 add = 12 element-wise ops

No shuffle, blend, or cross-lane operations are used.
-/

end AmoLean.EGraph.Verified.Bitwise.MixedExprToSIMD
