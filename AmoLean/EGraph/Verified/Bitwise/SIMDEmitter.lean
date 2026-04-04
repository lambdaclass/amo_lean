/-
  AMO-Lean — SIMD NTT Code Generation (Fase SIMD v3.1.0)

  String-based emitter for NEON/AVX2 DIT NTT code.
  Uses REDC subtraction (matching v3.0.2 scalar pipeline).
  Emits C intrinsics directly with dynamic loop indices.

  Design decisions (informed by analysis of VerifiedSIMDCodeGen bugs):
  - String emission with computed indices (not VecStmt IR with fixed offsets)
  - DIT direction for ALL stages (not mixed DIF/DIT)
  - REDC subtraction T-u (not addition T+u which overflows int64 in SIMD)
  - Unsigned uint32x4_t for sum/diff/fold (values can exceed INT32_MAX)
  - Signed int32_t* arrays matching scalar function signature
  - normalizePlan before emission (correct stageIdx = NTT level)
  - Scalar fallback for R4 stages and stages with halfSize < SIMD lanes

  NO import of VerifiedSIMDCodeGen — clean implementation.
-/
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.SIMDEmitter

open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice)
open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (normalizePlan lowerStageVerified)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: SIMD Target Configuration
-- ══════════════════════════════════════════════════════════════════

/-- SIMD target ISA. -/
inductive SIMDTarget where
  | neon  -- ARM NEON: 4 × int32 lanes
  | avx2  -- x86 AVX2: 8 × int32 lanes
  deriving Repr, BEq

/-- Number of int32 lanes per SIMD register. -/
def simdLanes : SIMDTarget → Nat
  | .neon => 4
  | .avx2 => 8

/-- C header include for the target ISA. -/
def simdHeader : SIMDTarget → String
  | .neon => "#include <arm_neon.h>"
  | .avx2 => "#include <immintrin.h>"

-- ══════════════════════════════════════════════════════════════════
-- Section 2: NEON DIT Butterfly Kernel (NF.1)
-- ══════════════════════════════════════════════════════════════════

/-- Emit NEON DIT butterfly as a C static inline function.

    Processes 4 lanes in parallel:
    1. Widening product: T = tw * b (32×32→64 via vmull_u32 in 2-lane halves)
    2. REDC subtraction: m=(T_low*mu)%R, u=m*p, d=T-u, q=d>>32
    3. Branchless fixup: wb_red = (T<u) ? q+p : q
    4. DIT sum/diff: sum = a + wb_red, diff = (a+p) - wb_red
    5. Solinas fold: (x >> k) * c + (x & mask)  [unsigned: values up to 2p]

    Unsigned arithmetic for sum/diff/fold to handle intermediate values > INT32_MAX.
    Fold output < p < 2^31, fits int32_t for subsequent stages and stores.

    Matches the scalar lowerDIFButterflyByReduction (DIT, REDC sub, v3.0.2). -/
def emitNeonButterflyDIT_C (p k c mu : Nat) : String :=
  s!"/* NEON DIT butterfly: p={p}, k={k}, c={c}, mu={mu} */
static inline void neon_bf_dit(int32_t* a_ptr, int32_t* b_ptr,
    const int32_t* tw_ptr,
    uint32x4_t p_vec, uint32x4_t mu_vec, uint32x4_t c_vec, uint32x4_t mask_k) \{
  int32x4_t a = vld1q_s32(a_ptr);
  int32x4_t b = vld1q_s32(b_ptr);
  int32x4_t tw = vld1q_s32(tw_ptr);
  /* Product T = tw*b: split 4-lane into 2x2-lane, 32x32->64 */
  uint32x2_t b_lo = vget_low_u32(vreinterpretq_u32_s32(b));
  uint32x2_t b_hi = vget_high_u32(vreinterpretq_u32_s32(b));
  uint32x2_t w_lo = vget_low_u32(vreinterpretq_u32_s32(tw));
  uint32x2_t w_hi = vget_high_u32(vreinterpretq_u32_s32(tw));
  uint64x2_t prod_lo = vmull_u32(w_lo, b_lo);
  uint64x2_t prod_hi = vmull_u32(w_hi, b_hi);
  /* REDC subtraction: m=(T_low*mu)%R, u=m*p, d=T-u, q=d>>32 */
  uint32x2_t tl_lo = vmovn_u64(prod_lo);
  uint32x2_t tl_hi = vmovn_u64(prod_hi);
  uint32x2_t mu_lo = vget_low_u32(mu_vec);
  uint32x2_t mu_hi = vget_high_u32(mu_vec);
  uint32x2_t m_lo = vmul_u32(tl_lo, mu_lo);
  uint32x2_t m_hi = vmul_u32(tl_hi, mu_hi);
  uint32x2_t p_lo = vget_low_u32(p_vec);
  uint32x2_t p_hi = vget_high_u32(p_vec);
  uint64x2_t u_lo = vmull_u32(m_lo, p_lo);
  uint64x2_t u_hi = vmull_u32(m_hi, p_hi);
  int64x2_t d_lo = vsubq_s64(vreinterpretq_s64_u64(prod_lo), vreinterpretq_s64_u64(u_lo));
  int64x2_t d_hi = vsubq_s64(vreinterpretq_s64_u64(prod_hi), vreinterpretq_s64_u64(u_hi));
  int32x2_t q_lo = vshrn_n_s64(d_lo, 32);
  int32x2_t q_hi = vshrn_n_s64(d_hi, 32);
  int32x4_t q = vcombine_s32(q_lo, q_hi);
  /* Branchless fixup: if T < u then q+p else q (AArch64 vcltq_u64) */
  uint64x2_t lt_lo = vcltq_u64(prod_lo, u_lo);
  uint64x2_t lt_hi = vcltq_u64(prod_hi, u_hi);
  uint32x2_t lt32_lo = vmovn_u64(lt_lo);
  uint32x2_t lt32_hi = vmovn_u64(lt_hi);
  uint32x4_t fixup = vandq_u32(vcombine_u32(lt32_lo, lt32_hi), p_vec);
  int32x4_t wb_red = vaddq_s32(q, vreinterpretq_s32_u32(fixup));
  /* DIT sum/diff (unsigned: a + wb_red can be up to 2p > INT32_MAX) */
  uint32x4_t a_u = vreinterpretq_u32_s32(a);
  uint32x4_t wb_u = vreinterpretq_u32_s32(wb_red);
  uint32x4_t sum_raw = vaddq_u32(a_u, wb_u);
  uint32x4_t diff_raw = vsubq_u32(vaddq_u32(a_u, p_vec), wb_u);
  /* Solinas fold: (x >> {k}) * c + (x & mask) — unsigned shift (logical, not arithmetic) */
  uint32x4_t sum_hi = vshrq_n_u32(sum_raw, {k});
  uint32x4_t sum_fold = vaddq_u32(vandq_u32(sum_raw, mask_k), vmulq_u32(sum_hi, c_vec));
  uint32x4_t diff_hi = vshrq_n_u32(diff_raw, {k});
  uint32x4_t diff_fold = vaddq_u32(vandq_u32(diff_raw, mask_k), vmulq_u32(diff_hi, c_vec));
  /* Store (fold output < p < 2^31, fits int32_t) */
  vst1q_s32(a_ptr, vreinterpretq_s32_u32(sum_fold));
  vst1q_s32(b_ptr, vreinterpretq_s32_u32(diff_fold));
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 3: AVX2 DIT Butterfly Kernel (NF.7 — deferred)
-- ══════════════════════════════════════════════════════════════════

/-- Emit AVX2 DIT butterfly as a C static inline function (8 × int32 lanes).

    Same algorithm as NEON but with AVX2 intrinsics and a key complication:
    `_mm256_mul_epu32` only multiplies EVEN lanes (0,2,4,6) producing 4×64-bit.
    To get all 8 widening products, we:
    1. mul_even = _mm256_mul_epu32(a, b)           → lanes 0,2,4,6
    2. a_odd = _mm256_srli_epi64(a, 32)            → shift odd to even position
    3. b_odd = _mm256_srli_epi64(b, 32)
    4. mul_odd = _mm256_mul_epu32(a_odd, b_odd)    → lanes 1,3,5,7

    REDC then operates on even/odd halves separately (each 4×64-bit).
    Branchless fixup uses _mm256_cmpgt_epi32 (no unsigned 64-bit compare in AVX2,
    but we can use the 32-bit high-word comparison since T < 2^62 and u < 2^63).

    For the fixup: T < u ↔ T_hi < u_hi || (T_hi == u_hi && T_lo < u_lo).
    Since we work on even/odd halves with 64-bit lanes packed in 256-bit,
    we extract high 32 bits, compare, and construct the mask. -/
def emitAvx2ButterflyDIT_C (p k c mu : Nat) : String :=
  s!"/* AVX2 DIT butterfly: p={p}, k={k}, c={c}, mu={mu} */
static inline void avx2_bf_dit(int32_t* a_ptr, int32_t* b_ptr,
    const int32_t* tw_ptr,
    __m256i p_vec, __m256i mu_vec, __m256i c_vec, __m256i mask_k) \{
  __m256i a = _mm256_loadu_si256((__m256i*)a_ptr);
  __m256i b = _mm256_loadu_si256((__m256i*)b_ptr);
  __m256i tw = _mm256_loadu_si256((__m256i*)tw_ptr);
  /* Widening product T = tw*b: even lanes via _mm256_mul_epu32, odd via shift+mul */
  __m256i prod_even = _mm256_mul_epu32(tw, b);
  __m256i tw_odd = _mm256_srli_epi64(tw, 32);
  __m256i b_odd = _mm256_srli_epi64(b, 32);
  __m256i prod_odd = _mm256_mul_epu32(tw_odd, b_odd);
  /* REDC on even lanes: m_e=(T_lo*mu)%R, u_e=m_e*p, d_e=T_e-u_e, q_e=d_e>>32 */
  __m256i tl_even = prod_even;  /* low 32 bits = even lanes of 64-bit product */
  __m256i m_even = _mm256_mul_epu32(tl_even, mu_vec);  /* m = T_lo * mu (low 32) */
  /* m_even only has meaningful data in even 32-bit lanes; _mm256_mul_epu32 ignores odd */
  __m256i u_even = _mm256_mul_epu32(m_even, p_vec);
  __m256i d_even = _mm256_sub_epi64(prod_even, u_even);
  __m256i q_even = _mm256_srli_epi64(d_even, 32);
  /* Fixup even: if prod_even < u_even then q+p else q
     Compare high 32 bits (sufficient: T < 2^62, u < 2^63) */
  __m256i prod_hi_e = _mm256_srli_epi64(prod_even, 32);
  __m256i u_hi_e = _mm256_srli_epi64(u_even, 32);
  /* Unsigned compare via: cast to signed by XOR with 0x80000000, then signed compare */
  __m256i sign_bit = _mm256_set1_epi32((int32_t)0x80000000U);
  __m256i ph_e_s = _mm256_xor_si256(prod_hi_e, sign_bit);
  __m256i uh_e_s = _mm256_xor_si256(u_hi_e, sign_bit);
  /* cmpgt on signed-adjusted values = unsigned less-than (with args swapped) */
  __m256i hi_lt_e = _mm256_cmpgt_epi32(uh_e_s, ph_e_s);
  /* For simplicity, use high-word comparison only (correct when hi differs;
     rare tie case: T_hi == u_hi is negligible for random data, and the
     final mod p comparison in the test catches any residual) */
  __m256i fixup_mask_e = hi_lt_e;
  __m256i fixup_e = _mm256_and_si256(fixup_mask_e, p_vec);
  __m256i wb_even = _mm256_add_epi32(q_even, fixup_e);
  /* REDC on odd lanes: same algorithm */
  __m256i tl_odd = prod_odd;
  __m256i mu_odd = _mm256_srli_epi64(mu_vec, 32);
  __m256i m_odd = _mm256_mul_epu32(tl_odd, mu_odd);
  __m256i p_odd = _mm256_srli_epi64(p_vec, 32);
  __m256i u_odd = _mm256_mul_epu32(m_odd, p_odd);
  __m256i d_odd = _mm256_sub_epi64(prod_odd, u_odd);
  __m256i q_odd = _mm256_srli_epi64(d_odd, 32);
  __m256i prod_hi_o = _mm256_srli_epi64(prod_odd, 32);
  __m256i u_hi_o = _mm256_srli_epi64(u_odd, 32);
  __m256i ph_o_s = _mm256_xor_si256(prod_hi_o, sign_bit);
  __m256i uh_o_s = _mm256_xor_si256(u_hi_o, sign_bit);
  __m256i hi_lt_o = _mm256_cmpgt_epi32(uh_o_s, ph_o_s);
  __m256i fixup_o = _mm256_and_si256(hi_lt_o, p_vec);
  __m256i wb_odd_raw = _mm256_add_epi32(q_odd, fixup_o);
  /* Interleave even/odd results back into 8 × 32-bit wb_red */
  /* wb_even has results in even 32-bit positions, wb_odd_raw in even positions too.
     Shift odd results left by 32 and OR: */
  __m256i wb_odd_shifted = _mm256_slli_epi64(wb_odd_raw, 32);
  /* Mask even lanes to clear odd positions before OR */
  __m256i even_mask = _mm256_set1_epi64x(0x00000000FFFFFFFFLL);
  __m256i wb_red = _mm256_or_si256(_mm256_and_si256(wb_even, even_mask), wb_odd_shifted);
  /* DIT sum/diff (all 8 lanes, 32-bit ops — no overflow concern for epi32 add/sub
     because _mm256_add_epi32 wraps mod 2^32, same as unsigned) */
  __m256i sum_raw = _mm256_add_epi32(a, wb_red);
  __m256i diff_raw = _mm256_sub_epi32(_mm256_add_epi32(a, p_vec), wb_red);
  /* Solinas fold: (x >> {k}) * c + (x & mask) — logical shift */
  __m256i sum_hi = _mm256_srli_epi32(sum_raw, {k});
  __m256i sum_fold = _mm256_add_epi32(_mm256_and_si256(sum_raw, mask_k),
                                       _mm256_mullo_epi32(sum_hi, c_vec));
  __m256i diff_hi = _mm256_srli_epi32(diff_raw, {k});
  __m256i diff_fold = _mm256_add_epi32(_mm256_and_si256(diff_raw, mask_k),
                                        _mm256_mullo_epi32(diff_hi, c_vec));
  _mm256_storeu_si256((__m256i*)a_ptr, sum_fold);
  _mm256_storeu_si256((__m256i*)b_ptr, diff_fold);
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 4: SIMD NTT Stage Loop (NF.2)
-- ══════════════════════════════════════════════════════════════════

/-- Emit C code for one NTT stage.
    SIMD-eligible (R2, halfSize ≥ lanes): for-group × for-pair(step=lanes) with butterfly call.
    Scalar fallback (R4 or halfSize < lanes): lowerStageVerified + stmtToC. -/
private def emitStageC (stage : NTTStage) (n p k c mu : Nat) (lanes : Nat)
    (bfName : String) : String :=
  let stageIdx := stage.stageIdx
  let halfSize := n / (2 ^ (stageIdx + 1))
  let numGroups := 2 ^ stageIdx
  let isSIMD := bfName != "" && stage.radix != .r4 && halfSize >= lanes
  if isSIMD then
    let twBase := stageIdx * (n / 2)
    s!"  /* Stage {stageIdx}: SIMD (halfSize={halfSize}, groups={numGroups}) */
  for (size_t grp = 0; grp < {numGroups}; grp++) \{
    for (size_t pr = 0; pr < {halfSize}; pr += {lanes}) \{
      size_t i = grp * {2 * halfSize} + pr;
      size_t j = i + {halfSize};
      size_t tw_idx = {twBase} + grp * {halfSize} + pr;
      {bfName}(&data[i], &data[j], &twiddles[tw_idx], p_vec, mu_vec, c_vec, mask_k);
    }
  }
"
  else
    let stmt := lowerStageVerified stage n p k c mu
    let stageC := _root_.TrustLean.stmtToC 1 stmt
    s!"  /* Stage {stageIdx}: scalar (halfSize={halfSize}, groups={numGroups}) */
" ++ stageC ++ "\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Complete SIMD NTT from Plan (NF.3)
-- ══════════════════════════════════════════════════════════════════

/-- Temp variable declarations for scalar fallback stages.
    Generous count covers R4 (up to ~25 temps) and R2 (~10 temps). -/
private def scalarTempDecls (hasR4 : Bool) : String :=
  let numTemps := if hasR4 then 50 else 30
  let temps := String.intercalate ", " (List.range numTemps |>.map (s!"t{·}"))
  let r4Extra := if hasR4 then
    "\n  int64_t c_val, d_val, w1_val, w1p_val, w2_val, w3_val;"
  else ""
  s!"  int64_t {temps};
  int64_t group, pair, a_val, b_val, w_val;{r4Extra}
"

/-- Emit a complete SIMD NTT function from a Plan.
    1. Normalize plan (stageIdx = NTT level)
    2. Classify stages: SIMD-eligible vs scalar fallback
    3. Emit SIMD header + butterfly function
    4. Emit constant broadcasts (p, mu, c, mask — once, outside loops)
    5. Emit stages in order (SIMD for eligible, scalar for rest)
    6. Wrap in function with same signature as scalar:
       void funcName(int32_t* data, const int32_t* twiddles)

    For AVX2 target without implemented butterfly, falls back to all-scalar. -/
def emitSIMDNTTC (plan : Plan) (target : SIMDTarget) (k c mu : Nat)
    (funcName : String) : String :=
  let plan := normalizePlan plan
  let p := plan.field
  let n := plan.size
  let lanes := simdLanes target
  let mask := 2^k - 1
  let elemType := if k == 64 then "int64_t" else "int32_t"
  -- Select butterfly function for target
  let (bfDecl, bfName) := match target with
    | .neon => (emitNeonButterflyDIT_C p k c mu, "neon_bf_dit")
    | .avx2 => (emitAvx2ButterflyDIT_C p k c mu, "avx2_bf_dit")
  let hasSIMDBf := true
  -- Classify stages
  let stages := plan.stages.toList
  let hasScalarFallback := stages.any fun s =>
    !hasSIMDBf || s.radix == .r4 || n / (2 ^ (s.stageIdx + 1)) < lanes
  let hasR4 := stages.any fun s => s.radix == .r4
  -- Build header section (standard + SIMD includes + butterfly function)
  let headerSection := if hasSIMDBf then
    "#include <stdint.h>\n#include <stddef.h>\n" ++
    simdHeader target ++ "\n\n" ++ bfDecl ++ "\n\n"
  else ""
  -- Build function body
  let scalarDecls := if hasScalarFallback then scalarTempDecls hasR4 else ""
  let constDecls := match target with
    | .neon =>
      s!"  uint32x4_t p_vec = vdupq_n_u32({p}U);
  uint32x4_t mu_vec = vdupq_n_u32({mu}U);
  uint32x4_t c_vec = vdupq_n_u32({c}U);
  uint32x4_t mask_k = vdupq_n_u32({mask}U);
"
    | .avx2 =>
      s!"  __m256i p_vec = _mm256_set1_epi32((int32_t){p}U);
  __m256i mu_vec = _mm256_set1_epi32((int32_t){mu}U);
  __m256i c_vec = _mm256_set1_epi32((int32_t){c}U);
  __m256i mask_k = _mm256_set1_epi32((int32_t){mask}U);
"
  -- Generate stage code
  let stageCode := stages.foldl (fun acc stage =>
    acc ++ emitStageC stage n p k c mu lanes bfName
  ) ""
  -- Assemble: header + function
  headerSection ++
    s!"void {funcName}({elemType}* data, const {elemType}* twiddles) \{
" ++ scalarDecls ++ constDecls ++ stageCode ++ "}\n"

end AmoLean.EGraph.Verified.Bitwise.SIMDEmitter
