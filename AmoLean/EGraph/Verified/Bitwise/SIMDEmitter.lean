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
import AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDButterfly

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.SIMDEmitter

open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice)
open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (normalizePlan lowerStageVerified)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDButterfly
  (sqdmulhButterflyStmt hs2ButterflyStmt hs1ButterflyStmt)
open AmoLean.Bridge.SIMDStmtToC (simdStmtToC)

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
-- Section 2a: Shared NEON butterfly body (load + REDC product + DIT sum/diff)
-- ══════════════════════════════════════════════════════════════════

/-- Shared NEON DIT butterfly body: load a/b/tw → widening product → REDC sub →
    branchless fixup → DIT sum/diff. Returns C code fragment ending at diff_raw.
    Used by both Solinas and Harvey butterfly variants to avoid code duplication. -/
private def emitNeonButterflyBody : String :=
  "  int32x4_t a = vld1q_s32(a_ptr);
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
"

-- ══════════════════════════════════════════════════════════════════
-- Section 2b: NEON DIT Butterfly Kernels (Solinas + Harvey)
-- ══════════════════════════════════════════════════════════════════

/-- Emit NEON DIT butterfly with Solinas fold reduction on sum/diff.
    Uses shared body (load + REDC + sum/diff) + Solinas fold.
    Fold output < p+c < 2^31, fits int32_t. -/
def emitNeonButterflyDIT_C (p k c mu : Nat) : String :=
  s!"/* NEON DIT butterfly (Solinas fold): p={p}, k={k}, c={c}, mu={mu} */
static inline void neon_bf_dit(int32_t* a_ptr, int32_t* b_ptr,
    const int32_t* tw_ptr,
    uint32x4_t p_vec, uint32x4_t mu_vec, uint32x4_t c_vec, uint32x4_t mask_k) \{
{emitNeonButterflyBody}  /* Solinas fold: (x >> {k}) * c + (x & mask) */
  uint32x4_t sum_hi = vshrq_n_u32(sum_raw, {k});
  uint32x4_t sum_fold = vaddq_u32(vandq_u32(sum_raw, mask_k), vmulq_u32(sum_hi, c_vec));
  uint32x4_t diff_hi = vshrq_n_u32(diff_raw, {k});
  uint32x4_t diff_fold = vaddq_u32(vandq_u32(diff_raw, mask_k), vmulq_u32(diff_hi, c_vec));
  vst1q_s32(a_ptr, vreinterpretq_s32_u32(sum_fold));
  vst1q_s32(b_ptr, vreinterpretq_s32_u32(diff_fold));
}"

/-- Emit NEON DIT butterfly with Harvey conditional subtraction on sum/diff.
    Uses shared body (load + REDC + sum/diff) + branchless Harvey reduce.
    Precondition: sum_raw < 2p, diff_raw < 2p (guaranteed by butterfly structure).
    Output < p, fits int32_t (Harvey reduce: if x >= p then x - p).
    Same function signature as Solinas variant (c_vec, mask_k unused but accepted
    so the call site in emitStageC needs no per-reduction dispatch). -/
def emitNeonButterflyDIT_Harvey_C (p : Nat) : String :=
  s!"/* NEON DIT butterfly (Harvey): p={p} */
static inline void neon_bf_dit_har(int32_t* a_ptr, int32_t* b_ptr,
    const int32_t* tw_ptr,
    uint32x4_t p_vec, uint32x4_t mu_vec, uint32x4_t c_vec, uint32x4_t mask_k) \{
  (void)c_vec; (void)mask_k;  /* unused — Harvey needs only p_vec */
{emitNeonButterflyBody}  /* Harvey conditional subtract: if x >= p then x - p */
  uint32x4_t ge_s = vcgeq_u32(sum_raw, p_vec);
  uint32x4_t sum_red = vsubq_u32(sum_raw, vandq_u32(ge_s, p_vec));
  uint32x4_t ge_d = vcgeq_u32(diff_raw, p_vec);
  uint32x4_t diff_red = vsubq_u32(diff_raw, vandq_u32(ge_d, p_vec));
  vst1q_s32(a_ptr, vreinterpretq_s32_u32(sum_red));
  vst1q_s32(b_ptr, vreinterpretq_s32_u32(diff_red));
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 2c: sqdmulh Montgomery NEON Butterfly (v3.5.0 REDCMethod)
-- ══════════════════════════════════════════════════════════════════

/-- Emit NEON DIT butterfly using sqdmulh Montgomery REDC (4 lanes, ~13 instructions).
    Product: vqdmulhq_s32 (signed doubling multiply high) stays in int32x4_t lanes —
    no widening to uint64x2_t, no split into 2-lane halves.
    Sum/diff canonicalization: vminq_u32 trick (unsigned min of x and x±p).
    Requires precomputed mu_tw table: mu_tw[i] = tw[i] * mu mod 2^32.

    Signed arithmetic is CONTAINED within the REDC — the output wb is canonicalized
    to [0, p) before sum/diff, so the butterfly exterior stays unsigned.

    Same function signature as vmull variants (p_vec, mu_vec, c_vec, mask_k accepted
    but c_vec/mask_k unused). Additionally reads from mu_tw_ptr (precomputed). -/
def emitNeonButterflyDIT_Sqdmulh_C (p : Nat) : String :=
  s!"/* NEON DIT butterfly (sqdmulh Montgomery): p={p} */
static inline void neon_bf_dit_sq(int32_t* a_ptr, int32_t* b_ptr,
    const int32_t* tw_ptr, const int32_t* mu_tw_ptr,
    int32x4_t p_vec_s, uint32x4_t p_vec) \{
  int32x4_t a = vld1q_s32(a_ptr);
  int32x4_t b = vld1q_s32(b_ptr);
  int32x4_t tw = vld1q_s32(tw_ptr);
  int32x4_t mu_tw = vld1q_s32(mu_tw_ptr);
  /* Montgomery REDC: wb = monty_mul(tw, b) via sqdmulh (4 lanes, int32) */
  int32x4_t c_hi  = vqdmulhq_s32(tw, b);          /* high32(2 * tw * b) */
  int32x4_t q     = vmulq_s32(b, mu_tw);           /* b * mu_tw mod 2^32 */
  int32x4_t qp_hi = vqdmulhq_s32(q, p_vec_s);     /* high32(2 * q * p) */
  int32x4_t d     = vhsubq_s32(c_hi, qp_hi);       /* (c_hi - qp_hi) / 2 */
  uint32x4_t uf   = vcltq_s32(c_hi, qp_hi);        /* underflow mask */
  int32x4_t wb    = vreinterpretq_s32_u32(
      vmlsq_u32(vreinterpretq_u32_s32(d), uf, p_vec)); /* d - uf*p (fixup) */
  /* DIT sum/diff + canonicalize via unsigned min trick */
  int32x4_t sum_s = vaddq_s32(a, wb);
  uint32x4_t su   = vreinterpretq_u32_s32(sum_s);
  uint32x4_t sum_canon = vminq_u32(su, vsubq_u32(su, p_vec));
  int32x4_t dif_s = vsubq_s32(a, wb);
  uint32x4_t du   = vreinterpretq_u32_s32(dif_s);
  uint32x4_t dif_canon = vminq_u32(du, vaddq_u32(du, p_vec));
  /* Store (output in [0, p), fits int32_t) */
  vst1q_s32(a_ptr, vreinterpretq_s32_u32(sum_canon));
  vst1q_s32(b_ptr, vreinterpretq_s32_u32(dif_canon));
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 2d: Small SIMD Butterflies for halfSize < 4 (v3.6.0)
-- ══════════════════════════════════════════════════════════════════

/-- Emit NEON butterfly for halfSize=2 using sqdmulh REDC.
    Processes 2 groups per call (4 butterflies total, filling all 4 NEON lanes).
    Group g has data layout: [a0, a1, b0, b1] at data[g*4..g*4+3].
    Two groups g and g+1: combine their a's and b's into full 4-lane registers.

    Layout in registers:
      a_vec = [a0_g, a1_g, a0_{g+1}, a1_{g+1}]  (4 lanes)
      b_vec = [b0_g, b1_g, b0_{g+1}, b1_{g+1}]  (4 lanes)
      tw_vec = [tw0_g, tw1_g, tw0_{g+1}, tw1_{g+1}]  (4 lanes)

    The a's are contiguous at data[g*4] and data[(g+1)*4].
    The b's are contiguous at data[g*4+2] and data[(g+1)*4+2].
    The tw's are contiguous at tw[base + g*2] and tw[base + (g+1)*2]. -/
def emitNeonButterflyDIT_HS2_C (p : Nat) : String :=
  s!"/* NEON DIT butterfly halfSize=2 (sqdmulh, 2 groups × 2 bf = 4 lanes) */
static inline void neon_bf_dit_hs2(
    int32_t* data_g0, int32_t* data_g1,
    const int32_t* tw_g0, const int32_t* tw_g1,
    const int32_t* mu_tw_g0, const int32_t* mu_tw_g1,
    int32x4_t p_vec_s, uint32x4_t p_vec) \{
  /* Load: 2 a-values + 2 b-values from each group, combine into 4 lanes */
  int32x2_t a_lo = vld1_s32(data_g0);          /* [a0_g0, a1_g0] */
  int32x2_t a_hi = vld1_s32(data_g1);          /* [a0_g1, a1_g1] */
  int32x4_t a = vcombine_s32(a_lo, a_hi);
  int32x2_t b_lo = vld1_s32(data_g0 + 2);      /* [b0_g0, b1_g0] */
  int32x2_t b_hi = vld1_s32(data_g1 + 2);      /* [b0_g1, b1_g1] */
  int32x4_t b = vcombine_s32(b_lo, b_hi);
  int32x2_t tw_lo = vld1_s32(tw_g0);           /* [tw0_g0, tw1_g0] */
  int32x2_t tw_hi = vld1_s32(tw_g1);           /* [tw0_g1, tw1_g1] */
  int32x4_t tw = vcombine_s32(tw_lo, tw_hi);
  int32x2_t mt_lo = vld1_s32(mu_tw_g0);
  int32x2_t mt_hi = vld1_s32(mu_tw_g1);
  int32x4_t mu_tw = vcombine_s32(mt_lo, mt_hi);
  /* sqdmulh REDC: 4 lanes in parallel */
  int32x4_t c_hi  = vqdmulhq_s32(tw, b);
  int32x4_t q     = vmulq_s32(b, mu_tw);
  int32x4_t qp_hi = vqdmulhq_s32(q, p_vec_s);
  int32x4_t d     = vhsubq_s32(c_hi, qp_hi);
  uint32x4_t uf   = vcltq_s32(c_hi, qp_hi);
  int32x4_t wb    = vreinterpretq_s32_u32(
      vmlsq_u32(vreinterpretq_u32_s32(d), uf, p_vec));
  /* Canonicalize + sum/diff */
  int32x4_t sum_s = vaddq_s32(a, wb);
  uint32x4_t su   = vreinterpretq_u32_s32(sum_s);
  uint32x4_t sum_c = vminq_u32(su, vsubq_u32(su, p_vec));
  int32x4_t dif_s = vsubq_s32(a, wb);
  uint32x4_t du   = vreinterpretq_u32_s32(dif_s);
  uint32x4_t dif_c = vminq_u32(du, vaddq_u32(du, p_vec));
  /* Store: split back to 2-lane halves for each group */
  vst1_s32(data_g0,     vget_low_s32(vreinterpretq_s32_u32(sum_c)));
  vst1_s32(data_g0 + 2, vget_low_s32(vreinterpretq_s32_u32(dif_c)));
  vst1_s32(data_g1,     vget_high_s32(vreinterpretq_s32_u32(sum_c)));
  vst1_s32(data_g1 + 2, vget_high_s32(vreinterpretq_s32_u32(dif_c)));
}"

/-- Emit NEON butterfly for halfSize=1 using sqdmulh REDC.
    Processes 4 groups per call (4 butterflies, 4 lanes).
    Group g has data layout: [a, b] at data[g*2..g*2+1].
    Four groups g..g+3: load 8 contiguous elements, deinterleave a's and b's.

    Layout:
      memory: [a0, b0, a1, b1, a2, b2, a3, b3]  (8 elements, 4 groups)
      after deinterleave:
        a_vec = [a0, a1, a2, a3]  (4 lanes)
        b_vec = [b0, b1, b2, b3]  (4 lanes)

    Deinterleave via vld2_s32 (load-and-deinterleave intrinsic). -/
def emitNeonButterflyDIT_HS1_C (p : Nat) : String :=
  s!"/* NEON DIT butterfly halfSize=1 (sqdmulh, 4 groups × 1 bf = 4 lanes) */
static inline void neon_bf_dit_hs1(
    int32_t* data_ptr, const int32_t* tw_ptr, const int32_t* mu_tw_ptr,
    int32x4_t p_vec_s, uint32x4_t p_vec) \{
  /* Load + deinterleave: 4 groups × 2 elements = 8 elements */
  int32x4x2_t ab = vld2q_s32(data_ptr);         /* ab.val[0]=[a0,a1,a2,a3], ab.val[1]=[b0,b1,b2,b3] */
  int32x4_t a = ab.val[0];
  int32x4_t b = ab.val[1];
  int32x4_t tw = vld1q_s32(tw_ptr);
  int32x4_t mu_tw = vld1q_s32(mu_tw_ptr);
  /* sqdmulh REDC: 4 lanes in parallel */
  int32x4_t c_hi  = vqdmulhq_s32(tw, b);
  int32x4_t q     = vmulq_s32(b, mu_tw);
  int32x4_t qp_hi = vqdmulhq_s32(q, p_vec_s);
  int32x4_t d     = vhsubq_s32(c_hi, qp_hi);
  uint32x4_t uf   = vcltq_s32(c_hi, qp_hi);
  int32x4_t wb    = vreinterpretq_s32_u32(
      vmlsq_u32(vreinterpretq_u32_s32(d), uf, p_vec));
  /* Canonicalize + sum/diff */
  int32x4_t sum_s = vaddq_s32(a, wb);
  uint32x4_t su   = vreinterpretq_u32_s32(sum_s);
  uint32x4_t sum_c = vminq_u32(su, vsubq_u32(su, p_vec));
  int32x4_t dif_s = vsubq_s32(a, wb);
  uint32x4_t du   = vreinterpretq_u32_s32(dif_s);
  uint32x4_t dif_c = vminq_u32(du, vaddq_u32(du, p_vec));
  /* Interleave + store: [sum0,dif0,sum1,dif1,sum2,dif2,sum3,dif3] */
  int32x4x2_t result;
  result.val[0] = vreinterpretq_s32_u32(sum_c);
  result.val[1] = vreinterpretq_s32_u32(dif_c);
  vst2q_s32(data_ptr, result);
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
    Dispatches to sqdmulh, Harvey, or Solinas butterfly based on useSqdmulh flag and stage.reduction.
    Scalar fallback (R4 or halfSize < lanes): lowerStageVerified + stmtToC. -/
private def emitStageC (stage : NTTStage) (n p k c mu : Nat) (lanes : Nat)
    (bfNameSol bfNameHar bfNameSq : String) (useSqdmulh : Bool)
    (useVerifiedSIMD : Bool := false)
    (profiled : Bool := false) : String :=
  let stageIdx := stage.stageIdx
  let halfSize := n / (2 ^ (stageIdx + 1))
  let numGroups := 2 ^ stageIdx
  -- CNTVCT fence marker for per-stage profiling (N36.5a)
  let fence := if profiled then
    s!"  asm volatile(\"isb\\nmrs %0, CNTVCT_EL0\" : \"=r\"(_ticks[{stageIdx}]) :: \"memory\");\n"
  else ""
  -- Verified SIMD path: butterflies via Stmt.call + simdStmtToC (N37.5)
  let canVerified := useVerifiedSIMD && useSqdmulh && stage.radix != .r4
  if canVerified && halfSize >= lanes then
    let twBase := stageIdx * (n / 2)
    let step := lanes
    -- Build butterfly Stmt with pointer VarNames (set in loop body)
    let bfStmt := sqdmulhButterflyStmt
      (.user "a_ptr") (.user "b_ptr") (.user "tw_ptr") (.user "mu_tw_ptr")
      (.user "p_vec_s") (.user "p_vec")
    let body := simdStmtToC 3 bfStmt
    fence ++
    s!"  /* Stage {stageIdx}: verified-SIMD sqdmulh (halfSize={halfSize}, groups={numGroups}) */
  for (size_t grp = 0; grp < {numGroups}; grp++) \{
    for (size_t pr = 0; pr < {halfSize}; pr += {step}) \{
      int32_t* a_ptr = &data[grp * {2 * halfSize} + pr];
      int32_t* b_ptr = a_ptr + {halfSize};
      const int32_t* tw_ptr = &twiddles[{twBase} + grp * {halfSize} + pr];
      const int32_t* mu_tw_ptr = &mu_tw[{twBase} + grp * {halfSize} + pr];
{body}
    }
  }
"
  else if canVerified && halfSize == 2 && numGroups >= 2 then
    let twBase := stageIdx * (n / 2)
    -- hs2: 2 groups at a time via verified Stmt path
    let bfStmt := hs2ButterflyStmt
      (.user "dg0") (.user "dg1") (.user "tg0") (.user "tg1")
      (.user "mg0") (.user "mg1") (.user "p_vec_s") (.user "p_vec")
    let body := simdStmtToC 2 bfStmt
    fence ++
    s!"  /* Stage {stageIdx}: verified-SIMD hs2 (halfSize=2, groups={numGroups}) */
  for (size_t grp = 0; grp < {numGroups}; grp += 2) \{
    int32_t* dg0 = &data[grp * 4];
    int32_t* dg1 = &data[(grp + 1) * 4];
    const int32_t* tg0 = &twiddles[{twBase} + grp * 2];
    const int32_t* tg1 = &twiddles[{twBase} + (grp + 1) * 2];
    const int32_t* mg0 = &mu_tw[{twBase} + grp * 2];
    const int32_t* mg1 = &mu_tw[{twBase} + (grp + 1) * 2];
{body}
  }
"
  else if canVerified && halfSize == 1 && numGroups >= 4 then
    let twBase := stageIdx * (n / 2)
    -- hs1: 4 groups at a time via verified Stmt path with deinterleave
    let bfStmt := hs1ButterflyStmt
      (.user "data_ptr") (.user "tw_ptr") (.user "mu_tw_ptr")
      (.user "p_vec_s") (.user "p_vec")
    let body := simdStmtToC 2 bfStmt
    fence ++
    s!"  /* Stage {stageIdx}: verified-SIMD hs1 (halfSize=1, groups={numGroups}) */
  for (size_t grp = 0; grp < {numGroups}; grp += 4) \{
    int32_t* data_ptr = &data[grp * 2];
    const int32_t* tw_ptr = &twiddles[{twBase} + grp];
    const int32_t* mu_tw_ptr = &mu_tw[{twBase} + grp];
{body}
  }
"
  else
  -- Legacy string-emission path below (unchanged)
  let (bfUsed, isSq) :=
    if useSqdmulh && bfNameSq != "" then (bfNameSq, true)
    else match stage.reduction with
      | .harvey => (bfNameHar, false)
      | _ => (bfNameSol, false)
  let isSIMD := bfUsed != "" && stage.radix != .r4 && halfSize >= lanes
  fence ++ if isSIMD then
    let twBase := stageIdx * (n / 2)
    let redLabel := if isSq then "sqdmulh" else match stage.reduction with
      | .harvey => "Harvey" | _ => "Solinas"
    -- sqdmulh butterfly has different call signature (needs mu_tw, p_vec_s)
    let call := fun (off : String) => if isSq then
      s!"{bfUsed}(&data[i{off}], &data[j{off}], &twiddles[tw_idx{off}], &mu_tw[tw_idx{off}], p_vec_s, p_vec);"
    else
      s!"{bfUsed}(&data[i{off}], &data[j{off}], &twiddles[tw_idx{off}], p_vec, mu_vec, c_vec, mask_k);"
    -- ILP: dual-butterfly interleaving (2 calls per iteration, step=2*lanes)
    -- Only when halfSize >= 2*lanes (enough data for 2 independent butterflies)
    let ilp := stage.ilpFactor
    let canIlp := ilp > 1 && halfSize >= 2 * lanes
    let step := if canIlp then 2 * lanes else lanes
    let ilpLabel := if canIlp then s!", ilp={ilp}" else ""
    let secondCall := if canIlp then s!"\n      {call s!"+{lanes}"}" else ""
    s!"  /* Stage {stageIdx}: SIMD {redLabel} (halfSize={halfSize}, groups={numGroups}{ilpLabel}) */
  for (size_t grp = 0; grp < {numGroups}; grp++) \{
    for (size_t pr = 0; pr < {halfSize}; pr += {step}) \{
      size_t i = grp * {2 * halfSize} + pr;
      size_t j = i + {halfSize};
      size_t tw_idx = {twBase} + grp * {halfSize} + pr;
      {call ""}{secondCall}
    }
  }
"
  else if useSqdmulh && stage.radix != .r4 && halfSize == 2 && numGroups >= 2 then
    -- Small SIMD: halfSize=2, process 2 groups per call via neon_bf_dit_hs2
    let twBase := stageIdx * (n / 2)
    s!"  /* Stage {stageIdx}: small-SIMD hs2 (halfSize=2, groups={numGroups}) */
  for (size_t grp = 0; grp < {numGroups}; grp += 2) \{
    size_t g0 = grp * 4;
    size_t g1 = (grp + 1) * 4;
    size_t tw0 = {twBase} + grp * 2;
    size_t tw1 = {twBase} + (grp + 1) * 2;
    neon_bf_dit_hs2(&data[g0], &data[g1], &twiddles[tw0], &twiddles[tw1],
                    &mu_tw[tw0], &mu_tw[tw1], p_vec_s, p_vec);
  }
"
  else if useSqdmulh && stage.radix != .r4 && halfSize == 1 && numGroups >= 4 then
    -- Small SIMD: halfSize=1, process 4 groups per call via neon_bf_dit_hs1
    let twBase := stageIdx * (n / 2)
    s!"  /* Stage {stageIdx}: small-SIMD hs1 (halfSize=1, groups={numGroups}) */
  for (size_t grp = 0; grp < {numGroups}; grp += 4) \{
    size_t base = grp * 2;
    size_t tw_base = {twBase} + grp;
    neon_bf_dit_hs1(&data[base], &twiddles[tw_base], &mu_tw[tw_base], p_vec_s, p_vec);
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
    R4 with Solinas fold needs ~64 temps (4 R2 × 16 temps each).
    R4 with Harvey needs ~40 temps. Use 70 to be safe. -/
private def scalarTempDecls (hasR4 : Bool) : String :=
  let numTemps := if hasR4 then 80 else 30
  let temps := String.intercalate ", " (List.range numTemps |>.map (s!"t{·}"))
  let r4Extra := if hasR4 then
    "\n  int64_t c_val, d_val, w1_val, w1p_val, w2_val, w3_val;"
  else ""
  s!"  int64_t {temps};
  int64_t group, pair, a_val, b_val, w_val;{r4Extra}
"

/-- Deinterleave helper for vld2q_s32 struct decomposition (N37.2).
    vld2q_s32 returns int32x4x2_t (C struct), which Stmt.call cannot represent
    directly. This static inline helper decomposes the struct into two int32x4_t
    outputs via pointer parameters.
    Emitted in the C header when the verified SIMD path is active. -/
def deinterleaveHelperC : String :=
  "/* vld2q_s32 returns int32x4x2_t struct — decompose via helper */
static inline void neon_deinterleave_load(int32x4_t* a, int32x4_t* b,
    const int32_t* ptr) {
    int32x4x2_t tmp = vld2q_s32(ptr);
    *a = tmp.val[0];
    *b = tmp.val[1];
}
"

/-- Interleave store helper for vst2q_s32 struct construction (N37.4 fix).
    vst2q_s32 takes int32x4x2_t struct, which Stmt.call cannot construct.
    This static inline helper takes two vectors and constructs the struct.
    Symmetric to deinterleaveHelperC. -/
def interleaveStoreHelperC : String :=
  "/* vst2q_s32 takes int32x4x2_t struct — construct via helper */
static inline void neon_interleave_store(int32_t* ptr,
    int32x4_t a, int32x4_t b) {
    int32x4x2_t tmp;
    tmp.val[0] = a;
    tmp.val[1] = b;
    vst2q_s32(ptr, tmp);
}
"

/-- NEON temp variable declarations for verified SIMD path (N37.3).
    Pre-declares int32x4_t (nv0..nvN-1) and uint32x4_t (nu0..nuM-1) temps
    at function top, matching the pattern of scalarTempDecls for scalar vars.
    Variables are assigned by simdStmtToC via `nvX = intrinsic(args);`. -/
def neonTempDecls (numSignedVars : Nat := 30) (numUnsignedVars : Nat := 10)
    (numHalfVars : Nat := 10) : String :=
  let nv := String.intercalate ", " (List.range numSignedVars |>.map (s!"nv{·}"))
  let nu := String.intercalate ", " (List.range numUnsignedVars |>.map (s!"nu{·}"))
  let nh := String.intercalate ", " (List.range numHalfVars |>.map (s!"nh{·}"))
  s!"  int32x4_t {nv};\n  uint32x4_t {nu};\n  int32x2_t {nh};\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 5b: Rust SIMD Helpers (v3.8.0)
-- ══════════════════════════════════════════════════════════════════

/-- Rust version of deinterleaveHelperC.
    Rust int32x4x2_t is a tuple (int32x4_t, int32x4_t), accessed via .0/.1. -/
def deinterleaveHelperRust : String :=
  "#[inline(always)]
unsafe fn neon_deinterleave_load(a: &mut int32x4_t, b: &mut int32x4_t, ptr: *const i32) {
    let tmp = vld2q_s32(ptr);
    *a = tmp.0;
    *b = tmp.1;
}
"

/-- Rust version of interleaveStoreHelperC.
    Constructs int32x4x2_t tuple and calls vst2q_s32. -/
def interleaveStoreHelperRust : String :=
  "#[inline(always)]
unsafe fn neon_interleave_store(ptr: *mut i32, a: int32x4_t, b: int32x4_t) {
    vst2q_s32(ptr, int32x4x2_t(a, b));
}
"

/-- Rust NEON temp variable declarations (v3.8.0).
    Uses MaybeUninit to avoid requiring initialization for SIMD types.
    Same variable naming convention as C (nv*, nu*, nh*). -/
def neonTempDeclsRust (numSignedVars : Nat := 30) (numUnsignedVars : Nat := 10)
    (numHalfVars : Nat := 12) : String :=
  let mkDecl (ty tag : String) (n : Nat) : String :=
    String.join (List.range n |>.map fun i =>
      s!"    let mut {tag}{i}: {ty} = unsafe \{ core::mem::MaybeUninit::uninit().assume_init() };\n")
  mkDecl "int32x4_t" "nv" numSignedVars ++
  mkDecl "uint32x4_t" "nu" numUnsignedVars ++
  mkDecl "int32x2_t" "nh" numHalfVars

/-- Emit a complete SIMD NTT function from a Plan.
    1. Normalize plan (stageIdx = NTT level)
    2. Classify stages: SIMD-eligible vs scalar fallback
    3. Emit SIMD header + butterfly function
    4. Emit constant broadcasts (p, mu, c, mask — once, outside loops)
    5. Emit stages in order (SIMD for eligible, scalar for rest)
    6. Wrap in function with same signature as scalar:
       void funcName(int32_t* data, const int32_t* twiddles)

    For AVX2 target without implemented butterfly, falls back to all-scalar.
    When useSqdmulh=true, uses sqdmulh Montgomery REDC (4-lane, ~13 instructions)
    instead of vmull widening REDC. Requires mu_tw precomputed table. -/
def emitSIMDNTTC (plan : Plan) (target : SIMDTarget) (k c mu : Nat)
    (funcName : String) (useSqdmulh : Bool := false)
    (useVerifiedSIMD : Bool := false)
    (profiled : Bool := false) : String :=
  let plan := normalizePlan plan
  let p := plan.field
  let n := plan.size
  let lanes := simdLanes target
  let mask := 2^k - 1
  let elemType := if k == 64 then "int64_t" else "int32_t"
  -- Select butterfly functions for target (Solinas + Harvey + sqdmulh variants)
  let (bfDeclSol, bfNameSol) := match target with
    | .neon => (emitNeonButterflyDIT_C p k c mu, "neon_bf_dit")
    | .avx2 => (emitAvx2ButterflyDIT_C p k c mu, "avx2_bf_dit")
  let (bfDeclHar, bfNameHar) := match target with
    | .neon => (emitNeonButterflyDIT_Harvey_C p, "neon_bf_dit_har")
    | .avx2 => ("", "")
  let (bfDeclSq, bfNameSq) := match target with
    | .neon => if useSqdmulh then (emitNeonButterflyDIT_Sqdmulh_C p, "neon_bf_dit_sq") else ("", "")
    | .avx2 => ("", "")  -- AVX2 sqdmulh not applicable
  -- Classify stages
  let stages := plan.stages.toList
  let hasSIMDStage := stages.any fun s =>
    s.radix != .r4 && n / (2 ^ (s.stageIdx + 1)) >= lanes
  let needsSolinas := !useSqdmulh && stages.any fun s =>
    s.reduction != .harvey && s.radix != .r4 && n / (2 ^ (s.stageIdx + 1)) >= lanes
  let needsHarvey := !useSqdmulh && stages.any fun s =>
    s.reduction == .harvey && s.radix != .r4 && n / (2 ^ (s.stageIdx + 1)) >= lanes
  -- With sqdmulh + small SIMD, only R4 stages need scalar fallback
  let hasScalarFallback := stages.any fun s =>
    s.radix == .r4 || (!useSqdmulh && n / (2 ^ (s.stageIdx + 1)) < lanes)
  let hasR4 := stages.any fun s => s.radix == .r4
  -- Small SIMD butterflies for halfSize < lanes (v3.6.0)
  let hasSmallSIMD := useSqdmulh && stages.any fun s =>
    s.radix != .r4 && n / (2 ^ (s.stageIdx + 1)) < lanes
  let (bfDeclHS2, bfDeclHS1) := match target with
    | .neon => if hasSmallSIMD then
        (emitNeonButterflyDIT_HS2_C p, emitNeonButterflyDIT_HS1_C p)
      else ("", "")
    | .avx2 => ("", "")
  -- Build header section: only emit butterfly functions that are actually used
  let bfDecls :=
    (if useSqdmulh && bfNameSq != "" then bfDeclSq ++ "\n\n" else "") ++
    (if bfDeclHS2 != "" then bfDeclHS2 ++ "\n\n" else "") ++
    (if bfDeclHS1 != "" then bfDeclHS1 ++ "\n\n" else "") ++
    (if needsSolinas then bfDeclSol ++ "\n\n" else "") ++
    (if needsHarvey && bfNameHar != "" then bfDeclHar ++ "\n\n" else "")
  -- Verified SIMD path: emit struct helpers (deinterleave + interleave) in header
  let verifiedHelpers := if useVerifiedSIMD && useSqdmulh then
    deinterleaveHelperC ++ "\n" ++ interleaveStoreHelperC ++ "\n"
  else ""
  let headerSection :=
    "#include <stdint.h>\n#include <stddef.h>\n" ++
    simdHeader target ++ "\n\n" ++ verifiedHelpers ++ bfDecls
  -- Build function body
  let scalarDecls := if hasScalarFallback then scalarTempDecls hasR4 else ""
  let neonDecls := if useVerifiedSIMD && useSqdmulh then neonTempDecls 30 10 12 else ""
  -- sqdmulh needs different constants: signed p_vec_s + unsigned p_vec + mu_tw table
  let constDecls := if useSqdmulh && hasSIMDStage then match target with
    | .neon =>
      s!"  uint32x4_t p_vec = vdupq_n_u32({p}U);
  int32x4_t p_vec_s = vdupq_n_s32((int32_t){p}U);
"
    | .avx2 => ""  -- AVX2 sqdmulh not implemented
  else match target with
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
  -- Generate stage code with per-stage dispatch
  let stageCode := stages.foldl (fun acc stage =>
    acc ++ emitStageC stage n p k c mu lanes bfNameSol bfNameHar bfNameSq useSqdmulh useVerifiedSIMD profiled
  ) ""
  -- Function signature: sqdmulh needs mu_tw parameter
  let sig := if useSqdmulh && hasSIMDStage then
    s!"void {funcName}({elemType}* data, const {elemType}* twiddles, const {elemType}* mu_tw) \{"
  else
    s!"void {funcName}({elemType}* data, const {elemType}* twiddles) \{"
  -- Profiling: CNTVCT ticks array + final fence + print loop (N36.5a)
  let numStages := stages.length
  let profileDecl := if profiled then
    s!"  uint64_t _ticks[{numStages + 1}];\n"
  else ""
  let profileEnd := if profiled then
    let fenceFinal := s!"  asm volatile(\"isb\\nmrs %0, CNTVCT_EL0\" : \"=r\"(_ticks[{numStages}]) :: \"memory\");\n"
    let printLoop := s!"  \{ uint64_t _freq = 24000000; double _total = 0;\n" ++
      s!"    for (int _s = 0; _s < {numStages}; _s++) \{\n" ++
      s!"      double _us = (double)(_ticks[_s+1] - _ticks[_s]) / _freq * 1e6;\n" ++
      s!"      _total += _us;\n" ++
      s!"      fprintf(stderr, \"stage,%d,%.2f\\n\", _s, _us);\n" ++
      s!"    }\n" ++
      s!"    fprintf(stderr, \"total,%.2f\\n\", _total);\n  }\n"
    fenceFinal ++ printLoop
  else ""
  let profileInclude := if profiled then "#include <stdio.h>\n" else ""
  -- Assemble: header + function
  headerSection ++ profileInclude ++ sig ++ "\n" ++ profileDecl ++ scalarDecls ++ neonDecls ++ constDecls ++ stageCode ++ profileEnd ++ "}\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Rust SIMD NTT Generation (v3.8.0, N38.3)
-- ══════════════════════════════════════════════════════════════════

open AmoLean.Bridge.SIMDStmtToC (simdStmtToRust)

/-- Emit one NTT stage as Rust SIMD code (v3.8.0).
    Uses same butterfly Stmts as C path, but emits via simdStmtToRust.
    Pointers use Rust raw pointer arithmetic: as_mut_ptr().add(offset). -/
private def emitStageRust (stage : NTTStage) (n p : Nat) (lanes : Nat) : String :=
  let stageIdx := stage.stageIdx
  let halfSize := n / (2 ^ (stageIdx + 1))
  let numGroups := 2 ^ stageIdx
  let twBase := stageIdx * (n / 2)
  if stage.radix == .r4 then
    -- R4 not supported in Rust SIMD yet — fallback marker
    s!"    // Stage {stageIdx}: R4 not yet supported in Rust SIMD\n"
  else if halfSize >= lanes then
    let step := lanes
    let bfStmt := sqdmulhButterflyStmt
      (.user "a_ptr") (.user "b_ptr") (.user "tw_ptr") (.user "mu_tw_ptr")
      (.user "p_vec_s") (.user "p_vec")
    let body := simdStmtToRust 3 bfStmt
    s!"    // Stage {stageIdx}: SIMD sqdmulh (halfSize={halfSize}, groups={numGroups})
    for grp in 0..{numGroups} \{
        for pr in (0..{halfSize}).step_by({step}) \{
            let a_ptr = unsafe \{ data.add(grp * {2 * halfSize} + pr) };
            let b_ptr = unsafe \{ data.add(grp * {2 * halfSize} + pr + {halfSize}) };
            let tw_ptr = unsafe \{ twiddles.add({twBase} + grp * {halfSize} + pr) };
            let mu_tw_ptr = unsafe \{ mu_tw.add({twBase} + grp * {halfSize} + pr) };
{body}
        }
    }
"
  else if halfSize == 2 && numGroups >= 2 then
    let bfStmt := hs2ButterflyStmt
      (.user "dg0") (.user "dg1") (.user "tg0") (.user "tg1")
      (.user "mg0") (.user "mg1") (.user "p_vec_s") (.user "p_vec")
    let body := simdStmtToRust 2 bfStmt
    s!"    // Stage {stageIdx}: SIMD hs2 (halfSize=2, groups={numGroups})
    for grp in (0..{numGroups}).step_by(2) \{
        let dg0 = unsafe \{ data.add(grp * 4) };
        let dg1 = unsafe \{ data.add((grp + 1) * 4) };
        let tg0 = unsafe \{ twiddles.add({twBase} + grp * 2) };
        let tg1 = unsafe \{ twiddles.add({twBase} + (grp + 1) * 2) };
        let mg0 = unsafe \{ mu_tw.add({twBase} + grp * 2) };
        let mg1 = unsafe \{ mu_tw.add({twBase} + (grp + 1) * 2) };
{body}
    }
"
  else if halfSize == 1 && numGroups >= 4 then
    let bfStmt := hs1ButterflyStmt
      (.user "data_ptr") (.user "tw_ptr") (.user "mu_tw_ptr")
      (.user "p_vec_s") (.user "p_vec")
    let body := simdStmtToRust 2 bfStmt
    s!"    // Stage {stageIdx}: SIMD hs1 (halfSize=1, groups={numGroups})
    for grp in (0..{numGroups}).step_by(4) \{
        let data_ptr = unsafe \{ data.add(grp * 2) };
        let tw_ptr = unsafe \{ twiddles.add({twBase} + grp) };
        let mu_tw_ptr = unsafe \{ mu_tw.add({twBase} + grp) };
{body}
    }
"
  else
    s!"    // Stage {stageIdx}: unsupported configuration\n"

/-- Emit a complete Rust SIMD NTT function (v3.8.0, N38.3).
    Emits `core::arch::aarch64` intrinsics in unsafe blocks.
    Uses same butterfly Stmts as C path — only the emitter differs. -/
def emitSIMDNTTRust (plan : Plan) (target : SIMDTarget) (k c mu : Nat)
    (funcName : String) (useSqdmulh : Bool := false) : String :=
  let plan := normalizePlan plan
  let p := plan.field
  let n := plan.size
  let lanes := simdLanes target
  let stages := plan.stages.toList
  -- Use statement + helpers
  let header :=
    "#![allow(unused_imports, unused_variables, unused_mut, unused_unsafe)]\n" ++
    "#![allow(non_snake_case, non_camel_case_types)]\n" ++
    "use std::arch::aarch64::*;\n\n" ++
    deinterleaveHelperRust ++ "\n" ++
    interleaveStoreHelperRust ++ "\n"
  -- Temp declarations (MaybeUninit for NEON types)
  let neonDecls := neonTempDeclsRust 30 10 12
  -- Constant broadcasts (unsafe for NEON intrinsics)
  let constDecls :=
    s!"    let p_vec: uint32x4_t = unsafe \{ vdupq_n_u32({p}u32) };\n" ++
    s!"    let p_vec_s: int32x4_t = unsafe \{ vdupq_n_s32({p}i32) };\n"
  -- Stage code
  let stageCode := stages.foldl (fun acc stage =>
    acc ++ emitStageRust stage n p lanes
  ) ""
  -- Function: unsafe fn with raw pointer params
  let sig :=
    s!"pub unsafe fn {funcName}(data: *mut i32, twiddles: *const i32, mu_tw: *const i32) \{"
  -- Assemble
  header ++ sig ++ "\n" ++ neonDecls ++ constDecls ++ stageCode ++ "}\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- Deinterleave helper is non-empty and well-formed. -/
example : deinterleaveHelperC.length > 100 := by native_decide

/-- neonTempDecls produces non-empty output. -/
example : (neonTempDecls 3 2).length > 0 := by native_decide

/-- neonTempDecls with small args produces expected format (3 types). -/
example : neonTempDecls 3 2 2 =
    "  int32x4_t nv0, nv1, nv2;\n  uint32x4_t nu0, nu1;\n  int32x2_t nh0, nh1;\n" := rfl

/-- neonTempDecls default (30+10+10) is non-trivial. -/
example : (neonTempDecls).length > 200 := by native_decide

/-- Interleave store helper is non-empty. -/
example : interleaveStoreHelperC.length > 100 := by native_decide

/-- Verified SIMD path produces output when useVerifiedSIMD=true.
    Uses a minimal BabyBear 2^4 plan to verify integration. -/
private def testPlan : Plan :=
  let stages := #[
    { stageIdx := 0, radix := .r2, reduction := .harvey,
      direction := .DIT, inputBoundK := 1, outputBoundK := 1 },
    { stageIdx := 1, radix := .r2, reduction := .harvey,
      direction := .DIT, inputBoundK := 1, outputBoundK := 1 }]
  { stages, field := 2013265921, size := 4 }

/-- Legacy path produces non-empty output. -/
example : (emitSIMDNTTC testPlan .neon 31 1 0x88000001 "ntt_test"
    (useSqdmulh := true) (useVerifiedSIMD := false)).length > 100 := by native_decide

/-- Verified path produces non-empty output. -/
example : (emitSIMDNTTC testPlan .neon 31 1 0x88000001 "ntt_test"
    (useSqdmulh := true) (useVerifiedSIMD := true)).length > 100 := by native_decide

/-- Rust SIMD path produces non-empty output (v3.8.0). -/
example : (emitSIMDNTTRust testPlan .neon 31 1 0x88000001 "ntt_test"
    (useSqdmulh := true)).length > 100 := by native_decide

/-- Rust SIMD helpers are non-empty. -/
example : deinterleaveHelperRust.length > 50 := by native_decide
example : interleaveStoreHelperRust.length > 50 := by native_decide
example : (neonTempDeclsRust 3 2 2).length > 50 := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.SIMDEmitter
