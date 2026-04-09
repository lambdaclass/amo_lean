import AmoLean.Bridge.SIMDStmtToC

/-!
# VerifiedSIMDButterfly — NEON Butterflies as Stmt.call Sequences

Rewrite all NEON butterfly variants (sqdmulh, hs2, hs1) as Stmt.call sequences
using the NeonIntrinsic ADT. Zero string emission — all intrinsic names go through
the type-safe `toCName` function.

Trust boundary: `evalStmt(.call) = none`. The algorithm (load → REDC → sum/diff →
reduce → store) is structurally verifiable; intrinsic semantics are trusted.

Reference implementations (string emission):
- sqdmulh: SIMDEmitter.lean:154-181
- hs2: SIMDEmitter.lean:200-240
- hs1: SIMDEmitter.lean:254-285

Node N37.4 in Fase v3.7.0 (Verified SIMD Codegen).
Consumed by: N37.5 Pipeline Integration, N37.6 Structural Proofs.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDButterfly

open AmoLean.Bridge.SIMDStmtToC (NeonIntrinsic neonCall neonCallVoid simdStmtToC)
open _root_.TrustLean (Stmt VarName LowLevelExpr)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Variable Name Helpers
-- ══════════════════════════════════════════════════════════════════

/-- Make a user VarName with given tag and index. -/
private def mkVar (tag : String) (idx : Nat) : VarName := .user s!"{tag}{idx}"

/-- Make a LowLevelExpr.varRef from tag+index. -/
private def ref (tag : String) (idx : Nat) : LowLevelExpr := .varRef (mkVar tag idx)

/-- Shorthand for .varRef of a named user variable. -/
private def vr (name : String) : LowLevelExpr := .varRef (.user name)

/-- Compose a list of Stmt into a left-nested Stmt.seq chain. -/
private def seqAll : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (seqAll rest)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: sqdmulh Butterfly (4-lane, halfSize ≥ 4)
-- ══════════════════════════════════════════════════════════════════

/-- sqdmulh Montgomery REDC butterfly as Stmt.call sequence.
    Algorithm: tw*b via sqdmulh Montgomery → canonicalize → DIT sum/diff → reduce.
    All operations unsigned after REDC canonicalization (no reinterpret needed).

    Parameters are VarName references (set up by the calling loop):
    - a, b: data pointers (int32_t*, 4 elements each)
    - tw, muTw: twiddle and precomputed mu*twiddle pointers
    - pVecS: signed p broadcast (int32x4_t, for sqdmulh)
    - pVec: unsigned p broadcast (uint32x4_t, for arithmetic)

    Produces 20 Stmt.call operations. Output: a ← sum mod p, b ← diff mod p.
    Reference: SIMDEmitter.lean:154-181. -/
def sqdmulhButterflyStmt (a b tw muTw pVecS pVec : VarName) : Stmt :=
  -- Phase 1: Load 4-lane vectors (4 ops)
  let s_la := neonCall .load4_s32 (mkVar "nv" 0) [.varRef a]
  let s_lb := neonCall .load4_s32 (mkVar "nv" 1) [.varRef b]
  let s_ltw := neonCall .load4_s32 (mkVar "nv" 2) [.varRef tw]
  let s_lmt := neonCall .load4_s32 (mkVar "nv" 3) [.varRef muTw]
  -- Phase 2: sqdmulh Montgomery REDC (4 ops) → raw ∈ (-p, p)
  let s_chi  := neonCall .sqdmulh (mkVar "nv" 4) [ref "nv" 2, ref "nv" 1]  -- high(2*tw*b)
  let s_q    := neonCall .mul_s32 (mkVar "nv" 5) [ref "nv" 1, ref "nv" 3]  -- b*mu_tw
  let s_qphi := neonCall .sqdmulh (mkVar "nv" 6) [ref "nv" 5, .varRef pVecS] -- high(2*q*p)
  let s_raw  := neonCall .hsub    (mkVar "nv" 7) [ref "nv" 4, ref "nv" 6]  -- (chi-qphi)/2
  -- Phase 3: Canonicalize raw ∈ (-p, p) → [0, p) via min trick (3 ops)
  let s_rpp := neonCall .add_u32 (mkVar "nu" 0) [ref "nv" 7, .varRef pVec] -- raw+p ∈ [0,2p)
  let s_rpm := neonCall .sub_u32 (mkVar "nu" 1) [ref "nu" 0, .varRef pVec] -- raw+p-p = raw
  let s_wb  := neonCall .min_u32 (mkVar "nu" 2) [ref "nu" 0, ref "nu" 1]   -- min → [0,p)
  -- Phase 4: DIT sum + canonicalize (3 ops)
  let s_sum  := neonCall .add_u32 (mkVar "nu" 3) [ref "nv" 0, ref "nu" 2]  -- a+wb ∈ [0,2p)
  let s_sums := neonCall .sub_u32 (mkVar "nu" 4) [ref "nu" 3, .varRef pVec] -- sum-p
  let s_sumr := neonCall .min_u32 (mkVar "nu" 5) [ref "nu" 3, ref "nu" 4]  -- min → [0,p)
  -- Phase 5: DIT diff + canonicalize (4 ops)
  let s_app  := neonCall .add_u32 (mkVar "nu" 6) [ref "nv" 0, .varRef pVec] -- a+p
  let s_diff := neonCall .sub_u32 (mkVar "nu" 7) [ref "nu" 6, ref "nu" 2]  -- (a+p)-wb ∈ (0,2p)
  let s_difs := neonCall .sub_u32 (mkVar "nu" 8) [ref "nu" 7, .varRef pVec] -- diff-p
  let s_difr := neonCall .min_u32 (mkVar "nu" 9) [ref "nu" 7, ref "nu" 8]  -- min → [0,p)
  -- Phase 6: Store (2 ops, void)
  let s_sta := neonCallVoid .store4_s32 [.varRef a, ref "nu" 5]
  let s_stb := neonCallVoid .store4_s32 [.varRef b, ref "nu" 9]
  seqAll [s_la, s_lb, s_ltw, s_lmt, s_chi, s_q, s_qphi, s_raw,
          s_rpp, s_rpm, s_wb, s_sum, s_sums, s_sumr,
          s_app, s_diff, s_difs, s_difr, s_sta, s_stb]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: hs2 Butterfly (halfSize=2, 2 groups × 2 butterflies)
-- ══════════════════════════════════════════════════════════════════

/-- hs2 butterfly (halfSize=2) as Stmt.call sequence.
    Loads 2-lane halves from two groups, combines into 4-lane vectors,
    performs sqdmulh REDC butterfly, then splits and stores back.

    Parameters:
    - dg0, dg1: pointers to data for group 0 and group 1
    - twg0, twg1: twiddle pointers for group 0 and 1
    - mtg0, mtg1: mu*twiddle pointers for group 0 and 1
    - pVecS, pVec: p broadcast vectors

    Reference: SIMDEmitter.lean:200-240. -/
def hs2ButterflyStmt (dg0 dg1 twg0 twg1 mtg0 mtg1 pVecS pVec : VarName) : Stmt :=
  -- Phase 1: Load 2-lane halves and combine (8 ops: 4 load2 + 4 combine)
  let s_alo := neonCall .load2_s32   (mkVar "nh" 0) [.varRef dg0]
  let s_ahi := neonCall .load2_s32   (mkVar "nh" 1) [.varRef dg1]
  let s_a   := neonCall .combine_s32 (mkVar "nv" 0) [ref "nh" 0, ref "nh" 1]
  -- b: offset +2 from each group
  let s_blo := neonCall .load2_s32   (mkVar "nh" 2)
    [.binOp .add (.varRef dg0) (.litInt 2)]
  let s_bhi := neonCall .load2_s32   (mkVar "nh" 3)
    [.binOp .add (.varRef dg1) (.litInt 2)]
  let s_b   := neonCall .combine_s32 (mkVar "nv" 1) [ref "nh" 2, ref "nh" 3]
  -- tw
  let s_tlo := neonCall .load2_s32   (mkVar "nh" 4) [.varRef twg0]
  let s_thi := neonCall .load2_s32   (mkVar "nh" 5) [.varRef twg1]
  let s_tw  := neonCall .combine_s32 (mkVar "nv" 2) [ref "nh" 4, ref "nh" 5]
  -- mu_tw
  let s_mlo := neonCall .load2_s32   (mkVar "nh" 6) [.varRef mtg0]
  let s_mhi := neonCall .load2_s32   (mkVar "nh" 7) [.varRef mtg1]
  let s_mt  := neonCall .combine_s32 (mkVar "nv" 3) [ref "nh" 6, ref "nh" 7]
  -- Phase 2: sqdmulh REDC (4 ops) → same as sqdmulh butterfly
  let s_chi  := neonCall .sqdmulh (mkVar "nv" 4) [ref "nv" 2, ref "nv" 1]
  let s_q    := neonCall .mul_s32 (mkVar "nv" 5) [ref "nv" 1, ref "nv" 3]
  let s_qphi := neonCall .sqdmulh (mkVar "nv" 6) [ref "nv" 5, .varRef pVecS]
  let s_raw  := neonCall .hsub    (mkVar "nv" 7) [ref "nv" 4, ref "nv" 6]
  -- Phase 3: Canonicalize + DIT sum/diff (10 ops, same as sqdmulh butterfly phases 3-5)
  let s_rpp  := neonCall .add_u32 (mkVar "nu" 0) [ref "nv" 7, .varRef pVec]
  let s_rpm  := neonCall .sub_u32 (mkVar "nu" 1) [ref "nu" 0, .varRef pVec]
  let s_wb   := neonCall .min_u32 (mkVar "nu" 2) [ref "nu" 0, ref "nu" 1]
  let s_sum  := neonCall .add_u32 (mkVar "nu" 3) [ref "nv" 0, ref "nu" 2]
  let s_sums := neonCall .sub_u32 (mkVar "nu" 4) [ref "nu" 3, .varRef pVec]
  let s_sumr := neonCall .min_u32 (mkVar "nu" 5) [ref "nu" 3, ref "nu" 4]
  let s_app  := neonCall .add_u32 (mkVar "nu" 6) [ref "nv" 0, .varRef pVec]
  let s_diff := neonCall .sub_u32 (mkVar "nu" 7) [ref "nu" 6, ref "nu" 2]
  let s_difs := neonCall .sub_u32 (mkVar "nu" 8) [ref "nu" 7, .varRef pVec]
  let s_difr := neonCall .min_u32 (mkVar "nu" 9) [ref "nu" 7, ref "nu" 8]
  -- Phase 4: Split 4-lane back to 2-lane halves and store (8 ops)
  let s_slr := neonCall .get_low_s32  (mkVar "nh" 8) [ref "nu" 5]   -- sum lo (g0)
  let s_shr := neonCall .get_high_s32 (mkVar "nh" 9) [ref "nu" 5]   -- sum hi (g1)
  let s_dlr := neonCall .get_low_s32  (mkVar "nh" 10) [ref "nu" 9]  -- diff lo (g0)
  let s_dhr := neonCall .get_high_s32 (mkVar "nh" 11) [ref "nu" 9]  -- diff hi (g1)
  let s_sag0 := neonCallVoid .store2_s32 [.varRef dg0, ref "nh" 8]
  let s_sdg0 := neonCallVoid .store2_s32
    [.binOp .add (.varRef dg0) (.litInt 2), ref "nh" 10]
  let s_sag1 := neonCallVoid .store2_s32 [.varRef dg1, ref "nh" 9]
  let s_sdg1 := neonCallVoid .store2_s32
    [.binOp .add (.varRef dg1) (.litInt 2), ref "nh" 11]
  seqAll [s_alo, s_ahi, s_a, s_blo, s_bhi, s_b,
          s_tlo, s_thi, s_tw, s_mlo, s_mhi, s_mt,
          s_chi, s_q, s_qphi, s_raw,
          s_rpp, s_rpm, s_wb, s_sum, s_sums, s_sumr,
          s_app, s_diff, s_difs, s_difr,
          s_slr, s_shr, s_dlr, s_dhr,
          s_sag0, s_sdg0, s_sag1, s_sdg1]

-- ══════════════════════════════════════════════════════════════════
-- Section 4: hs1 Butterfly (halfSize=1, 4 groups × 1 butterfly)
-- ══════════════════════════════════════════════════════════════════

/-- hs1 butterfly (halfSize=1) as Stmt.call sequence.
    Uses deinterleave load (vld2q_s32 via helper) to separate interleaved a,b data.
    Uses interleave store (vst2q_s32) to write back.

    Parameters:
    - dataPtr: pointer to 8 contiguous elements [a0,b0,a1,b1,a2,b2,a3,b3]
    - twPtr, muTwPtr: twiddle/mu*twiddle pointers (4 elements each)
    - pVecS, pVec: p broadcast vectors

    Reference: SIMDEmitter.lean:254-285. -/
def hs1ButterflyStmt (dataPtr twPtr muTwPtr pVecS pVec : VarName) : Stmt :=
  -- Phase 1: Deinterleave load (1 op via helper + 2 loads for tw/mu_tw)
  let aVec := mkVar "nv" 0
  let bVec := mkVar "nv" 1
  let s_dil := neonCallVoid .deinterleaveLoad
    [.addrOf aVec, .addrOf bVec, .varRef dataPtr]
  let s_ltw := neonCall .load4_s32 (mkVar "nv" 2) [.varRef twPtr]
  let s_lmt := neonCall .load4_s32 (mkVar "nv" 3) [.varRef muTwPtr]
  -- Phase 2: sqdmulh REDC (4 ops)
  let s_chi  := neonCall .sqdmulh (mkVar "nv" 4) [ref "nv" 2, ref "nv" 1]
  let s_q    := neonCall .mul_s32 (mkVar "nv" 5) [ref "nv" 1, ref "nv" 3]
  let s_qphi := neonCall .sqdmulh (mkVar "nv" 6) [ref "nv" 5, .varRef pVecS]
  let s_raw  := neonCall .hsub    (mkVar "nv" 7) [ref "nv" 4, ref "nv" 6]
  -- Phase 3: Canonicalize + DIT sum/diff (10 ops)
  let s_rpp  := neonCall .add_u32 (mkVar "nu" 0) [ref "nv" 7, .varRef pVec]
  let s_rpm  := neonCall .sub_u32 (mkVar "nu" 1) [ref "nu" 0, .varRef pVec]
  let s_wb   := neonCall .min_u32 (mkVar "nu" 2) [ref "nu" 0, ref "nu" 1]
  let s_sum  := neonCall .add_u32 (mkVar "nu" 3) [ref "nv" 0, ref "nu" 2]
  let s_sums := neonCall .sub_u32 (mkVar "nu" 4) [ref "nu" 3, .varRef pVec]
  let s_sumr := neonCall .min_u32 (mkVar "nu" 5) [ref "nu" 3, ref "nu" 4]
  let s_app  := neonCall .add_u32 (mkVar "nu" 6) [ref "nv" 0, .varRef pVec]
  let s_diff := neonCall .sub_u32 (mkVar "nu" 7) [ref "nu" 6, ref "nu" 2]
  let s_difs := neonCall .sub_u32 (mkVar "nu" 8) [ref "nu" 7, .varRef pVec]
  let s_difr := neonCall .min_u32 (mkVar "nu" 9) [ref "nu" 7, ref "nu" 8]
  -- Phase 4: Interleave store (1 op, void)
  let s_st := neonCallVoid .store4x2_s32
    [.varRef dataPtr, ref "nu" 5, ref "nu" 9]
  seqAll [s_dil, s_ltw, s_lmt,
          s_chi, s_q, s_qphi, s_raw,
          s_rpp, s_rpm, s_wb, s_sum, s_sums, s_sumr,
          s_app, s_diff, s_difs, s_difr,
          s_st]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Structural Properties
-- ══════════════════════════════════════════════════════════════════

/-- Count Stmt.call nodes in a Stmt tree. -/
def countCalls : Stmt → Nat
  | .call _ _ _ => 1
  | .seq s1 s2 => countCalls s1 + countCalls s2
  | _ => 0

/-- All Stmt.call fnames in a Stmt tree (for intrinsic name verification). -/
def collectCallNames : Stmt → List String
  | .call _ fname _ => [fname]
  | .seq s1 s2 => collectCallNames s1 ++ collectCallNames s2
  | _ => []

/-- Check that all call names in a Stmt are known NeonIntrinsics. -/
def allCallsKnown (s : Stmt) : Bool :=
  (collectCallNames s).all fun name => (NeonIntrinsic.fromCName name).isSome

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

private def testA := VarName.user "a_ptr"
private def testB := VarName.user "b_ptr"
private def testTw := VarName.user "tw_ptr"
private def testMuTw := VarName.user "mu_tw_ptr"
private def testPVecS := VarName.user "p_vec_s"
private def testPVec := VarName.user "p_vec"

/-- sqdmulh butterfly produces 20 calls. -/
example : countCalls (sqdmulhButterflyStmt testA testB testTw testMuTw testPVecS testPVec)
    = 20 := rfl

/-- sqdmulh butterfly uses only known intrinsics. -/
example : allCallsKnown (sqdmulhButterflyStmt testA testB testTw testMuTw testPVecS testPVec)
    = true := rfl

/-- sqdmulh butterfly produces non-empty C code via simdStmtToC. -/
example : (simdStmtToC 1 (sqdmulhButterflyStmt testA testB testTw testMuTw testPVecS testPVec)).length > 100 := by native_decide

/-- hs1 butterfly uses only known intrinsics. -/
example : allCallsKnown (hs1ButterflyStmt testA testTw testMuTw testPVecS testPVec)
    = true := rfl

/-- hs1 butterfly produces 18 calls. -/
example : countCalls (hs1ButterflyStmt testA testTw testMuTw testPVecS testPVec)
    = 18 := rfl

private def dg0 := VarName.user "data_g0"
private def dg1 := VarName.user "data_g1"
private def tg0 := VarName.user "tw_g0"
private def tg1 := VarName.user "tw_g1"
private def mg0 := VarName.user "mu_tw_g0"
private def mg1 := VarName.user "mu_tw_g1"

/-- hs2 butterfly uses only known intrinsics. -/
example : allCallsKnown (hs2ButterflyStmt dg0 dg1 tg0 tg1 mg0 mg1 testPVecS testPVec)
    = true := rfl

/-- hs2 butterfly produces 34 calls. -/
example : countCalls (hs2ButterflyStmt dg0 dg1 tg0 tg1 mg0 mg1 testPVecS testPVec)
    = 34 := rfl

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDButterfly
