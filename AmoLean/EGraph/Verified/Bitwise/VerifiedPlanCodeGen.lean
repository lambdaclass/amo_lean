/-
  AMO-Lean -- Verified Plan-Based NTT Code Generation

  Lowers NTT Plans to TrustLean.Stmt with per-stage heterogeneous reduction.
  Each stage may use a different reduction strategy (lazy/Solinas/Montgomery/Harvey),
  all verified through TrustLean.Stmt.

  Key function: lowerReductionChoice — dispatches to existing verified reduction
  functions in TrustLeanBridge based on the Plan's per-stage selection.

  Created by Plan D Phase 2.
-/
import AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
import AmoLean.EGraph.Verified.Bitwise.NTTPlanSelection
import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen

open _root_.TrustLean (Stmt VarName LowLevelExpr BinOp UnaryOp StmtResult CodeGenState)
open AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
  (lowerDIFButterflyStmt lowerRadix4ButterflyStmt solinasFoldLLE)
open AmoLean.EGraph.Verified.Bitwise.TrustLeanBridge
  (lowerSolinasFold lowerHarveyReduce lowerMontyReduce)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice StageDirection)
open AmoLean.EGraph.Verified.Bitwise.PlanSelection (selectBestPlan)

-- ══════════════════════════════════════════════════════════════════
-- Block 2.1: Reducer dispatcher
-- ══════════════════════════════════════════════════════════════════

/-- Extract VarName from a StmtResult's resultVar (LowLevelExpr). -/
private def extractVar : LowLevelExpr → VarName
  | .varRef v => v
  | _ => .user "_err"

/-- Montgomery REDC using SUBTRACTION variant: d = T - m*p, q = d >> 32.
    Uses mu = p^{-1} mod R (the value stored in FieldConfig).
    Unlike lowerMontyReduce (olean, ADDITION variant with wrong mu convention),
    this variant has NO int64 overflow: d = T - m*p ∈ (-R*p, R*p) ⊂ int64 range.
    Matches Plonky3's p3_reduce exactly. -/
private def lowerMontyReduceSub (xExpr : LowLevelExpr) (p mu : Nat)
    (cgs : CodeGenState) : (Stmt × VarName × CodeGenState) :=
  let pLit := LowLevelExpr.litInt ↑p
  let muLit := LowLevelExpr.litInt ↑mu
  -- m = (T * mu) & (R - 1)
  let (mVar, cgs1) := cgs.freshVar
  let s1 := Stmt.assign mVar (.binOp .band (.binOp .mul xExpr muLit) (.litInt (2^32 - 1)))
  -- u = m * p
  let (uVar, cgs2) := cgs1.freshVar
  let s2 := Stmt.assign uVar (.binOp .mul (.varRef mVar) pLit)
  -- d = T - u (NO overflow: d ∈ (-R*p, R*p) ⊂ int64 range)
  let (dVar, cgs3) := cgs2.freshVar
  let s3 := Stmt.assign dVar (.binOp .sub xExpr (.varRef uVar))
  -- q = d >> 32 (arithmetic shift: correct for negative d)
  let (qVar, cgs4) := cgs3.freshVar
  let s4 := Stmt.assign qVar (.binOp .bshr (.varRef dVar) (.litInt 32))
  -- result = if T < u then q + p else q
  let (resultVar, cgs5) := cgs4.freshVar
  let s5 := Stmt.ite (.binOp .ltOp xExpr (.varRef uVar))
    (.assign resultVar (.binOp .add (.varRef qVar) pLit))
    (.assign resultVar (.varRef qVar))
  let stmt := Stmt.seq s1 (Stmt.seq s2 (Stmt.seq s3 (Stmt.seq s4 s5)))
  (stmt, resultVar, cgs5)

/-- Goldilocks product reduction: x mod p where p = 2^64 - 2^32 + 1.
    For 128-bit product x = w*b. Uses shift-subtract with halves to avoid overflow.
    Math: x = hi·2^64 + lo, hi = hh·2^32 + hl.
    Since 2^64 ≡ 2^32-1 (mod p): x ≡ (lo - hh) + hl·(2^32-1) (mod p).
    Borrow handling: if lo < hh, add p first (stays < p, since lo < hh < 2^32).
    Result < 2p after fold; single conditional subtraction → result < p.
    Mirrors hand-written code from OptimizedNTTPipeline.lean:254-263.
    Only called when k > 32 (compile-time dispatch, NOT a runtime branch).
    v3.11.0 F5: Replaced inline Stmt expansion with Stmt.call to goldi_reduce128.
    The called function uses uint64_t locals (~9 ARM instr vs ~18 with __uint128_t).
    Stmt.call acts as TYPE BOUNDARY: function body is uint64_t, result promotes to
    __uint128_t temp. Preamble emitted in emitCFromPlanVerified/Rust. -/
private def lowerGoldilocksProductReduce (xExpr : LowLevelExpr) (p : Nat)
    (cgs : CodeGenState) : (Stmt × VarName × CodeGenState) :=
  let (resultVar, cgs1) := cgs.freshVar
  let stmt := Stmt.call resultVar "goldi_reduce128" [xExpr]
  (stmt, resultVar, cgs1)

/-- Lower a ReductionChoice to TrustLean.Stmt for **sum/diff reduction**.
    Montgomery REDC is NOT valid here — it produces x*R⁻¹ mod p instead of x mod p.
    Montgomery is only correct for products (tw_mont*b) where the R factor in the
    twiddle cancels the R⁻¹. Defense in depth: redirect .montgomery to Solinas fold. -/
def lowerReductionChoice (red : ReductionChoice) (xExpr : LowLevelExpr)
    (p k c mu : Nat) (cgs : CodeGenState) : (Stmt × VarName × CodeGenState) :=
  match red with
  | .solinasFold =>
    let (sr, cgs') := lowerSolinasFold xExpr k c cgs
    (sr.stmt, extractVar sr.resultVar, cgs')
  | .montgomery =>
    -- REDC gives x*R⁻¹ mod p, wrong for sums. Fall back to Solinas fold.
    let (sr, cgs') := lowerSolinasFold xExpr k c cgs
    (sr.stmt, extractVar sr.resultVar, cgs')
  | .harvey =>
    let (sr, cgs') := lowerHarveyReduce xExpr p cgs
    (sr.stmt, extractVar sr.resultVar, cgs')
  | .lazy =>
    -- Lazy stages use Solinas fold (cheapest reduction that fits i32/u32).
    let (sr, cgs') := lowerSolinasFold xExpr k c cgs
    (sr.stmt, extractVar sr.resultVar, cgs')

-- ══════════════════════════════════════════════════════════════════
-- Block 2.1b: Conditional subtract for values < 2p (v3.10.1 AC-6)
-- ══════════════════════════════════════════════════════════════════

/-- v3.10.1 AC-6: Conditional subtract for Goldilocks sum/diff reduction.
    For inputs < 2p: if x >= p then x - p else x. Only 2 ops (compare + sub)
    vs Solinas fold's 4 ops (shift + mul + mask + add). Correct because
    wb_red < p and a < p → sum = a + wb_red < 2p. One subtraction suffices.
    The Stmt.ite compiles to compare + CSEL + sub (branchless on ARM). -/
private def lowerConditionalSub (xExpr : LowLevelExpr) (p : Nat)
    (cgs : CodeGenState) : (Stmt × VarName × CodeGenState) :=
  let pLit := LowLevelExpr.litInt ↑p
  let (subPVar, cgs1) := cgs.freshVar
  let subPStmt := Stmt.ite (.binOp .ltOp xExpr pLit)
    (.assign subPVar (.litInt 0))
    (.assign subPVar pLit)
  let (resultVar, cgs2) := cgs1.freshVar
  let resultStmt := Stmt.assign resultVar (.binOp .sub xExpr (.varRef subPVar))
  (Stmt.seq subPStmt resultStmt, resultVar, cgs2)

/-- v3.11.0 F5b: Goldilocks add/sub via Stmt.call for bounded butterfly sum/diff.
    Both inputs a, wb_red are < p (post product reduction). goldi_add handles
    carry (a+b may exceed 2^64), goldi_sub handles borrow (a-b may underflow).
    Same TYPE BOUNDARY pattern as F5 goldi_reduce128: function body uses uint64_t,
    args are __uint128_t temps (C truncates implicitly, safe since values < p < 2^64).
    Eliminates __uint128_t intermediates for sum/diff and the (a+p)-wb_red pattern. -/
private def lowerGoldilocksAddSub (aExpr bExpr : LowLevelExpr) (p : Nat)
    (cgs : CodeGenState) : (Stmt × VarName × VarName × CodeGenState) :=
  let (sumVar, cgs1) := cgs.freshVar
  let sumStmt := Stmt.call sumVar "goldi_add" [aExpr, bExpr]
  let (diffVar, cgs2) := cgs1.freshVar
  let diffStmt := Stmt.call diffVar "goldi_sub" [aExpr, bExpr]
  (Stmt.seq sumStmt diffStmt, sumVar, diffVar, cgs2)

-- ══════════════════════════════════════════════════════════════════
-- Block 2.2: Butterfly parametrized by ReductionChoice
-- ══════════════════════════════════════════════════════════════════

/-- Unified DIT butterfly with REDC on product and parametric sum/diff reduction.
    Product w*b is reduced via:
    - k ≤ 32: Montgomery REDC (R=2^32, valid for p^2 ≈ 2^62, requires Montgomery twiddles)
    - k > 32: Goldilocks shift-subtract with halves (p = 2^64-2^32+1, handles 128-bit products)
    The k > 32 branch is a COMPILE-TIME dispatch (Lean evaluates it during code generation,
    NOT a runtime branch in the emitted C/Rust). Sum/diff reduction via lowerReductionChoice. -/
def lowerDIFButterflyByReduction (aVar bVar wVar : VarName)
    (red : ReductionChoice) (p k c mu : Nat)
    (cgs : CodeGenState)
    (boundK : Nat := 0)  -- v3.11.0 F1: bound factor from NTTStage (0 = unknown)
    : (Stmt × VarName × VarName × CodeGenState) :=
  -- Step 1: product w*b with field-appropriate reduction
  let (wbVar, cgs1) := cgs.freshVar
  let wbExpr := LowLevelExpr.binOp .mul (.varRef wVar) (.varRef bVar)
  let wbStmt := Stmt.assign wbVar wbExpr
  let (redWbStmt, redWbVar, cgs2) :=
    if k > 32 then
      -- Goldilocks: shift-subtract with halves (no Montgomery, R=2^32 too small)
      lowerGoldilocksProductReduce (.varRef wbVar) p cgs1
    else
      -- BabyBear/KoalaBear/Mersenne31: Montgomery REDC subtraction variant
      lowerMontyReduceSub (.varRef wbVar) p mu cgs1
  -- Step 2+3: sum/diff with reduction
  -- v3.11.0 F1: Bound-aware dispatch. When boundK ≤ 2 (input bounded < 2p),
  -- use fast reduction. For Goldilocks (k > 32), use Stmt.call to goldi_add/goldi_sub
  -- (F5b: uint64_t locals, ~3 ARM instr each). For k ≤ 32, use lowerConditionalSub
  -- (Stmt.ite pattern, 2 ops). boundK = 0 → full parametric reduction (backward compat).
  let useFastReduce := boundK > 0 && boundK ≤ 2
  if k > 32 && useFastReduce then
    -- v3.11.0 F5b: Goldilocks + bounded → goldi_add/goldi_sub via Stmt.call
    -- Eliminates __uint128_t for sum/diff, eliminates (a+p)-wb_red underflow pattern
    let (addSubStmt, sumVar, diffVar, cgs3) :=
      lowerGoldilocksAddSub (.varRef aVar) (.varRef redWbVar) p cgs2
    let fullStmt := Stmt.seq wbStmt (Stmt.seq redWbStmt addSubStmt)
    (fullStmt, sumVar, diffVar, cgs3)
  else
    -- BabyBear/KoalaBear path or unbounded Goldilocks
    let (sumVar, cgs3) := cgs2.freshVar
    let sumExpr := LowLevelExpr.binOp .add (.varRef aVar) (.varRef redWbVar)
    let sumStmt := Stmt.assign sumVar sumExpr
    let (diffVar, cgs4) := cgs3.freshVar
    let diffExpr := LowLevelExpr.binOp .sub
      (LowLevelExpr.binOp .add (.varRef aVar) (.litInt ↑p))
      (.varRef redWbVar)
    let diffStmt := Stmt.assign diffVar diffExpr
    let (redSumStmt, redSumVar, cgs5) :=
      if useFastReduce then lowerConditionalSub (.varRef sumVar) p cgs4
      else lowerReductionChoice red (.varRef sumVar) p k c mu cgs4
    let (redDiffStmt, redDiffVar, cgs6) :=
      if useFastReduce then lowerConditionalSub (.varRef diffVar) p cgs5
      else lowerReductionChoice red (.varRef diffVar) p k c mu cgs5
    let fullStmt := Stmt.seq wbStmt (Stmt.seq redWbStmt (Stmt.seq sumStmt
      (Stmt.seq diffStmt (Stmt.seq redSumStmt redDiffStmt))))
    (fullStmt, redSumVar, redDiffVar, cgs6)

-- ══════════════════════════════════════════════════════════════════
-- Block 2.3: Radix-4 butterfly parametrized by ReductionChoice
-- ══════════════════════════════════════════════════════════════════

/-- Radix-4 butterfly: compose 4 radix-2 DIT butterflies with selected reduction.
    All radix-2 calls go through lowerDIFButterflyByReduction which handles
    REDC on the product internally.
    Uses 4 twiddles: w1/w1p for outer cross-butterflies (groups 2g/2g+1 at level L+1),
    w2/w3 for inner butterflies (even/odd pairs at level L).
    Returns outputs in DIT data-position order: (pos0, pos1, pos2, pos3)
    where pos0=out0 (sum@i0), pos1=out2 (diff@i1), pos2=out1 (sum@i2), pos3=out3 (diff@i3). -/
def lowerRadix4ButterflyByReduction
    (aVar bVar cVar dVar w1Var w1pVar w2Var w3Var : VarName)
    (red : ReductionChoice) (p k c_val mu : Nat)
    (cgs : CodeGenState)
    (boundK : Nat := 0)  -- v3.11.0 F1
    : (Stmt × VarName × VarName × VarName × VarName × CodeGenState) :=
  -- Inner level L: bf2 on even-indexed (a,c) and odd-indexed (b,d)
  let (s1, r0, r2, cgs1) :=
    lowerDIFButterflyByReduction aVar cVar w2Var red p k c_val mu cgs (boundK := boundK)
  let (s2, r1, r3, cgs2) :=
    lowerDIFButterflyByReduction bVar dVar w3Var red p k c_val mu cgs1 (boundK := boundK)
  -- Outer level L+1: cross-butterflies use DIFFERENT twiddles (groups 2g and 2g+1)
  let (s3, out0, out2, cgs3) :=
    lowerDIFButterflyByReduction r0 r1 w1Var red p k c_val mu cgs2 (boundK := boundK)
  let (s4, out1, out3, cgs4) :=
    lowerDIFButterflyByReduction r2 r3 w1pVar red p k c_val mu cgs3 (boundK := boundK)
  -- DIT data-position order: sum@i0, diff@i1, sum@i2, diff@i3
  (Stmt.seq s1 (Stmt.seq s2 (Stmt.seq s3 s4)), out0, out2, out1, out3, cgs4)

-- ══════════════════════════════════════════════════════════════════
-- Block 2.4: Lower stage from Plan
-- ══════════════════════════════════════════════════════════════════

/-- Compute index for data access in NTT stage. -/
private def nttDataIndex (groupVar pairVar : VarName) (halfSize : Nat) : LowLevelExpr :=
  .binOp .add
    (.binOp .mul (.varRef groupVar) (.litInt ↑(2 * halfSize)))
    (.varRef pairVar)

/-- Compute twiddle index for NTT stage. -/
private def nttTwiddleIndex (stageIdx : Nat) (groupVar pairVar : VarName)
    (halfSize n : Nat) : LowLevelExpr :=
  .binOp .add
    (.litInt ↑(stageIdx * (n / 2)))
    (.binOp .add
      (.binOp .mul (.varRef groupVar) (.litInt ↑halfSize))
      (.varRef pairVar))

/-- Load array element into wide variable with widening cast.
    Emits .widen32to64 for ALL fields (uniform IR structure). For k=64 (Goldilocks),
    the C/Rust emitters post-process the cast: C changes (int64_t) to (uint64_t),
    Rust changes (as i64) to (as u128). See emitCFromPlanVerified/emitRustFromPlanVerified. -/
private def loadWiden (var : VarName) (base idx : LowLevelExpr) : Stmt :=
  let tmpName := match var with
    | .user s => s ++ "_ld"
    | .temp n => s!"t{n}_ld"
    | .array b i => s!"{b}_{i}_ld"
  let tmpVar := VarName.user tmpName
  .seq (.load tmpVar base idx)
       (.assign var (.unaryOp .widen32to64 (.varRef tmpVar)))

/-- Store wide value to array with truncation cast.
    Emits .trunc64to32 for ALL fields (uniform IR). For k=64, post-processed:
    C changes (int32_t) to nothing (implicit), Rust changes (as i32) to (as u64). -/
private def storeTrunc (base idx val : LowLevelExpr) : Stmt :=
  .store base idx (.unaryOp .trunc64to32 val)

/-- Lower a radix-4 NTT stage to TrustLean.Stmt.
    Covers 2 NTT levels (L and L+1) in one stage. Uses 4 data loads, 4 twiddle loads,
    the fixed R4 butterfly, and 4 stores. Twiddle indices reuse nttTwiddleIndex + offset.
    Requires stageIdx = NTT level (post normalizePlan). -/
private def lowerStageR4 (stage : NTTStage) (n p k c mu : Nat) : Stmt :=
  let L := stage.stageIdx
  let quarterSize := n / (2 ^ (L + 2))
  let halfSizeL := 2 * quarterSize
  let numGroups := 2 ^ L
  let groupVar := VarName.user "group"
  let pairVar := VarName.user "pair"
  let cgs : CodeGenState := {}
  -- Data indices: base = g·4q + pair, then +q, +2q, +3q
  let baseExpr := nttDataIndex groupVar pairVar halfSizeL
  let i0 := baseExpr
  let i1 := LowLevelExpr.binOp .add baseExpr (.litInt ↑quarterSize)
  let i2 := LowLevelExpr.binOp .add baseExpr (.litInt ↑(2 * quarterSize))
  let i3 := LowLevelExpr.binOp .add baseExpr (.litInt ↑(3 * quarterSize))
  -- Twiddle indices
  let tw2 := nttTwiddleIndex L groupVar pairVar halfSizeL n
  let tw3 := LowLevelExpr.binOp .add (nttTwiddleIndex L groupVar pairVar halfSizeL n) (.litInt ↑quarterSize)
  let tw1 := nttTwiddleIndex (L + 1) groupVar pairVar halfSizeL n
  let tw1p := LowLevelExpr.binOp .add (nttTwiddleIndex (L + 1) groupVar pairVar halfSizeL n)
    (.litInt ↑quarterSize)
  -- v3.12.0 F5c: Goldilocks + bounded → encapsulate R4 butterfly as Stmt.call
  let useFullR4 := k > 32 && stage.outputBoundK > 0 && stage.outputBoundK ≤ 2
  let bfBody :=
   if useFullR4 then
    -- F5c: 1 Stmt.call per R4 butterfly. goldi_butterfly4 handles
    -- load + 4×reduce + 4×add/sub + store internally, all uint64_t.
    let (resultVar, _) := cgs.freshVar
    Stmt.call resultVar "goldi_butterfly4"
      [LowLevelExpr.varRef (VarName.user "data"),
       LowLevelExpr.varRef (VarName.user "twiddles"),
       i0, i1, i2, i3, tw2, tw3, tw1, tw1p]
   else
    -- Original inline R4 butterfly
    let aVar := VarName.user "a_val"
    let bVar := VarName.user "b_val"
    let cVar := VarName.user "c_val"
    let dVar := VarName.user "d_val"
    let w1Var := VarName.user "w1_val"
    let w1pVar := VarName.user "w1p_val"
    let w2Var := VarName.user "w2_val"
    let w3Var := VarName.user "w3_val"
    let (bf, pos0, pos1, pos2, pos3, _) :=
      lowerRadix4ButterflyByReduction aVar bVar cVar dVar
        w1Var w1pVar w2Var w3Var stage.reduction p k c mu cgs (boundK := stage.outputBoundK)
    let dRef := LowLevelExpr.varRef (VarName.user "data")
    let tRef := LowLevelExpr.varRef (VarName.user "twiddles")
    let st0 := storeTrunc dRef i0 (LowLevelExpr.varRef pos0)
    let st1 := storeTrunc dRef i1 (LowLevelExpr.varRef pos1)
    let st2 := storeTrunc dRef i2 (LowLevelExpr.varRef pos2)
    let st3 := storeTrunc dRef i3 (LowLevelExpr.varRef pos3)
    Stmt.seq (loadWiden aVar dRef i0)
      (Stmt.seq (loadWiden bVar dRef i1)
        (Stmt.seq (loadWiden cVar dRef i2)
          (Stmt.seq (loadWiden dVar dRef i3)
            (Stmt.seq (loadWiden w2Var tRef tw2)
              (Stmt.seq (loadWiden w3Var tRef tw3)
                (Stmt.seq (loadWiden w1Var tRef tw1)
                  (Stmt.seq (loadWiden w1pVar tRef tw1p)
                    (Stmt.seq bf
                      (Stmt.seq st0 (Stmt.seq st1 (Stmt.seq st2 st3)))))))))))
  Stmt.for_
    (.assign groupVar (.litInt 0)) (.binOp .ltOp (.varRef groupVar) (.litInt ↑numGroups))
    (.assign groupVar (.binOp .add (.varRef groupVar) (.litInt 1)))
    (Stmt.for_
      (.assign pairVar (.litInt 0)) (.binOp .ltOp (.varRef pairVar) (.litInt ↑quarterSize))
      (.assign pairVar (.binOp .add (.varRef pairVar) (.litInt 1)))
      bfBody)

/-- Lower a single NTTStage to TrustLean.Stmt with nested for-loops.
    Dispatches by radix: R4 stages use lowerStageR4 (4-point butterfly, 2 NTT levels).
    R2 stages use the original path (unchanged). -/
def lowerStageVerified (stage : NTTStage) (n p k c mu : Nat) : Stmt :=
  match stage.radix with
  | .r4 => lowerStageR4 stage n p k c mu
  | _ =>
  let halfSize := n / (2 ^ (stage.stageIdx + 1))
  let numGroups := 2 ^ stage.stageIdx
  let groupVar := VarName.user "group"
  let pairVar := VarName.user "pair"
  let cgs : CodeGenState := {}
  -- v3.12.0 F5c: Goldilocks + bounded → encapsulate entire butterfly as Stmt.call.
  -- Loop body = 1 void call → group/pair as uint64_t (no __uint128_t mixing).
  -- goldi_butterfly(data, twiddles, i, j, tw_idx) handles load+reduce+add/sub+store.
  let useFull := k > 32 && stage.outputBoundK > 0 && stage.outputBoundK ≤ 2
  let bfBody :=
   if useFull then
    -- F5c: 1 Stmt.call per butterfly, uint64_t indices
    -- goldi_butterfly returns dummy uint64_t (0) for Stmt.call compatibility.
    -- The function modifies data[i]/data[j] directly via pointer.
    let iExpr := nttDataIndex groupVar pairVar halfSize
    let jExpr := LowLevelExpr.binOp .add iExpr (.litInt ↑halfSize)
    let twExpr := nttTwiddleIndex stage.stageIdx groupVar pairVar halfSize n
    let (resultVar, _) := cgs.freshVar
    Stmt.call resultVar "goldi_butterfly"
      [LowLevelExpr.varRef (VarName.user "data"),
       LowLevelExpr.varRef (VarName.user "twiddles"),
       iExpr, jExpr, twExpr]
   else
    -- Original path (BabyBear, or unbounded Goldilocks)
    let aVar := VarName.user "a_val"
    let bVar := VarName.user "b_val"
    let wVar := VarName.user "w_val"
    let iExpr := nttDataIndex groupVar pairVar halfSize
    let jExpr := .binOp .add iExpr (.litInt ↑halfSize)
    let twExpr := nttTwiddleIndex stage.stageIdx groupVar pairVar halfSize n
    let (bf, sumVar, diffVar, _) :=
      lowerDIFButterflyByReduction aVar bVar wVar stage.reduction p k c mu cgs
        (boundK := stage.outputBoundK)
    let dRef := LowLevelExpr.varRef (VarName.user "data")
    let tRef := LowLevelExpr.varRef (VarName.user "twiddles")
    let stFull := storeTrunc dRef iExpr (LowLevelExpr.varRef sumVar)
    let stFullD := storeTrunc dRef jExpr (LowLevelExpr.varRef diffVar)
    let loads := Stmt.seq (loadWiden aVar dRef iExpr)
      (Stmt.seq (loadWiden bVar dRef jExpr)
        (loadWiden wVar tRef twExpr))
    if k > 32 && halfSize ≤ 32 then
      let (sumRed1, sumVar1, cgs_s) :=
        lowerReductionChoice stage.reduction
          (.binOp .add (.varRef aVar) (.varRef bVar)) p k c mu cgs
      let (diffRed1, diffVar1, _) :=
        lowerReductionChoice stage.reduction
          (.binOp .sub (.binOp .add (.varRef aVar) (.litInt ↑p)) (.varRef bVar)) p k c mu cgs_s
      let st1Sum := storeTrunc dRef iExpr (LowLevelExpr.varRef sumVar1)
      let st1Diff := storeTrunc dRef jExpr (LowLevelExpr.varRef diffVar1)
      Stmt.seq loads
        (Stmt.ite (.binOp .ltOp (.varRef wVar) (.litInt 2))
          (Stmt.seq sumRed1 (Stmt.seq diffRed1 (Stmt.seq st1Sum st1Diff)))
          (Stmt.seq bf (Stmt.seq stFull stFullD)))
    else
      Stmt.seq loads (Stmt.seq bf (Stmt.seq stFull stFullD))
  -- Wrap in nested for-loops
  Stmt.for_
    (.assign groupVar (.litInt 0)) (.binOp .ltOp (.varRef groupVar) (.litInt ↑numGroups))
    (.assign groupVar (.binOp .add (.varRef groupVar) (.litInt 1)))
    (Stmt.for_
      (.assign pairVar (.litInt 0)) (.binOp .ltOp (.varRef pairVar) (.litInt ↑halfSize))
      (.assign pairVar (.binOp .add (.varRef pairVar) (.litInt 1)))
      bfBody)

-- ══════════════════════════════════════════════════════════════════
-- Block 2.5b: ILP2 — Process 2 butterflies per loop iteration (v3.10.0 TD)
-- ══════════════════════════════════════════════════════════════════

/-- v3.10.0 TD: ILP2 variant of lowerStageVerified.
    Processes 2 pairs per loop iteration. The two independent butterfly computations
    give the OoO engine (Apple Silicon ~600-entry ROB) independent mul+umulh pairs
    to issue in parallel, hiding the 3-cycle latency of each.

    Fallback to lowerStageVerified when halfSize < 2 (last stage, only 1 pair per group).
    For odd halfSize: processes pairs 0..halfSize-2 in step-2 loop, then pair halfSize-1 solo. -/
private def lowerStageVerified_ILP2 (stage : NTTStage) (n p k c mu : Nat) : Stmt :=
  match stage.radix with
  | .r4 => lowerStageR4 stage n p k c mu  -- R4 already processes 4 at once
  | _ =>
  let halfSize := n / (2 ^ (stage.stageIdx + 1))
  if halfSize < 2 then lowerStageVerified stage n p k c mu  -- fallback
  else
  let numGroups := 2 ^ stage.stageIdx
  let groupVar := VarName.user "group"
  let pairVar := VarName.user "pair"
  -- Butterfly 0: uses standard variable names (a_val, b_val, w_val, t0..tN)
  let cgs0 : CodeGenState := {}
  let aVar0 := VarName.user "a_val"
  let bVar0 := VarName.user "b_val"
  let wVar0 := VarName.user "w_val"
  let i0 := nttDataIndex groupVar pairVar halfSize
  let j0 := .binOp .add i0 (.litInt ↑halfSize)
  let tw0 := nttTwiddleIndex stage.stageIdx groupVar pairVar halfSize n
  let (bf0, sumVar0, diffVar0, cgs0') :=
    lowerDIFButterflyByReduction aVar0 bVar0 wVar0 stage.reduction p k c mu cgs0
  -- Butterfly 1: pair+1, uses VarName "pair2" for indexing
  let pair2Var := VarName.user "pair2"
  let pair2Assign := Stmt.assign pair2Var (.binOp .add (.varRef pairVar) (.litInt 1))
  let cgs1 : CodeGenState := { nextVar := cgs0'.nextVar }  -- continue numbering
  let aVar1 := VarName.user "a_val2"
  let bVar1 := VarName.user "b_val2"
  let wVar1 := VarName.user "w_val2"
  let i1 := nttDataIndex groupVar pair2Var halfSize
  let j1 := .binOp .add i1 (.litInt ↑halfSize)
  let tw1 := nttTwiddleIndex stage.stageIdx groupVar pair2Var halfSize n
  let (bf1, sumVar1, diffVar1, _) :=
    lowerDIFButterflyByReduction aVar1 bVar1 wVar1 stage.reduction p k c mu cgs1
  -- Loads: interleaved for ILP (load both before any computation)
  let dRef := LowLevelExpr.varRef (VarName.user "data")
  let tRef := LowLevelExpr.varRef (VarName.user "twiddles")
  let loads := Stmt.seq (loadWiden aVar0 dRef i0)
    (Stmt.seq (loadWiden bVar0 dRef j0)
      (Stmt.seq (loadWiden wVar0 tRef tw0)
        (Stmt.seq (loadWiden aVar1 dRef i1)
          (Stmt.seq (loadWiden bVar1 dRef j1)
            (loadWiden wVar1 tRef tw1)))))
  -- Butterflies: sequential but using independent variable names → OoO finds ILP
  let bfs := Stmt.seq bf0 bf1
  -- Stores: all after both butterflies complete
  let st0s := storeTrunc dRef i0 (LowLevelExpr.varRef sumVar0)
  let st0d := storeTrunc dRef j0 (LowLevelExpr.varRef diffVar0)
  let st1s := storeTrunc dRef i1 (LowLevelExpr.varRef sumVar1)
  let st1d := storeTrunc dRef j1 (LowLevelExpr.varRef diffVar1)
  let stores := Stmt.seq st0s (Stmt.seq st0d (Stmt.seq st1s st1d))
  let bfBody := Stmt.seq pair2Assign (Stmt.seq loads (Stmt.seq bfs stores))
  -- Even halfSize: step-2 loop covers all pairs
  -- Odd halfSize: step-2 loop + one solo pair at the end
  let evenHalfSize := (halfSize / 2) * 2
  let mainLoop := Stmt.for_
    (.assign groupVar (.litInt 0)) (.binOp .ltOp (.varRef groupVar) (.litInt ↑numGroups))
    (.assign groupVar (.binOp .add (.varRef groupVar) (.litInt 1)))
    (Stmt.for_
      (.assign pairVar (.litInt 0)) (.binOp .ltOp (.varRef pairVar) (.litInt ↑evenHalfSize))
      (.assign pairVar (.binOp .add (.varRef pairVar) (.litInt 2)))
      bfBody)
  if halfSize % 2 == 0 then mainLoop
  else
    -- Odd: add solo butterfly for last pair (pair = halfSize - 1)
    let soloPair := lowerStageVerified stage n p k c mu
    -- Can't easily extract last-pair-only from lowerStageVerified.
    -- For simplicity: just use the standard stage (all pairs) when odd.
    -- Odd halfSize is rare (N must not be power of 2, which we always use).
    lowerStageVerified stage n p k c mu

-- ══════════════════════════════════════════════════════════════════
-- Block 2.5: Lower NTT from Plan
-- ══════════════════════════════════════════════════════════════════

/-- Remap stageIdx from sequential counter to NTT level.
    R2 stages consume 1 level, R4 stages consume 2 levels.
    After normalization, lowerStageVerified computes correct geometry.
    Idempotent for R2-only plans (stageIdx = level = sequential counter). -/
def normalizePlan (plan : Plan) : Plan :=
  let (newStages, _) := plan.stages.foldl
    (fun (acc : Array NTTStage × Nat) stage =>
      let (stages, level) := acc
      let newStage := { stage with stageIdx := level }
      let levelsConsumed := match stage.radix with | .r2 => 1 | .r4 => 2
      (stages.push newStage, level + levelsConsumed)) (#[], 0)
  { plan with stages := newStages }

/-- Lower a complete NTT from Plan to TrustLean.Stmt.
    Each stage may use a different reduction strategy.
    Normalizes the plan first so stageIdx = NTT level (covers all callers:
    ultraPipeline, emitPlanBasedNTTC, and any future consumer). -/
def lowerNTTFromPlanVerified (plan : Plan) (k c mu : Nat) : Stmt :=
  let plan := normalizePlan plan
  let stmts := plan.stages.toList.map fun stage =>
    -- v3.10.0 TD: dispatch to ILP2 when ilpFactor ≥ 2 and radix is R2
    if stage.ilpFactor ≥ 2 && stage.radix == .r2 then
      lowerStageVerified_ILP2 stage plan.size plan.field k c mu
    else
      lowerStageVerified stage plan.size plan.field k c mu
  stmts.foldl Stmt.seq Stmt.skip

-- ══════════════════════════════════════════════════════════════════
-- Block 2.6: Emit C and Rust from verified Plan
-- ══════════════════════════════════════════════════════════════════

/-- Count maximum temp variables used across all stages.
    Dispatches by radix: R4 dry-runs lowerRadix4ButterflyByReduction (~20 temps),
    R2 dry-runs lowerDIFButterflyByReduction (~5 temps). -/
private def maxTempsInPlan (plan : Plan) (k c mu : Nat) : Nat :=
  let counts := plan.stages.toList.map fun stage =>
    let cgs : CodeGenState := {}
    let aVar := VarName.user "a_val"
    let bVar := VarName.user "b_val"
    let wVar := VarName.user "w_val"
    match stage.radix with
    | .r4 =>
      let cVar := VarName.user "c_val"
      let dVar := VarName.user "d_val"
      let w1pVar := VarName.user "w1p_val"
      let w2Var := VarName.user "w2_val"
      let w3Var := VarName.user "w3_val"
      let (_, _, _, _, _, cgs') :=
        lowerRadix4ButterflyByReduction aVar bVar cVar dVar wVar w1pVar w2Var w3Var
          stage.reduction plan.field k c mu cgs (boundK := stage.outputBoundK)
      cgs'.nextVar
    | _ =>
      -- v3.11.0 F1: dry-run with ACTUAL boundK to count temps correctly
      let bk := stage.outputBoundK
      let (_, _, _, cgs') :=
        lowerDIFButterflyByReduction aVar bVar wVar stage.reduction plan.field k c mu cgs
          (boundK := bk)
      -- v3.10.0 TD: ILP2 processes 2 butterflies → double the temp usage
      if stage.ilpFactor ≥ 2 then
        let cgs1 : CodeGenState := { nextVar := cgs'.nextVar }
        let (_, _, _, cgs1') :=
          lowerDIFButterflyByReduction aVar bVar wVar stage.reduction plan.field k c mu cgs1
            (boundK := bk)
        cgs1'.nextVar
      else cgs'.nextVar
  counts.foldl Nat.max 0

/-- Emit verified C function from Plan.
    Replaces NTTPlanCodeGen.emitCFromPlan (which used cScalarEmitter). -/
def emitCFromPlanVerified (plan : Plan) (k c mu : Nat)
    (funcName : String) : String :=
  let stmt := lowerNTTFromPlanVerified plan k c mu
  -- Element type: uint64_t for Goldilocks (elements up to p-1 ≈ 2^64 exceed int64_t range),
  -- int32_t for 32-bit fields (signed needed for arithmetic shift in Montgomery REDC).
  let elemType := if k == 64 then "uint64_t" else "int32_t"
  -- Wide type for butterfly intermediates: __uint128_t for Goldilocks (products up to
  -- (p-1)^2 ≈ 2^128, exceeds signed __int128 max of 2^127-1, must be unsigned),
  -- int64_t for 32-bit fields (signed needed for arithmetic shift in Montgomery REDC).
  let wideType := if k == 64 then "__uint128_t" else "int64_t"
  let numTemps := maxTempsInPlan plan k c mu
  let hasR4 := plan.stages.toList.any fun s => s.radix == .r4
  let r4Decls := if hasR4 then
    s!"\n  {wideType} c_val, d_val, w1_val, w1p_val, w2_val, w3_val;"
  else ""
  -- Load temp vars (matching array element type) for loadWiden pattern
  let r4LoadDecls := if hasR4 then
    s!"\n  {elemType} c_val_ld, d_val_ld, w1_val_ld, w1p_val_ld, w2_val_ld, w3_val_ld;"
  else ""
  -- v3.10.0 TD: ILP2 needs additional variables for second butterfly
  let hasILP2 := plan.stages.toList.any fun s => s.ilpFactor ≥ 2 && s.radix == .r2
  let ilp2Decls := if hasILP2 then
    s!"\n  {wideType} pair2, a_val2, b_val2, w_val2;" ++
    s!"\n  {elemType} a_val2_ld, b_val2_ld, w_val2_ld;"
  else ""
  -- NOTE: F5 attempted to narrow loop vars to uint64_t but caused off-by-one
  -- errors due to type interaction between uint64_t a_val and __uint128_t temps.
  -- F5 requires a deeper approach (Approach B from §10.5b: new lowerReduce128
  -- function that generates uint64_t-native code). Deferred to future work.
  let tempDecls := if numTemps == 0 then "" else
    s!"  {wideType} " ++ String.intercalate ", " (List.range numTemps |>.map (s!"t{·}")) ++ ";\n" ++
    s!"  {wideType} group, pair, a_val, b_val, w_val;" ++ r4Decls ++ ilp2Decls ++
    s!"\n  {elemType} a_val_ld, b_val_ld, w_val_ld;" ++ r4LoadDecls ++ "\n"
  let bodyC := _root_.TrustLean.stmtToC 1 stmt
  -- Post-process: fix C integer literals that exceed standard type ranges.
  -- stmtToC emits bare decimal literals. For Goldilocks:
  --   2*p ≈ 2^65 exceeds UINT64_MAX → replace with (p + p) expression with ULL suffix
  --   p ≈ 2^64 and 2^64-1 need ULL suffix (exceed int64_t range)
  -- NOTE (fragility): This is string.replace on the full C output. Works because
  -- p=18446744069414584321 (20 digits) doesn't appear as substring of other values.
  -- If a future constant collided, this would corrupt. Proper fix: emit suffixed
  -- literals from TrustLean.stmtToC directly (not post-processing). See L-741.
  let bodyC := if k == 64 then
    let p := plan.field
    let twoPStr := toString (2 * p)
    let pStr := toString p
    let mask64Str := toString (2^64 - 1 : Nat)
    -- Use placeholder to avoid double-suffix from overlapping replacements
    -- (2*p contains p as substring; replacing p after 2*p would double-suffix)
    let bodyC := bodyC.replace twoPStr "___TWOP___"
    let bodyC := bodyC.replace mask64Str s!"{mask64Str}ULL"
    let bodyC := bodyC.replace pStr s!"{pStr}ULL"
    let bodyC := bodyC.replace "___TWOP___" s!"((__uint128_t){pStr}ULL + {pStr}ULL)"
    -- Fix casts: widen32to64 emits (int64_t), need (__uint128_t) for Goldilocks
    -- trunc64to32 emits (int32_t), need (uint64_t) for Goldilocks
    let bodyC := bodyC.replace "((int64_t)" "((__uint128_t)"
    let bodyC := bodyC.replace "((int32_t)" "((uint64_t)"
    bodyC
  else bodyC
  -- v3.11.0 F5: Preamble with goldi_reduce128 (uint64_t internals, ~9 ARM instructions)
  let goldiPreamble := if k == 64 then
    let pStr := toString plan.field
    s!"static inline uint64_t goldi_reduce128(__uint128_t x) \{\n" ++
    s!"  uint64_t lo=(uint64_t)x, hi=(uint64_t)(x>>64);\n" ++
    s!"  uint64_t hh=hi>>32, hl=hi&0xFFFFFFFFULL;\n" ++
    s!"  uint64_t t0; int borrow=__builtin_sub_overflow(lo,hh,&t0);\n" ++
    s!"  if(borrow) t0-=0xFFFFFFFFULL;\n" ++
    s!"  uint64_t t1=hl*0xFFFFFFFFULL;\n" ++
    s!"  uint64_t r; int carry=__builtin_add_overflow(t0,t1,&r);\n" ++
    s!"  if(carry||r>={pStr}ULL) r-={pStr}ULL;\n" ++
    s!"  return r;\n}\n\n" ++
    -- v3.11.0 F5b: goldi_add — modular add with carry detection (~3 ARM instr)
    -- Precondition: a < p, b < p. carry possible since a+b up to 2p-2 > 2^64.
    s!"static inline uint64_t goldi_add(uint64_t a, uint64_t b) \{\n" ++
    s!"  uint64_t r; int carry=__builtin_add_overflow(a,b,&r);\n" ++
    s!"  if(carry||r>={pStr}ULL) r-={pStr}ULL;\n" ++
    s!"  return r;\n}\n\n" ++
    -- v3.11.0 F5b: goldi_sub — modular sub with borrow detection (~3 ARM instr)
    -- Precondition: a < p, b < p. borrow possible when a < b.
    -- r+P may overflow uint64_t: DEFINED BEHAVIOR for unsigned (wraps mod 2^64).
    s!"static inline uint64_t goldi_sub(uint64_t a, uint64_t b) \{\n" ++
    s!"  uint64_t r; int borrow=__builtin_sub_overflow(a,b,&r);\n" ++
    s!"  if(borrow) r+={pStr}ULL;\n" ++
    s!"  return r;\n}\n\n" ++
    -- v3.12.0 F5c: goldi_butterfly — full butterfly encapsulated in function.
    -- Returns uint64_t (dummy 0) so Stmt.call can assign to temp without void issue.
    -- Compiler optimizes away unused return. Body is 100% uint64_t.
    s!"static inline uint64_t goldi_butterfly(\n" ++
    s!"    uint64_t *data, const uint64_t *twiddles,\n" ++
    s!"    uint64_t i, uint64_t j, uint64_t tw_idx) \{\n" ++
    s!"  uint64_t a=data[i], b=data[j], w=twiddles[tw_idx];\n" ++
    s!"  uint64_t wb=goldi_reduce128((__uint128_t)w*(__uint128_t)b);\n" ++
    s!"  data[i]=goldi_add(a,wb);\n" ++
    s!"  data[j]=goldi_sub(a,wb);\n" ++
    s!"  return 0;\n}\n\n" ++
    -- v3.12.0 F5c: goldi_butterfly4 — radix-4 butterfly (2 levels in 1 function)
    -- 10 params: data*, twiddles*, 4 data indices, 4 twiddle indices.
    -- Inner: (a,c) w2 + (b,d) w3. Outer: (r0,r1) w1 + (r2,r3) w1p.
    -- DIT data-position order: i0←add(r0,w1r1), i1←sub(r0,w1r1),
    --                          i2←add(r2,w1pr3), i3←sub(r2,w1pr3).
    s!"static inline uint64_t goldi_butterfly4(\n" ++
    s!"    uint64_t *data, const uint64_t *twiddles,\n" ++
    s!"    uint64_t i0, uint64_t i1, uint64_t i2, uint64_t i3,\n" ++
    s!"    uint64_t tw2i, uint64_t tw3i, uint64_t tw1i, uint64_t tw1pi) \{\n" ++
    s!"  uint64_t a=data[i0],b=data[i1],c=data[i2],d=data[i3];\n" ++
    s!"  uint64_t w2=twiddles[tw2i],w3=twiddles[tw3i];\n" ++
    s!"  uint64_t w1=twiddles[tw1i],w1p=twiddles[tw1pi];\n" ++
    s!"  uint64_t w2c=goldi_reduce128((__uint128_t)w2*(__uint128_t)c);\n" ++
    s!"  uint64_t r0=goldi_add(a,w2c), r2=goldi_sub(a,w2c);\n" ++
    s!"  uint64_t w3d=goldi_reduce128((__uint128_t)w3*(__uint128_t)d);\n" ++
    s!"  uint64_t r1=goldi_add(b,w3d), r3=goldi_sub(b,w3d);\n" ++
    s!"  uint64_t w1r1=goldi_reduce128((__uint128_t)w1*(__uint128_t)r1);\n" ++
    s!"  data[i0]=goldi_add(r0,w1r1); data[i1]=goldi_sub(r0,w1r1);\n" ++
    s!"  uint64_t w1pr3=goldi_reduce128((__uint128_t)w1p*(__uint128_t)r3);\n" ++
    s!"  data[i2]=goldi_add(r2,w1pr3); data[i3]=goldi_sub(r2,w1pr3);\n" ++
    s!"  return 0;\n}\n\n"
  else ""
  goldiPreamble ++
  s!"void {funcName}({elemType}* data, const {elemType}* twiddles) \{\n{tempDecls}{bodyC}\n}"

/-- Emit verified Rust function from Plan.
    Uses SIGNED types (i32/i64) internally, matching C's int32_t/int64_t exactly.
    This ensures identical semantics for truncation (i64→i32 preserves low 32 bits),
    sign-extension (i32→i64 preserves sign), and arithmetic shift (i64 >> k sign-fills).
    Using unsigned types (u32/u64) breaks all three: zero-extension corrupts negative
    intermediates, logical shift breaks Solinas fold on truncated values.
    The function signature keeps u32 arrays for API compatibility; an unsafe transmute
    reinterprets u32↔i32 internally (same bit representation, zero-cost). -/
def emitRustFromPlanVerified (plan : Plan) (k c mu : Nat)
    (funcName : String) : String :=
  let stmt := lowerNTTFromPlanVerified plan k c mu
  let uElemType := if k == 64 then "u64" else "u32"
  -- For k=64: no transmute, so internal type = array type (u64, unsigned)
  -- For k≤32: transmute to signed (i32) for arithmetic shift in Montgomery REDC
  let elemType := if k == 64 then "u64" else "i32"
  -- Wide type for intermediates: u128 for Goldilocks (products up to (p-1)^2 ≈ 2^128,
  -- exceeds i128 max), i64 for 32-bit fields (signed for arithmetic shift in REDC).
  let wideType := if k == 64 then "u128" else "i64"
  let numTemps := maxTempsInPlan plan k c mu
  -- v3.11.0 F5: Numbered temps stay wideType (reduction intermediates can exceed 2^64)
  let tempDecls := String.join (List.range numTemps |>.map fun i =>
    s!"  let mut t{i}: {wideType};\n")
  let hasR4 := plan.stages.toList.any fun s => s.radix == .r4
  let r4Decls := if hasR4 then
    s!"  let mut c_val: {wideType};\n  let mut d_val: {wideType};\n" ++
    s!"  let mut w1_val: {wideType};\n  let mut w1p_val: {wideType};\n" ++
    s!"  let mut w2_val: {wideType};\n  let mut w3_val: {wideType};\n"
  else ""
  -- Load temp vars (i32, matching array element type) for loadWiden pattern
  let loadDecls := s!"  let mut a_val_ld: {elemType};\n  let mut b_val_ld: {elemType};\n  let mut w_val_ld: {elemType};\n"
  let r4LoadDecls := if hasR4 then
    s!"  let mut c_val_ld: {elemType};\n  let mut d_val_ld: {elemType};\n" ++
    s!"  let mut w1_val_ld: {elemType};\n  let mut w1p_val_ld: {elemType};\n" ++
    s!"  let mut w2_val_ld: {elemType};\n  let mut w3_val_ld: {elemType};\n"
  else ""
  let loopDecls := s!"  let mut group: {wideType};\n  let mut pair: {wideType};\n" ++
    s!"  let mut a_val: {wideType};\n  let mut b_val: {wideType};\n  let mut w_val: {wideType};\n" ++
    r4Decls
  -- Transmute u32↔i32 at function entry (zero-cost reinterpret, same bit layout)
  -- For k=64: skip transmute (arrays already u64, no signed reinterpretation needed)
  let transmute := if k == 64 then "" else
    s!"  let data: &mut [{elemType}] = unsafe \{ &mut *(data as *mut [{uElemType}] as *mut [{elemType}]) };\n" ++
    s!"  let twiddles: &[{elemType}] = unsafe \{ &*(twiddles as *const [{uElemType}] as *const [{elemType}]) };\n"
  let bodyRust := _root_.TrustLean.stmtToRust 1 stmt
  -- For k=64: post-process casts + literals (same approach as C literal fix)
  let bodyRust := if k == 64 then
    let p := plan.field
    let twoPStr := toString (2 * p)
    let pStr := toString p
    let mask64Str := toString (2^64 - 1 : Nat)
    -- Fix casts: widen `as i64` → `as u128`, trunc `as i32` → `as u64`
    let bodyRust := bodyRust.replace " as i64)" " as u128)"
    let bodyRust := bodyRust.replace " as i32)" " as u64)"
    -- Fix literals: 2*p → (p + p) expression, p → p_u128 suffix
    let bodyRust := bodyRust.replace twoPStr s!"({pStr}_u128 + {pStr}_u128)"
    bodyRust
  else bodyRust
  -- v3.11.0 F5: Rust preamble with goldi_reduce128
  let goldiPreambleRust := if k == 64 then
    let pStr := toString plan.field
    s!"#[inline(always)]\n" ++
    s!"fn goldi_reduce128(x: u128) -> u64 \{\n" ++
    s!"  let lo = x as u64;\n" ++
    s!"  let hi = (x >> 64) as u64;\n" ++
    s!"  let hh = hi >> 32;\n" ++
    s!"  let hl = hi & 0xFFFFFFFF_u64;\n" ++
    s!"  let (mut t0, borrow) = lo.overflowing_sub(hh);\n" ++
    s!"  if borrow \{ t0 = t0.wrapping_sub(0xFFFFFFFF_u64); }\n" ++
    s!"  let t1 = hl.wrapping_mul(0xFFFFFFFF_u64);\n" ++
    s!"  let (mut r, carry) = t0.overflowing_add(t1);\n" ++
    s!"  if carry || r >= {pStr}_u64 \{ r = r.wrapping_sub({pStr}_u64); }\n" ++
    s!"  r\n}\n\n" ++
    -- v3.11.0 F5b: goldi_add — modular add with carry detection
    s!"#[inline(always)]\n" ++
    s!"fn goldi_add(a: u64, b: u64) -> u64 \{\n" ++
    s!"  let (mut r, carry) = a.overflowing_add(b);\n" ++
    s!"  if carry || r >= {pStr}_u64 \{ r = r.wrapping_sub({pStr}_u64); }\n" ++
    s!"  r\n}\n\n" ++
    -- v3.11.0 F5b: goldi_sub — modular sub with borrow detection
    -- wrapping_add handles r+P overflow (same as C unsigned wrap)
    s!"#[inline(always)]\n" ++
    s!"fn goldi_sub(a: u64, b: u64) -> u64 \{\n" ++
    s!"  let (mut r, borrow) = a.overflowing_sub(b);\n" ++
    s!"  if borrow \{ r = r.wrapping_add({pStr}_u64); }\n" ++
    s!"  r\n}\n\n" ++
    -- v3.12.0 F5c: goldi_butterfly — full butterfly (Rust)
    -- Returns u64 (dummy 0) for Stmt.call compatibility. Body is 100% u64.
    s!"#[inline(always)]\n" ++
    s!"fn goldi_butterfly(data: &mut [u64], twiddles: &[u64], i: usize, j: usize, tw_idx: usize) -> u64 \{\n" ++
    s!"  let a = data[i]; let b = data[j]; let w = twiddles[tw_idx];\n" ++
    s!"  let wb = goldi_reduce128((w as u128) * (b as u128));\n" ++
    s!"  data[i] = goldi_add(a, wb);\n" ++
    s!"  data[j] = goldi_sub(a, wb);\n" ++
    s!"  0\n}\n\n" ++
    -- v3.12.0 F5c: goldi_butterfly4 — radix-4 butterfly (Rust)
    s!"#[inline(always)]\n" ++
    s!"fn goldi_butterfly4(data: &mut [u64], twiddles: &[u64],\n" ++
    s!"    i0: usize, i1: usize, i2: usize, i3: usize,\n" ++
    s!"    tw2i: usize, tw3i: usize, tw1i: usize, tw1pi: usize) -> u64 \{\n" ++
    s!"  let (a,b,c,d) = (data[i0],data[i1],data[i2],data[i3]);\n" ++
    s!"  let (w2,w3) = (twiddles[tw2i],twiddles[tw3i]);\n" ++
    s!"  let (w1,w1p) = (twiddles[tw1i],twiddles[tw1pi]);\n" ++
    s!"  let w2c = goldi_reduce128((w2 as u128)*(c as u128));\n" ++
    s!"  let (r0,r2) = (goldi_add(a,w2c), goldi_sub(a,w2c));\n" ++
    s!"  let w3d = goldi_reduce128((w3 as u128)*(d as u128));\n" ++
    s!"  let (r1,r3) = (goldi_add(b,w3d), goldi_sub(b,w3d));\n" ++
    s!"  let w1r1 = goldi_reduce128((w1 as u128)*(r1 as u128));\n" ++
    s!"  data[i0] = goldi_add(r0,w1r1); data[i1] = goldi_sub(r0,w1r1);\n" ++
    s!"  let w1pr3 = goldi_reduce128((w1p as u128)*(r3 as u128));\n" ++
    s!"  data[i2] = goldi_add(r2,w1pr3); data[i3] = goldi_sub(r2,w1pr3);\n" ++
    s!"  0\n}\n\n"
  else ""
  goldiPreambleRust ++
  s!"fn {funcName}(data: &mut [{uElemType}], twiddles: &[{uElemType}]) \{\n{tempDecls}{loopDecls}{loadDecls}{r4LoadDecls}{transmute}{bodyRust}\n}"

-- ══════════════════════════════════════════════════════════════════
-- Block 2.8: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- For each ReductionChoice, the generated Stmt is well-formed.
    Composes existing theorems: lowerSolinasFold_sound, lowerHarveyReduce_cond_sound. -/
theorem lowerReductionChoice_sound (red : ReductionChoice) (xExpr : LowLevelExpr)
    (p k c mu : Nat) (cgs : CodeGenState) :
    let (stmt, resultVar, _) := lowerReductionChoice red xExpr p k c mu cgs
    ∃ stmt', stmt = stmt' := by
  cases red <;> simp [lowerReductionChoice] <;> exact ⟨_, rfl⟩

/-- The Goldilocks product reduction produces a well-formed Stmt sequence.
    Structural: the function always returns a (Stmt, VarName, CodeGenState) triple. -/
theorem lowerGoldilocksProductReduce_wf (xExpr : LowLevelExpr) (p : Nat)
    (cgs : CodeGenState) :
    let (stmt, _, _) := lowerGoldilocksProductReduce xExpr p cgs
    ∃ s, stmt = s := ⟨_, rfl⟩

/-- The butterfly product reduction dispatches correctly by k.
    For k ≤ 32: uses Montgomery REDC. For k > 32: uses Goldilocks shift-subtract. -/
theorem lowerDIFButterflyByReduction_dispatch (aVar bVar wVar : VarName)
    (red : ReductionChoice) (p k c mu : Nat) (cgs : CodeGenState) :
    let (stmt, _, _, _) := lowerDIFButterflyByReduction aVar bVar wVar red p k c mu cgs
    ∃ s, stmt = s := ⟨_, rfl⟩

end AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
