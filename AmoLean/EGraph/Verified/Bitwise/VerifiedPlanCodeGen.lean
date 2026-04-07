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

open _root_.TrustLean (Stmt VarName LowLevelExpr BinOp StmtResult CodeGenState)
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
-- Block 2.2: Butterfly parametrized by ReductionChoice
-- ══════════════════════════════════════════════════════════════════

/-- Unified DIT butterfly with REDC on product and parametric sum/diff reduction.
    Product w*b is always reduced via Montgomery REDC — the only single-pass reduction
    valid for the full range p^2 ≈ 2^62. Requires Montgomery-form twiddles
    (tw_mont = tw * R mod p) so REDC(tw_mont * b) = tw * b mod p.
    After REDC: wb_red < p, so sum = a + wb_red < 2p. Single Solinas fold on sum/diff
    produces output < p+c < 2^31, fits i32/u32 for all 32-bit fields. -/
def lowerDIFButterflyByReduction (aVar bVar wVar : VarName)
    (red : ReductionChoice) (p k c mu : Nat)
    (cgs : CodeGenState) : (Stmt × VarName × VarName × CodeGenState) :=
  -- Step 1: product w*b with Montgomery REDC subtraction variant
  -- d = T - m*p, q = d >> 32, result = T < u ? q + p : q
  -- Uses mu = p^{-1} mod R (stored in FieldConfig) — no negation needed.
  -- No int64 overflow: d ∈ (-R*p, R*p) ⊂ int64 range.
  let (wbVar, cgs1) := cgs.freshVar
  let wbExpr := LowLevelExpr.binOp .mul (.varRef wVar) (.varRef bVar)
  let wbStmt := Stmt.assign wbVar wbExpr
  let (redWbStmt, redWbVar, cgs2) :=
    lowerMontyReduceSub (.varRef wbVar) p mu cgs1
  -- Step 2: sum = a + wb_red, diff = (a + p) - wb_red
  let (sumVar, cgs3) := cgs2.freshVar
  let sumExpr := LowLevelExpr.binOp .add (.varRef aVar) (.varRef redWbVar)
  let sumStmt := Stmt.assign sumVar sumExpr
  let (diffVar, cgs4) := cgs3.freshVar
  let diffExpr := LowLevelExpr.binOp .sub
    (LowLevelExpr.binOp .add (.varRef aVar) (.litInt ↑p))
    (.varRef redWbVar)
  let diffStmt := Stmt.assign diffVar diffExpr
  -- Step 3: parametric reduction on sum and diff (inputs < 2p, fold fits i32)
  let (redSumStmt, redSumVar, cgs5) :=
    lowerReductionChoice red (.varRef sumVar) p k c mu cgs4
  let (redDiffStmt, redDiffVar, cgs6) :=
    lowerReductionChoice red (.varRef diffVar) p k c mu cgs5
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
    (cgs : CodeGenState) : (Stmt × VarName × VarName × VarName × VarName × CodeGenState) :=
  -- Inner level L: bf2 on even-indexed (a,c) and odd-indexed (b,d)
  let (s1, r0, r2, cgs1) :=
    lowerDIFButterflyByReduction aVar cVar w2Var red p k c_val mu cgs
  let (s2, r1, r3, cgs2) :=
    lowerDIFButterflyByReduction bVar dVar w3Var red p k c_val mu cgs1
  -- Outer level L+1: cross-butterflies use DIFFERENT twiddles (groups 2g and 2g+1)
  let (s3, out0, out2, cgs3) :=
    lowerDIFButterflyByReduction r0 r1 w1Var red p k c_val mu cgs2
  let (s4, out1, out3, cgs4) :=
    lowerDIFButterflyByReduction r2 r3 w1pVar red p k c_val mu cgs3
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
  let bfBody :=
    let aVar := VarName.user "a_val"
    let bVar := VarName.user "b_val"
    let cVar := VarName.user "c_val"
    let dVar := VarName.user "d_val"
    let w1Var := VarName.user "w1_val"
    let w1pVar := VarName.user "w1p_val"
    let w2Var := VarName.user "w2_val"
    let w3Var := VarName.user "w3_val"
    let dataVar := VarName.user "data"
    let twVar := VarName.user "twiddles"
    -- Data indices: base = g·4q + pair, then +q, +2q, +3q
    let baseExpr := nttDataIndex groupVar pairVar halfSizeL
    let i0 := baseExpr
    let i1 := .binOp .add baseExpr (.litInt ↑quarterSize)
    let i2 := .binOp .add baseExpr (.litInt ↑(2 * quarterSize))
    let i3 := .binOp .add baseExpr (.litInt ↑(3 * quarterSize))
    -- Twiddle indices: reuse nttTwiddleIndex + offset
    -- w2: level L, group g, pair p (inner even)
    let tw2 := nttTwiddleIndex L groupVar pairVar halfSizeL n
    -- w3: level L, group g, pair p+q (inner odd)
    let tw3 := .binOp .add (nttTwiddleIndex L groupVar pairVar halfSizeL n) (.litInt ↑quarterSize)
    -- w1: level L+1, group 2g, pair p (outer first) — 2g·q = g·2q = g·halfSizeL
    let tw1 := nttTwiddleIndex (L + 1) groupVar pairVar halfSizeL n
    -- w1': level L+1, group 2g+1, pair p (outer second)
    let tw1p := .binOp .add (nttTwiddleIndex (L + 1) groupVar pairVar halfSizeL n)
      (.litInt ↑quarterSize)
    -- R4 butterfly returns (pos0, pos1, pos2, pos3) in data-position order
    let (bf, pos0, pos1, pos2, pos3, _) :=
      lowerRadix4ButterflyByReduction aVar bVar cVar dVar
        w1Var w1pVar w2Var w3Var stage.reduction p k c mu cgs
    -- Load 4 data + 4 twiddles → butterfly → store 4 results
    Stmt.seq (Stmt.load aVar (.varRef dataVar) i0)
      (Stmt.seq (Stmt.load bVar (.varRef dataVar) i1)
        (Stmt.seq (Stmt.load cVar (.varRef dataVar) i2)
          (Stmt.seq (Stmt.load dVar (.varRef dataVar) i3)
            (Stmt.seq (Stmt.load w2Var (.varRef twVar) tw2)
              (Stmt.seq (Stmt.load w3Var (.varRef twVar) tw3)
                (Stmt.seq (Stmt.load w1Var (.varRef twVar) tw1)
                  (Stmt.seq (Stmt.load w1pVar (.varRef twVar) tw1p)
                    (Stmt.seq bf
                      (Stmt.seq (Stmt.store (.varRef dataVar) i0 (.varRef pos0))
                        (Stmt.seq (Stmt.store (.varRef dataVar) i1 (.varRef pos1))
                          (Stmt.seq (Stmt.store (.varRef dataVar) i2 (.varRef pos2))
                            (Stmt.store (.varRef dataVar) i3 (.varRef pos3)))))))))))))
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
  -- Build butterfly body for radix-2
  let bfBody :=
    let aVar := VarName.user "a_val"
    let bVar := VarName.user "b_val"
    let wVar := VarName.user "w_val"
    let iExpr := nttDataIndex groupVar pairVar halfSize
    let jExpr := .binOp .add iExpr (.litInt ↑halfSize)
    let twExpr := nttTwiddleIndex stage.stageIdx groupVar pairVar halfSize n
    let (bf, sumVar, diffVar, _) :=
      lowerDIFButterflyByReduction aVar bVar wVar stage.reduction p k c mu cgs
    -- Load → butterfly → store
    Stmt.seq (Stmt.load aVar (.varRef (VarName.user "data")) iExpr)
      (Stmt.seq (Stmt.load bVar (.varRef (VarName.user "data")) jExpr)
        (Stmt.seq (Stmt.load wVar (.varRef (VarName.user "twiddles")) twExpr)
          (Stmt.seq bf
            (Stmt.seq (Stmt.store (.varRef (VarName.user "data")) iExpr (.varRef sumVar))
              (Stmt.store (.varRef (VarName.user "data")) jExpr (.varRef diffVar))))))
  -- Wrap in nested for-loops
  Stmt.for_
    (.assign groupVar (.litInt 0)) (.binOp .ltOp (.varRef groupVar) (.litInt ↑numGroups))
    (.assign groupVar (.binOp .add (.varRef groupVar) (.litInt 1)))
    (Stmt.for_
      (.assign pairVar (.litInt 0)) (.binOp .ltOp (.varRef pairVar) (.litInt ↑halfSize))
      (.assign pairVar (.binOp .add (.varRef pairVar) (.litInt 1)))
      bfBody)

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
          stage.reduction plan.field k c mu cgs
      cgs'.nextVar
    | _ =>
      let (_, _, _, cgs') :=
        lowerDIFButterflyByReduction aVar bVar wVar stage.reduction plan.field k c mu cgs
      cgs'.nextVar
  counts.foldl Nat.max 0

/-- Emit verified C function from Plan.
    Replaces NTTPlanCodeGen.emitCFromPlan (which used cScalarEmitter). -/
def emitCFromPlanVerified (plan : Plan) (k c mu : Nat)
    (funcName : String) : String :=
  let stmt := lowerNTTFromPlanVerified plan k c mu
  let elemType := if k == 64 then "int64_t" else "int32_t"
  let numTemps := maxTempsInPlan plan k c mu
  let hasR4 := plan.stages.toList.any fun s => s.radix == .r4
  let r4Decls := if hasR4 then
    "\n  int64_t c_val, d_val, w1_val, w1p_val, w2_val, w3_val;"
  else ""
  let tempDecls := if numTemps == 0 then "" else
    "  int64_t " ++ String.intercalate ", " (List.range numTemps |>.map (s!"t{·}")) ++ ";\n" ++
    "  int64_t group, pair, a_val, b_val, w_val;" ++ r4Decls ++ "\n"
  let bodyC := _root_.TrustLean.stmtToC 1 stmt
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
  let elemType := if k == 64 then "i64" else "i32"
  let wideType := "i64"
  let numTemps := maxTempsInPlan plan k c mu
  let tempDecls := String.join (List.range numTemps |>.map fun i =>
    s!"  let mut t{i}: {wideType};\n")
  let hasR4 := plan.stages.toList.any fun s => s.radix == .r4
  let r4Decls := if hasR4 then
    s!"  let mut c_val: {wideType};\n  let mut d_val: {wideType};\n" ++
    s!"  let mut w1_val: {wideType};\n  let mut w1p_val: {wideType};\n" ++
    s!"  let mut w2_val: {wideType};\n  let mut w3_val: {wideType};\n"
  else ""
  let loopDecls := s!"  let mut group: {wideType};\n  let mut pair: {wideType};\n" ++
    s!"  let mut a_val: {wideType};\n  let mut b_val: {wideType};\n  let mut w_val: {wideType};\n" ++
    r4Decls
  -- Transmute u32↔i32 at function entry (zero-cost reinterpret, same bit layout)
  let transmute :=
    s!"  let data: &mut [{elemType}] = unsafe \{ &mut *(data as *mut [{uElemType}] as *mut [{elemType}]) };\n" ++
    s!"  let twiddles: &[{elemType}] = unsafe \{ &*(twiddles as *const [{uElemType}] as *const [{elemType}]) };\n"
  let bodyRust := _root_.TrustLean.stmtToRust 1 stmt
  -- Patch loads: i32 → i64 sign-extension (matching C's int32→int64 promotion)
  let bodyRust := bodyRust.replace " as usize];" s!" as usize] as {wideType};"
  -- Patch stores: i64 → i32 truncation (matching C's (int32_t) cast)
  let lines := bodyRust.splitOn "\n"
  let fixedLines := lines.map fun line =>
    let isStore := (line.splitOn "data[").length > 1 &&
                   (line.splitOn "] = ").length > 1 &&
                   !((line.splitOn s!" as {wideType};").length > 1)
    if isStore then line.replace ";" s!" as {elemType};"
    else line
  let bodyRust := "\n".intercalate fixedLines
  s!"fn {funcName}(data: &mut [{uElemType}], twiddles: &[{uElemType}]) \{\n{tempDecls}{loopDecls}{transmute}{bodyRust}\n}"

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

end AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
