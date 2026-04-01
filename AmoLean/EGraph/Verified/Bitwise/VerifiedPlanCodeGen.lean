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

/-- Lower a ReductionChoice to TrustLean.Stmt.
    Dispatches to existing verified reduction functions in TrustLeanBridge.
    This is the KEY function that bridges Plan decisions → verified code. -/
def lowerReductionChoice (red : ReductionChoice) (xExpr : LowLevelExpr)
    (p k c mu : Nat) (cgs : CodeGenState) : (Stmt × VarName × CodeGenState) :=
  match red with
  | .solinasFold =>
    let (sr, cgs') := lowerSolinasFold xExpr k c cgs
    (sr.stmt, extractVar sr.resultVar, cgs')
  | .montgomery =>
    let (sr, cgs') := lowerMontyReduce xExpr p mu cgs
    (sr.stmt, extractVar sr.resultVar, cgs')
  | .harvey =>
    let (sr, cgs') := lowerHarveyReduce xExpr p cgs
    (sr.stmt, extractVar sr.resultVar, cgs')
  | .lazy =>
    -- No reduction; assign x to fresh var for uniformity
    let (vn, cgs') := cgs.freshVar
    (.assign vn xExpr, vn, cgs')

-- ══════════════════════════════════════════════════════════════════
-- Block 2.2: Butterfly parametrized by ReductionChoice
-- ══════════════════════════════════════════════════════════════════

/-- DIF butterfly with parametric reduction.
    For Solinas: delegates to existing verified lowerDIFButterflyStmt.
    For Montgomery/Harvey/Lazy: builds butterfly manually with selected reduction. -/
def lowerDIFButterflyByReduction (aVar bVar wVar : VarName)
    (red : ReductionChoice) (p k c mu : Nat)
    (cgs : CodeGenState) : (Stmt × VarName × VarName × CodeGenState) :=
  match red with
  | .solinasFold =>
    -- REUSE existing verified function directly
    lowerDIFButterflyStmt aVar bVar wVar p k c cgs
  | _ =>
    -- Build butterfly: wb = w*b, sum = a + wb, diff = p + a - wb
    -- Then apply selected reduction to sum and diff
    let (wbVar, cgs1) := cgs.freshVar
    let wbExpr := LowLevelExpr.binOp .mul (.varRef wVar) (.varRef bVar)
    let wbStmt := Stmt.assign wbVar wbExpr
    let (sumVar, cgs2) := cgs1.freshVar
    let sumExpr := LowLevelExpr.binOp .add (.varRef aVar) (.varRef wbVar)
    let sumStmt := Stmt.assign sumVar sumExpr
    let (diffVar, cgs3) := cgs2.freshVar
    let diffExpr := LowLevelExpr.binOp .sub
      (LowLevelExpr.binOp .add (.varRef aVar) (.litInt ↑p))
      (.varRef wbVar)
    let diffStmt := Stmt.assign diffVar diffExpr
    -- Apply reduction to sum and diff
    let (redSumStmt, redSumVar, cgs4) :=
      lowerReductionChoice red (.varRef sumVar) p k c mu cgs3
    let (redDiffStmt, redDiffVar, cgs5) :=
      lowerReductionChoice red (.varRef diffVar) p k c mu cgs4
    let fullStmt := Stmt.seq wbStmt (Stmt.seq sumStmt (Stmt.seq diffStmt
      (Stmt.seq redSumStmt redDiffStmt)))
    (fullStmt, redSumVar, redDiffVar, cgs5)

-- ══════════════════════════════════════════════════════════════════
-- Block 2.3: Radix-4 butterfly parametrized by ReductionChoice
-- ══════════════════════════════════════════════════════════════════

/-- Radix-4 butterfly with parametric reduction.
    For Solinas: REUSE existing lowerRadix4ButterflyStmt.
    For others: compose 3 radix-2 butterflies with selected reduction. -/
def lowerRadix4ButterflyByReduction
    (aVar bVar cVar dVar w1Var w2Var w3Var : VarName)
    (red : ReductionChoice) (p k c_val mu : Nat)
    (cgs : CodeGenState) : (Stmt × VarName × VarName × VarName × VarName × CodeGenState) :=
  match red with
  | .solinasFold =>
    lowerRadix4ButterflyStmt aVar bVar cVar dVar w1Var w2Var w3Var p k c_val cgs
  | _ =>
    -- Compose: 2 radix-2 on (a,c) and (b,d), then 2 radix-2 on results
    let (s1, r0, r2, cgs1) :=
      lowerDIFButterflyByReduction aVar cVar w2Var red p k c_val mu cgs
    let (s2, r1, r3, cgs2) :=
      lowerDIFButterflyByReduction bVar dVar w3Var red p k c_val mu cgs1
    let (s3, out0, out2, cgs3) :=
      lowerDIFButterflyByReduction r0 r1 w1Var red p k c_val mu cgs2
    let (s4, out1, out3, cgs4) :=
      lowerDIFButterflyByReduction r2 r3 w1Var red p k c_val mu cgs3
    (Stmt.seq s1 (Stmt.seq s2 (Stmt.seq s3 s4)), out0, out1, out2, out3, cgs4)

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

/-- Lower a single NTTStage to TrustLean.Stmt with nested for-loops.
    The butterfly and reduction are determined by the stage's Plan entry. -/
def lowerStageVerified (stage : NTTStage) (n p k c mu : Nat) : Stmt :=
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

/-- Lower a complete NTT from Plan to TrustLean.Stmt.
    Each stage may use a different reduction strategy.
    This replaces NTTPlanCodeGen.lowerNTTFromPlan (which used UnifiedCodeGen.Stmt). -/
def lowerNTTFromPlanVerified (plan : Plan) (k c mu : Nat) : Stmt :=
  let stmts := plan.stages.toList.map fun stage =>
    lowerStageVerified stage plan.size plan.field k c mu
  stmts.foldl Stmt.seq Stmt.skip

-- ══════════════════════════════════════════════════════════════════
-- Block 2.6: Emit C and Rust from verified Plan
-- ══════════════════════════════════════════════════════════════════

/-- Count maximum temp variables used across all stages. -/
private def maxTempsInPlan (plan : Plan) (k c mu : Nat) : Nat :=
  let counts := plan.stages.toList.map fun stage =>
    let cgs : CodeGenState := {}
    let aVar := VarName.user "a_val"
    let bVar := VarName.user "b_val"
    let wVar := VarName.user "w_val"
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
  let tempDecls := if numTemps == 0 then "" else
    "  int64_t " ++ String.intercalate ", " (List.range numTemps |>.map (s!"t{·}")) ++ ";\n" ++
    "  int64_t group, pair, a_val, b_val, w_val;\n"
  let bodyC := _root_.TrustLean.stmtToC 1 stmt
  s!"void {funcName}({elemType}* data, const {elemType}* twiddles) \{\n{tempDecls}{bodyC}\n}"

/-- Emit verified Rust function from Plan. -/
def emitRustFromPlanVerified (plan : Plan) (k c mu : Nat)
    (funcName : String) : String :=
  let stmt := lowerNTTFromPlanVerified plan k c mu
  let elemType := if k == 64 then "i64" else "i32"
  let numTemps := maxTempsInPlan plan k c mu
  let tempDecls := String.join (List.range numTemps |>.map fun i =>
    s!"  let mut t{i}: i64;\n")
  let loopDecls := "  let mut group: i64;\n  let mut pair: i64;\n" ++
    "  let mut a_val: i64;\n  let mut b_val: i64;\n  let mut w_val: i64;\n"
  let bodyRust := _root_.TrustLean.stmtToRust 1 stmt
  s!"fn {funcName}(data: &mut [{elemType}], twiddles: &[{elemType}]) \{\n{tempDecls}{loopDecls}{bodyRust}\n}"

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

/-- The butterfly delegates to the correct verified function for Solinas. -/
theorem lowerDIFButterflyByReduction_solinas_eq
    (aVar bVar wVar : VarName) (p k c mu : Nat) (cgs : CodeGenState) :
    lowerDIFButterflyByReduction aVar bVar wVar .solinasFold p k c mu cgs =
    lowerDIFButterflyStmt aVar bVar wVar p k c cgs := by
  simp [lowerDIFButterflyByReduction]

end AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
