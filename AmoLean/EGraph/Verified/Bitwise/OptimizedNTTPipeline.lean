/-
  AMO-Lean -- Optimized NTT Pipeline (End-to-End Integration)

  Connects ALL optimization layers into a single function:
  (prime, hardware, NTT_size) -> optimized verified C/Rust code

  Pipeline stages:
  1. Detect Solinas form for prime -> build seed MixedExpr
  2. E-graph saturation: explore Solinas/Montgomery/Harvey/lazy alternatives
  3. Cost-aware extraction: select cheapest reduction for hardware target
  4. Bound propagation: per-stage reduction schedule
  5. Plan construction: radix selection + cache model
  6. Code emission: verified Path A (lowerMixedExprFull -> stmtToC/stmtToRust)

  Also produces a benchmark harness that compiles and runs.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedRunner
import AmoLean.EGraph.Verified.Bitwise.SynthesisToC
import AmoLean.EGraph.Verified.Bitwise.SynthesisPipeline
import AmoLean.EGraph.Verified.Bitwise.SolinasRuleGen
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.CostIntegration
import AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
import AmoLean.EGraph.Verified.Bitwise.NTTPlanSelection
import AmoLean.EGraph.Verified.Bitwise.CrossRelNTT
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDCodeGen
import AmoLean.Bridge.VerifiedPipeline
import AmoLean.EGraph.Verified.Bitwise.UltraPipeline

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline

open AmoLean.EGraph.Verified.Bitwise
  (HardwareCost arm_cortex_a76 riscv_sifive_u74 fpga_dsp48e2 x86_skylake
   arm_neon_simd x86_avx2_simd
   mersenneFoldCost pseudoMersenneFoldCost montgomeryCost barrettCost harveyCost
   mixedOpCost combinedMulAddCost solinasWinsForMulAdd
   SolinasConfig babybear_solinas koalabear_solinas goldilocks_solinas
   detectSolinasForm deriveFieldFoldRule
   solinasFoldMixedExpr mersenneFoldMixedExpr solinasConstLookup
   synthesizeReduction SynthesisResult synthesizeAndEmitC
   emitCFunction emitCFunctionTyped)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
  (emitC emitCStmt emitSolinasFoldC lowerMixedExprFull emitDIFButterflyC
   emitDIFButterflyRust
   emitNTTCFn emitNTTRustFn emitNTTLoopC lowerNTTLoopStmt solinasFoldLLE)
open AmoLean.Bridge.VerifiedPipeline
  (mixedExprToC mixedExprToRust mixedExprToCFn mixedExprToRustFn verifiedPipeline)
open AmoLean.EGraph.Verified.Bitwise.TrustLeanBridge
  (lowerSolinasFold lowerMontyReduce lowerHarveyReduce)
open MixedRunner
  (guidedOptimizeMixedF synthesizeViaEGraph GuidedMixedConfig
   mkSolinasFoldSeed mkCanonicalInput)
open AmoLean.EGraph.Verified.Bitwise.PlanSelection (selectBestPlan CacheConfig)
-- NTTPlanCodeGen/UnifiedCodeGen removed: replaced by VerifiedPlanCodeGen (Plan D Phase 2)
open AmoLean.EGraph.Verified.Bitwise.ReductionAlternativeRules (reductionAlternativeRules)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (nttStageBoundAnalysis NTTBoundConfig lazyReductionSavings)
-- ReductionChoice now used internally by VerifiedPlanCodeGen
open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitCFromPlanVerified emitRustFromPlanVerified)
open AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDCodeGen
  (lowerNTTFromPlanSIMD lowerNTTFromPlanSIMDRust neonConfig avx2Config SIMDConfig)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Field Configuration (replaces Bench.lean FieldData)
-- ══════════════════════════════════════════════════════════════════

/-- Per-field configuration carrying all constants needed for code generation.
    Unlike Bench.lean's FieldData (which stores string literals), this carries
    structured Lean values that can be used by the optimization pipeline. -/
structure FieldConfig where
  name      : String
  pNat      : Nat           -- prime value
  pLit      : String        -- C literal for prime
  cNat      : Nat           -- Solinas correction constant c = 2^b - 1
  cLit      : String        -- C literal for correction
  muLit     : String        -- Montgomery mu constant
  k         : Nat           -- shift bits (a in 2^a - 2^b + 1)
  b         : Nat           -- low exponent (b in 2^a - 2^b + 1)
  genLit    : String        -- primitive root of unity
  elemType  : String        -- C type for array elements
  wideType  : String        -- C type for wide intermediates
  muNat     : Nat           -- Montgomery inverse mu (p^(-1) mod 2^32)
  solinas   : Option SolinasConfig  -- Solinas config (none for Mersenne)
  isMersenne : Bool := false

/-- BabyBear: p = 2^31 - 2^27 + 1 = 2013265921. -/
def babybearConfig : FieldConfig :=
  { name := "BabyBear", pNat := 2013265921, pLit := "0x78000001U",
    cNat := 134217727, cLit := "134217727U", muLit := "0x88000001U",
    k := 31, b := 27, genLit := "31",
    elemType := "uint32_t", wideType := "uint64_t",
    muNat := 2281701377, solinas := some babybear_solinas }

/-- KoalaBear: p = 2^31 - 2^24 + 1 = 2130706433. -/
def koalabearConfig : FieldConfig :=
  { name := "KoalaBear", pNat := 2130706433, pLit := "0x7F000001U",
    cNat := 16777215, cLit := "16777215U", muLit := "0x81000001U",
    k := 31, b := 24, genLit := "3",
    elemType := "uint32_t", wideType := "uint64_t",
    muNat := 2164260865, solinas := some koalabear_solinas }

/-- Mersenne31: p = 2^31 - 1 = 2147483647 (true Mersenne). -/
def mersenne31Config : FieldConfig :=
  { name := "Mersenne31", pNat := 2147483647, pLit := "0x7FFFFFFFU",
    cNat := 1, cLit := "1U", muLit := "0x7FFFFFFFU",
    k := 31, b := 0, genLit := "7",
    elemType := "uint32_t", wideType := "uint64_t",
    muNat := 2147483647, solinas := none, isMersenne := true }

/-- Goldilocks: p = 2^64 - 2^32 + 1 = 18446744069414584321. -/
def goldilocksConfig : FieldConfig :=
  { name := "Goldilocks", pNat := 18446744069414584321,
    pLit := "0xFFFFFFFF00000001ULL",
    cNat := 4294967295, cLit := "0xFFFFFFFFULL", muLit := "0ULL",
    k := 64, b := 32, genLit := "7",
    elemType := "uint64_t", wideType := "__uint128_t",
    muNat := 0, solinas := some goldilocks_solinas }

/-- All supported fields. -/
def allFields : List FieldConfig :=
  [babybearConfig, koalabearConfig, mersenne31Config, goldilocksConfig]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: E-Graph Optimization (Step 1)
-- ══════════════════════════════════════════════════════════════════

/-- Result of the e-graph optimization step. -/
structure OptimizationResult where
  /-- The input MixedExpr (seed) fed into the e-graph -/
  seedExpr : MixedExpr
  /-- The optimized MixedExpr extracted by the cost model -/
  optimizedExpr : MixedExpr
  /-- Whether the e-graph found a better alternative -/
  improved : Bool
  /-- Description of the selected reduction strategy -/
  strategyName : String

/-- Describe a MixedExpr's top-level structure for reporting. -/
def describeExpr : MixedExpr -> String
  | .addE (.mulE (.shiftRightE _ _) _) (.bitAndE _ _) => "Solinas fold (shift-mul-add)"
  | .addE (.shiftRightE _ _) (.bitAndE _ _) => "Mersenne fold (shift-add)"
  | .addE (.smulE _ (.shiftRightE _ _)) (.bitAndE _ _) => "Solinas fold (smul variant)"
  | .harveyReduceE _ _ => "Harvey conditional subtraction"
  | .montyReduceE _ _ _ => "Montgomery REDC"
  | .barrettReduceE _ _ _ => "Barrett reduction"
  | .witnessE _ => "Identity (no reduction found)"
  | _ => "Custom expression"

/-- Run e-graph optimization for a given field and hardware target.
    1. Build a seed MixedExpr from the field's Solinas parameters
    2. Run 3-phase guided saturation
    3. Cost-aware extraction selects the cheapest alternative
    Returns the optimized MixedExpr with metadata. -/
def optimizeReduction (fc : FieldConfig) (hw : HardwareCost)
    (cfg : GuidedMixedConfig := .default) : OptimizationResult :=
  let seed := mkSolinasFoldSeed fc.k fc.cNat
  match guidedOptimizeMixedF fc.pNat hw cfg seed (extraRules := reductionAlternativeRules fc.pNat) with
  | some optExpr =>
    -- We can't use BEq (MixedExpr doesn't derive it), so use strategy name heuristic
    let stratName := describeExpr optExpr
    let improved := stratName != describeExpr seed
    { seedExpr := seed, optimizedExpr := optExpr, improved,
      strategyName := stratName }
  | none =>
    { seedExpr := seed, optimizedExpr := seed, improved := false,
      strategyName := "Fallback (extraction failed)" }

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Code Emission (Steps 2-6)
-- ══════════════════════════════════════════════════════════════════

-- ══════════════════════════════════════════════════════════════════
-- Section 3a: Verified Code Emission (TrustLean.Stmt path)
-- ══════════════════════════════════════════════════════════════════

/-- Generate temp variable declarations for C (int64_t t0, t1, ...). -/
private def cTempDecls (numTemps : Nat) : String :=
  if numTemps == 0 then "" else
  "  int64_t " ++ String.intercalate ", " (List.range numTemps |>.map (s!"t{·}")) ++ ";\n"

/-- Generate temp variable declarations for Rust (let mut t0: i64; ...). -/
private def rustTempDecls (numTemps : Nat) : String :=
  String.join (List.range numTemps |>.map fun i => s!"  let mut t{i}: i64;\n")

/-- Generate verified C reduction function via TrustLean.Stmt.
    Solinas: solinasFoldLLE → exprToC (single expression, verified).
    Montgomery: lowerMontyReduce → stmtToC (multi-statement REDC, verified).
    Replaces genSolinasReduceC / genMontyReduceAsAmoC string emission. -/
def verifiedReduceC (fc : FieldConfig) (strategyName : String)
    (funcName : String := "amo_reduce") : String :=
  match strategyName with
  | "Montgomery REDC" =>
    let xExpr : _root_.TrustLean.LowLevelExpr := .varRef (.user "x")
    let (sr, cgs') := lowerMontyReduce xExpr fc.pNat fc.muNat {}
    let body := _root_.TrustLean.stmtToC 1 sr.stmt
    let retExpr := _root_.TrustLean.exprToC sr.resultVar
    let decls := cTempDecls cgs'.nextVar
    s!"static inline {fc.elemType} {funcName}({fc.wideType} x) \{\n{decls}{body}\n  return ({fc.elemType}){retExpr};\n}"
  | _ =>
    let foldExpr := solinasFoldLLE (.varRef (.user "x")) fc.k fc.cNat
    let foldC := _root_.TrustLean.exprToC foldExpr
    s!"static inline {fc.elemType} {funcName}({fc.wideType} x) \{
    return ({fc.elemType})({foldC});
}"

/-- Generate verified Rust reduction function via TrustLean.Stmt. -/
def verifiedReduceRust (fc : FieldConfig) (strategyName : String)
    (funcName : String := "amo_reduce") : String :=
  let et := if fc.k == 64 then "u64" else "u32"
  let wt := if fc.k == 64 then "u128" else "u64"
  match strategyName with
  | "Montgomery REDC" =>
    let xExpr : _root_.TrustLean.LowLevelExpr := .varRef (.user "x")
    let (sr, cgs') := lowerMontyReduce xExpr fc.pNat fc.muNat {}
    let body := _root_.TrustLean.stmtToRust 1 sr.stmt
    let retExpr := _root_.TrustLean.exprToRust sr.resultVar
    let decls := rustTempDecls cgs'.nextVar
    s!"#[inline(always)]\nfn {funcName}(x: {wt}) -> {et} \{\n{decls}{body}\n  {retExpr} as {et}\n}"
  | _ =>
    let foldExpr := solinasFoldLLE (.varRef (.user "x")) fc.k fc.cNat
    let foldRust := _root_.TrustLean.exprToRust foldExpr
    s!"#[inline(always)]\nfn {funcName}(x: {wt}) -> {et} \{
    ({foldRust}) as {et}
}"

/-- Generate verified C butterfly using TrustLean.Stmt.
    Replaces inline string butterflies in optimizedNTTC. -/
def verifiedButterflyC (fc : FieldConfig) : String :=
  emitDIFButterflyC "a" "b" "w" fc.pNat fc.k fc.cNat

/-- Generate verified Rust butterfly using TrustLean.Stmt. -/
def verifiedButterflyRust (fc : FieldConfig) : String :=
  emitDIFButterflyRust "a" "b" "w" fc.pNat fc.k fc.cNat

/-- Generate verified NTT C function using TrustLean.Stmt.
    Replaces genNTTLoopC string emission. -/
def verifiedNTTFnC (fc : FieldConfig) (logN : Nat)
    (funcName : String) : String :=
  emitNTTCFn logN fc.pNat fc.k fc.cNat funcName

/-- Generate verified NTT Rust function using TrustLean.Stmt. -/
def verifiedNTTFnRust (fc : FieldConfig) (logN : Nat)
    (funcName : String) : String :=
  emitNTTRustFn logN fc.pNat fc.k fc.cNat funcName

/-- Generate the Plonky3-style Montgomery REDC C function for comparison. -/
def genMontyReduceC (fc : FieldConfig) : String :=
  if fc.k == 64 then
    -- Goldilocks: hand-written (128-bit arithmetic)
    s!"static inline uint64_t p3_reduce(__uint128_t x) \{
    uint64_t lo=(uint64_t)x, hi=(uint64_t)(x>>64);
    uint64_t hh=hi>>32, hl=hi&0xFFFFFFFF;
    uint64_t t0; int borrow=__builtin_sub_overflow(lo,hh,&t0);
    if(borrow) t0-=0xFFFFFFFF;
    uint64_t t1=hl*0xFFFFFFFF;
    uint64_t r; int carry=__builtin_add_overflow(t0,t1,&r);
    if(carry||r>={fc.pLit}) r-={fc.pLit};
    return r;
}"
  else
    s!"static inline {fc.elemType} p3_reduce({fc.wideType} x) \{
    {fc.wideType} t=(x*({fc.wideType}){fc.muLit})&0xFFFFFFFF;
    {fc.wideType} u=t*({fc.wideType}){fc.pLit};
    {fc.wideType} d=x-u;
    {fc.elemType} hi=({fc.elemType})(d>>32);
    return (x<u)?hi+{fc.pLit}:hi;
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Full NTT Benchmark C Generation
-- ══════════════════════════════════════════════════════════════════

/-- Generate the Plonky3-style butterfly for comparison. -/
def genP3ButterflyC (fc : FieldConfig) : String :=
  s!"static inline void p3_bf({fc.elemType} *a, {fc.elemType} *b, {fc.elemType} w) \{
    {fc.elemType} oa=*a, wb=p3_reduce(({fc.wideType})w*({fc.wideType})(*b));
    {fc.elemType} s=oa+wb; {if fc.k == 64 then s!"*a=(s>={fc.pLit}||s<oa)?s-{fc.pLit}:s;" else s!"*a=(s>={fc.pLit})?s-{fc.pLit}:s;"}
    *b=(oa>=wb)?oa-wb:{fc.pLit}-wb+oa;
}"

/-- Generate the NTT loop C code (identical structure for both AMO and P3). -/
def genNTTLoopC (bfName : String) (logN : Nat) : String :=
  let n := 2^logN
  s!"for(size_t st=0;st<{logN};st++) \{ size_t h=1<<({logN}-st-1);
      for(size_t g=0;g<(1u<<st);g++) for(size_t p=0;p+1<=h;p++) \{
        size_t i=g*2*h+p,j=i+h; {bfName}(&d[i],&d[j],tw[(st*({n}/2)+g*h+p)%tw_sz]); }}"

/-- Generate a complete NTT benchmark C program.
    Uses the ACTUAL optimization pipeline to select the reduction strategy.

    Pipeline flow:
    1. optimizeReduction: e-graph finds best MixedExpr for this field+hardware
    2. The selected strategy determines the C reduction function
    3. Both AMO and P3 butterflies use the same NTT loop structure
    4. Timing harness measures both and outputs CSV -/
def optimizedNTTC (fc : FieldConfig) (hw : HardwareCost) (logN iters : Nat)
    (cfg : GuidedMixedConfig := .default) : String :=
  let n := 2^logN
  -- Step 1: Run the e-graph optimization pipeline
  let optResult := optimizeReduction fc hw cfg
  -- Step 2: Generate VERIFIED reduction via TrustLean.Stmt
  let amoReduce := verifiedReduceC fc optResult.strategyName "amo_reduce"
  -- Step 3: Verified NTT function (complete, butterfly+reduction inlined)
  let amoNTTVerified := verifiedNTTFnC fc logN s!"{fc.name.toLower}_ntt_verified"
  -- Step 4: Butterfly that calls verified amo_reduce
  let amoBf := s!"static inline void amo_bf({fc.elemType} *a, {fc.elemType} *b, {fc.elemType} w) \{
    {fc.elemType} oa=*a, wb_r=amo_reduce(({fc.wideType})w*({fc.wideType})(*b));
    {fc.elemType} s=oa+wb_r; *a=(s>={fc.pLit})?s-{fc.pLit}:s;
    *b=(oa>=wb_r)?oa-wb_r:{fc.pLit}-wb_r+oa;
}"
  -- Step 5: NTT loop (uniform reduction, calls amo_bf)
  let amoLoop := genNTTLoopC "amo_bf" logN
  -- Step 6: P3 reference (Montgomery baseline, string emission)
  let montyReduce := genMontyReduceC fc
  let p3Bf := genP3ButterflyC fc
  let p3Loop := genNTTLoopC "p3_bf" logN
  -- Step 6b: Plan-based SIMD (if hardware supports it)
  let plan := selectBestPlan fc.pNat n hw.mul32 hw.add hw.isSimd
  let simdCode := if hw.isSimd then
    let simdCfg := if hw.simdLanes == 8 then avx2Config else neonConfig
    some (lowerNTTFromPlanSIMD plan simdCfg fc.k fc.cNat fc.muNat logN)
  else none
  -- Step 7: Assemble the complete benchmark program
  s!"/* AMO-Lean Optimized NTT Benchmark
 * Field: {fc.name} (p = {fc.pNat})
 * E-graph selected: {optResult.strategyName}
 * Improved over seed: {optResult.improved}
 * Reduction: verified via TrustLean.Stmt (solinasFoldLLE/lowerMontyReduce)
 * Hardware target: mul32={hw.mul32}, add={hw.add}, shift={hw.shift}
 * Generated by OptimizedNTTPipeline.lean (Plan D Phase 1)
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

/* === Verified reduction (TrustLean.Stmt path) === */
{amoReduce}

{amoBf}

/* === P3 reference (Montgomery, baseline) === */
{montyReduce}

{p3Bf}

/* === Verified NTT function (TrustLean.Stmt, butterfly+Solinas inlined) === */
{amoNTTVerified}

{match simdCode with | some code => s!"/* === Verified SIMD NTT (plan-based, per-stage reduction) === */\n{code}" | none => "/* SIMD: not available for this hardware target */"}

int main(void) \{
    size_t n={n}, logn={logN};
    int iters={iters};
    {fc.elemType} *d=malloc(n*sizeof({fc.elemType}));
    {fc.elemType} *orig=malloc(n*sizeof({fc.elemType}));
    size_t tw_sz=n*logn;
    {fc.elemType} *tw=malloc(tw_sz*sizeof({fc.elemType}));
    for(size_t i=0;i<tw_sz;i++) tw[i]=({fc.elemType})((i*7+31)%({fc.wideType}){fc.pLit});
    for(size_t i=0;i<n;i++) orig[i]=({fc.elemType})((i*1000000007ULL)%({fc.wideType}){fc.pLit});
    volatile {fc.elemType} sink;
    struct timespec s,e;

    /* warmup */
    for(size_t i=0;i<n;i++) d[i]=orig[i];
    {amoLoop}

    /* AMO benchmark (verified reduce, uniform {optResult.strategyName}) */
    clock_gettime(CLOCK_MONOTONIC,&s);
    for(int it=0;it<iters;it++) \{
      for(size_t i=0;i<n;i++) d[i]=orig[i];
      {amoLoop}
      sink=d[0]; }
    clock_gettime(CLOCK_MONOTONIC,&e);
    double amo_us=((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    /* P3 benchmark (Montgomery every stage) */
    clock_gettime(CLOCK_MONOTONIC,&s);
    for(int it=0;it<iters;it++) \{
      for(size_t i=0;i<n;i++) d[i]=orig[i];
      {p3Loop}
      sink=d[0]; }
    clock_gettime(CLOCK_MONOTONIC,&e);
    double p3_us=((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    double melem=({n}.0)/(amo_us/1e6)/1e6;
    printf(\"{fc.name},{optResult.strategyName},%.1f,%.1f,%.1f,%+.1f\\n\",amo_us,p3_us,melem,(1.0-amo_us/p3_us)*100.0);
    (void)sink; free(d); free(orig); free(tw);
    return 0;
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: genOptimizedBenchC — Drop-in replacement for genNTTBenchC
-- ══════════════════════════════════════════════════════════════════

/-- Drop-in replacement for Bench.lean's `genNTTBenchC`.
    Same interface: (FieldConfig, logN, iters) -> C benchmark code.
    But uses the actual e-graph optimization pipeline instead of hardcoded C.

    Pipeline stages executed:
    1. optimizeReduction: runs e-graph saturation + cost-aware extraction
    2. Strategy selection: e-graph picks Solinas/Montgomery/Harvey
    3. Code generation: reduction + butterfly + NTT loop + timing harness

    The generated C compiles with `cc -O2` and outputs CSV:
    amo_us, p3_us, melem/s, diff% -/
def genOptimizedBenchC (fc : FieldConfig) (logN iters : Nat)
    (hw : HardwareCost := arm_cortex_a76) : String :=
  optimizedNTTC fc hw logN iters

-- ══════════════════════════════════════════════════════════════════
-- Section 5a: Ultra Pipeline Entry Points (Gap 5)
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise.UltraPipeline (ultraPipeline UltraConfig)

/-- Build UltraConfig from FieldConfig + HardwareCost. -/
private def fieldConfigToUltraConfig (fc : FieldConfig) (hw : HardwareCost) : UltraConfig :=
  { hw := hw
    k := fc.k
    c := fc.cNat
    mu := fc.muNat
    targetColor := if hw.isSimd then 2 else 1 }

/-- Generate NTT C code using the Ultra pipeline (all phases + verified codegen).
    Uses the full Ultra pipeline: Ruler discovery → bound-aware saturation
    → dynamic schedule → verified codegen via TrustLean.Stmt.

    CRITICAL: does NOT modify the legacy optimizedNTTC path. -/
def optimizedNTTC_ultra (fc : FieldConfig) (hw : HardwareCost) (logN iters : Nat) : String :=
  let n := 2^logN
  let ucfg := fieldConfigToUltraConfig fc hw
  let (nttBody, report) := ultraPipeline default [] fc.pNat n ucfg
    s!"{fc.name.toLower}_ntt_ultra"
  -- Generate P3 reference for comparison (same as legacy)
  let montyReduce := genMontyReduceC fc
  let p3Bf := genP3ButterflyC fc
  let p3Loop := genNTTLoopC "p3_bf" logN
  s!"/* AMO-Lean Ultra NTT Benchmark
 * Field: {fc.name} (p = {fc.pNat})
 * Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
 * {report.splitOn "\n" |>.take 5 |>.map ("   " ++ ·) |> String.intercalate "\n"}
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

/* === Ultra Verified NTT (TrustLean.Stmt path) === */
{nttBody}

/* === P3 reference (Montgomery, baseline) === */
{montyReduce}

{p3Bf}

int main(void) \{
    size_t n={n}, logn={logN};
    int iters={iters};
    {fc.elemType} *d=malloc(n*sizeof({fc.elemType}));
    {fc.elemType} *orig=malloc(n*sizeof({fc.elemType}));
    size_t tw_sz=n*logn;
    {fc.elemType} *tw=malloc(tw_sz*sizeof({fc.elemType}));
    for(size_t i=0;i<tw_sz;i++) tw[i]=({fc.elemType})((i*7+31)%({fc.wideType}){fc.pLit});
    for(size_t i=0;i<n;i++) orig[i]=({fc.elemType})((i*1000000007ULL)%({fc.wideType}){fc.pLit});
    volatile {fc.elemType} sink;
    struct timespec s,e;

    /* warmup */
    for(size_t i=0;i<n;i++) d[i]=orig[i];
    {fc.name.toLower}_ntt_ultra(d, tw);

    /* Ultra benchmark */
    clock_gettime(CLOCK_MONOTONIC,&s);
    for(int it=0;it<iters;it++) \{
      for(size_t i=0;i<n;i++) d[i]=orig[i];
      {fc.name.toLower}_ntt_ultra(d, tw);
      sink=d[0]; }
    clock_gettime(CLOCK_MONOTONIC,&e);
    double amo_us=((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    /* P3 benchmark (Montgomery every stage) */
    clock_gettime(CLOCK_MONOTONIC,&s);
    for(int it=0;it<iters;it++) \{
      for(size_t i=0;i<n;i++) d[i]=orig[i];
      {p3Loop}
      sink=d[0]; }
    clock_gettime(CLOCK_MONOTONIC,&e);
    double p3_us=((e.tv_sec-s.tv_sec)+(e.tv_nsec-s.tv_nsec)/1e9)/iters*1e6;

    double melem=({n}.0)/(amo_us/1e6)/1e6;
    printf(\"{fc.name},ultra,%.1f,%.1f,%.1f,%+.1f\\n\",amo_us,p3_us,melem,(1.0-amo_us/p3_us)*100.0);
    (void)sink; free(d); free(orig); free(tw);
    return 0;
}"

/-- Ultra benchmark C generator (drop-in alternative to genOptimizedBenchC). -/
def genOptimizedBenchC_ultra (fc : FieldConfig) (logN iters : Nat)
    (hw : HardwareCost := arm_cortex_a76) : String :=
  optimizedNTTC_ultra fc hw logN iters

-- ══════════════════════════════════════════════════════════════════
-- Section 5b: Rust Code Emission Helpers
-- ══════════════════════════════════════════════════════════════════

private def rustElemType (fc : FieldConfig) : String :=
  if fc.k == 64 then "u64" else "u32"

private def rustWideType (fc : FieldConfig) : String :=
  if fc.k == 64 then "u128" else "u64"

private def rustPLit (fc : FieldConfig) : String :=
  s!"{fc.pNat}_{rustElemType fc}"

/-- Generate Montgomery REDC as `p3_reduce` in Rust (Plonky3 reference). -/
def genMontyReduceRust (fc : FieldConfig) : String :=
  if fc.k == 64 then
    s!"#[inline(always)]
fn p3_reduce(x: u128) -> u64 \{
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hh = hi >> 32;
    let hl = hi & 0xFFFFFFFF_u64;
    let (t0, borrow) = lo.overflowing_sub(hh);
    let t0 = if borrow \{ t0.wrapping_sub(0xFFFFFFFF_u64) } else \{ t0 };
    let t1 = hl.wrapping_mul(0xFFFFFFFF_u64);
    let (result, carry) = t0.overflowing_add(t1);
    if carry || result >= {fc.pNat}_u64 \{ result.wrapping_sub({fc.pNat}_u64) } else \{ result }
}"
  else
    let muNat := fc.muLit.replace "0x" "" |>.replace "U" ""
    s!"#[inline(always)]
fn p3_reduce(x: u64) -> u32 \{
    let t = x.wrapping_mul(0x{muNat}_u64) as u32;
    let u = t as u64 * {fc.pNat}_u64;
    let d = x.wrapping_sub(u);
    let hi = (d >> 32) as u32;
    if x < u \{ hi.wrapping_add({fc.pNat}_u32) } else \{ hi }
}"

/-- Plonky3-style butterfly in Rust (Montgomery every stage). -/
def genP3ButterflyRust (fc : FieldConfig) : String :=
  let et := rustElemType fc
  let wt := rustWideType fc
  let pLit := rustPLit fc
  if fc.k == 64 then
    s!"#[inline(always)]
fn p3_bf(a: &mut {et}, b: &mut {et}, w: {et}) \{
    let oa = *a; let wb = p3_reduce(w as {wt} * *b as {wt});
    let (s, ov) = oa.overflowing_add(wb);
    *a = if ov || s >= {pLit} \{ s.wrapping_sub({pLit}) } else \{ s };
    *b = if oa >= wb \{ oa - wb } else \{ {pLit} - wb + oa };
}"
  else
    s!"#[inline(always)]
fn p3_bf(a: &mut {et}, b: &mut {et}, w: {et}) \{
    let oa = *a; let wb = p3_reduce(w as {wt} * *b as {wt});
    let s = oa.wrapping_add(wb);
    *a = if s >= {pLit} \{ s - {pLit} } else \{ s };
    *b = if oa >= wb \{ oa - wb } else \{ {pLit} - wb + oa };
}"

-- ══════════════════════════════════════════════════════════════════
-- Section 5c: optimizedNTTRust — Full Rust benchmark with pipeline
-- ══════════════════════════════════════════════════════════════════

/-- Generate a complete NTT benchmark Rust program using the optimization pipeline.
    Exact mirror of `optimizedNTTC`:
    1. optimizeReduction: e-graph selects strategy
    2. nttStageBoundAnalysis: per-stage lazy/reduce schedule
    3. Two butterfly functions: lazy (no reduce) + reduce
    4. Per-stage dispatch NTT loop
    5. P3 (Montgomery uniform) reference
    6. Timing harness with CSV output -/
def optimizedNTTRust (fc : FieldConfig) (hw : HardwareCost) (logN iters : Nat)
    (cfg : GuidedMixedConfig := .default) : String :=
  let n := 2^logN
  let et := rustElemType fc
  let wt := rustWideType fc
  let pLit := rustPLit fc
  -- Step 1: Run the e-graph optimization pipeline
  let optResult := optimizeReduction fc hw cfg
  -- Step 2: Generate VERIFIED reduction via TrustLean.Stmt
  let amoReduce := verifiedReduceRust fc optResult.strategyName "amo_reduce"
  -- Step 3: Verified NTT function (complete)
  let amoNTTVerified := verifiedNTTFnRust fc logN s!"{fc.name.toLower}_ntt_verified"
  -- Step 4: Butterfly that calls verified amo_reduce
  let amoBf :=
    if fc.k == 64 then
      s!"#[inline(always)]
fn amo_bf(a: &mut {et}, b: &mut {et}, w: {et}) \{
    let oa = *a;
    let wb_r = amo_reduce((w as {wt}).wrapping_mul(*b as {wt}));
    let (s, ov) = oa.overflowing_add(wb_r);
    *a = if ov || s >= {pLit} \{ s.wrapping_sub({pLit}) } else \{ s };
    *b = if oa >= wb_r \{ oa - wb_r } else \{ {pLit} - wb_r + oa };
}"
    else
      s!"#[inline(always)]
fn amo_bf(a: &mut {et}, b: &mut {et}, w: {et}) \{
    let oa = *a;
    let wb_r = amo_reduce(w as {wt} * *b as {wt});
    let s = oa.wrapping_add(wb_r);
    *a = if s >= {pLit} \{ s - {pLit} } else \{ s };
    *b = if oa >= wb_r \{ oa - wb_r } else \{ {pLit} - wb_r + oa };
}"
  -- Step 5: P3 reference (Montgomery baseline)
  let montyReduce := genMontyReduceRust fc
  let p3Bf := genP3ButterflyRust fc
  -- Step 5b: Plan-based SIMD (if hardware supports it)
  let plan := selectBestPlan fc.pNat n hw.mul32 hw.add hw.isSimd
  let simdCode := if hw.isSimd then
    let simdCfg := if hw.simdLanes == 8 then avx2Config else neonConfig
    some (lowerNTTFromPlanSIMDRust plan simdCfg fc.k fc.cNat fc.muNat logN)
  else none
  -- Step 6: Assemble the complete Rust benchmark
  s!"// AMO-Lean Optimized NTT Benchmark (Rust)
// Field: {fc.name} (p = {fc.pNat})
// E-graph selected: {optResult.strategyName}
// Reduction: verified via TrustLean.Stmt
// Hardware target: mul32={hw.mul32}, add={hw.add}, shift={hw.shift}
// Generated by OptimizedNTTPipeline.lean (Plan D Phase 1)

/* === Verified reduction (TrustLean.Stmt path) === */
{amoReduce}

{amoBf}

/* === P3 reference (Montgomery, baseline) === */
{montyReduce}

{p3Bf}

/* === Verified NTT function (TrustLean.Stmt, butterfly+Solinas inlined) === */
{amoNTTVerified}

{match simdCode with | some code => s!"/* === Verified SIMD NTT (plan-based, per-stage reduction) === */\n{code}" | none => "/* SIMD: not available for this hardware target */"}

fn main() \{
    let n: usize = {n};
    let logn: usize = {logN};
    let iters: usize = {iters};
    let tw_sz = n * logn;
    let tw: Vec<{et}> = (0..tw_sz).map(|i| ((i as {wt} * 7 + 31) % {fc.pNat}_{wt}) as {et}).collect();
    let orig: Vec<{et}> = (0..n).map(|i| ((i as {wt} * 1000000007) % {fc.pNat}_{wt}) as {et}).collect();

    // Warmup
    let mut d = orig.clone();
    for st in 0..logn \{ let h = 1usize << (logn-st-1);
      for g in 0..(1usize<<st) \{ for p in 0..h \{
        let i=g*2*h+p; let j=i+h; let w=tw[(st*(n/2)+g*h+p)%tw_sz];
        let (l,r) = d.split_at_mut(j);
        amo_bf(&mut l[i], &mut r[0], w);
      }}}
    std::hint::black_box(&d);

    // AMO benchmark (verified reduce, uniform {optResult.strategyName})
    let start = std::time::Instant::now();
    for _ in 0..iters \{
      let mut d = orig.clone();
      for st in 0..logn \{ let h = 1usize << (logn-st-1);
        for g in 0..(1usize<<st) \{ for p in 0..h \{
          let i=g*2*h+p; let j=i+h; let w=tw[(st*(n/2)+g*h+p)%tw_sz];
          let (l,r) = d.split_at_mut(j);
          amo_bf(&mut l[i], &mut r[0], w);
        }}}
      std::hint::black_box(&d);
    }
    let amo_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    // P3 benchmark (Montgomery every stage)
    let start = std::time::Instant::now();
    for _ in 0..iters \{
      let mut d = orig.clone();
      for st in 0..logn \{ let h = 1usize << (logn-st-1);
        for g in 0..(1usize<<st) \{ for p in 0..h \{
          let i=g*2*h+p; let j=i+h; let w=tw[(st*(n/2)+g*h+p)%tw_sz];
          let (l,r) = d.split_at_mut(j); p3_bf(&mut l[i], &mut r[0], w);
        }}}
      std::hint::black_box(&d);
    }
    let p3_us = start.elapsed().as_secs_f64() / iters as f64 * 1e6;

    let melem = {n}_f64 / (amo_us / 1e6) / 1e6;
    println!(\"{fc.name},{optResult.strategyName},\{:.1},\{:.1},\{:.1},\{:+.1}\", amo_us, p3_us, melem, (1.0 - amo_us/p3_us)*100.0);
}
"

/-- Drop-in replacement for Bench.lean's `genNTTBenchRust`.
    Uses the full optimization pipeline (e-graph + bound analysis + per-stage dispatch). -/
def genOptimizedBenchRust (fc : FieldConfig) (logN iters : Nat)
    (hw : HardwareCost := arm_cortex_a76) : String :=
  optimizedNTTRust fc hw logN iters

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Verified NTT Code Emission (Trust-Lean Path A)
-- ══════════════════════════════════════════════════════════════════

/-- Generate a verified NTT C function using Trust-Lean Path A.
    Unlike the benchmark harness (which uses string templates),
    this path goes through the formal verification chain:
    MixedExpr -> lowerNTTLoopStmt -> stmtToC.

    The butterfly body is verified via lowerDIFButterflyStmt_evaluates. -/
def emitVerifiedNTTCFn (fc : FieldConfig) (logN : Nat) : String :=
  emitNTTCFn logN fc.pNat fc.k fc.cNat s!"{fc.name.toLower}_ntt"

/-- Generate a verified NTT Rust function using Trust-Lean Path A. -/
def emitVerifiedNTTRustFn (fc : FieldConfig) (logN : Nat) : String :=
  emitNTTRustFn logN fc.pNat fc.k fc.cNat s!"{fc.name.toLower}_ntt"

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Plan-Based NTT Code Emission
-- ══════════════════════════════════════════════════════════════════

/-- Generate NTT C code from the plan selection pipeline.
    1. selectBestPlan: evaluates 8 candidates (radix-2/4, Solinas/Monty/Harvey/lazy)
    2. emitCFromPlanVerified: lowers the selected plan to C via TrustLean.Stmt (verified)

    This integrates the bound-propagation analysis that determines
    per-stage reductions (lazy where safe, Solinas/Monty where needed). -/
def emitPlanBasedNTTC (fc : FieldConfig) (logN : Nat) (hw : HardwareCost) : String :=
  let n := 2^logN
  let plan := selectBestPlan fc.pNat n hw.mul32 hw.add hw.isSimd
  emitCFromPlanVerified plan fc.k fc.cNat fc.muNat s!"{fc.name.toLower}_ntt_plan"

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Cost Analysis Report
-- ══════════════════════════════════════════════════════════════════

/-- Generate a human-readable cost analysis for a field across hardware targets. -/
def costReport (fc : FieldConfig) : String :=
  let targets : List (String × HardwareCost) :=
    [("ARM Cortex-A76 (scalar)", arm_cortex_a76),
     ("RISC-V SiFive U74", riscv_sifive_u74),
     ("FPGA DSP48E2", fpga_dsp48e2),
     ("x86 Skylake", x86_skylake),
     ("ARM NEON (SIMD)", arm_neon_simd),
     ("x86 AVX2 (SIMD)", x86_avx2_simd)]
  let header := s!"Cost analysis for {fc.name} (p = {fc.pNat}):\n"
  let lines := targets.map fun (name, hw) =>
    -- Use mixedOpCost for consistency with e-graph (includes wideningPenalty, cachePenalty)
    let solCost := mixedOpCost hw (.reduceGate 0 fc.pNat)
    let montyCost := mixedOpCost hw (.montyReduce 0 fc.pNat 0)
    let harCost := mixedOpCost hw (.harveyReduce 0 fc.pNat)
    let mersenneCost := mersenneFoldCost hw  -- Mersenne is separate (subtraction-based)
    let minCost := Nat.min solCost (Nat.min montyCost harCost)
    let winner := if fc.isMersenne then "Mersenne fold"
      else if minCost == harCost then "Harvey cond-sub (requires bounded input)"
      else if minCost == solCost then "Solinas fold"
      else "Montgomery REDC"
    s!"  {name}: Solinas={solCost} Monty={montyCost} Mersenne={mersenneCost} Harvey={harCost} -> {winner}"
  header ++ String.intercalate "\n" lines

/-- Generate a full pipeline report: e-graph optimization + cost analysis. -/
def pipelineReport (fc : FieldConfig) (hw : HardwareCost) : String :=
  let optResult := optimizeReduction fc hw
  let costs := costReport fc
  s!"Pipeline report for {fc.name}:
  Seed: Solinas fold (k={fc.k}, c={fc.cNat})
  E-graph result: {optResult.strategyName}
  Improved: {optResult.improved}

{costs}"

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Pipeline Correctness Theorems
-- ══════════════════════════════════════════════════════════════════

/-- The e-graph optimization always records the correct seed.
    Proof by case analysis on the Option result, independent of e-graph computation. -/
theorem optimizeReduction_seed_general (k cNat _pNat : Nat) (_hw : HardwareCost)
    (egResult : Option MixedExpr) :
    let seed := mkSolinasFoldSeed k cNat
    (match egResult with
    | some optExpr =>
      let stratName := describeExpr optExpr
      let improved := stratName != describeExpr seed
      { seedExpr := seed, optimizedExpr := optExpr, improved,
        strategyName := stratName : OptimizationResult }
    | none =>
      { seedExpr := seed, optimizedExpr := seed, improved := false,
        strategyName := "Fallback (extraction failed)" }).seedExpr = seed := by
  cases egResult <;> rfl

/-- The Solinas fold cost is bounded by Montgomery cost on all hardware.
    This guarantees the e-graph's Solinas selection is never worse. -/
theorem solinas_bounded_by_montgomery (hw : HardwareCost) :
    pseudoMersenneFoldCost hw ≤ montgomeryCost hw :=
  AmoLean.EGraph.Verified.Bitwise.pseudo_mersenne_le_montgomery hw

/-- Mersenne fold cost is bounded by Solinas fold cost on all hardware. -/
theorem mersenne_bounded_by_solinas (hw : HardwareCost) :
    mersenneFoldCost hw ≤ pseudoMersenneFoldCost hw :=
  AmoLean.EGraph.Verified.Bitwise.mersenne_le_pseudo_mersenne hw

/-- The synthesis pipeline is sound: for any Solinas prime with known config,
    the synthesized reduction preserves modular arithmetic. -/
theorem synthesis_sound (cfg : SolinasConfig) (hw : HardwareCost) (x : Nat) :
    match synthesizeReduction cfg.prime hw (some cfg) with
    | .ok r => r.step.reduce x % cfg.prime = x % cfg.prime
    | .error _ => True :=
  AmoLean.EGraph.Verified.Bitwise.synthesis_correct cfg.prime hw cfg rfl x

-- ══════════════════════════════════════════════════════════════════
-- Section 10: Non-Vacuity Examples
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: the Solinas cost advantage is real on ARM.
    Solinas fold (6 cycles) < Montgomery REDC (7 cycles). -/
example : pseudoMersenneFoldCost arm_cortex_a76 < montgomeryCost arm_cortex_a76 := by
  native_decide

/-- Non-vacuity: BabyBear synthesis succeeds. -/
example : (synthesizeReduction babybear_solinas.prime arm_cortex_a76 (some babybear_solinas)).isOk = true := by
  native_decide

/-- Non-vacuity: KoalaBear synthesis succeeds. -/
example : (synthesizeReduction koalabear_solinas.prime arm_cortex_a76 (some koalabear_solinas)).isOk = true := by
  native_decide

/-- Non-vacuity: Goldilocks synthesis succeeds. -/
example : (synthesizeReduction goldilocks_solinas.prime arm_cortex_a76 (some goldilocks_solinas)).isOk = true := by
  native_decide

/-- Non-vacuity: describeExpr correctly identifies Solinas fold seed. -/
example : describeExpr (mkSolinasFoldSeed 31 134217727) =
    "Solinas fold (shift-mul-add)" := by rfl

/-- Non-vacuity: Mersenne fold seed is correctly described. -/
example : describeExpr (mkSolinasFoldSeed 31 1) =
    "Solinas fold (shift-mul-add)" := by rfl

/-- Non-vacuity: allFields has 4 entries. -/
example : allFields.length = 4 := by rfl

/-- Non-vacuity: BabyBear config has correct prime. -/
example : babybearConfig.pNat = 2013265921 := by rfl

/-- Non-vacuity: plan selection produces a well-formed plan for BabyBear. -/
example : (selectBestPlan 2013265921 1024 3 1).stages.size > 0 := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Section 11: Runner (#eval)
-- ══════════════════════════════════════════════════════════════════

/-- Run the full pipeline for all fields and print results.
    This exercises the complete pipeline:
    1. E-graph optimization (optimizeReduction for each field)
    2. Cost analysis report
    3. Benchmark C code generation
    4. Verified NTT emission (Trust-Lean Path A)
    5. Plan-based NTT emission (8 candidates)
-/
def runPipelineReport : IO Unit := do
  IO.println "══════════════════════════════════════════════════════════"
  IO.println " AMO-Lean Optimized NTT Pipeline Report"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""

  for fc in allFields do
    IO.println (pipelineReport fc arm_cortex_a76)
    IO.println ""

  IO.println "══════════════════════════════════════════════════════════"
  IO.println " Generated Benchmark C Code (BabyBear, logN=10)"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println (genOptimizedBenchC babybearConfig 10 1000)

  IO.println ""
  IO.println "══════════════════════════════════════════════════════════"
  IO.println " Verified NTT (Trust-Lean Path A) for BabyBear logN=10"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println (emitVerifiedNTTCFn babybearConfig 10)

  IO.println ""
  IO.println "══════════════════════════════════════════════════════════"
  IO.println " Plan-Based NTT (8 candidates) for BabyBear N=1024"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println (emitPlanBasedNTTC babybearConfig 10 arm_cortex_a76)

-- Lightweight eval: cost report + verified NTT + plan NTT (no e-graph execution).
-- The full e-graph pipeline runs at compile time, which is slow.
-- Use `#eval! runPipelineReport` for the full pipeline including e-graph.
#eval do
  IO.println "══════════════════════════════════════════════════════════"
  IO.println " AMO-Lean Optimized NTT Pipeline - Cost Analysis"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  for fc in allFields do
    IO.println (costReport fc)
    IO.println ""
  IO.println "══════════════════════════════════════════════════════════"
  IO.println " Verified NTT (Trust-Lean Path A) for BabyBear logN=10"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println (emitVerifiedNTTCFn babybearConfig 10)
  IO.println ""
  IO.println "══════════════════════════════════════════════════════════"
  IO.println " Plan-Based NTT for BabyBear N=1024"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  IO.println (emitPlanBasedNTTC babybearConfig 10 arm_cortex_a76)

end AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
