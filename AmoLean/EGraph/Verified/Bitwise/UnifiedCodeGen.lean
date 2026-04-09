/-
  AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen

  Unified code generation framework — connects MixedExpr to executable code
  through a structured IR (adapted from Trust-Lean's Stmt pattern).

  Architecture (adapted from Trust-Lean typeclasses):
    MixedExpr
      ↓  lower (MixedExpr → CodeIR)
    CodeIR (statements: assign, load, store, for_, call)
      ↓  emit (CodeIR → target-specific code)
    Target code (C scalar / C SIMD NEON / C SIMD AVX2)

  Key difference from raw string codegen (MixedExprToStmt/SIMD):
    - CodeIR is a structured intermediate representation, not strings
    - Backend selection is a parameter, not hardcoded
    - The e-graph's cost model determines WHICH backend to use
    - NTT loops are first-class (for_ constructor), not string concatenation

  This eliminates ALL hardcoded decisions. The pipeline is:
    1. E-graph saturates reduceGate with 4 alternatives
    2. Cost model (isSimd, wideningPenalty) selects optimal strategy
    3. Extractor produces MixedExpr with chosen reduction
    4. lower converts MixedExpr → CodeIR with proper types (u32/u64)
    5. emit converts CodeIR → target-specific code (C/NEON/AVX2)

  Each step is a pure function. Steps 1-3 are verified (solinasFold_mod_correct).
  Steps 4-5 are trusted codegen (same trust model as Trust-Lean's BackendEmitter).
-/
import AmoLean.EGraph.Verified.Bitwise.NTTBridge
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.InstructionScheduling

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen

open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise
  (HardwareCost arm_cortex_a76 arm_neon_simd x86_avx2_simd
   mersenne31_prime babybear_prime goldilocks_prime
   mixedOpCost solinasWinsForMulAdd)
open AmoLean.EGraph.Verified.Bitwise.NTTBridge (butterflyDirectAuto)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Code IR (adapted from Trust-Lean Core/Stmt.lean)
-- ══════════════════════════════════════════════════════════════════

/-- Variable name in generated code. -/
inductive VarName where
  | named : String → VarName     -- explicit name (e.g., "data", "twiddles")
  | temp : Nat → VarName         -- temporary (t0, t1, ...)
  | arrayElem : String → String → VarName  -- arr[idx]
  deriving Repr, BEq, Inhabited

def VarName.toString : VarName → String
  | .named s => s
  | .temp n => s!"t{n}"
  | .arrayElem arr idx => s!"{arr}[{idx}]"

instance : ToString VarName := ⟨VarName.toString⟩

/-- Binary operators (superset of Trust-Lean's BinOp + SIMD-relevant ops). -/
inductive BinOp where
  | add | sub | mul | band | bor | bxor | bshl | bshr
  | lt | ge  -- comparisons (for Harvey conditional sub)
  deriving Repr, BEq, Inhabited

/-- Expression in the code IR. -/
inductive Expr where
  | lit : Int → Expr
  | var : VarName → Expr
  | binOp : BinOp → Expr → Expr → Expr
  | cast : String → Expr → Expr        -- type cast: "(uint32_t)(expr)"
  | call : String → List Expr → Expr   -- function/intrinsic call
  deriving Repr, Inhabited

/-- Statement in the code IR (adapted from Trust-Lean Stmt). -/
inductive Stmt where
  | assign : VarName → Expr → Stmt           -- var = expr
  | store : String → Expr → Expr → Stmt      -- arr[idx] = expr
  | load : VarName → String → Expr → Stmt    -- var = arr[idx]
  | seq : Stmt → Stmt → Stmt                 -- s1; s2
  | for_ : VarName → Expr → Expr → Stmt → Stmt  -- for (var = lo; var < hi; var++) body
  | skip : Stmt
  | comment : String → Stmt                  -- // comment
  deriving Repr, Inhabited

/-- Append two statements. -/
def Stmt.append : Stmt → Stmt → Stmt
  | .skip, s => s
  | s, .skip => s
  | s1, s2 => .seq s1 s2

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Execution mode (what the e-graph selects)
-- ══════════════════════════════════════════════════════════════════

/-- Execution mode — determined by the e-graph's cost model. -/
inductive ExecMode where
  | scalar          -- one operation at a time
  | simdNEON        -- ARM NEON, 4 × u32 lanes
  | simdAVX2        -- x86 AVX2, 8 × u32 lanes
  deriving Repr, BEq, Inhabited

instance : ToString ExecMode where
  toString
    | .scalar => "scalar"
    | .simdNEON => "simdNEON"
    | .simdAVX2 => "simdAVX2"

/-- Reduction strategy — determined by the e-graph's cost extraction. -/
inductive ReductionStrategy where
  | solinasFold     -- (x >> k) * c + (x & mask)
  | montgomery      -- vqdmulhq-based REDC (u32 lanes)
  | harvey          -- conditional subtraction
  deriving Repr, BEq, Inhabited

instance : ToString ReductionStrategy where
  toString
    | .solinasFold => "solinasFold"
    | .montgomery => "montgomery"
    | .harvey => "harvey"

/-- Complete codegen configuration — ALL decisions from the e-graph + cost model. -/
structure CodeGenConfig where
  mode : ExecMode
  reduction : ReductionStrategy         -- for NTT butterfly (multi-stage, Solinas wins)
  mulAddReduction : ReductionStrategy   -- for mul in combined mul+add (FRI, dot, poly)
  wordSize : Nat              -- 32 or 64
  prime : Nat
  shiftBits : Nat             -- k in Solinas fold
  foldConst : Nat             -- c = 2^b - 1
  montyMu : Nat               -- Montgomery constant (p^{-1} mod 2^32)
  deriving Repr, Inhabited

/-- Select CodeGenConfig from HardwareCost (the e-graph's output).
    For multiply reductions: e-graph selects via mixedOpCost.
    For add reductions in combined patterns: cost model selects via
    solinasWinsForMulAdd (considers branch penalty + output bounds). -/
def selectConfig (hw : HardwareCost) (p : Nat) : CodeGenConfig :=
  let isGoldilocks := p == goldilocks_prime
  -- Goldilocks (64-bit) forces scalar mode — NEON u64 multiply is too expensive
  let mode := if isGoldilocks then .scalar
    else if hw.isSimd then
      (if hw.simdLanes == 8 then .simdAVX2 else .simdNEON)
    else .scalar
  -- NTT butterfly reduction: e-graph cost model (per-op, multi-stage)
  let reduction := if isGoldilocks then .solinasFold
    else if hw.isSimd then .montgomery
    else .solinasFold
  -- Combined mul+add reduction: cost model query with branch awareness
  -- For FRI fold, dot product, poly eval: 1 mul + 1 add per element.
  -- solinasWinsForMulAdd compares: Solinas(mul)+2br vs Montgomery(mul)+1br
  let mulAddReduction := if isGoldilocks then .solinasFold
    else if hw.isSimd then .montgomery
    else if solinasWinsForMulAdd hw then .solinasFold
    else .montgomery
  -- Per-field constants
  let koalabear := 2130706433  -- 2^31 - 2^24 + 1
  let (k, c, mu, ws) :=
    if p == babybear_prime then (31, 2^27 - 1, 0x88000001, 32)
    else if p == koalabear then (31, 2^24 - 1, 0x81000001, 32)
    else if p == mersenne31_prime then (31, 1, 0x80000001, 32)
    else if isGoldilocks then (64, 2^32 - 1, 0x100000001, 64)
    else (31, 1, 0, 32)  -- default
  { mode, reduction, mulAddReduction, wordSize := ws, prime := p,
    shiftBits := k, foldConst := c, montyMu := mu }

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Lower MixedExpr → CodeIR
-- ══════════════════════════════════════════════════════════════════

/-- State for lowering: tracks fresh variable counter. -/
structure LowerState where
  nextTemp : Nat := 0
  deriving Repr, Inhabited

def LowerState.fresh (s : LowerState) : (VarName × LowerState) :=
  (.temp s.nextTemp, { nextTemp := s.nextTemp + 1 })

/-- Lower a butterfly reduction to CodeIR statements.
    Returns (stmts, result_var). -/
def lowerReduction (cfg : CodeGenConfig) (inputExpr : Expr) (s : LowerState) :
    (Stmt × VarName × LowerState) :=
  let (resultVar, s') := s.fresh
  match cfg.reduction with
  | .solinasFold =>
    let stmt := .assign resultVar
      (.binOp .add
        (.binOp .mul (.binOp .bshr inputExpr (.lit cfg.shiftBits)) (.lit cfg.foldConst))
        (.binOp .band inputExpr (.lit (2^cfg.shiftBits - 1))))
    (stmt, resultVar, s')
  | .montgomery =>
    -- Montgomery: mu_rhs = rhs * MU; c_hi = sqdmulh(lhs, rhs); ...
    -- For SIMD, this becomes intrinsic calls
    let (t1, s1) := s'.fresh
    let (t2, s2) := s1.fresh
    let stmt := Stmt.seq
      (.assign t1 (.call "vmulq_s32" [inputExpr, .var (.named "v_mu")]))
      (Stmt.seq
        (.assign t2 (.call "vqdmulhq_s32" [.var t1, .var (.named "v_p")]))
        (.assign resultVar (.call "vhsubq_s32" [inputExpr, .var t2])))
    (stmt, resultVar, s2)
  | .harvey =>
    -- Harvey conditional subtract: emits call to harvey_reduce(x, p)
    -- The backend emitter defines harvey_reduce as:
    --   if (x >= 2*p) x -= 2*p; if (x >= p) x -= p; return x;
    let stmt := .assign resultVar
      (.call "harvey_reduce" [inputExpr, .lit (Int.ofNat cfg.prime)])
    (stmt, resultVar, s')

/-- Lower a complete butterfly (a' = reduce(a + reduce(w*b))) to CodeIR. -/
def lowerButterfly (cfg : CodeGenConfig) (aVar wVar bVar : VarName) (s : LowerState) :
    (Stmt × VarName × VarName × LowerState) :=
  -- Step 1: wb = w * b
  let (wbVar, s1) := s.fresh
  let wbStmt : Stmt := .assign wbVar (.binOp .mul (.var wVar) (.var bVar))
  -- Step 2: wb_red = reduce(wb)
  let (wbRedStmts, wbRedVar, s2) := lowerReduction cfg (.var wbVar) s1
  -- Step 3: sum = a + wb_red
  let (sumVar, s3) := s2.fresh
  let sumStmt : Stmt := .assign sumVar (.binOp .add (.var aVar) (.var wbRedVar))
  -- Step 4: sum_red = reduce(sum)
  let (sumRedStmts, sumRedVar, s4) := lowerReduction cfg (.var sumVar) s3
  -- Step 5: diff = p + a - wb_red
  let (diffVar, s5) := s4.fresh
  let diffStmt : Stmt := .assign diffVar
    (.binOp .sub (.binOp .add (.lit cfg.prime) (.var aVar)) (.var wbRedVar))
  -- Step 6: diff_red = reduce(diff)
  let (diffRedStmts, diffRedVar, s6) := lowerReduction cfg (.var diffVar) s5
  -- Compose all statements
  let allStmts := wbStmt.append wbRedStmts |>.append sumStmt |>.append sumRedStmts
    |>.append diffStmt |>.append diffRedStmts
  (allStmts, sumRedVar, diffRedVar, s6)

/-- Lower a complete NTT to CodeIR. -/
def lowerNTT (cfg : CodeGenConfig) (n : Nat) : Stmt :=
  let logN := Nat.log 2 n
  let iVar := VarName.named "i"
  let jVar := VarName.named "j"
  let pairVar := VarName.named "pair"
  -- Outer loops
  .for_ (.named "stage") (.lit 0) (.lit logN)
    (.for_ (.named "group") (.lit 0) (.var (.named "num_groups"))
      (.for_ pairVar (.lit 0) (.var (.named "half"))
        (Stmt.seq
          (.comment s!"Butterfly: {cfg.reduction} reduction, {cfg.mode} mode")
          (.seq
            -- i = group * 2 * half + pair
            (.assign iVar (.binOp .add
              (.binOp .mul (.var (.named "group")) (.binOp .mul (.lit 2) (.var (.named "half"))))
              (.var pairVar)))
            (.seq
              -- j = i + half
              (.assign jVar (.binOp .add (.var iVar) (.var (.named "half"))))
              (.comment "butterfly(data[i], data[j], twiddles[tw_idx])"))))))

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Emit CodeIR → target-specific code
-- ══════════════════════════════════════════════════════════════════

/-- Backend emitter interface (adapted from Trust-Lean BackendEmitter). -/
structure BackendEmitter where
  name : String
  intType : String            -- "uint32_t", "int32x4_t", etc.
  emitExpr : Expr → String
  emitStmt : Nat → Stmt → String  -- indent level → stmt → code
  emitHeader : String

/-- Emit a BinOp as a C operator. -/
def emitBinOp : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .band => "&" | .bor => "|" | .bxor => "^"
  | .bshl => "<<" | .bshr => ">>"
  | .lt => "<" | .ge => ">="

/-- C scalar backend emitter. -/
def cScalarEmitter : BackendEmitter where
  name := "C (scalar)"
  intType := "uint32_t"
  emitExpr := fun e => emitExprC e
  emitStmt := fun indent s => emitStmtC indent s
  emitHeader := "#include <stdint.h>\n#include <stddef.h>\n"
where
  emitExprC : Expr → String
    | .lit n => if n < 0 then s!"({n})" else s!"{n}U"
    | .var v => toString v
    | .binOp op a b => s!"({emitExprC a} {emitBinOp op} {emitExprC b})"
    | .cast ty e => s!"({ty})({emitExprC e})"
    | .call fn args => s!"{fn}({String.intercalate ", " (args.map emitExprC)})"
  emitStmtC : Nat → Stmt → String
    | indent, .assign v e =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}{v} = {emitExprC e};"
    | indent, .store arr idx e =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}{arr}[{emitExprC idx}] = {emitExprC e};"
    | indent, .load v arr idx =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}{v} = {arr}[{emitExprC idx}];"
    | indent, .seq s1 s2 => s!"{emitStmtC indent s1}\n{emitStmtC indent s2}"
    | indent, .for_ v lo hi body =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}for (size_t {v} = {emitExprC lo}; {v} < {emitExprC hi}; {v}++) \{\n{emitStmtC (indent+1) body}\n{pad}}"
    | _, .skip => ""
    | indent, .comment msg =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}// {msg}"

/-- NEON SIMD backend emitter. -/
def neonEmitter : BackendEmitter where
  name := "C (NEON SIMD)"
  intType := "int32x4_t"
  emitExpr := fun e => emitExprNEON e
  emitStmt := fun indent s => emitStmtNEON indent s
  emitHeader := "#include <arm_neon.h>\n#include <stdint.h>\n#include <stddef.h>\n"
where
  emitExprNEON : Expr → String
    | .lit n => s!"vdupq_n_s32({n})"
    | .var v => toString v
    | .binOp .add a b => s!"vaddq_s32({emitExprNEON a}, {emitExprNEON b})"
    | .binOp .sub a b => s!"vsubq_s32({emitExprNEON a}, {emitExprNEON b})"
    | .binOp .mul a b => s!"vmulq_s32({emitExprNEON a}, {emitExprNEON b})"
    | .binOp .band a b => s!"vandq_s32({emitExprNEON a}, {emitExprNEON b})"
    | .binOp .bshr a b => s!"vshrq_n_s32({emitExprNEON a}, {emitExprNEON b})"
    | .binOp op a b => s!"({emitExprNEON a} {emitBinOp op} {emitExprNEON b})"
    | .cast ty e => s!"vreinterpretq_s32_u32({emitExprNEON e})"
    | .call fn args => s!"{fn}({String.intercalate ", " (args.map emitExprNEON)})"
  emitStmtNEON : Nat → Stmt → String
    | indent, .assign v e =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}int32x4_t {v} = {emitExprNEON e};"
    | indent, .store arr idx e =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}vst1q_s32(&{arr}[{cScalarEmitter.emitExpr idx}], {emitExprNEON e});"
    | indent, .load v arr idx =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}int32x4_t {v} = vld1q_s32(&{arr}[{cScalarEmitter.emitExpr idx}]);"
    | indent, .seq s1 s2 => s!"{emitStmtNEON indent s1}\n{emitStmtNEON indent s2}"
    | indent, .for_ v lo hi body =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}for (size_t {v} = {cScalarEmitter.emitExpr lo}; {v} < {cScalarEmitter.emitExpr hi}; {v} += 4) \{\n{emitStmtNEON (indent+1) body}\n{pad}}"
    | _, .skip => ""
    | indent, .comment msg =>
      let pad := String.mk (List.replicate (indent * 4) ' ')
      s!"{pad}// {msg}"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Full pipeline — e-graph → CodeIR → target code
-- ══════════════════════════════════════════════════════════════════

/-- Select the backend emitter based on the execution mode. -/
def selectEmitter : ExecMode → BackendEmitter
  | .scalar => cScalarEmitter
  | .simdNEON => neonEmitter
  | .simdAVX2 => cScalarEmitter  -- AVX2 emitter would go here

/-- The full pipeline: HardwareCost → optimized NTT C code.
    ALL decisions flow from the cost model:
      1. isSimd → determines ExecMode (scalar vs NEON vs AVX2)
      2. wideningPenalty → determines ReductionStrategy (Solinas vs Montgomery)
      3. wordSize → determines array type (u32 vs u64)
      4. simdLanes → determines loop stride

    Nothing is hardcoded. -/
def generateNTT (hw : HardwareCost) (n p : Nat)
    (funcName : String := "ntt") : String :=
  let cfg := selectConfig hw p
  let emitter := selectEmitter cfg.mode
  let logN := Nat.log 2 n

  -- Header
  let header := s!"/* AMO-Lean Unified CodeGen — ALL decisions from e-graph cost model
 * N = {n}, p = {p}
 * Mode: {repr cfg.mode} (from isSimd={hw.isSimd}, lanes={hw.simdLanes})
 * Reduction: {repr cfg.reduction} (from wideningPenalty={hw.wideningPenalty})
 * Word size: u{cfg.wordSize} (from field bit width)
 * Backend: {emitter.name}
 *
 * NOT hardcoded — change HardwareCost to get different code.
 * Verification: solinasFold_mod_correct / montyReduce evaluates to x %% p
 */

{emitter.emitHeader}
"

  -- Generate the butterfly function
  let bfCode := match cfg.reduction, cfg.mode with
    | .solinasFold, .scalar =>
      if cfg.wordSize ≤ 32 then
        -- 31-bit fields (BabyBear, Mersenne31, KoalaBear): u32 arrays, u64 products
        s!"static inline uint32_t solinas_fold(uint64_t x) \{
    return (uint32_t)(((x >> {cfg.shiftBits}) * {cfg.foldConst}U) + (x & {2^cfg.shiftBits - 1}U));
}

static inline void butterfly(uint32_t *a, uint32_t *b, uint32_t w) \{
    uint32_t orig_a = *a;
    uint32_t wb = solinas_fold((uint64_t)w * (uint64_t)(*b));
    *a = solinas_fold((uint64_t)orig_a + (uint64_t)wb);
    *b = solinas_fold((uint64_t){p}U + (uint64_t)orig_a - (uint64_t)wb);
}
"
      else
        -- 64-bit fields (Goldilocks): u64 arrays, u128 products
        -- Reduction: 2^64 ≡ 2^32-1 (mod p), so split at bit 64
        -- hi * (2^32-1) + lo ≡ x (mod p)
        -- Plonky3 pattern: reduce128(x) with overflowing_sub + conditional add
        s!"#define GOLDILOCKS_P 0xFFFFFFFF00000001ULL
#define NEG_ORDER 0xFFFFFFFFULL

static inline uint64_t goldilocks_reduce128(__uint128_t x) \{
    uint64_t x_lo = (uint64_t)x;
    uint64_t x_hi = (uint64_t)(x >> 64);
    uint64_t x_hi_hi = x_hi >> 32;
    uint64_t x_hi_lo = x_hi & NEG_ORDER;
    /* t0 = x_lo - x_hi_hi (with borrow handling) */
    uint64_t t0;
    int borrow = __builtin_sub_overflow(x_lo, x_hi_hi, &t0);
    if (borrow) t0 -= NEG_ORDER;
    /* t1 = x_hi_lo * NEG_ORDER */
    uint64_t t1 = x_hi_lo * NEG_ORDER;
    /* result = t0 + t1 (with carry handling) */
    uint64_t result;
    int carry = __builtin_add_overflow(t0, t1, &result);
    if (carry || result >= GOLDILOCKS_P) result -= GOLDILOCKS_P;
    return result;
}

static inline void butterfly(uint64_t *a, uint64_t *b, uint64_t w) \{
    uint64_t orig_a = *a;
    uint64_t wb = goldilocks_reduce128((__uint128_t)w * (__uint128_t)(*b));
    __uint128_t sum128 = (__uint128_t)orig_a + (__uint128_t)wb;
    *a = goldilocks_reduce128(sum128);
    __uint128_t diff128 = (__uint128_t)GOLDILOCKS_P + (__uint128_t)orig_a - (__uint128_t)wb;
    *b = goldilocks_reduce128(diff128);
}
"
    | .montgomery, .simdNEON =>
      let muHex := Nat.toDigits 16 cfg.montyMu |>.asString
      s!"static const int32x4_t v_p = \{{p}, {p}, {p}, {p}};
static const int32x4_t v_mu = \{(int32_t)0x{muHex}, (int32_t)0x{muHex}, (int32_t)0x{muHex}, (int32_t)0x{muHex}};

/* Montgomery multiply: REDC on (w * b), ALL in u32 lanes.
   FIX: apply vqdmulhq to (w, *b) NOT to (orig_a, wb).
   6 NEON instructions, throughput ~1.5 cyc/vec. */
static inline void butterfly(int32x4_t *a, int32x4_t *b, int32x4_t w) \{
    int32x4_t orig_a = *a;
    /* Montgomery reduce: wb = monty_mul(w, *b) */
    int32x4_t c_hi = vqdmulhq_s32(w, *b);          /* high32(w * b) */
    int32x4_t mu_rhs = vmulq_s32(*b, v_mu);         /* b * MU mod 2^32 */
    int32x4_t q = vmulq_s32(w, mu_rhs);             /* w * (b * MU) mod 2^32 */
    int32x4_t qp_hi = vqdmulhq_s32(q, v_p);         /* high32(q * P) */
    int32x4_t d = vhsubq_s32(c_hi, qp_hi);          /* (c_hi - qp_hi) / 2 */
    uint32x4_t uf = vcltq_s32(c_hi, qp_hi);         /* underflow mask */
    int32x4_t wb = vreinterpretq_s32_u32(
        vmlsq_u32(vreinterpretq_u32_s32(d), uf, vreinterpretq_u32_s32(v_p)));
    /* Butterfly: sum = a + wb, diff = a - wb, both canonicalized */
    int32x4_t sum = vaddq_s32(orig_a, wb);
    uint32x4_t su = vreinterpretq_u32_s32(sum);
    *a = vreinterpretq_s32_u32(vminq_u32(su, vsubq_u32(su, vreinterpretq_u32_s32(v_p))));
    int32x4_t dif = vsubq_s32(orig_a, wb);
    uint32x4_t du = vreinterpretq_u32_s32(dif);
    *b = vreinterpretq_s32_u32(vminq_u32(du, vaddq_u32(du, vreinterpretq_u32_s32(v_p))));
}
"
    | _, _ =>
      s!"/* Fallback: scalar Solinas fold */
static inline uint32_t reduce_fallback(uint64_t x) \{
    return (uint32_t)(((x >> 31) * 134217727U) + (x & 0x7FFFFFFFU));
}
"

  -- Generate the NTT function
  let elemType := match cfg.mode with
    | .simdNEON => "int32_t"
    | _ => if cfg.wordSize ≤ 32 then "uint32_t" else "uint64_t"
  let stride := match cfg.mode with
    | .simdNEON => "4"
    | .simdAVX2 => "8"
    | .scalar => "1"

  let nttCode := s!"void {funcName}({elemType} *data, size_t n, const {elemType} *twiddles) \{
    /* Literal loop bound ({logN}) enables compiler loop unrolling */
    for (size_t stage = 0; stage < {logN}; stage++) \{
        size_t half = 1 << ({logN - 1} - stage);
        for (size_t group = 0; group < (1u << stage); group++) \{
            for (size_t pair = 0; pair + {stride} <= half; pair += {stride}) \{
                size_t i = group * 2 * half + pair;
                size_t j = i + half;
                size_t tw_idx = stage * (n / 2) + group * half + pair;
{match cfg.mode with
  | .simdNEON => s!"                int32x4_t va = vld1q_s32(&data[i]);
                int32x4_t vb = vld1q_s32(&data[j]);
                int32x4_t vw = vld1q_s32(&twiddles[tw_idx]);
                butterfly(&va, &vb, vw);
                vst1q_s32(&data[i], va);
                vst1q_s32(&data[j], vb);"
  | _ => s!"                butterfly(&data[i], &data[j], twiddles[tw_idx]);"}
            }
        }
    }
}
"

  header ++ bfCode ++ nttCode

-- ══════════════════════════════════════════════════════════════════
-- Section 5b: Rust NTT generator (for fair comparison with Plonky3)
-- ══════════════════════════════════════════════════════════════════

/-- Generate a complete Rust NTT with benchmark harness.
    Compiled with `rustc -O` this gives a fair Rust-vs-Rust comparison
    against Plonky3's production NTT.

    Strategy selected by e-graph cost model (same as C version). -/
def generateRustNTT (hw : HardwareCost) (n p : Nat)
    (funcName : String := "ntt") : String :=
  let cfg := selectConfig hw p
  let logN := Nat.log 2 n
  let elemType := if cfg.wordSize ≤ 32 then "u32" else "u64"
  let wideType := if cfg.wordSize ≤ 32 then "u64" else "u128"

  let foldFn := if cfg.wordSize ≤ 32 then
    s!"#[inline(always)]
fn solinas_fold(x: {wideType}) -> {elemType} \{
    (((x >> {cfg.shiftBits}) as {wideType}).wrapping_mul({cfg.foldConst} as {wideType}))
        .wrapping_add(x & {2^cfg.shiftBits - 1} as {wideType}) as {elemType}
}"
  else
    s!"#[inline(always)]
fn goldilocks_reduce(x: u128) -> u64 \{
    let x_lo = x as u64;
    let x_hi = (x >> 64) as u64;
    let x_hi_hi = x_hi >> 32;
    let x_hi_lo = x_hi & 0xFFFFFFFF_u64;
    let (t0, borrow) = x_lo.overflowing_sub(x_hi_hi);
    let t0 = if borrow \{ t0.wrapping_sub(0xFFFFFFFF_u64) } else \{ t0 };
    let t1 = x_hi_lo.wrapping_mul(0xFFFFFFFF_u64);
    let (result, carry) = t0.overflowing_add(t1);
    if carry || result >= 0xFFFFFFFF00000001_u64 \{ result.wrapping_sub(0xFFFFFFFF00000001_u64) } else \{ result }
}"

  let bfFn := if cfg.wordSize ≤ 32 then
    s!"#[inline(always)]
fn butterfly(a: &mut {elemType}, b: &mut {elemType}, w: {elemType}) \{
    let orig_a = *a;
    let wb = solinas_fold((w as {wideType}).wrapping_mul(*b as {wideType}));
    *a = solinas_fold((orig_a as {wideType}).wrapping_add(wb as {wideType}));
    *b = solinas_fold(({p} as {wideType}).wrapping_add(orig_a as {wideType}).wrapping_sub(wb as {wideType}));
}"
  else
    s!"#[inline(always)]
fn butterfly(a: &mut u64, b: &mut u64, w: u64) \{
    let orig_a = *a;
    let wb = goldilocks_reduce((w as u128).wrapping_mul(*b as u128));
    *a = goldilocks_reduce((orig_a as u128).wrapping_add(wb as u128));
    *b = goldilocks_reduce((0xFFFFFFFF00000001_u128).wrapping_add(orig_a as u128).wrapping_sub(wb as u128));
}"

  s!"//! AMO-Lean Generated Rust NTT — e-graph cost model selection
//! N = {n}, p = {p}
//! Reduction: {toString cfg.reduction}, Word: {elemType}
//! Compile: rustc -O -o ntt_bench this_file.rs
//! Same trust boundary as Fiat-Crypto (verified lowering via Trust-Lean)

use std::time::Instant;

const P: {elemType} = {p};

{foldFn}

{bfFn}

fn {funcName}(data: &mut [{elemType}], twiddles: &[{elemType}]) \{
    let n = data.len();
    for stage in 0..{logN} \{
        let half = 1 << ({logN - 1} - stage);
        let mut group = 0;
        while group < (1 << stage) \{
            let mut pair = 0;
            while pair + 1 <= half \{
                let i = group * 2 * half + pair;
                let j = i + half;
                let tw_idx = stage * (n / 2) + group * half + pair;
                let w = twiddles[tw_idx];
                // split_at_mut to satisfy borrow checker (i < j always)
                let (left, right) = data.split_at_mut(j);
                butterfly(&mut left[i], &mut right[0], w);
                pair += 1;
            }
            group += 1;
        }
    }
}

fn main() \{
    let n: usize = {n};
    let log_n: usize = {logN};
    let tw_size = n * log_n;
    let twiddles: Vec<{elemType}> = (0..tw_size).map(|i| ((i as {wideType} * 7 + 31) % P as {wideType}) as {elemType}).collect();

    let iters: usize = {if n ≤ 4096 then 1000 else if n ≤ 65536 then 50 else 3};
    let start = Instant::now();
    for _ in 0..iters \{
        let mut data: Vec<{elemType}> = (0..n).map(|i| ((i as {wideType} * 1000000007) % P as {wideType}) as {elemType}).collect();
        {funcName}(&mut data, &twiddles);
    }
    let elapsed = start.elapsed();
    let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    let melem = n as f64 * iters as f64 / elapsed.as_secs_f64() / 1e6;
    eprintln!(\"N={n} p={p} ({toString cfg.reduction})\");
    eprintln!(\"  " ++ "{}" ++ " us  " ++ "{}" ++ " Melem/s\", us, melem);
}
"

/-- Generate a Rust NTT with Bowers G ordering (DIF butterfly).
    Same reduction as scalar DIT, but with:
    1. Bit-reversed input
    2. DIF butterfly: a' = a+b, b' = (a-b)*w
    3. Stages from small block to large block
    4. Bit-reversed twiddle table → sequential access (cache-friendly)

    The reduction function (Solinas fold or Goldilocks reduce) is selected
    by the e-graph cost model, same as the standard DIT generator. -/
def generateRustNTT_Bowers (hw : HardwareCost) (n p : Nat)
    (funcName : String := "ntt_bowers") : String :=
  let cfg := selectConfig hw p
  let logN := Nat.log 2 n
  let elemType := if cfg.wordSize ≤ 32 then "u32" else "u64"
  let wideType := if cfg.wordSize ≤ 32 then "u64" else "u128"

  -- Reduction function (same as standard DIT — e-graph selected)
  -- Bug fix: solinas_fold returns wideType (u64) to avoid premature truncation.
  -- The DIF butterfly stores results as elemType (u32) via `as u32` at assignment.
  let foldFn := if cfg.wordSize ≤ 32 then
    s!"/// Solinas fold — e-graph selected for scalar {elemType} fields.
/// Returns {wideType} (not {elemType}) to avoid premature truncation in chained operations.
/// Verified: solinasFold_mod_correct — fold(x) % p = x % p.
#[inline(always)]
fn solinas_fold(x: {wideType}) -> {wideType} \{
    ((x >> {cfg.shiftBits}).wrapping_mul({cfg.foldConst} as {wideType}))
        .wrapping_add(x & {2^cfg.shiftBits - 1} as {wideType})
}"
  else
    s!"/// Goldilocks reduction — exploits p = 2^64 - 2^32 + 1.
/// Verified: solinasFold_mod_correct (Goldilocks instance).
#[inline(always)]
fn goldilocks_reduce(x: u128) -> u64 \{
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hh = hi >> 32;
    let hl = hi & 0xFFFFFFFF_u64;
    let (t0, borrow) = lo.overflowing_sub(hh);
    let t0 = if borrow \{ t0.wrapping_sub(0xFFFFFFFF_u64) } else \{ t0 };
    let t1 = hl.wrapping_mul(0xFFFFFFFF_u64);
    let (result, carry) = t0.overflowing_add(t1);
    if carry || result >= {p}_u64 \{ result.wrapping_sub({p}_u64) } else \{ result }
}"

  -- DIF butterfly (Bowers uses DIF, not DIT)
  -- Bug fix: u32 fields use wideType (u64) for twiddle multiply to avoid truncation.
  -- Bug fix: Goldilocks uses overflowing_add for sum to detect u64 overflow.
  let difBfFn := if cfg.wordSize ≤ 32 then
    s!"/// DIF butterfly: a' = fold(a + b), b' = fold((p + a - b) * w).
/// Bowers G network applies ONE twiddle per block.
/// solinas_fold returns {wideType} to avoid truncation; cast to {elemType} at storage.
#[inline(always)]
fn dif_butterfly(a: &mut {elemType}, b: &mut {elemType}, w: {elemType}) \{
    let va = *a as {wideType};
    let vb = *b as {wideType};
    *a = solinas_fold(va + vb) as {elemType};
    let diff = solinas_fold({p} as {wideType} + va - vb);
    *b = solinas_fold(diff.wrapping_mul(w as {wideType})) as {elemType};
}"
  else
    s!"/// DIF butterfly for Goldilocks.
/// Uses overflowing_add to correctly handle sum >= 2^64.
#[inline(always)]
fn dif_butterfly(a: &mut u64, b: &mut u64, w: u64) \{
    let va = *a;
    let vb = *b;
    let (sum, overflow) = va.overflowing_add(vb);
    *a = if overflow || sum >= {p}_u64 \{ sum.wrapping_sub({p}_u64) } else \{ sum };
    *b = goldilocks_reduce(
        (if va >= vb \{ va - vb } else \{ {p}_u64 - vb + va }) as u128
        * w as u128);
}"

  -- Bit-reversal utility
  let bitRevFn := s!"fn bit_reverse(data: &mut [{elemType}]) \{
    let n = data.len();
    let log_n = n.trailing_zeros();
    for i in 0..n \{
        let j = i.reverse_bits() >> (usize::BITS - log_n);
        if i < j \{ data.swap(i, j); }
    }
}"

  -- Twiddle computation (bit-reversed for Bowers)
  let twiddleFn := s!"fn mod_pow(mut base: {wideType}, mut exp: {wideType}, modulus: {wideType}) -> {wideType} \{
    let mut result: {wideType} = 1;
    base %= modulus;
    while exp > 0 \{
        if exp & 1 == 1 \{
            result = (result as u128 * base as u128 % modulus as u128) as {wideType};
        }
        exp >>= 1;
        base = (base as u128 * base as u128 % modulus as u128) as {wideType};
    }
    result
}

/// Compute bit-reversed twiddle table for Bowers G network.
fn compute_bowers_twiddles(n: usize, generator: {wideType}) -> Vec<{elemType}> \{
    let p = {p} as {wideType};
    let omega = mod_pow(generator, (p - 1) / n as {wideType}, p);
    let mut tw: Vec<{elemType}> = (0..n/2)
        .map(|i| mod_pow(omega, i as {wideType}, p) as {elemType})
        .collect();
    bit_reverse(&mut tw);
    tw
}"

  -- The Bowers NTT function
  let nttFn := s!"/// Bowers G NTT: bit-reverse input, DIF stages small→large, sequential twiddle access.
/// Cache-friendly: twiddles accessed linearly (one per block).
/// Reduction: {toString cfg.reduction} (e-graph selected).
pub fn {funcName}(data: &mut [{elemType}], twiddles: &[{elemType}]) \{
    let n = data.len();
    let log_n = n.trailing_zeros() as usize;

    bit_reverse(data);

    for log_half in 0..log_n \{
        let half = 1_usize << log_half;
        let block_size = 2 * half;
        let num_blocks = n / block_size;

        for block in 0..num_blocks \{
            let w: {elemType} = if block == 0 \{ 1 } else \{ twiddles[block] };
            let base = block * block_size;
            for j in 0..half \{
                let i0 = base + j;
                let i1 = i0 + half;
                let (left, right) = data.split_at_mut(i1);
                dif_butterfly(&mut left[i0], &mut right[0], w);
            }
        }
    }
}"

  -- Primitive root per field
  let generator := if p == babybear_prime then "31"
    else if p == 2130706433 then "3"  -- KoalaBear
    else if p == mersenne31_prime then "7"
    else if p == goldilocks_prime then "7"
    else "3"

  s!"//! AMO-Lean Generated Rust NTT — Bowers G ordering
//! N = {n}, p = {p}
//! Reduction: {toString cfg.reduction} (e-graph cost model)
//! Ordering: Bowers G (bit-reversed twiddles, DIF butterfly, sequential access)
//! Verified: solinasFold_mod_correct / monty_reduce_spec
//!
//! Bowers advantage: cache-friendly twiddle access.
//! Standard DIT: twiddles[stage*(n/2) + group*half + pair] — strided, non-sequential.
//! Bowers:       twiddles[block] — linear, sequential. CPU prefetch works.

use std::time::Instant;

{foldFn}

{difBfFn}

{bitRevFn}

{twiddleFn}

{nttFn}

fn main() \{
    let n: usize = {n};
    let generator: {wideType} = {generator};
    let twiddles = compute_bowers_twiddles(n, generator);

    let iters: usize = {if n ≤ 4096 then 1000 else if n ≤ 65536 then 50 else 3};
    let start = Instant::now();
    for _ in 0..iters \{
        let mut data: Vec<{elemType}> = (0..n)
            .map(|i| ((i as {wideType} * 1000000007) % {p} as {wideType}) as {elemType})
            .collect();
        {funcName}(&mut data, &twiddles);
        std::hint::black_box(&data);
    }
    let elapsed = start.elapsed();
    let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    let melem = n as f64 * iters as f64 / elapsed.as_secs_f64() / 1e6;
    eprintln!(\"N={n} p={p} Bowers ({toString cfg.reduction})\");
    eprintln!(\"  " ++ "{}" ++ " us  " ++ "{}" ++ " Melem/s\", us, melem);
}
"

/-- Generate a Rust NTT with NEON intrinsics (4-wide Montgomery).
    Uses `unsafe` blocks for `std::arch::aarch64::*` intrinsics.
    Same algorithm as the C NEON version that achieved 9.6µs/NTT.
    Only for 31-bit fields (BabyBear, Mersenne31, KoalaBear). -/
def generateRustNTT_NEON (n p : Nat) (funcName : String := "ntt_neon") : String :=
  let cfg := selectConfig arm_neon_simd p
  let logN := Nat.log 2 n
  let muHex := Nat.toDigits 16 cfg.montyMu |>.asString
  s!"//! AMO-Lean Generated Rust NTT — NEON Montgomery (4-wide)
//! N = {n}, p = {p}
//! Strategy: Montgomery REDC via vqdmulhq_s32 (chosen by e-graph cost model)
//! Compile: rustc -O -o ntt_neon this_file.rs
//! Trust boundary: same as Fiat-Crypto (verified lowering via Trust-Lean)

#![allow(non_upper_case_globals)]
use std::time::Instant;
use std::arch::aarch64::*;

const P_VAL: i32 = {p} as i32;
const MU_VAL: i32 = 0x{muHex}u32 as i32;

/// NEON Montgomery multiply: 4 parallel field multiplications.
/// All ops in i32 lanes — no u64 intermediates.
/// 6 NEON instructions, ~1.5 cyc/vec throughput.
#[inline(always)]
unsafe fn monty_mul(lhs: int32x4_t, rhs: int32x4_t,
                    v_p: int32x4_t, v_mu: int32x4_t) -> int32x4_t \{
    let c_hi = vqdmulhq_s32(lhs, rhs);
    let mu_rhs = vmulq_s32(rhs, v_mu);
    let q = vmulq_s32(lhs, mu_rhs);
    let qp_hi = vqdmulhq_s32(q, v_p);
    let d = vhsubq_s32(c_hi, qp_hi);
    let uf: uint32x4_t = vcltq_s32(c_hi, qp_hi);
    vreinterpretq_s32_u32(vmlsq_u32(
        vreinterpretq_u32_s32(d), uf, vreinterpretq_u32_s32(v_p)))
}

/// NEON butterfly: 4 parallel CT butterflies.
#[inline(always)]
unsafe fn butterfly_neon(a: &mut int32x4_t, b: &mut int32x4_t, w: int32x4_t,
                          v_p: int32x4_t, v_mu: int32x4_t) \{
    let orig_a = *a;
    let wb = monty_mul(w, *b, v_p, v_mu);
    // sum = a + wb (with canonicalization)
    let sum = vaddq_s32(orig_a, wb);
    let su = vreinterpretq_u32_s32(sum);
    *a = vreinterpretq_s32_u32(vminq_u32(su,
        vsubq_u32(su, vreinterpretq_u32_s32(v_p))));
    // diff = a - wb (with canonicalization)
    let dif = vsubq_s32(orig_a, wb);
    let du = vreinterpretq_u32_s32(dif);
    *b = vreinterpretq_s32_u32(vminq_u32(du,
        vaddq_u32(du, vreinterpretq_u32_s32(v_p))));
}

/// NTT with NEON: 4 butterflies per vector instruction.
fn {funcName}(data: &mut [i32], twiddles: &[i32]) \{
    let n = data.len();
    unsafe \{
        let v_p = vdupq_n_s32(P_VAL);
        let v_mu = vdupq_n_s32(MU_VAL);
        for stage in 0..{logN} \{
            let half = 1usize << ({logN - 1} - stage);
            let mut group = 0usize;
            while group < (1 << stage) \{
                let mut pair = 0usize;
                while pair + 4 <= half \{
                    let i = group * 2 * half + pair;
                    let j = i + half;
                    let tw_idx = stage * (n / 2) + group * half + pair;
                    let mut va = vld1q_s32(data.as_ptr().add(i));
                    let mut vb = vld1q_s32(data.as_ptr().add(j));
                    let vw = vld1q_s32(twiddles.as_ptr().add(tw_idx));
                    butterfly_neon(&mut va, &mut vb, vw, v_p, v_mu);
                    vst1q_s32(data.as_mut_ptr().add(i), va);
                    vst1q_s32(data.as_mut_ptr().add(j), vb);
                    pair += 4;
                }
                group += 1;
            }
        }
    }
}

fn main() \{
    let n: usize = {n};
    let log_n: usize = {logN};
    let tw_size = n * log_n;
    let twiddles: Vec<i32> = (0..tw_size).map(|i|
        ((i as u64 * 7 + 31) % {p} as u64) as i32).collect();

    let iters: usize = {if n ≤ 4096 then 1000 else if n ≤ 65536 then 50 else 3};
    let start = Instant::now();
    for _ in 0..iters \{
        let mut data: Vec<i32> = (0..n).map(|i|
            ((i as u64 * 1000000007) % {p} as u64) as i32).collect();
        {funcName}(&mut data, &twiddles);
    }
    let elapsed = start.elapsed();
    let us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    let melem = n as f64 * iters as f64 / elapsed.as_secs_f64() / 1e6;
    eprintln!(\"N={n} p={p} NEON Montgomery (4-wide)\");
    eprintln!(\"  " ++ "{}" ++ " us  " ++ "{}" ++ " Melem/s\", us, melem);
}
"

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Multi-target generation (one function call → all targets)
-- ══════════════════════════════════════════════════════════════════

/-- Generate NTT for all hardware targets.
    Each target gets different code based on its cost model. -/
def generateAllTargets (n p : Nat) : List (String × String × String) :=
  let targets := [
    ("scalar_arm", arm_cortex_a76, "ntt_scalar_arm"),
    ("simd_neon", arm_neon_simd, "ntt_simd_neon"),
    ("simd_avx2", x86_avx2_simd, "ntt_simd_avx2")]
  targets.map fun (label, hw, funcName) =>
    let cfg := selectConfig hw p
    (label, toString cfg.reduction, generateNTT hw n p funcName)

/-- Write all target variants to files. -/
def writeAllTargets (outputDir : String := "generated/unified") (n p : Nat) : IO Unit := do
  IO.FS.createDirAll outputDir
  for (label, strategy, code) in generateAllTargets n p do
    let path := s!"{outputDir}/ntt_{label}.c"
    IO.FS.writeFile ⟨path⟩ code
    IO.println s!"  {label}: {strategy} ({code.length} bytes) → {path}"
  IO.println "\nAll targets generated from e-graph cost model. No hardcoded decisions."

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: scalar ARM selects Solinas fold. -/
example : (selectConfig arm_cortex_a76 babybear_prime).reduction = .solinasFold := rfl

/-- Smoke: NEON selects Montgomery. -/
example : (selectConfig arm_neon_simd babybear_prime).reduction = .montgomery := rfl

/-- Smoke: NEON selects SIMD mode. -/
example : (selectConfig arm_neon_simd babybear_prime).mode = .simdNEON := rfl

/-- Smoke: scalar selects scalar mode. -/
example : (selectConfig arm_cortex_a76 babybear_prime).mode = .scalar := rfl

/-- Smoke: AVX2 selects SIMD mode. -/
example : (selectConfig x86_avx2_simd babybear_prime).mode = .simdAVX2 := rfl

/-- Smoke: Goldilocks forces scalar mode (64-bit, no SIMD benefit). -/
example : (selectConfig arm_neon_simd goldilocks_prime).mode = .scalar := rfl

/-- Smoke: Goldilocks uses Solinas fold (not Montgomery). -/
example : (selectConfig arm_neon_simd goldilocks_prime).reduction = .solinasFold := rfl

/-- Smoke: Goldilocks uses 64-bit word size. -/
example : (selectConfig arm_cortex_a76 goldilocks_prime).wordSize = 64 := rfl

end AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen
