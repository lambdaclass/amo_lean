/-
  AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer

  v3.13.0 F.2-F.4: Path A — verified codegen for crypto primitives.
  Uses lowerReductionChoice (verified TrustLean lowering) instead of
  string emission (Path B). All reduction code goes through the same
  verified pipeline as NTT butterflies.

  Primitives:
    1. FRI fold: result = even + alpha * odd (mod p)
    2. Polynomial evaluation (Horner): a₀ + x(a₁ + x(a₂ + ...))  (mod p)
    3. Dot product: Σ aᵢ * bᵢ (mod p)
-/
import AmoLean.EGraph.Verified.Bitwise.MixedRunner
import AmoLean.EGraph.Verified.Bitwise.NTTBridge
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer

open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise
  (HardwareCost arm_cortex_a76 arm_neon_simd
   mersenne31_prime babybear_prime goldilocks_prime)
open _root_.TrustLean (Stmt VarName LowLevelExpr BinOp CodeGenState stmtToC varNameToC)
open AmoLean.EGraph.Verified.Bitwise.TrustLeanBridge (lowerSolinasFold lowerHarveyReduce)

-- ══════════════════════════════════════════════════════════════════
-- Section 0: Field parameters for verified codegen
-- ══════════════════════════════════════════════════════════════════

/-- Field parameters for verified lowering: Solinas constants + C type info. -/
structure FieldParams where
  p : Nat
  k : Nat       -- Solinas shift bits
  c : Nat       -- Solinas fold constant
  mu : Nat      -- Montgomery mu (unused for primitive codegen)
  elemType : String
  wideType : String

/-- Compute field parameters from prime. Matches UltraConfig presets. -/
def fieldParamsOf (p : Nat) : FieldParams :=
  if p == goldilocks_prime then
    { p, k := 64, c := 4294967295, mu := 0,
      elemType := "uint64_t", wideType := "__uint128_t" }
  else if p == babybear_prime then
    { p, k := 31, c := 134217727, mu := 0x88000001,
      elemType := "int32_t", wideType := "int64_t" }
  else -- Mersenne31 and others
    { p, k := 31, c := 1, mu := 0,
      elemType := "int32_t", wideType := "int64_t" }

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Verified kernel builder — multiply + reduce + add + reduce
-- ══════════════════════════════════════════════════════════════════

/-- Build a verified multiply-accumulate kernel via TrustLean Stmt:
    result = harvey(solinasFold(w_0 + solinasFold(w_1 * w_2, k, c), k, c), p)
    Uses Solinas fold for intermediate reductions, Harvey for final < p guarantee.
    Returns (kernel Stmt, result VarName, numTemps used). -/
def buildMulAccKernel (fp : FieldParams) :
    (Stmt × VarName × Nat) :=
  let cgs : CodeGenState := {}
  -- Step 1: product = w_1 * w_2
  let prodExpr := LowLevelExpr.binOp .mul (.varRef (.user "w_1")) (.varRef (.user "w_2"))
  let (prodVar, cgs1) := cgs.freshVar
  let prodStmt := Stmt.assign prodVar prodExpr
  -- Step 2: reduce product via Solinas fold (handles any product size)
  let (sr1, cgs2) := lowerSolinasFold (.varRef prodVar) fp.k fp.c cgs1
  let prodRedVar := match sr1.resultVar with | .varRef v => v | _ => .user "err"
  -- Step 3: sum = w_0 + reduced product
  let sumExpr := LowLevelExpr.binOp .add (.varRef (.user "w_0")) (.varRef prodRedVar)
  let (sumVar, cgs3) := cgs2.freshVar
  let sumStmt := Stmt.assign sumVar sumExpr
  -- Step 4: reduce sum via Solinas fold
  let (sr2, cgs4) := lowerSolinasFold (.varRef sumVar) fp.k fp.c cgs3
  let sumRedVar := match sr2.resultVar with | .varRef v => v | _ => .user "err"
  -- Step 5: Harvey conditional subtract (ensures output < p)
  let (sr3, cgs5) := lowerHarveyReduce (.varRef sumRedVar) fp.p cgs4
  let resVar := match sr3.resultVar with | .varRef v => v | _ => .user "err"
  -- Compose all stmts
  let kernel := Stmt.seq prodStmt
    (Stmt.seq sr1.stmt
      (Stmt.seq sumStmt
        (Stmt.seq sr2.stmt sr3.stmt)))
  (kernel, resVar, cgs5.nextVar)

/-- Emit temp variable declarations for a kernel. -/
private def tempDecls (wideType : String) (n : Nat) : String :=
  if n == 0 then ""
  else s!"  {wideType} " ++
    String.intercalate ", " (List.range n |>.map (s!"t{·}")) ++ ";\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 1b: MixedExpr definitions (kept for e-graph compatibility)
-- ══════════════════════════════════════════════════════════════════

/-- FRI fold as MixedExpr: result = reduce(even + reduce(alpha * odd)).
    witness(0) = even, witness(1) = alpha, witness(2) = odd.
    The two reduceGate nodes will be optimized by the e-graph. -/
def friFoldExpr (p : Nat) : MixedExpr :=
  .reduceE (.addE (.witnessE 0) (.reduceE (.mulE (.witnessE 1) (.witnessE 2)) p)) p

/-- Build Horner's method as MixedExpr for degree-d polynomial.
    p(x) = a₀ + x(a₁ + x(a₂ + ... + x·aₐ))
    Coefficients are witness(0)..witness(d), evaluation point is witness(d+1).
    Each multiply and add is wrapped in reduceGate(_, p). -/
def hornerExpr (degree : Nat) (p : Nat) : MixedExpr :=
  let x := MixedExpr.witnessE (degree + 1)
  let rec build : Nat → MixedExpr
    | 0 => .witnessE 0
    | n + 1 =>
      .reduceE (.addE (.witnessE (degree - n - 1))
        (.reduceE (.mulE x (build n)) p)) p
  build degree

-- ══════════════════════════════════════════════════════════════════
-- Section 2: FRI fold — Path A verified codegen
-- ══════════════════════════════════════════════════════════════════

/-- Generate verified C for FRI fold via Path A (TrustLean Stmt lowering).
    result[i] = reduce(even[i] + reduce(alpha * odd[i]))
    All reductions go through verified lowerSolinasFold + lowerHarveyReduce. -/
def friFoldToC (_hw : HardwareCost) (p : Nat) (_n : Nat)
    (funcName : String := "fri_fold") : String :=
  let fp := fieldParamsOf p
  let (kernel, resVar, numTemps) := buildMulAccKernel fp
  let kernelC := stmtToC 2 kernel
  let resName := varNameToC resVar
  s!"/* AMO-Lean FRI Fold — Path A (verified TrustLean lowering)\n" ++
  s!" * p = {p}, reduction = solinasFold + harvey\n" ++
  s!" * Verified: lowerSolinasFold, lowerHarveyReduce (0 sorry)\n" ++
  s!" */\n" ++
  s!"#include <stdint.h>\n#include <stddef.h>\n\n" ++
  s!"void {funcName}(const {fp.elemType} *even, const {fp.elemType} *odd,\n" ++
  s!"               {fp.elemType} alpha, {fp.elemType} *result, size_t n) \{\n" ++
  tempDecls fp.wideType numTemps ++
  s!"  {fp.wideType} w_0, w_1, w_2;\n" ++
  s!"  for (size_t i = 0; i < n; i++) \{\n" ++
  s!"    w_0 = ({fp.wideType})even[i];\n" ++
  s!"    w_1 = ({fp.wideType})alpha;\n" ++
  s!"    w_2 = ({fp.wideType})odd[i];\n" ++
  kernelC ++ "\n" ++
  s!"    result[i] = ({fp.elemType}){resName};\n" ++
  s!"  }\n}\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Polynomial evaluation (Horner) — Path A
-- ══════════════════════════════════════════════════════════════════

/-- Generate verified C for Horner polynomial evaluation via Path A.
    p(x) = a₀ + x(a₁ + x(a₂ + ... + x·aₐ))
    Each step is: acc = reduce(coeff[i] + reduce(x * acc)) -/
def hornerToC (_hw : HardwareCost) (p : Nat) (degree : Nat)
    (funcName : String := "poly_eval") : String :=
  let fp := fieldParamsOf p
  -- Kernel: w_0 = coeff[i-1], w_1 = x, w_2 = acc → result = reduce(w_0 + reduce(w_1 * w_2))
  let (kernel, resVar, numTemps) := buildMulAccKernel fp
  let kernelC := stmtToC 2 kernel
  let resName := varNameToC resVar
  s!"/* AMO-Lean Poly Eval (Horner) — Path A (verified TrustLean lowering)\n" ++
  s!" * p = {p}, degree = {degree}, reduction = solinasFold + harvey\n" ++
  s!" * Verified: lowerSolinasFold, lowerHarveyReduce (0 sorry)\n" ++
  s!" */\n" ++
  s!"#include <stdint.h>\n#include <stddef.h>\n\n" ++
  s!"{fp.elemType} {funcName}(const {fp.elemType} *coeffs, size_t degree, {fp.elemType} x) \{\n" ++
  tempDecls fp.wideType numTemps ++
  s!"  {fp.wideType} w_0, w_1, w_2;\n" ++
  s!"  {fp.wideType} acc = ({fp.wideType})coeffs[degree];\n" ++
  s!"  for (size_t i = degree; i > 0; i--) \{\n" ++
  s!"    w_0 = ({fp.wideType})coeffs[i-1];\n" ++
  s!"    w_1 = ({fp.wideType})x;\n" ++
  s!"    w_2 = acc;\n" ++
  kernelC ++ "\n" ++
  s!"    acc = ({fp.wideType}){resName};\n" ++
  s!"  }\n" ++
  s!"  return ({fp.elemType})acc;\n}\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Dot product — Path A
-- ══════════════════════════════════════════════════════════════════

/-- Generate verified C for dot product via Path A.
    result = Σ reduce(a[i] * b[i])
    Accumulates with reduce after each multiply-add step. -/
def dotProductToC (_hw : HardwareCost) (p : Nat)
    (funcName : String := "dot_product") : String :=
  let fp := fieldParamsOf p
  -- Kernel: w_0 = acc, w_1 = a[i], w_2 = b[i] → result = reduce(acc + reduce(a[i] * b[i]))
  let (kernel, resVar, numTemps) := buildMulAccKernel fp
  let kernelC := stmtToC 2 kernel
  let resName := varNameToC resVar
  s!"/* AMO-Lean Dot Product — Path A (verified TrustLean lowering)\n" ++
  s!" * p = {p}, reduction = solinasFold + harvey\n" ++
  s!" * Verified: lowerSolinasFold, lowerHarveyReduce (0 sorry)\n" ++
  s!" */\n" ++
  s!"#include <stdint.h>\n#include <stddef.h>\n\n" ++
  s!"{fp.elemType} {funcName}(const {fp.elemType} *a, const {fp.elemType} *b, size_t n) \{\n" ++
  tempDecls fp.wideType numTemps ++
  s!"  {fp.wideType} w_0, w_1, w_2;\n" ++
  s!"  {fp.wideType} acc = 0;\n" ++
  s!"  for (size_t i = 0; i < n; i++) \{\n" ++
  s!"    w_0 = acc;\n" ++
  s!"    w_1 = ({fp.wideType})a[i];\n" ++
  s!"    w_2 = ({fp.wideType})b[i];\n" ++
  kernelC ++ "\n" ++
  s!"    acc = ({fp.wideType}){resName};\n" ++
  s!"  }\n" ++
  s!"  return ({fp.elemType})acc;\n}\n"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Generate all primitives for a field
-- ══════════════════════════════════════════════════════════════════

/-- Generate verified C for all primitives on a given field + hardware. -/
def generateAllPrimitives (hw : HardwareCost) (p : Nat) (n : Nat := 4096)
    (outputDir : String := "generated/primitives") : IO Unit := do
  IO.FS.createDirAll outputDir
  let fieldName := if p == babybear_prime then "babybear"
    else if p == mersenne31_prime then "mersenne31"
    else if p == goldilocks_prime then "goldilocks"
    else s!"p{p}"

  let fri := friFoldToC hw p n s!"fri_fold_{fieldName}"
  let friPath := s!"{outputDir}/fri_fold_{fieldName}.c"
  IO.FS.writeFile ⟨friPath⟩ fri
  IO.println s!"  FRI fold (Path A verified): {friPath}"

  let poly := hornerToC hw p 7 s!"poly_eval_{fieldName}"
  let polyPath := s!"{outputDir}/poly_eval_{fieldName}.c"
  IO.FS.writeFile ⟨polyPath⟩ poly
  IO.println s!"  Poly eval deg-7 (Path A verified): {polyPath}"

  let dot := dotProductToC hw p s!"dot_product_{fieldName}"
  let dotPath := s!"{outputDir}/dot_product_{fieldName}.c"
  IO.FS.writeFile ⟨dotPath⟩ dot
  IO.println s!"  Dot product (Path A verified): {dotPath}"

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: FRI fold expr has the right structure. -/
example : friFoldExpr 7 =
    .reduceE (.addE (.witnessE 0) (.reduceE (.mulE (.witnessE 1) (.witnessE 2)) 7)) 7 := rfl

/-- Smoke: Horner degree-0 is just witness(0). -/
example : hornerExpr 0 7 = .witnessE 0 := rfl

/-- Smoke: FRI fold Path A produces non-empty C code. -/
example : (friFoldToC arm_cortex_a76 babybear_prime 1024).length > 0 := by native_decide

/-- Smoke: Horner Path A produces non-empty C code. -/
example : (hornerToC arm_cortex_a76 babybear_prime 7).length > 0 := by native_decide

/-- Smoke: Dot product Path A produces non-empty C code. -/
example : (dotProductToC arm_cortex_a76 babybear_prime).length > 0 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer
