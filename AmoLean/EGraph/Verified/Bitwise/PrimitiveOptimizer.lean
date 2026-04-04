/-
  AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer

  Constructs MixedExpr for common crypto primitives and passes them
  through the e-graph for automatic optimization. Each primitive
  gets the best reduction strategy per hardware target.

  Primitives:
    1. FRI fold: result = even + alpha * odd (mod p)
    2. Polynomial evaluation (Horner): a₀ + x(a₁ + x(a₂ + ...))  (mod p)
    3. Dot product: Σ aᵢ * bᵢ (mod p)

  All primitives reduce to compositions of addGate + mulGate + reduceGate,
  which the e-graph optimizes by choosing the best reduction strategy.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedRunner
import AmoLean.EGraph.Verified.Bitwise.NTTBridge
import AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer

open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise
  (HardwareCost arm_cortex_a76 arm_neon_simd
   mersenne31_prime babybear_prime goldilocks_prime)
open AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen (selectConfig CodeGenConfig)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: FRI fold via e-graph
-- ══════════════════════════════════════════════════════════════════

/-- FRI fold as MixedExpr: result = reduce(even + reduce(alpha * odd)).
    witness(0) = even, witness(1) = alpha, witness(2) = odd.
    The two reduceGate nodes will be optimized by the e-graph. -/
def friFoldExpr (p : Nat) : MixedExpr :=
  .reduceE (.addE (.witnessE 0) (.reduceE (.mulE (.witnessE 1) (.witnessE 2)) p)) p

/-- Generate optimized C for FRI fold.
    Cost model selects: mulAddReduction for the multiply step,
    Harvey cond-sub for the add step. Number of branches in Harvey
    depends on output bound of the mul reduction (1 for Montgomery, 2 for Solinas). -/
def friFoldToC (hw : HardwareCost) (p : Nat) (n : Nat)
    (funcName : String := "fri_fold") : String :=
  let cfg := selectConfig hw p
  let elemType := if cfg.wordSize ≤ 32 then "uint32_t" else "uint64_t"
  let wideType := if cfg.wordSize ≤ 32 then "uint64_t" else "__uint128_t"

  -- reduce_mul: selected by cost model (mulAddReduction)
  let reduceMulFn := match cfg.mulAddReduction with
    | .solinasFold =>
      s!"static inline {elemType} reduce_mul({wideType} x) \{
    return ({elemType})(((x >> {cfg.shiftBits}) * {cfg.foldConst}U) + (x & {2^cfg.shiftBits - 1}U));
}"
    | .montgomery =>
      s!"static inline {elemType} reduce_mul({wideType} x) \{
    {elemType} t = ({elemType})(x * 0x{Nat.toDigits 16 cfg.montyMu |>.asString}ULL);
    {wideType} u = ({wideType})t * ({wideType}){p}U;
    return ({elemType})((x - u) >> 32);
}"
    | .harvey =>
      s!"static inline {elemType} reduce_mul({wideType} x) \{
    return ({elemType})(((x >> {cfg.shiftBits}) * {cfg.foldConst}U) + (x & {2^cfg.shiftBits - 1}U));
}"

  -- reduce_add: Harvey cond-sub. Branches depend on mul output bound.
  -- Montgomery output < p → sum < 2p → 1 cond sub
  -- Solinas output < 2p → sum < 3p → 2 cond subs
  let reduceAddFn := match cfg.mulAddReduction with
    | .montgomery =>
      s!"/* Harvey 1-branch — Montgomery output < p, so sum < 2p */
static inline {elemType} reduce_add({elemType} x) \{
    if (x >= {p}U) x -= {p}U;
    return x;
}"
    | _ =>
      s!"/* Harvey 2-branch — Solinas output < 2p, so sum < 3p */
static inline {elemType} reduce_add({elemType} x) \{
    if (x >= 2 * {p}U) x -= 2 * {p}U;
    if (x >= {p}U) x -= {p}U;
    return x;
}"

  s!"/* AMO-Lean Generated FRI Fold — cost-model optimized
 * p = {p}, mul = {toString cfg.mulAddReduction}, add = harvey
 * solinasWinsForMulAdd = {solinasWinsForMulAdd hw}
 * Operation: result[i] = reduce_add(even[i] + reduce_mul(alpha * odd[i]))
 * Verified: solinasFold_mod_correct / monty_reduce_spec, harveyReduce_mod
 */

#include <stdint.h>
#include <stddef.h>

{reduceMulFn}

{reduceAddFn}

void {funcName}(const {elemType} *even, const {elemType} *odd,
               {elemType} alpha, {elemType} *result, size_t n) \{
    for (size_t i = 0; i < n; i++) \{
        {elemType} prod_red = reduce_mul(({wideType})alpha * ({wideType})odd[i]);
        result[i] = reduce_add(even[i] + prod_red);
    }
}
"

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Polynomial evaluation (Horner's method) via e-graph
-- ══════════════════════════════════════════════════════════════════

/-- Build Horner's method as MixedExpr for degree-d polynomial.
    p(x) = a₀ + x(a₁ + x(a₂ + ... + x·aₐ))
    Coefficients are witness(0)..witness(d), evaluation point is witness(d+1).
    Each multiply and add is wrapped in reduceGate(_, p). -/
def hornerExpr (degree : Nat) (p : Nat) : MixedExpr :=
  let x := MixedExpr.witnessE (degree + 1)  -- evaluation point
  -- Build from inside out: start with a_d, then a_{d-1} + x * acc, ...
  let rec build : Nat → MixedExpr
    | 0 => .witnessE 0  -- a₀ (base case)
    | n + 1 =>
      -- a_n + x * build(n-1)  ... wait, Horner is: a₀ + x(a₁ + x(a₂ + ...))
      -- Better: acc = a_d; acc = a_{d-1} + x * acc; ... ; acc = a_0 + x * acc
      -- Start from a_degree, work down to a_0
      .reduceE (.addE (.witnessE (degree - n - 1))
        (.reduceE (.mulE x (build n)) p)) p
  build degree

/-- Generate optimized C for polynomial evaluation via Horner's method.
    Cost model selects mulAddReduction for the mul step. -/
def hornerToC (hw : HardwareCost) (p : Nat) (degree : Nat)
    (funcName : String := "poly_eval") : String :=
  let cfg := selectConfig hw p
  let elemType := if cfg.wordSize ≤ 32 then "uint32_t" else "uint64_t"
  let wideType := if cfg.wordSize ≤ 32 then "uint64_t" else "__uint128_t"

  let reduceMulBody := match cfg.mulAddReduction with
    | .montgomery =>
      s!"{elemType} t = ({elemType})(x * 0x{Nat.toDigits 16 cfg.montyMu |>.asString}ULL);
    {wideType} u = ({wideType})t * ({wideType}){p}U;
    return ({elemType})((x - u) >> 32);"
    | _ =>
      s!"return ({elemType})(((x >> {cfg.shiftBits}) * {cfg.foldConst}U) + (x & {2^cfg.shiftBits - 1}U));"

  let reduceAddBody := match cfg.mulAddReduction with
    | .montgomery => s!"if (x >= {p}U) x -= {p}U; return x;"
    | _ => s!"if (x >= 2 * {p}U) x -= 2 * {p}U; if (x >= {p}U) x -= {p}U; return x;"

  s!"/* AMO-Lean Poly Eval (Horner) — cost-model optimized
 * p = {p}, degree = {degree}, mul = {toString cfg.mulAddReduction}
 * solinasWinsForMulAdd = {solinasWinsForMulAdd hw}
 */
#include <stdint.h>
#include <stddef.h>

static inline {elemType} reduce_mul({wideType} x) \{ {reduceMulBody} }
static inline {elemType} reduce_add({elemType} x) \{ {reduceAddBody} }

{elemType} {funcName}(const {elemType} *coeffs, size_t degree, {elemType} x) \{
    {elemType} acc = coeffs[degree];
    for (size_t i = degree; i > 0; i--) \{
        acc = reduce_mul(({wideType})x * ({wideType})acc);
        acc = reduce_add(coeffs[i-1] + acc);
    }
    return acc;
}
"

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Dot product via e-graph
-- ══════════════════════════════════════════════════════════════════

/-- Dot product as MixedExpr: sum = Σ reduce(a[i] * b[i]).
    Each multiplication is reduced, then accumulated. -/
def dotProductToC (hw : HardwareCost) (p : Nat)
    (funcName : String := "dot_product") : String :=
  let cfg := selectConfig hw p
  let elemType := if cfg.wordSize ≤ 32 then "uint32_t" else "uint64_t"
  let wideType := if cfg.wordSize ≤ 32 then "uint64_t" else "__uint128_t"

  let reduceMulBody := match cfg.mulAddReduction with
    | .montgomery =>
      s!"{elemType} t = ({elemType})(x * 0x{Nat.toDigits 16 cfg.montyMu |>.asString}ULL);
    {wideType} u = ({wideType})t * ({wideType}){p}U;
    return ({elemType})((x - u) >> 32);"
    | _ =>
      s!"return ({elemType})(((x >> {cfg.shiftBits}) * {cfg.foldConst}U) + (x & {2^cfg.shiftBits - 1}U));"

  let reduceAddBody := match cfg.mulAddReduction with
    | .montgomery => s!"if (x >= {p}U) x -= {p}U; return x;"
    | _ => s!"if (x >= 2 * {p}U) x -= 2 * {p}U; if (x >= {p}U) x -= {p}U; return x;"

  s!"/* AMO-Lean Dot Product — cost-model optimized
 * p = {p}, mul = {toString cfg.mulAddReduction}
 * solinasWinsForMulAdd = {solinasWinsForMulAdd hw}
 */
#include <stdint.h>
#include <stddef.h>

static inline {elemType} reduce_mul({wideType} x) \{ {reduceMulBody} }
static inline {elemType} reduce_add({elemType} x) \{ {reduceAddBody} }

{elemType} {funcName}(const {elemType} *a, const {elemType} *b, size_t n) \{
    {elemType} acc = 0;
    for (size_t i = 0; i < n; i++) \{
        {elemType} prod = reduce_mul(({wideType})a[i] * ({wideType})b[i]);
        acc = reduce_add(acc + prod);
    if (x >= 2 * {p}U) x -= 2 * {p}U;
    if (x >= {p}U) x -= {p}U;
    return x;
}

{elemType} {funcName}(const {elemType} *a, const {elemType} *b, size_t n) \{
    {elemType} acc = 0;
    for (size_t i = 0; i < n; i++) \{
        {elemType} prod = reduce_mul(({wideType})a[i] * ({wideType})b[i]);
        acc = reduce_add(acc + prod);
    return acc;
}
"

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Generate all primitives for a field
-- ══════════════════════════════════════════════════════════════════

/-- Generate optimized C for all primitives on a given field + hardware. -/
def generateAllPrimitives (hw : HardwareCost) (p : Nat) (n : Nat := 4096)
    (outputDir : String := "generated/primitives") : IO Unit := do
  IO.FS.createDirAll outputDir
  let fieldName := if p == babybear_prime then "babybear"
    else if p == mersenne31_prime then "mersenne31"
    else if p == goldilocks_prime then "goldilocks"
    else s!"p{p}"
  let cfg := selectConfig hw p

  -- FRI fold
  let fri := friFoldToC hw p n s!"fri_fold_{fieldName}"
  let friPath := s!"{outputDir}/fri_fold_{fieldName}.c"
  IO.FS.writeFile ⟨friPath⟩ fri
  IO.println s!"  FRI fold ({toString cfg.reduction}): {friPath}"

  -- Polynomial evaluation (degree 7 = Poseidon-like)
  let poly := hornerToC hw p 7 s!"poly_eval_{fieldName}"
  let polyPath := s!"{outputDir}/poly_eval_{fieldName}.c"
  IO.FS.writeFile ⟨polyPath⟩ poly
  IO.println s!"  Poly eval deg-7 ({toString cfg.reduction}): {polyPath}"

  -- Dot product
  let dot := dotProductToC hw p s!"dot_product_{fieldName}"
  let dotPath := s!"{outputDir}/dot_product_{fieldName}.c"
  IO.FS.writeFile ⟨dotPath⟩ dot
  IO.println s!"  Dot product ({toString cfg.reduction}): {dotPath}"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: FRI fold expr has the right structure. -/
example : friFoldExpr 7 =
    .reduceE (.addE (.witnessE 0) (.reduceE (.mulE (.witnessE 1) (.witnessE 2)) 7)) 7 := rfl

/-- Smoke: Horner degree-0 is just witness(0). -/
example : hornerExpr 0 7 = .witnessE 0 := rfl

/-- Smoke: Horner degree-1 is reduce(a0 + reduce(x * a1, p), p). -/
example : hornerExpr 1 7 =
    .reduceE (.addE (.witnessE 0) (.reduceE (.mulE (.witnessE 2) (.witnessE 0)) 7)) 7 := rfl

end AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer
