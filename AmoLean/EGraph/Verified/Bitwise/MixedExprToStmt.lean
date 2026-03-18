/-
  AmoLean.EGraph.Verified.Bitwise.MixedExprToStmt — Convert MixedExpr to codegen IR

  Converts MixedExpr (AMO-Lean's extracted expression) to a lightweight C-level
  IR suitable for emission as C source code. The IR (CodegenExpr) mirrors
  Trust-Lean's LowLevelExpr without importing it, keeping the Bitwise/ directory
  self-contained.

  Provides:
  - CodegenBinOp: mirrors Trust-Lean's BinOp (bitwise subset)
  - CodegenExpr: lightweight IR for C code emission
  - toCodegenExpr: 13-case conversion function
  - evalCodegenExpr: evaluation on Int (for soundness reasoning)
  - toCodegenExpr_sound: soundness for the bitwise subset (Nat to Int cast)
  - CodegenExpr.toC: pretty-printer to C syntax
  - emitCFunction: full C function emitter

  Design: Trust-Lean integration happens in SynthesisToC.lean (B87); this file
  provides the AMO-Lean side of the bridge.
-/
import AmoLean.EGraph.Verified.Bitwise.EnhancedCostModel
import Mathlib.Data.Int.Bitwise

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified (CircuitEnv)

/-! ## CodegenBinOp: Binary operations for C-level IR -/

/-- Binary operations mirroring Trust-Lean's BinOp (bitwise + arithmetic subset).
    Covers all operations needed by the Solinas fold codegen path. -/
inductive CodegenBinOp where
  | add   -- +
  | sub   -- -
  | mul   -- *
  | band  -- &
  | bor   -- |
  | bxor  -- ^
  | bshl  -- <<
  | bshr  -- >>
  deriving Repr, DecidableEq, BEq

/-! ## CodegenExpr: Lightweight C-level IR -/

/-- Lightweight expression IR for C code emission.
    Mirrors Trust-Lean's LowLevelExpr without importing it.
    - `litInt`: integer literal
    - `varRef`: variable reference (witness, public input, etc.)
    - `binOp`: binary operation
    Negation is represented as `binOp .sub (litInt 0) e`. -/
inductive CodegenExpr where
  | litInt : Int → CodegenExpr
  | varRef : String → CodegenExpr
  | binOp  : CodegenBinOp → CodegenExpr → CodegenExpr → CodegenExpr
  deriving Repr

/-! ## Conversion: MixedExpr to CodegenExpr -/

/-- Convert a MixedExpr to CodegenExpr for C code emission.
    `constLookup` resolves constant indices to their Int values.
    Each of the 13 MixedExpr constructors maps to a CodegenExpr. -/
def toCodegenExpr (e : MixedExpr) (constLookup : Nat → Int) : CodegenExpr :=
  match e with
  | .constE n        => .litInt (constLookup n)
  | .witnessE n      => .varRef s!"w_{n}"
  | .pubInputE n     => .varRef s!"pub_{n}"
  | .addE a b        => .binOp .add (toCodegenExpr a constLookup) (toCodegenExpr b constLookup)
  | .mulE a b        => .binOp .mul (toCodegenExpr a constLookup) (toCodegenExpr b constLookup)
  | .negE a          => .binOp .sub (.litInt 0) (toCodegenExpr a constLookup)
  | .smulE n a       => .binOp .mul (.litInt (constLookup n)) (toCodegenExpr a constLookup)
  | .shiftLeftE a n  => .binOp .bshl (toCodegenExpr a constLookup) (.litInt (↑n))
  | .shiftRightE a n => .binOp .bshr (toCodegenExpr a constLookup) (.litInt (↑n))
  | .bitAndE a b     => .binOp .band (toCodegenExpr a constLookup) (toCodegenExpr b constLookup)
  | .bitXorE a b     => .binOp .bxor (toCodegenExpr a constLookup) (toCodegenExpr b constLookup)
  | .bitOrE a b      => .binOp .bor  (toCodegenExpr a constLookup) (toCodegenExpr b constLookup)
  | .constMaskE n    => .litInt (↑(2 ^ n - 1 : Nat))
  | .subE a b        => .binOp .sub (toCodegenExpr a constLookup) (toCodegenExpr b constLookup)

/-! ## Evaluation of CodegenExpr on Int -/

/-- Evaluate a CodegenExpr in the Int domain.
    Variable references are resolved via `env : String → Int`. -/
def evalCodegenExpr (e : CodegenExpr) (env : String → Int) : Int :=
  match e with
  | .litInt n       => n
  | .varRef name    => env name
  | .binOp op a b   =>
    let va := evalCodegenExpr a env
    let vb := evalCodegenExpr b env
    match op with
    | .add  => va + vb
    | .sub  => va - vb
    | .mul  => va * vb
    | .band => Int.land va vb
    | .bor  => Int.lor va vb
    | .bxor => Int.xor va vb
    | .bshl => Int.shiftLeft va vb.toNat
    | .bshr => Int.shiftRight va vb.toNat

/-! ## Soundness: toCodegenExpr preserves evaluation (bitwise subset) -/

/-- A MixedExpr is in the "bitwise subset" if it only uses constructors that
    have clean Nat to Int semantics: constE, witnessE, pubInputE, shiftLeftE,
    shiftRightE, bitAndE, bitXorE, bitOrE, constMaskE, addE, mulE, smulE.
    negE is excluded because Nat negation returns 0 while Int negation
    returns the additive inverse. -/
inductive IsBitwiseSubset : MixedExpr → Prop where
  | constE      : ∀ (n : Nat), IsBitwiseSubset (.constE n)
  | witnessE    : ∀ (n : Nat), IsBitwiseSubset (.witnessE n)
  | pubInputE   : ∀ (n : Nat), IsBitwiseSubset (.pubInputE n)
  | addE        : ∀ (ea eb : MixedExpr), IsBitwiseSubset ea → IsBitwiseSubset eb →
                  IsBitwiseSubset (.addE ea eb)
  | mulE        : ∀ (ea eb : MixedExpr), IsBitwiseSubset ea → IsBitwiseSubset eb →
                  IsBitwiseSubset (.mulE ea eb)
  | smulE       : ∀ (n : Nat) (ea : MixedExpr), IsBitwiseSubset ea →
                  IsBitwiseSubset (.smulE n ea)
  | shiftLeftE  : ∀ (ea : MixedExpr) (n : Nat), IsBitwiseSubset ea →
                  IsBitwiseSubset (.shiftLeftE ea n)
  | shiftRightE : ∀ (ea : MixedExpr) (n : Nat), IsBitwiseSubset ea →
                  IsBitwiseSubset (.shiftRightE ea n)
  | bitAndE     : ∀ (ea eb : MixedExpr), IsBitwiseSubset ea → IsBitwiseSubset eb →
                  IsBitwiseSubset (.bitAndE ea eb)
  | bitXorE     : ∀ (ea eb : MixedExpr), IsBitwiseSubset ea → IsBitwiseSubset eb →
                  IsBitwiseSubset (.bitXorE ea eb)
  | bitOrE      : ∀ (ea eb : MixedExpr), IsBitwiseSubset ea → IsBitwiseSubset eb →
                  IsBitwiseSubset (.bitOrE ea eb)
  | constMaskE  : ∀ (n : Nat), IsBitwiseSubset (.constMaskE n)

/-- Environment consistency: the CodegenExpr String-keyed env agrees with
    the MixedEnv Nat-keyed env, and constLookup matches env.constVal. -/
structure EnvConsistent (env : CircuitEnv Nat) (constLookup : Nat → Int)
    (cgEnv : String → Int) : Prop where
  hconst : ∀ (n : Nat), constLookup n = ↑(env.constVal n)
  hwit   : ∀ (n : Nat), cgEnv s!"w_{n}" = ↑(env.witnessVal n)
  hpub   : ∀ (n : Nat), cgEnv s!"pub_{n}" = ↑(env.pubInputVal n)

/-! ### Cast helper lemmas: Nat bitwise to Int bitwise -/

private theorem nat_shiftLeft_cast (a n : Nat) :
    (↑(Nat.shiftLeft a n) : Int) = Int.shiftLeft (↑a) n := by
  simp [Nat.shiftLeft_eq, Int.shiftLeft]

private theorem nat_shiftRight_cast (a n : Nat) :
    (↑(Nat.shiftRight a n) : Int) = Int.shiftRight (↑a) n := by
  simp [Nat.shiftRight_eq, Int.shiftRight]

private theorem nat_land_cast (a b : Nat) :
    Int.land (↑a) (↑b) = ↑(Nat.land a b) := by
  show Int.land (↑a) (↑b) = ↑(a &&& b); simp [Int.land]

private theorem nat_xor_cast (a b : Nat) :
    Int.xor (↑a) (↑b) = ↑(Nat.xor a b) := by
  show Int.xor (↑a) (↑b) = ↑(a ^^^ b); simp [Int.xor]

private theorem nat_lor_cast (a b : Nat) :
    Int.lor (↑a) (↑b) = ↑(Nat.lor a b) := by
  show Int.lor (↑a) (↑b) = ↑(a ||| b); simp [Int.lor]

/-- Soundness of MixedExpr → CodegenExpr translation for the bitwise subset.

    Proves: evalCodegenExpr(toCodegenExpr e) = ↑(MixedExpr.eval e) when environments agree.

    **Verification chain** (distributed across projects):
    1. This theorem: MixedExpr.eval (Nat) = evalCodegenExpr (Int) [AMO-Lean]
    2. toCodegenExpr → Trust-Lean LowLevelExpr [bridge, not in this file]
    3. stmtToMicroC_correct: Stmt eval = MicroC eval [Trust-Lean]
    4. microCToString roundtrip: parse(emit(mc)) = mc [Trust-Lean]

    The `EnvConsistent` hypothesis bridges AMO-Lean's `CircuitEnv Nat` to the
    `String → Int` environment used by CodegenExpr. In the full pipeline, this
    is established by `synthesizeAndEmitC` which constructs both environments
    from the same `SolinasConfig`. -/
theorem toCodegenExpr_sound (e : MixedExpr) (env : CircuitEnv Nat)
    (constLookup : Nat → Int) (cgEnv : String → Int)
    (henv : EnvConsistent env constLookup cgEnv)
    (hsub : IsBitwiseSubset e) :
    evalCodegenExpr (toCodegenExpr e constLookup) cgEnv = ↑(e.eval env) := by
  induction hsub with
  | constE n =>
    simp [toCodegenExpr, evalCodegenExpr, MixedExpr.eval, henv.hconst]
  | witnessE n =>
    simp [toCodegenExpr, evalCodegenExpr, MixedExpr.eval, henv.hwit]
  | pubInputE n =>
    simp [toCodegenExpr, evalCodegenExpr, MixedExpr.eval, henv.hpub]
  | @addE ea eb _ _ iha ihb =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha, ihb]; simp [Nat.cast_add]
  | @mulE ea eb _ _ iha ihb =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha, ihb]; simp [Nat.cast_mul]
  | @smulE n ea _ iha =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha, henv.hconst]; simp [Nat.cast_mul]
  | @shiftLeftE ea n _ iha =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha]; simp [Int.toNat, Nat.shiftLeft_eq, Int.shiftLeft]
  | @shiftRightE ea n _ iha =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha]; simp [Int.toNat, Nat.shiftRight_eq, Int.shiftRight]
  | @bitAndE ea eb _ _ iha ihb =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha, ihb]; exact nat_land_cast _ _
  | @bitXorE ea eb _ _ iha ihb =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha, ihb]; exact nat_xor_cast _ _
  | @bitOrE ea eb _ _ iha ihb =>
    simp only [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]
    rw [iha, ihb]; exact nat_lor_cast _ _
  | constMaskE n =>
    simp [toCodegenExpr, evalCodegenExpr, MixedExpr.eval]

/-! ## C Code Pretty-Printer -/

/-- Render a CodegenBinOp as its C operator symbol. -/
def CodegenBinOp.toC : CodegenBinOp → String
  | .add  => "+"
  | .sub  => "-"
  | .mul  => "*"
  | .band => "&"
  | .bor  => "|"
  | .bxor => "^"
  | .bshl => "<<"
  | .bshr => ">>"

/-- Pretty-print a CodegenExpr as a C expression string.
    All binary operations are parenthesized for unambiguous precedence. -/
def CodegenExpr.toC : CodegenExpr → String
  | .litInt n    => if n < 0 then s!"({n})" else s!"{n}"
  | .varRef name => name
  | .binOp op a b => s!"({a.toC} {op.toC} {b.toC})"

/-- Emit a complete C function wrapping a MixedExpr.
    Generates `uint64_t funcName(uint64_t inputVar) { return ...; }`. -/
def emitCFunction (funcName : String) (inputVar : String) (e : MixedExpr)
    (constLookup : Nat → Int) : String :=
  let body := (toCodegenExpr e constLookup).toC
  s!"uint64_t {funcName}(uint64_t {inputVar}) \{\n  return {body};\n}"

/-! ## Demonstrations -/

-- Simple witness reference
#eval toCodegenExpr (.witnessE 0) (fun _ => 0) |>.toC
-- "w_0"

-- Bitwise AND of two witnesses
#eval toCodegenExpr (.bitAndE (.witnessE 0) (.witnessE 1)) (fun _ => 0) |>.toC
-- "(w_0 & w_1)"

-- Shift left by 32
#eval toCodegenExpr (.shiftLeftE (.witnessE 0) 32) (fun _ => 0) |>.toC
-- "(w_0 << 32)"

-- Solinas-style fold: (x >> 32) + (x & 0xFFFFFFFF)
private def solinasFoldExpr : MixedExpr :=
  .addE (.shiftRightE (.witnessE 0) 32) (.bitAndE (.witnessE 0) (.constMaskE 32))

#eval toCodegenExpr solinasFoldExpr (fun _ => 0) |>.toC
-- "((w_0 >> 32) + (w_0 & 4294967295))"

-- Full C function emission
#eval emitCFunction "goldilocks_reduce" "x" solinasFoldExpr (fun _ => 0)
-- "uint64_t goldilocks_reduce(uint64_t x) {\n  return ((w_0 >> 32) + (w_0 & 4294967295));\n}"

-- Negation case (0 - x)
#eval toCodegenExpr (.negE (.witnessE 0)) (fun _ => 0) |>.toC
-- "(0 - w_0)"

-- Scalar multiply: 3 * w_0 (constLookup maps 0 to 3)
#eval toCodegenExpr (.smulE 0 (.witnessE 0)) (fun n => if n == 0 then 3 else 0) |>.toC
-- "(3 * w_0)"

-- constMask 64: 2^64 - 1
#eval toCodegenExpr (.constMaskE 64) (fun _ => 0) |>.toC
-- "18446744073709551615"

-- Public input reference
#eval toCodegenExpr (.pubInputE 3) (fun _ => 0) |>.toC
-- "pub_3"

-- XOR of witnesses
#eval toCodegenExpr (.bitXorE (.witnessE 0) (.witnessE 1)) (fun _ => 0) |>.toC
-- "(w_0 ^ w_1)"

-- OR of witnesses
#eval toCodegenExpr (.bitOrE (.witnessE 2) (.witnessE 3)) (fun _ => 0) |>.toC
-- "(w_2 | w_3)"

/-! ## Non-vacuity: toCodegenExpr_sound hypotheses are jointly satisfiable -/

/-- Non-vacuity witness for EnvConsistent: all three conditions can be simultaneously
    satisfied when cgEnv maps every string to 0 and env values are all 0. -/
private def nvEnv : CircuitEnv Nat := ⟨fun _ => 7, fun _ => 0, fun _ => 0⟩
private def nvConstLookup : Nat → Int := fun _ => 7
private def nvCgEnv : String → Int := fun _ => 0

private theorem nvEnvConsistent : EnvConsistent nvEnv nvConstLookup nvCgEnv :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Non-vacuity: the soundness theorem applies to a concrete Solinas fold expression
    (add + shiftRight + bitAnd + constMask + witness). All five hypotheses are
    jointly satisfiable, and the conclusion holds by computation. -/
example : evalCodegenExpr (toCodegenExpr solinasFoldExpr nvConstLookup) nvCgEnv
    = ↑(solinasFoldExpr.eval nvEnv) :=
  toCodegenExpr_sound solinasFoldExpr nvEnv nvConstLookup nvCgEnv
    nvEnvConsistent
    (.addE _ _ (.shiftRightE _ 32 (.witnessE 0)) (.bitAndE _ _ (.witnessE 0) (.constMaskE 32)))

/-- Non-vacuity: constE case — constant lookup preserves value. -/
example : evalCodegenExpr (toCodegenExpr (.constE 0) nvConstLookup) nvCgEnv
    = ↑(MixedExpr.eval (.constE 0) nvEnv) :=
  toCodegenExpr_sound (.constE 0) nvEnv nvConstLookup nvCgEnv
    nvEnvConsistent (.constE 0)

/-- Non-vacuity: bitXorE case — XOR of two witnesses. -/
example : evalCodegenExpr
    (toCodegenExpr (.bitXorE (.witnessE 0) (.witnessE 1)) nvConstLookup) nvCgEnv
    = ↑(MixedExpr.eval (.bitXorE (.witnessE 0) (.witnessE 1)) nvEnv) :=
  toCodegenExpr_sound _ nvEnv nvConstLookup nvCgEnv
    nvEnvConsistent (.bitXorE _ _ (.witnessE 0) (.witnessE 1))

end AmoLean.EGraph.Verified.Bitwise
