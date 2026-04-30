import TRZK.ArithExpr

namespace TRZK

private def usedVarsAux (arity : Nat) : ArithExpr → Array Bool → Array Bool
  | .const _,  used => used
  | .var i,    used => if i < arity then used.set! i true else used
  | .add a b,  used => usedVarsAux arity b (usedVarsAux arity a used)
  | .mul a b,  used => usedVarsAux arity b (usedVarsAux arity a used)
  | .idiv a b, used => usedVarsAux arity b (usedVarsAux arity a used)
  | .shl a b,  used => usedVarsAux arity b (usedVarsAux arity a used)
  | .shr a b,  used => usedVarsAux arity b (usedVarsAux arity a used)

/-- Boolean array of length `arity`: `used[i]` is true iff `e` references
    `var i`. Vars with index ≥ arity are silently ignored (defensive: the
    contract is that callers pass `arity ≥ e.inputArity`). -/
def ArithExpr.usedVars (arity : Nat) (e : ArithExpr) : Array Bool :=
  usedVarsAux arity e (Array.replicate arity false)

/-- Emit a Rust `isize` expression. Negative literals are parenthesized.
    `shr` is logical right shift; emitted via `usize::unbounded_shr`, which is
    total over any `u32` count (out-of-range counts produce 0). -/
def emitExpr : ArithExpr → String
  | .const n =>
    if n < 0 then s!"(-{-n}isize)" else s!"{n}isize"
  | .var i    => s!"x{i}"
  | .add a b  => s!"({emitExpr a} + {emitExpr b})"
  | .mul a b  => s!"({emitExpr a} * {emitExpr b})"
  | .idiv a b => s!"({emitExpr a} / {emitExpr b})"
  | .shl a b  => s!"{emitExpr a}.unbounded_shl({emitExpr b} as u32)"
  | .shr a b  => s!"(({emitExpr a} as usize).unbounded_shr({emitExpr b} as u32) as isize)"

/-- Emit a full Rust function with a fixed positional arity: parameters are
    `x0..x(arity-1)` regardless of which survive optimization. Params not
    referenced by `e` get a leading `_` to silence Rust's unused-arg lint.
    Callers should pass the *pre-optimization* arity so the signature stays
    stable when rules eliminate variable references. -/
def emitFunction (name : String) (arity : Nat) (e : ArithExpr) : String :=
  let used := e.usedVars arity
  let params := (List.range arity).map fun i =>
    if used.getD i false then s!"x{i}: isize" else s!"_x{i}: isize"
  let args := String.intercalate ", " params
  let body := emitExpr e
  s!"pub fn {name}({args}) -> isize \{ {body} }"

end TRZK
