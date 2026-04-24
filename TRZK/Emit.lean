import TRZK.ArithExpr

namespace TRZK

/-- Insert `n` into a sorted-deduped list. -/
private def insertSortedDedup : Nat → List Nat → List Nat
  | n, []      => [n]
  | n, x :: xs =>
    if n < x then n :: x :: xs
    else if n == x then x :: xs
    else x :: insertSortedDedup n xs

private def collectVarsList : ArithExpr → List Nat → List Nat
  | .const _, acc => acc
  | .var i,   acc => insertSortedDedup i acc
  | .add a b, acc => collectVarsList b (collectVarsList a acc)

/-- Variables used in `e`, sorted ascending, deduplicated. -/
def collectVars (e : ArithExpr) : Array Nat :=
  (collectVarsList e []).toArray

/-- Emit a Rust `isize` expression. Negative literals are parenthesized. -/
def emitExpr : ArithExpr → String
  | .const n =>
    if n < 0 then s!"(-{-n}isize)" else s!"{n}isize"
  | .var i   => s!"x{i}"
  | .add a b => s!"({emitExpr a} + {emitExpr b})"

/-- Emit a full Rust function: `pub fn <name>(x0: isize, ...) -> isize { <body> }`.
    When the body is a bare variable or literal, no outer parens; otherwise use
    the expression's natural formatting. Zero-variable functions take no args. -/
def emitFunction (name : String) (e : ArithExpr) : String :=
  let vars := collectVars e
  let args := String.intercalate ", " (vars.toList.map (fun i => s!"x{i}: isize"))
  let body := emitExpr e
  s!"pub fn {name}({args}) -> isize \{ {body} }"

end TRZK
