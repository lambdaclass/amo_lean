namespace TRZK

/-- Arithmetic AST. The surface type users write specs in. -/
inductive ArithExpr where
  | const : Int → ArithExpr
  | var   : Nat → ArithExpr
  | add   : ArithExpr → ArithExpr → ArithExpr
  | mul   : ArithExpr → ArithExpr → ArithExpr
  | idiv  : ArithExpr → ArithExpr → ArithExpr
  | shl   : ArithExpr → ArithExpr → ArithExpr
  | shr   : ArithExpr → ArithExpr → ArithExpr
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Number of AST nodes. -/
def ArithExpr.size : ArithExpr → Nat
  | .const _  => 1
  | .var _    => 1
  | .add a b  => 1 + a.size + b.size
  | .mul a b  => 1 + a.size + b.size
  | .idiv a b => 1 + a.size + b.size
  | .shl a b  => 1 + a.size + b.size
  | .shr a b  => 1 + a.size + b.size

/-- Positional input arity: one more than the largest var index, or 0 if no
    vars. Computed pre-optimization so codegen preserves the source signature
    even when rules eliminate variable references (e.g. `a - a => 0`). -/
def ArithExpr.inputArity : ArithExpr → Nat
  | .const _  => 0
  | .var i    => i + 1
  | .add a b  => Nat.max a.inputArity b.inputArity
  | .mul a b  => Nat.max a.inputArity b.inputArity
  | .idiv a b => Nat.max a.inputArity b.inputArity
  | .shl a b  => Nat.max a.inputArity b.inputArity
  | .shr a b  => Nat.max a.inputArity b.inputArity

end TRZK
