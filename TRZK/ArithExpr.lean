namespace TRZK

/-- Arithmetic AST. The surface type users write specs in. -/
inductive ArithExpr where
  | const : Int → ArithExpr
  | var   : Nat → ArithExpr
  | add   : ArithExpr → ArithExpr → ArithExpr
  | mul   : ArithExpr → ArithExpr → ArithExpr
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Number of AST nodes. -/
def ArithExpr.size : ArithExpr → Nat
  | .const _ => 1
  | .var _   => 1
  | .add a b => 1 + a.size + b.size
  | .mul a b => 1 + a.size + b.size

end TRZK
