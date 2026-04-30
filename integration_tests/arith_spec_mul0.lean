-- ArithExpr spec exercising arity preservation: x0 * 0. Optimizer reduces to 0,
-- eliminating the variable; codegen must still emit a 1-ary function so the
-- caller interface stays stable.
open TRZK (ArithExpr)

def spec : ArithExpr := .mul (.var 0) (.const 0)
