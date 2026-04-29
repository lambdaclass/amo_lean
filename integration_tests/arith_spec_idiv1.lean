-- ArithExpr spec exercising `idiv`: x0 / 1. Optimizer should reduce it to x0.
open TRZK (ArithExpr)

def spec : ArithExpr := .idiv (.var 0) (.const 1)
