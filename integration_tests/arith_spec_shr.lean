-- ArithExpr spec exercising `shr`: x0 >> 0. Optimizer should reduce it to x0.
open TRZK (ArithExpr)

def spec : ArithExpr := .shr (.var 0) (.const 0)
