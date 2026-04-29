-- ArithExpr spec exercising `mul`: (x0 * 1) * x1. Optimizer should reduce it to x0 * x1.
open TRZK (ArithExpr)

def spec : ArithExpr := .mul (.mul (.var 0) (.const 1)) (.var 1)
