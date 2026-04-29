-- ArithExpr spec exercising `add`: x0 + 0. Optimizer should reduce it to x0.
open TRZK (ArithExpr)

def spec : ArithExpr := .add (.var 0) (.const 0)
