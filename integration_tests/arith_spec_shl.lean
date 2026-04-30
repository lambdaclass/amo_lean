-- ArithExpr spec exercising `shl`: y = x0 << x1 (via isize::unbounded_shl).
open TRZK (ArithExpr)

def spec : ArithExpr := .shl (.var 0) (.var 1)
