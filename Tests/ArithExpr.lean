import TRZK.ArithExpr

open TRZK

#guard ArithExpr.size (.const 0) == 1
#guard ArithExpr.size (.var 5) == 1
#guard ArithExpr.size (.add (.var 0) (.const 0)) == 3
#guard ArithExpr.size (.add (.add (.var 0) (.var 1)) (.const 7)) == 5
#guard ArithExpr.size (.mul (.var 0) (.const 1)) == 3
#guard ArithExpr.size (.mul (.add (.var 0) (.var 1)) (.var 2)) == 5

#guard (ArithExpr.const 0 : ArithExpr) == .const 0
#guard (ArithExpr.add (.var 0) (.const 0)) != (.add (.const 0) (.var 0))
#guard (ArithExpr.mul (.var 0) (.const 1)) != (.mul (.const 1) (.var 0))
#guard (ArithExpr.mul (.var 0) (.var 1)) != (.add (.var 0) (.var 1))
