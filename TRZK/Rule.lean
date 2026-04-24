import TRZK.ArithOp

open LambdaSat

namespace TRZK

/-- Right-identity of `Add`: `e + 0 → e`. -/
def addZeroRight : RewriteRule ArithOp where
  name := "add_zero_right"
  lhs := .node (.add 0 0) [.patVar 0, .node (.const 0) []]
  rhs := .patVar 0

/-- Registry of active rewrite rules. Adding a rule is a one-line change here. -/
def allRules : List (RewriteRule ArithOp) := [addZeroRight]

end TRZK
