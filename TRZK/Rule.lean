import TRZK.ArithOp

open LambdaSat

namespace TRZK

/-- Right-identity of `Add`: `e + 0 → e`. -/
def addZeroRight : RewriteRule ArithOp where
  name := "add_zero_right"
  lhs := .node (.add 0 0) [.patVar 0, .node (.const 0) []]
  rhs := .patVar 0

/-- Right-identity of `Mul`: `e * 1 → e`. -/
def mulOneRight : RewriteRule ArithOp where
  name := "mul_one_right"
  lhs := .node (.mul 0 0) [.patVar 0, .node (.const 1) []]
  rhs := .patVar 0

/-- Right-identity of `IDiv`: `e / 1 → e`. -/
def idivOneRight : RewriteRule ArithOp where
  name := "idiv_one_right"
  lhs := .node (.idiv 0 0) [.patVar 0, .node (.const 1) []]
  rhs := .patVar 0

/-- Shift-by-zero is identity: `e << 0 → e`. -/
def shlZeroRight : RewriteRule ArithOp where
  name := "shl_zero_right"
  lhs := .node (.shl 0 0) [.patVar 0, .node (.const 0) []]
  rhs := .patVar 0

/-- Right-identity of `Shr` (logical right shift): `e >> 0 → e`. -/
def shrZeroRight : RewriteRule ArithOp where
  name := "shr_zero_right"
  lhs := .node (.shr 0 0) [.patVar 0, .node (.const 0) []]
  rhs := .patVar 0

/-- Registry of active rewrite rules. Adding a rule is a one-line change here. -/
def allRules : List (RewriteRule ArithOp) :=
  [addZeroRight, mulOneRight, idivOneRight, shlZeroRight, shrZeroRight]

end TRZK
