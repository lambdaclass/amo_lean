import TRZK.ArithOp
import TRZK.Rule

open LambdaSat

namespace TRZK

/-- Recursively embed an `ArithExpr` into an `EGraph`.
    Returns the root e-class id and the updated graph. -/
partial def embed (g : EGraph ArithOp) : ArithExpr → (EClassId × EGraph ArithOp)
  | .const n  => g.add ⟨.const n⟩
  | .var i    => g.add ⟨.var i⟩
  | .add a b  =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.add ia ib⟩
  | .mul a b =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.mul ia ib⟩
  | .idiv a b =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.idiv ia ib⟩
  | .shl a b =>
    let (ia, g1) := embed g a
    let (ib, g2) := embed g1 b
    g2.add ⟨.shl ia ib⟩

/-- End-to-end optimization: embed → saturate → extract lowest-cost form.
    Fuel constants (50, 10, 50) are sized for v0 with a single rule; revisit
    when rules can explode the graph. -/
def optimize (expr : ArithExpr) : Option ArithExpr :=
  let (rootId, g0) := embed .empty expr
  let g_sat  := saturateF (fuel := 50) (maxIter := 10) (rebuildFuel := 50) g0 allRules
  let g_cost := computeCostsF g_sat (fun _ => 1) 50
  extractAuto g_cost rootId

end TRZK
