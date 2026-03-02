/-
  AmoLean.EGraph.VerifiedExtraction.Integration — End-to-End Integration + Tests

  Composes all VerifiedExtraction components for CircuitNodeOp:
  - Smoke tests for empty graph extraction
  - Unit tests for CircuitExpr.eval
  - Instantiation of extractF_correct for circuits
  - End-to-end correctness theorem
-/
import AmoLean.EGraph.VerifiedExtraction.CircuitAdaptor

namespace AmoLean.EGraph.VerifiedExtraction.Integration

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.VerifiedExtraction.Greedy
  (Extractable EvalExpr ExtractableSound extractF extractAuto
   extractF_correct extractAuto_correct)
open AmoLean.EGraph.VerifiedExtraction.CircuitAdaptor
  (CircuitExpr circuit_extractable_sound)
open AmoLean.EGraph.Verified (CircuitNodeOp CircuitEnv)

/-! ## Test Environment -/

private def testEnv : CircuitEnv Int :=
  ⟨Int.ofNat, fun _ => 0, fun _ => 0⟩

private def witnessEnv : CircuitEnv Int :=
  ⟨fun _ => 0, fun _ => 99, fun _ => 0⟩

private def pubInputEnv : CircuitEnv Int :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 77⟩

/-! ## Smoke Tests -/

/-- Smoke: greedy extraction from empty graph yields none. -/
theorem smoke_greedy_empty :
    extractF (Op := CircuitNodeOp) (Expr := CircuitExpr) EGraph.empty 0 10 = none := by
  simp [extractF, EGraph.empty, UnionFind.root, UnionFind.rootD, UnionFind.empty]

/-- Smoke: CircuitNodeOp satisfies ExtractableSound. -/
theorem smoke_circuit_sound :
    ExtractableSound CircuitNodeOp CircuitExpr (CircuitEnv Int) Int :=
  circuit_extractable_sound

/-! ## CircuitExpr.eval Unit Tests -/

/-- eval of constE returns the constant. -/
example : (CircuitExpr.constE 42).eval (Val := Int) testEnv = 42 := rfl

/-- eval of addE computes addition. -/
example : (CircuitExpr.addE (.constE 3) (.constE 4)).eval (Val := Int) testEnv = 7 := rfl

/-- eval of mulE computes multiplication. -/
example : (CircuitExpr.mulE (.constE 3) (.constE 4)).eval (Val := Int) testEnv = 12 := rfl

/-- eval of negE computes negation. -/
example : (CircuitExpr.negE (.constE 5)).eval (Val := Int) testEnv = -5 := rfl

/-- eval of smulE computes scalar multiplication. -/
example : (CircuitExpr.smulE 3 (.constE 4)).eval (Val := Int) testEnv = 12 := rfl

/-- eval of witnessE returns the witness value. -/
example : (CircuitExpr.witnessE 0).eval (Val := Int) witnessEnv = 99 := rfl

/-- eval of pubInputE returns the public input value. -/
example : (CircuitExpr.pubInputE 1).eval (Val := Int) pubInputEnv = 77 := rfl

/-! ## Nested Expression Test -/

/-- eval of a nested expression: neg(add(const 3, mul(const 2, const 5))). -/
example : (CircuitExpr.negE (.addE (.constE 3) (.mulE (.constE 2) (.constE 5)))).eval
    (Val := Int) testEnv = -13 := rfl

/-- Deeply nested: smul(2, add(mul(const 3, const 4), neg(const 1))). -/
example : (CircuitExpr.smulE 2
    (.addE (.mulE (.constE 3) (.constE 4)) (.negE (.constE 1)))).eval
    (Val := Int) testEnv = 22 := rfl

/-- All 7 constructors in one expression tree. -/
example : (CircuitExpr.addE
    (.mulE (.constE 2) (.witnessE 0))
    (.negE (.smulE 3 (.addE (.pubInputE 0) (.constE 1))))).eval
    (Val := Int) ⟨Int.ofNat, fun _ => 5, fun _ => 10⟩ = -23 := rfl

/-! ## End-to-End Correctness -/

/-- The generic extractF_correct theorem instantiates cleanly for CircuitNodeOp.
    This is the master correctness result: if the circuit e-graph has a consistent
    valuation and a well-formed union-find, then greedy extraction produces
    expressions that evaluate to the semantic value of the root class. -/
theorem circuit_extractF_correct
    {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (g : EGraph CircuitNodeOp) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (fuel : Nat) (classId : EClassId) (expr : CircuitExpr)
    (hext : extractF g classId fuel = some expr) :
    EvalExpr.evalExpr expr env = v (UnionFind.root g.unionFind classId) :=
  extractF_correct g env v hcv hwf hbni circuit_extractable_sound fuel classId expr hext

/-- Corollary: extractAuto is also correct for circuits. -/
theorem circuit_extractAuto_correct
    {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (g : EGraph CircuitNodeOp) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (rootId : EClassId) (expr : CircuitExpr)
    (hext : extractAuto g rootId = some expr) :
    EvalExpr.evalExpr expr env = v (UnionFind.root g.unionFind rootId) :=
  extractAuto_correct g env v hcv hwf hbni circuit_extractable_sound rootId expr hext

end AmoLean.EGraph.VerifiedExtraction.Integration
