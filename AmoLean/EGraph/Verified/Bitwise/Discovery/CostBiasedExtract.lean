/-
  AmoLean.EGraph.Verified.Bitwise.Discovery.CostBiasedExtract
  N26.4 — Cost-biased extraction from MixedEGraph

  Defines a cost model for MixedExpr that prefers shift/add over multiply,
  wraps greedy extraction with cost evaluation, and provides a semantic
  correctness theorem bridging to extractF_correct.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedExtract
import AmoLean.EGraph.Verified.Bitwise.Discovery.ReduceSpecAxiom

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open AmoLean.EGraph.Verified.Bitwise.MixedCoreSpec (MGraph MNode CId)
open AmoLean.EGraph.Verified.Bitwise.MixedSemanticSpec (CV VPMI)
open AmoLean.EGraph.VerifiedExtraction (ConsistentValuation BestNodeInv)
open AmoLean.EGraph.VerifiedExtraction.Greedy (Extractable EvalExpr ExtractableSound
  extractF extractF_correct)


/-! ## Section 1: CostBias structure -/

/-- Cost bias configuration: assigns a cost to each MixedExpr constructor.
    Lower cost = preferred in extraction selection. -/
structure CostBias where
  shiftCost   : Nat := 1
  addCost     : Nat := 1
  subCost     : Nat := 1
  mulCost     : Nat := 5
  andCost     : Nat := 1
  xorCost     : Nat := 1
  orCost      : Nat := 1
  reduceCost  : Nat := 10
  constCost   : Nat := 0
  witnessCost : Nat := 0
  deriving Repr, Inhabited, BEq

/-- Default bias: shifts and bitwise ops are cheap, multiply is expensive. -/
def CostBias.default : CostBias := {}

/-- Shift-preferring bias: shifts are near-free, multiply very expensive. -/
def CostBias.shiftPreferring : CostBias :=
  { shiftCost := 0, addCost := 1, subCost := 1, mulCost := 10,
    andCost := 1, xorCost := 1, orCost := 1, reduceCost := 15,
    constCost := 0, witnessCost := 0 }

/-- Balanced bias: all operations have similar cost. -/
def CostBias.balanced : CostBias :=
  { shiftCost := 2, addCost := 2, subCost := 2, mulCost := 3,
    andCost := 2, xorCost := 2, orCost := 2, reduceCost := 4,
    constCost := 1, witnessCost := 1 }

/-! ## Section 2: costOfExpr recursive function -/

/-- Compute the cost of a MixedExpr tree under a given bias.
    Cost is the sum of node costs over the entire tree. -/
def costOfExpr (bias : CostBias) : MixedExpr → Nat
  | .constE _           => bias.constCost
  | .witnessE _         => bias.witnessCost
  | .pubInputE _        => bias.witnessCost
  | .addE a b           => bias.addCost + costOfExpr bias a + costOfExpr bias b
  | .mulE a b           => bias.mulCost + costOfExpr bias a + costOfExpr bias b
  | .negE a             => bias.addCost + costOfExpr bias a
  | .smulE _ a          => bias.mulCost + costOfExpr bias a
  | .shiftLeftE a _     => bias.shiftCost + costOfExpr bias a
  | .shiftRightE a _    => bias.shiftCost + costOfExpr bias a
  | .bitAndE a b        => bias.andCost + costOfExpr bias a + costOfExpr bias b
  | .bitXorE a b        => bias.xorCost + costOfExpr bias a + costOfExpr bias b
  | .bitOrE a b         => bias.orCost + costOfExpr bias a + costOfExpr bias b
  | .constMaskE _       => bias.constCost
  | .subE a b           => bias.subCost + costOfExpr bias a + costOfExpr bias b
  | .reduceE a _        => bias.reduceCost + costOfExpr bias a
  | .kronPackE a b _    => bias.mulCost + costOfExpr bias a + costOfExpr bias b
  | .kronUnpackLoE a _  => bias.shiftCost + costOfExpr bias a
  | .kronUnpackHiE a _  => bias.shiftCost + costOfExpr bias a
  | .montyReduceE a _ _ => bias.reduceCost + costOfExpr bias a
  | .barrettReduceE a _ _ => bias.reduceCost + costOfExpr bias a
  | .harveyReduceE a _  => bias.reduceCost + costOfExpr bias a

/-! ## Section 3: ExtractionResult structure -/

/-- Result of cost-biased extraction: the extracted expression, its cost,
    and the class it was extracted from. -/
structure ExtractionResult where
  expr    : MixedExpr
  cost    : Nat
  classId : CId

instance : BEq ExtractionResult where
  beq a b := a.cost == b.cost && a.classId == b.classId

/-! ## Section 4: extractWithCostBias -/

/-- Extract an expression from a class and evaluate its cost under a bias.
    Uses greedy extraction from VerifiedExtraction.Greedy. -/
def extractWithCostBias (bias : CostBias) (g : MGraph) (classId : CId)
    (fuel : Nat := 100) : Option ExtractionResult :=
  match extractF (Op := MixedNodeOp) (Expr := MixedExpr) g classId fuel with
  | some expr => some { expr, cost := costOfExpr bias expr, classId }
  | none => none

/-! ## Section 5: Semantic correctness of extraction -/

/-- If we extract from a class in a graph with ConsistentValuation (CV),
    well-formed union-find, and BestNodeInv, the extracted expression
    evaluates to the class's valuation value (modulo root canonicalization).

    This is a direct consequence of `extractF_correct` from
    VerifiedExtraction.Greedy plus `mixed_extractable_sound`. -/
theorem extraction_preserves_semantics (g : MGraph) (env : MixedEnv)
    (v : CId → Nat) (classId : CId) (expr : MixedExpr) (fuel : Nat)
    (hcv : CV g env v)
    (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (h_ext : extractF g classId fuel = some expr) :
    EvalExpr.evalExpr expr env =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) :=
  extractF_correct g env v hcv hwf hbni
    AmoLean.EGraph.Verified.Bitwise.MixedExtract.mixed_extractable_sound
    fuel classId expr h_ext

/-- Cost-biased extraction preserves semantics: the expr field of the
    ExtractionResult evaluates correctly. -/
theorem costBiased_preserves_semantics (bias : CostBias)
    (g : MGraph) (env : MixedEnv) (v : CId → Nat)
    (classId : CId) (result : ExtractionResult) (fuel : Nat)
    (hcv : CV g env v)
    (hwf : AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (h_ext : extractWithCostBias bias g classId fuel = some result) :
    EvalExpr.evalExpr result.expr env =
      v (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId) := by
  unfold extractWithCostBias at h_ext
  split at h_ext
  · rename_i e he
    have heq : result = { expr := e, cost := costOfExpr bias e, classId := classId } := by
      simpa using h_ext.symm
    rw [heq]
    exact extraction_preserves_semantics g env v classId e fuel hcv hwf hbni he
  · exact absurd h_ext (by simp)

/-! ## Section 6: selectCheapest helper -/

/-- Select the cheapest result from a list of extraction results. -/
def selectCheapest : List ExtractionResult → Option ExtractionResult
  | []      => none
  | [r]     => some r
  | r :: rs =>
    match selectCheapest rs with
    | none      => some r
    | some best => if r.cost ≤ best.cost then some r else some best

/-- selectCheapest returns none iff the input list is empty. -/
theorem selectCheapest_none_iff (rs : List ExtractionResult) :
    selectCheapest rs = none ↔ rs = [] := by
  constructor
  · intro h
    match rs with
    | []      => rfl
    | [_]     => simp [selectCheapest] at h
    | r :: r2 :: rest =>
      simp [selectCheapest] at h
      split at h
      · simp at h
      · split at h <;> simp at h
  · intro h; subst h; rfl

/-! ## Section 7: Smoke tests -/

-- Shift is cheaper than multiply with default bias
#eval costOfExpr CostBias.default (.shiftLeftE (.witnessE 0) 3)    -- 1
#eval costOfExpr CostBias.default (.mulE (.witnessE 0) (.constE 8)) -- 5

example : costOfExpr CostBias.default (.shiftLeftE (.witnessE 0) 3) <
          costOfExpr CostBias.default (.mulE (.witnessE 0) (.constE 8)) := by native_decide

-- Shift-preferring bias makes shifts even cheaper
example : costOfExpr CostBias.shiftPreferring (.shiftLeftE (.witnessE 0) 3) <
          costOfExpr CostBias.shiftPreferring (.mulE (.witnessE 0) (.constE 8)) := by native_decide

-- selectCheapest picks the minimum cost entry
example : (selectCheapest [
    { expr := .mulE (.witnessE 0) (.constE 8), cost := 10, classId := 0 },
    { expr := .shiftLeftE (.witnessE 0) 3, cost := 1, classId := 0 }
  ]).map (·.cost) = some 1 := by native_decide

-- selectCheapest on empty list is none
example : selectCheapest ([] : List ExtractionResult) = none := rfl

-- costOfExpr is zero for constants with default bias
example : costOfExpr CostBias.default (.constE 42) = 0 := rfl

-- Nested expressions accumulate cost correctly
example : costOfExpr CostBias.default (.addE (.shiftLeftE (.witnessE 0) 3) (.constE 1)) = 2 := by
  native_decide

end AmoLean.EGraph.Verified.Bitwise.Discovery
