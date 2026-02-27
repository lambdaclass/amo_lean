/-
  AMO-Lean — Pipeline Soundness
  Fase 11 N11.5: End-to-end pipeline soundness via composition.

  Composes:
  - `saturateF_preserves_consistent` (N11.3, SaturationSpec)
  - `extractF_correct` + `extractILP_correct` (N11.4, ExtractSpec)

  Key theorems:
  - `congruence_merge`: merging equivalent classes preserves valuation
  - `congruence_extract`: extraction from equivalent classes yields equal values
  - `optimization_soundness_greedy`: saturate → greedy extract is sound
  - `optimization_soundness_ilp`: saturate → ILP extract is sound
  - `greedy_ilp_equivalent`: greedy and ILP extractions agree semantically
  - `full_pipeline_soundness`: main theorem (Level 1 soundness)
  - `full_pipeline_contract`: three-part contract (L-311)

  Adapted from OptiSat/TranslationValidation + SuperTensor/PipelineSoundness.
-/
import AmoLean.EGraph.Verified.ExtractSpec

namespace AmoLean.EGraph.Verified

open UnionFind ILP

set_option linter.unusedSectionVars false

variable {Val : Type} [Add Val] [Mul Val] [Neg Val]
variable {Expr : Type} [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Proof Witness
-- ══════════════════════════════════════════════════════════════════

/-- A proof witness captures the state needed to validate an optimization.
    Records the e-graph state, extraction result, and root class. -/
structure ProofWitness (Expr : Type) where
  /-- The e-graph after saturation -/
  graph : EGraph
  /-- Root class ID for extraction -/
  rootId : EClassId
  /-- The extracted expression -/
  extracted : Expr
  /-- Extraction fuel used -/
  fuel : Nat

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Congruence Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Merging equivalent classes preserves ConsistentValuation.
    Direct re-export of merge_consistent from SemanticSpec. -/
theorem congruence_merge (g : EGraph) (id1 id2 : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (h1 : id1 < g.unionFind.parent.size) (h2 : id2 < g.unionFind.parent.size)
    (heq : v (root g.unionFind id1) = v (root g.unionFind id2)) :
    ConsistentValuation (g.merge id1 id2) env v :=
  merge_consistent g id1 id2 env v hcv hwf h1 h2 heq

/-- Extraction from UF-equivalent classes yields expressions with the same
    value. If two class IDs share the same root, their extracted expressions
    evaluate identically. -/
theorem congruence_extract (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : CircuitExtractableSound Expr Val)
    (id1 id2 : EClassId) (expr1 expr2 : Expr) (fuel : Nat)
    (hroot : root g.unionFind id1 = root g.unionFind id2)
    (hext1 : extractF g id1 fuel = some expr1)
    (hext2 : extractF g id2 fuel = some expr2) :
    CircuitEvalExpr.evalExpr expr1 env = CircuitEvalExpr.evalExpr expr2 env := by
  have h1 := extractF_correct g env v hcv hwf hbni hsound fuel id1 expr1 hext1
  have h2 := extractF_correct g env v hcv hwf hbni hsound fuel id2 expr2 hext2
  rw [h1, h2, hroot]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Optimization Soundness (greedy)
-- ══════════════════════════════════════════════════════════════════

/-- Optimization soundness (greedy extraction):
    Saturate → extract produces a semantically correct expression.

    Given initial invariants (CV, PMI, SHI) and a step function that
    preserves them, the extracted expression evaluates to the correct
    value at the root class. -/
theorem optimization_soundness_greedy
    (step : EGraph → EGraph) (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step)
    (hwf_sat : WellFormed (saturateF step maxIter rebuildFuel g).unionFind)
    (hbni_sat : BestNodeInv (saturateF step maxIter rebuildFuel g).classes)
    (hsound : CircuitExtractableSound Expr Val)
    (rootId : EClassId) (extractFuel : Nat) (expr : Expr)
    (hext : extractF (saturateF step maxIter rebuildFuel g)
              rootId extractFuel = some expr) :
    ∃ v_sat : EClassId → Val,
      CircuitEvalExpr.evalExpr expr env =
        v_sat (root (saturateF step maxIter rebuildFuel g).unionFind rootId) := by
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent step maxIter rebuildFuel
    g env v hcv hpmi hshi h_step
  exact ⟨v_sat, extractF_correct _ env v_sat hcv_sat hwf_sat hbni_sat hsound
    extractFuel rootId expr hext⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Optimization Soundness (ILP)
-- ══════════════════════════════════════════════════════════════════

/-- Optimization soundness (ILP extraction):
    Saturate → ILP-guided extract produces a semantically correct expression. -/
theorem optimization_soundness_ilp
    (step : EGraph → EGraph) (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step)
    (hwf_sat : WellFormed (saturateF step maxIter rebuildFuel g).unionFind)
    (hsound : CircuitExtractableSound Expr Val)
    (rootId : EClassId) (sol : ILPSolution)
    (hvalid : ValidSolution (saturateF step maxIter rebuildFuel g) rootId sol)
    (extractFuel : Nat) (expr : Expr)
    (hext : extractILP (saturateF step maxIter rebuildFuel g) sol
              rootId extractFuel = some expr) :
    ∃ v_sat : EClassId → Val,
      CircuitEvalExpr.evalExpr expr env =
        v_sat (root (saturateF step maxIter rebuildFuel g).unionFind rootId) := by
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent step maxIter rebuildFuel
    g env v hcv hpmi hshi h_step
  exact ⟨v_sat, ilp_extraction_soundness _ rootId sol env v_sat hcv_sat hwf_sat hvalid
    hsound extractFuel expr hext⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Greedy–ILP Semantic Equivalence
-- ══════════════════════════════════════════════════════════════════

/-- Greedy and ILP extractions from the same root class yield semantically
    equivalent expressions. -/
theorem greedy_ilp_equivalent
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : CircuitExtractableSound Expr Val)
    (rootId : EClassId) (sol : ILPSolution)
    (hvalid : ValidSolution g rootId sol)
    (fuelG fuelI : Nat) (exprG exprI : Expr)
    (hextG : extractF g rootId fuelG = some exprG)
    (hextI : extractILP g sol rootId fuelI = some exprI) :
    CircuitEvalExpr.evalExpr exprG env =
      CircuitEvalExpr.evalExpr exprI env := by
  have hG := extractF_correct g env v hcv hwf hbni hsound fuelG rootId exprG hextG
  have hI := ilp_extraction_soundness g rootId sol env v hcv hwf hvalid hsound
    fuelI exprI hextI
  rw [hG, hI]

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Full Pipeline Soundness
-- ══════════════════════════════════════════════════════════════════

/-- **Full pipeline soundness** (main theorem, Level 1):
    Saturate → extract is semantically correct.

    Given:
    - An initial e-graph with the invariant triple (CV, PMI, SHI)
    - A step function that preserves the triple (via PreservesCV)
    - Post-saturation structural assumptions (UF well-formed, BestNodeInv)
    - Extraction succeeds

    Then the extracted expression evaluates to the correct value at the root,
    AND the saturated graph admits a ConsistentValuation.

    This is the Level 1 soundness theorem: internal e-graph consistency
    is preserved through the entire pipeline. Combined with Level 2
    (TranslationValidation, N11.11) to yield verified_optimization_pipeline. -/
theorem full_pipeline_soundness
    (step : EGraph → EGraph) (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step)
    (hwf_sat : WellFormed (saturateF step maxIter rebuildFuel g).unionFind)
    (hbni_sat : BestNodeInv (saturateF step maxIter rebuildFuel g).classes)
    (hsound : CircuitExtractableSound Expr Val)
    (rootId : EClassId) (extractFuel : Nat) (expr : Expr)
    (hext : extractF (saturateF step maxIter rebuildFuel g)
              rootId extractFuel = some expr) :
    ∃ v_sat : EClassId → Val,
      ConsistentValuation (saturateF step maxIter rebuildFuel g) env v_sat ∧
      CircuitEvalExpr.evalExpr expr env =
        v_sat (root (saturateF step maxIter rebuildFuel g).unionFind rootId) := by
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent step maxIter rebuildFuel
    g env v hcv hpmi hshi h_step
  exact ⟨v_sat, hcv_sat, extractF_correct _ env v_sat hcv_sat hwf_sat hbni_sat hsound
    extractFuel rootId expr hext⟩

/-- **Full pipeline soundness (ILP variant)**.
    Same as `full_pipeline_soundness` but uses ILP-guided extraction. -/
theorem full_pipeline_soundness_ilp
    (step : EGraph → EGraph) (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step)
    (hwf_sat : WellFormed (saturateF step maxIter rebuildFuel g).unionFind)
    (hsound : CircuitExtractableSound Expr Val)
    (rootId : EClassId) (sol : ILPSolution)
    (hvalid : ValidSolution (saturateF step maxIter rebuildFuel g) rootId sol)
    (extractFuel : Nat) (expr : Expr)
    (hext : extractILP (saturateF step maxIter rebuildFuel g) sol
              rootId extractFuel = some expr) :
    ∃ v_sat : EClassId → Val,
      ConsistentValuation (saturateF step maxIter rebuildFuel g) env v_sat ∧
      CircuitEvalExpr.evalExpr expr env =
        v_sat (root (saturateF step maxIter rebuildFuel g).unionFind rootId) := by
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent step maxIter rebuildFuel
    g env v hcv hpmi hshi h_step
  exact ⟨v_sat, hcv_sat, ilp_extraction_soundness _ rootId sol env v_sat hcv_sat hwf_sat
    hvalid hsound extractFuel expr hext⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Three-Part Contract (L-311)
-- ══════════════════════════════════════════════════════════════════

/-- **Three-part contract** (L-311): full pipeline delivers:
    1. A witness valuation `v_sat` with ConsistentValuation (frame preservation)
    2. Greedy extraction is sound (result semantics)
    3. ILP extraction is sound (result semantics)
    4. Greedy and ILP extractions agree at the same root (extraction agreement)

    This is the definitive Level 1 soundness statement. -/
theorem full_pipeline_contract
    (step : EGraph → EGraph) (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step)
    (hwf_sat : WellFormed (saturateF step maxIter rebuildFuel g).unionFind)
    (hbni_sat : BestNodeInv (saturateF step maxIter rebuildFuel g).classes)
    (hsound : CircuitExtractableSound Expr Val) :
    ∃ v_sat : EClassId → Val,
      -- Part 1: Frame — ConsistentValuation preserved
      ConsistentValuation (saturateF step maxIter rebuildFuel g) env v_sat ∧
      -- Part 2: Greedy extraction is sound
      (∀ (rootId : EClassId) (extractFuel : Nat) (expr : Expr),
        extractF (saturateF step maxIter rebuildFuel g)
          rootId extractFuel = some expr →
        CircuitEvalExpr.evalExpr expr env =
          v_sat (root (saturateF step maxIter rebuildFuel g).unionFind rootId)) ∧
      -- Part 3: ILP extraction is sound (when valid)
      (∀ (rootId : EClassId) (sol : ILPSolution) (extractFuel : Nat) (expr : Expr),
        ValidSolution (saturateF step maxIter rebuildFuel g) rootId sol →
        extractILP (saturateF step maxIter rebuildFuel g) sol
          rootId extractFuel = some expr →
        CircuitEvalExpr.evalExpr expr env =
          v_sat (root (saturateF step maxIter rebuildFuel g).unionFind rootId)) ∧
      -- Part 4: Greedy–ILP equivalence
      (∀ (rootId : EClassId) (sol : ILPSolution)
          (fuelG fuelI : Nat) (exprG exprI : Expr),
        ValidSolution (saturateF step maxIter rebuildFuel g) rootId sol →
        extractF (saturateF step maxIter rebuildFuel g)
          rootId fuelG = some exprG →
        extractILP (saturateF step maxIter rebuildFuel g) sol
          rootId fuelI = some exprI →
        CircuitEvalExpr.evalExpr exprG env =
          CircuitEvalExpr.evalExpr exprI env) := by
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent step maxIter rebuildFuel
    g env v hcv hpmi hshi h_step
  refine ⟨v_sat, hcv_sat, ?_, ?_, ?_⟩
  · -- Greedy soundness
    intro rootId extractFuel expr hext
    exact extractF_correct _ env v_sat hcv_sat hwf_sat hbni_sat hsound
      extractFuel rootId expr hext
  · -- ILP soundness
    intro rootId sol extractFuel expr hvalid hext
    exact ilp_extraction_soundness _ rootId sol env v_sat hcv_sat hwf_sat hvalid
      hsound extractFuel expr hext
  · -- Greedy-ILP equivalence
    intro rootId sol fuelG fuelI exprG exprI hvalid hextG hextI
    exact greedy_ilp_equivalent _ env v_sat hcv_sat hwf_sat hbni_sat hsound
      rootId sol hvalid fuelG fuelI exprG exprI hextG hextI

end AmoLean.EGraph.Verified
