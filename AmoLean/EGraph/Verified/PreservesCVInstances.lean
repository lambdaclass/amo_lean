/-
  AMO-Lean — PreservesCV Instances (B88)
  Proves that step functions built from sound rewrite rules satisfy PreservesCV.

  Key components:
  - `applyMerges`: spec-level merge application (foldl over EGraph.merge)
  - `mergeAll_preserves_triple`: joint preservation of (CV, PMI, SHI) through mergeAll
  - `SoundMergeStep`: spec-level predicate for step functions that apply sound merges
  - `soundMergeStep_preserves_cv`: SoundMergeStep implies PreservesCV
  - `SoundRuleMatch`: witness that a merge pair came from a sound rewrite rule
  - `soundRuleMatchMerges_preserves_cv`: merging e-class pairs from sound rule matches
    preserves CV — the direct bridge from BridgeCorrectness to PipelineSoundness
  - `id_preserves_cv`, `comp_preserves_cv`: structural combinators for PreservesCV

  This is the critical link: BridgeCorrectness provides 10 SoundRewriteRule instances,
  and PipelineSoundness requires PreservesCV. This module bridges the gap.

  Axiom census: 0 custom axioms. All proofs compose existing theorems from
  SemanticSpec (mergeAll_consistent, mergeAll_preserves_pmi, mergeAll_preserves_shi)
  and SoundRewriteRule (rule.soundness).
-/
import AmoLean.EGraph.Verified.SaturationSpec
import AmoLean.EGraph.Verified.BridgeCorrectness

namespace AmoLean.EGraph.Verified

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Spec-level merge application
-- ══════════════════════════════════════════════════════════════════

/-- Apply a list of merges to an e-graph. Specification-level: merges are
    given as (lhsId, rhsId) pairs, and we fold `EGraph.merge` over them. -/
def applyMerges (pairs : List (EClassId × EClassId)) (g : EGraph) : EGraph :=
  pairs.foldl (fun acc (id1, id2) => acc.merge id1 id2) g

/-- applyMerges with nil is identity. -/
@[simp] theorem applyMerges_nil (g : EGraph) : applyMerges [] g = g := rfl

/-- applyMerges with cons unfolds to merge then recurse. -/
theorem applyMerges_cons (p : EClassId × EClassId)
    (rest : List (EClassId × EClassId)) (g : EGraph) :
    applyMerges (p :: rest) g = applyMerges rest (g.merge p.1 p.2) := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: mergeAll preserves the triple (CV, PMI, SHI)
-- ══════════════════════════════════════════════════════════════════

/-- Joint preservation: mergeAll preserves the full triple (CV, PMI, SHI)
    when all merge pairs have v-equal values and are in-bounds.

    This composes `mergeAll_consistent`, `mergeAll_preserves_pmi`, and
    `mergeAll_preserves_shi` into a single result. -/
theorem mergeAll_preserves_triple {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (merges : List (EClassId × EClassId))
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (hval : ∀ p ∈ merges, v p.1 = v p.2)
    (hbnd : ∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧
                           p.2 < g.unionFind.parent.size) :
    ConsistentValuation (applyMerges merges g) env v ∧
    PostMergeInvariant (applyMerges merges g) ∧
    SemanticHashconsInv (applyMerges merges g) env v :=
  ⟨mergeAll_consistent merges g env v hcv hpmi.uf_wf hval hbnd,
   mergeAll_preserves_pmi merges g hpmi hbnd,
   mergeAll_preserves_shi merges g env v hcv hpmi.uf_wf hshi hval hbnd⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 3: SoundMergeStep — spec-level characterization
-- ══════════════════════════════════════════════════════════════════

/-- A step function is a "sound merge step" if, for every graph/valuation
    satisfying the triple, the step can be decomposed as applying a list
    of merges where:
    (1) each pair has v-equal values (semantic soundness), and
    (2) each pair is in-bounds (structural well-formedness).

    This captures any step built from sound rewrite rules without
    specifying the e-matching algorithm. -/
def SoundMergeStep {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (env : CircuitEnv Val) (step : EGraph → EGraph) : Prop :=
  ∀ (g : EGraph) (v : EClassId → Val),
    ConsistentValuation g env v →
    PostMergeInvariant g →
    SemanticHashconsInv g env v →
    ∃ (merges : List (EClassId × EClassId)),
      step g = applyMerges merges g ∧
      (∀ p ∈ merges, v p.1 = v p.2) ∧
      (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧
                      p.2 < g.unionFind.parent.size)

/-- **Core theorem**: Any SoundMergeStep satisfies PreservesCV.

    Proof: decompose the step into applyMerges, then apply the three
    mergeAll preservation theorems. The existential witness v' is the
    original v (mergeAll preserves it). -/
theorem soundMergeStep_preserves_cv {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (env : CircuitEnv Val) (step : EGraph → EGraph)
    (h : SoundMergeStep env step) :
    PreservesCV env step := by
  intro g v hcv hpmi hshi
  obtain ⟨merges, heq, hval, hbnd⟩ := h g v hcv hpmi hshi
  rw [heq]
  have hcv' := mergeAll_consistent merges g env v hcv hpmi.uf_wf hval hbnd
  have hpmi' := mergeAll_preserves_pmi merges g hpmi hbnd
  have hshi' := mergeAll_preserves_shi merges g env v hcv hpmi.uf_wf hshi hval hbnd
  exact ⟨v, hcv', hpmi', hshi'⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: SoundRuleMatch — witness from BridgeCorrectness
-- ══════════════════════════════════════════════════════════════════

/-- A single match from a sound rule: identifies an e-class pair (lhsId, rhsId)
    such that the rule's LHS evaluates to v(root lhsId) and RHS to v(root rhsId),
    guaranteeing semantic equality of the pair.

    Concrete for `(Expr Int, Int)` since `allSoundRules` is
    `List (SoundRewriteRule (Expr Int) Int)`. -/
structure SoundRuleMatch (g : EGraph) (env : CircuitEnv Int) (v : EClassId → Int) where
  /-- E-class where the LHS pattern matched -/
  lhsId : EClassId
  /-- E-class where the RHS should be merged into -/
  rhsId : EClassId
  /-- The sound rule that produced this match -/
  rule : SoundRewriteRule (Expr Int) Int
  /-- Variable assignment used for the match -/
  vars : Nat → Expr Int
  /-- The rule is in the verified collection -/
  rule_mem : rule ∈ (allSoundRules : List (SoundRewriteRule (Expr Int) Int))
  /-- LHS e-class evaluates to the rule's LHS expression -/
  lhs_eval : v (root g.unionFind lhsId) = rule.eval (rule.lhsExpr vars) env
  /-- RHS e-class evaluates to the rule's RHS expression -/
  rhs_eval : v (root g.unionFind rhsId) = rule.eval (rule.rhsExpr vars) env
  /-- LHS e-class is in bounds -/
  lhs_bound : lhsId < g.unionFind.parent.size
  /-- RHS e-class is in bounds -/
  rhs_bound : rhsId < g.unionFind.parent.size

/-- A match from a sound rule produces a merge pair with v-equal values.
    Uses `consistent_root_eq'` to convert between root-form and direct equality,
    then the rule's soundness to equate the two expressions.

    Chain: `v lhsId = v(root lhsId) = eval(lhs) = eval(rhs) = v(root rhsId) = v rhsId` -/
theorem soundRuleMatch_veq (g : EGraph) (env : CircuitEnv Int)
    (v : EClassId → Int) (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (m : SoundRuleMatch g env v) :
    v m.lhsId = v m.rhsId :=
  calc v m.lhsId
      = v (root g.unionFind m.lhsId) :=
        (consistent_root_eq' g env v hcv hwf m.lhsId).symm
    _ = m.rule.eval (m.rule.lhsExpr m.vars) env := m.lhs_eval
    _ = m.rule.eval (m.rule.rhsExpr m.vars) env := m.rule.soundness env m.vars
    _ = v (root g.unionFind m.rhsId) := m.rhs_eval.symm
    _ = v m.rhsId := consistent_root_eq' g env v hcv hwf m.rhsId

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Lifting SoundRuleMatch to lists
-- ══════════════════════════════════════════════════════════════════

/-- A list of sound rule matches all have v-equal pairs.
    Converts from root-based equality (from rule soundness)
    to the direct v-equality needed by mergeAll. -/
theorem soundRuleMatches_veq (g : EGraph) (env : CircuitEnv Int)
    (v : EClassId → Int) (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (ms : List (SoundRuleMatch g env v)) :
    ∀ p ∈ ms.map (fun m => (m.lhsId, m.rhsId)),
      v p.1 = v p.2 := by
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨m, _, rfl⟩ := hp
  exact soundRuleMatch_veq g env v hcv hwf m

/-- A list of sound rule matches all have in-bounds pairs. -/
theorem soundRuleMatches_bounded (g : EGraph) (env : CircuitEnv Int)
    (v : EClassId → Int)
    (ms : List (SoundRuleMatch g env v)) :
    ∀ p ∈ ms.map (fun m => (m.lhsId, m.rhsId)),
      p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size := by
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨m, _, rfl⟩ := hp
  exact ⟨m.lhs_bound, m.rhs_bound⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Concrete PreservesCV from allSoundRules
-- ══════════════════════════════════════════════════════════════════

/-- **PreservesCV for sound-rule-based steps**: any step that can be
    decomposed into merges arising from matches of `allSoundRules`
    satisfies PreservesCV.

    This is the theorem that connects BridgeCorrectness.allSoundRules
    to PipelineSoundness.full_pipeline_soundness. The hypothesis asks
    the caller to provide, for each (g, v) triple, a list of
    SoundRuleMatch witnesses showing that the step's merges come from
    verified rules. -/
theorem soundRuleMatchMerges_preserves_cv (env : CircuitEnv Int)
    (step : EGraph → EGraph)
    (h_decomp : ∀ (g : EGraph) (v : EClassId → Int),
      ConsistentValuation g env v →
      PostMergeInvariant g →
      SemanticHashconsInv g env v →
      ∃ (ms : List (SoundRuleMatch g env v)),
        step g = applyMerges (ms.map (fun m => (m.lhsId, m.rhsId))) g) :
    PreservesCV env step := by
  intro g v hcv hpmi hshi
  obtain ⟨ms, heq⟩ := h_decomp g v hcv hpmi hshi
  rw [heq]
  have hval := soundRuleMatches_veq g env v hcv hpmi.uf_wf ms
  have hbnd := soundRuleMatches_bounded g env v ms
  have hcv' := mergeAll_consistent _ g env v hcv hpmi.uf_wf hval hbnd
  have hpmi' := mergeAll_preserves_pmi _ g hpmi hbnd
  have hshi' := mergeAll_preserves_shi _ g env v hcv hpmi.uf_wf hshi hval hbnd
  exact ⟨v, hcv', hpmi', hshi'⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Generic PreservesCV construction (convenience alias)
-- ══════════════════════════════════════════════════════════════════

/-- **Main PreservesCV instance**: any step function that decomposes into
    a list of merges where each pair's v-values are equal satisfies
    PreservesCV. This is the most general form — it does not reference
    SoundRewriteRule or e-matching directly. -/
theorem mergeStep_preserves_cv {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (env : CircuitEnv Val) (step : EGraph → EGraph)
    (h_decomp : ∀ (g : EGraph) (v : EClassId → Val),
      ConsistentValuation g env v →
      PostMergeInvariant g →
      SemanticHashconsInv g env v →
      ∃ (merges : List (EClassId × EClassId)),
        step g = applyMerges merges g ∧
        (∀ p ∈ merges, v p.1 = v p.2) ∧
        (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧
                        p.2 < g.unionFind.parent.size)) :
    PreservesCV env step :=
  soundMergeStep_preserves_cv env step h_decomp

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Structural combinators
-- ══════════════════════════════════════════════════════════════════

/-- The identity step trivially preserves CV. -/
theorem id_preserves_cv {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (env : CircuitEnv Val) :
    PreservesCV env id := by
  intro g v hcv hpmi hshi
  exact ⟨v, hcv, hpmi, hshi⟩

/-- Composition of two PreservesCV steps preserves CV.
    This allows building multi-round saturation from single-round steps. -/
theorem comp_preserves_cv {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (env : CircuitEnv Val) (step1 step2 : EGraph → EGraph)
    (h1 : PreservesCV env step1) (h2 : PreservesCV env step2) :
    PreservesCV env (step2 ∘ step1) := by
  intro g v hcv hpmi hshi
  obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h1 g v hcv hpmi hshi
  obtain ⟨v2, hcv2, hpmi2, hshi2⟩ := h2 (step1 g) v1 hcv1 hpmi1 hshi1
  exact ⟨v2, hcv2, hpmi2, hshi2⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Non-vacuity examples
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: SoundMergeStep is satisfiable (identity step). -/
example (env : CircuitEnv Int) : SoundMergeStep env (id : EGraph → EGraph) := by
  intro g v _ _ _
  exact ⟨[], rfl, fun _ h => absurd h (List.not_mem_nil),
         fun _ h => absurd h (List.not_mem_nil)⟩

/-- Non-vacuity: PreservesCV is satisfiable via id_preserves_cv. -/
example (env : CircuitEnv Int) : PreservesCV env (id : EGraph → EGraph) :=
  id_preserves_cv env

/-- Non-vacuity: mergeAll_preserves_triple with empty merges. -/
example (g : EGraph) (env : CircuitEnv Int) (v : EClassId → Int)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) :
    ConsistentValuation (applyMerges [] g) env v ∧
    PostMergeInvariant (applyMerges [] g) ∧
    SemanticHashconsInv (applyMerges [] g) env v :=
  ⟨hcv, hpmi, hshi⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 10: Pipeline integration helpers
-- ══════════════════════════════════════════════════════════════════

/-- Convenience: given a step that is a SoundMergeStep, the full pipeline
    (saturateF) preserves ConsistentValuation.
    Direct corollary of `saturateF_preserves_consistent`. -/
theorem soundMergeStep_pipeline_cv {Val : Type} [Add Val] [Mul Val] [Neg Val]
    (env : CircuitEnv Val) (step : EGraph → EGraph)
    (h : SoundMergeStep env step)
    (maxIter rebuildFuel : Nat)
    (g : EGraph) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) :
    ∃ v', ConsistentValuation (saturateF step maxIter rebuildFuel g) env v' :=
  saturateF_preserves_consistent step maxIter rebuildFuel g env v
    hcv hpmi hshi (soundMergeStep_preserves_cv env step h)

-- ══════════════════════════════════════════════════════════════════
-- Axiom census: this module introduces 0 custom axioms.
-- All proofs compose existing theorems from SemanticSpec.lean,
-- SaturationSpec.lean, CoreSpec.lean, and BridgeCorrectness.lean.
-- ══════════════════════════════════════════════════════════════════

end AmoLean.EGraph.Verified
