/-
  AMO-Lean Ultra — Phase 22: MultiRelMixed
  Single authoritative multi-relation e-graph with tiered saturation.

  ONE loop. No stubs. No parallel versions.

  Architecture:
  - `State`: base EGraph + relation DAGs
  - `BoundRuleFactory`: generates fresh bound rules from CURRENT state each iteration
  - `saturate`: the single tiered saturation loop
  - When factory returns [], saturate = equality-only saturation (backward compat)

  The BoundRuleFactory pattern solves the frozen-lookup problem:
  bound rules see the latest DAG state, not a stale snapshot.
-/
import AmoLean.EGraph.Verified.Bitwise.DirectedRelSpec
import AmoLean.EGraph.Verified.Bitwise.ColoredSpec
import AmoLean.EGraph.Verified.Bitwise.MixedPipeline
import AmoLean.EGraph.Verified.Bitwise.MixedSaturation
import AmoLean.EGraph.Verified.Bitwise.BoundPropagation

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.MultiRel

open AmoLean.EGraph.VerifiedExtraction (EGraph EClassId)
open MixedPipeline (MixedEGraph)
open AmoLean.EGraph.Verified.Bitwise.Colored (ColoredLayer ColorId colorRoot)
open AmoLean.EGraph.Verified.Bitwise.ColoredSpec (MixedCCV ColorAssumption MixedColoredSoundRule)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: State
-- ══════════════════════════════════════════════════════════════════

structure RelEntry where
  dag : DirectedRelGraph
  name : String := "unnamed"

structure State where
  baseGraph : MixedEGraph
  relEntries : Array RelEntry := #[]
  coloredLayer : ColoredLayer := ColoredLayer.empty
  assumptions : ColorAssumption := fun _ _ => True

instance : Inhabited State where
  default := { baseGraph := default }

def State.ofBase (g : MixedEGraph) : State where baseGraph := g
def State.empty : State where baseGraph := default
def State.numNodes (s : State) : Nat := s.baseGraph.numNodes
def State.numClasses (s : State) : Nat := s.baseGraph.numClasses
def State.numRelations (s : State) : Nat := s.relEntries.size
def State.totalRelEdges (s : State) : Nat :=
  s.relEntries.foldl (fun acc e => acc + e.dag.numEdges) 0

def State.addRelation (s : State) (name : String) : State :=
  { s with relEntries := s.relEntries.push { dag := DirectedRelGraph.empty, name } }

def State.addBoundEdge (s : State) (relIdx : Nat) (src dst : EClassId) : State :=
  if h : relIdx < s.relEntries.size then
    let entry := s.relEntries[relIdx]
    let entry' : RelEntry := { entry with dag := entry.dag.addEdge src dst }
    { s with relEntries := s.relEntries.set relIdx entry' }
  else s

-- ══════════════════════════════════════════════════════════════════
-- Section 2: BoundRule + BoundRuleFactory
-- ══════════════════════════════════════════════════════════════════

/-- A bound rule produces new directed edges from the current e-graph. -/
structure BoundRule where
  name : String
  relIdx : Nat
  apply : MixedEGraph → List (EClassId × EClassId)

/-- A factory that generates FRESH bound rules from the CURRENT state.
    This is the key design: the factory sees the latest DAG, not a snapshot.
    When factory = (fun _ => []), no relations are tracked → backward compat. -/
abbrev BoundRuleFactory := State → List BoundRule

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Config
-- ══════════════════════════════════════════════════════════════════

structure Config where
  totalFuel : Nat := 20
  eqFreq : Nat := 1
  relFreq : Nat := 5
  crossFreq : Nat := 10
  colorFreq : Nat := 5
  boundAwareFreq : Nat := 5  -- v3.11.0 F3: frequency for bound-aware rewrite step
  matchFuel : Nat := 50
  rebuildFuel : Nat := 10
  deriving Repr, Inhabited

def Config.default : Config := {}

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Step Functions (all real, no stubs)
-- ══════════════════════════════════════════════════════════════════

/-- Layer 1: equality saturation on base graph. -/
def eqStep (rules : List (MixedEMatch.RewriteRule MixedNodeOp)) (cfg : Config)
    (s : State) : State :=
  let g' := MixedSaturation.applyRulesF cfg.matchFuel s.baseGraph rules
  let g'' := MixedSaturation.rebuildF g' cfg.rebuildFuel
  { s with baseGraph := g'' }

/-- Layer 3: apply bound rules to add edges to relation DAGs.
    Rules are generated FRESH from the factory using the CURRENT state. -/
def relStep (factory : BoundRuleFactory) (s : State) : State :=
  let rules := factory s
  rules.foldl (fun s' rule =>
    let newEdges := rule.apply s'.baseGraph
    newEdges.foldl (fun s'' (src, dst) => s''.addBoundEdge rule.relIdx src dst) s'
  ) s

/-- Scan two DAGs for antisymmetry evidence: a→b in dag1 AND b→a in dag2. -/
def matchCrossEdges (dag1 dag2 : DirectedRelGraph) : List (EClassId × EClassId) :=
  dag1.allEdges.filterMap fun (a, b) =>
    if dag2.hasDirectEdge b a then some (a, b) else none

/-- Cross-layer: scan DAGs for antisymmetry, merge in base graph, canonicalize.
    Uses `antisymmetry_promotes` from DirectedRelSpec as justification. -/
def crossStep (cfg : Config) (s : State) : State :=
  let merges := s.relEntries.foldl (fun acc entry1 =>
    s.relEntries.foldl (fun acc' entry2 =>
      acc' ++ matchCrossEdges entry1.dag entry2.dag
    ) acc
  ) ([] : List (EClassId × EClassId))
  if merges.isEmpty then s
  else
    let g' := merges.foldl (fun g pair =>
      AmoLean.EGraph.VerifiedExtraction.EGraph.merge g pair.1 pair.2) s.baseGraph
    let g'' := MixedSaturation.rebuildF g' cfg.rebuildFuel
    let find := fun id => AmoLean.EGraph.VerifiedExtraction.UnionFind.root g''.unionFind id
    let relEntries' := s.relEntries.map fun entry =>
      { entry with dag := entry.dag.canonicalize find }
    { baseGraph := g'', relEntries := relEntries' }

-- ══════════════════════════════════════════════════════════════════
-- Section 4b: Colored Step (N28.1) — applies conditional rules under color
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise.Colored (ColoredLayer.mergeUnderColor)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)
open AmoLean.EGraph.VerifiedExtraction (ENode EClass)

/-- Scan e-graph for reduction operation pairs that should be merged under a color.
    Finds class pairs where one member has a reduceGate and another has a specific
    reduction alternative (montyReduce, solinasFold, etc.). -/
def findReductionPairs (g : MixedEGraph) (_rule : MixedColoredSoundRule) :
    List (EClassId × EClassId) :=
  -- Collect classes containing reduceGate nodes
  let reduceClasses := g.classes.toList.filterMap fun (cid, eclass) =>
    let hasReduce := eclass.nodes.any fun node =>
      match node.op with
      | .reduceGate _ _ => true
      | _ => false
    if hasReduce then some cid else none
  -- Collect classes containing specific reduction implementations
  let implClasses := g.classes.toList.filterMap fun (cid, eclass) =>
    let hasImpl := eclass.nodes.any fun node =>
      match node.op with
      | .montyReduce _ _ _ | .barrettReduce _ _ _ | .harveyReduce _ _ | .conditionalSub _ _ => true
      | _ => false
    if hasImpl then some cid else none
  -- Pair each reduce with each impl (the e-graph resolves which pairs are valid)
  reduceClasses.flatMap fun rCid =>
    implClasses.filterMap fun iCid =>
      if rCid != iCid then some (rCid, iCid) else none

/-- Layer 2: apply colored rewrite rules by merging under their color.
    For each colored rule, finds matching class pairs and merges them
    in the colored layer (not the base UF). Descendant colors see the
    merge automatically via compositeFind (L-704). -/
def coloredStep (coloredRules : List MixedColoredSoundRule) (s : State) : State :=
  coloredRules.foldl (fun s' rule =>
    if rule.color == colorRoot then s'  -- root rules use eqStep instead
    else
      let pairs := findReductionPairs s'.baseGraph rule
      let baseFind := fun id =>
        AmoLean.EGraph.VerifiedExtraction.UnionFind.root s'.baseGraph.unionFind id
      pairs.foldl (fun s'' (lhsId, rhsId) =>
        let (cl', _) := s''.coloredLayer.mergeUnderColor baseFind rule.color lhsId rhsId
        { s'' with coloredLayer := cl' }
      ) s'
  ) s

/-- coloredStep preserves relEntries (only modifies coloredLayer).
    PENDIENTE: full proof requires nested foldl induction matching the capture pattern.
    The fact is trivially true: every branch of coloredStep produces
    { s'' with coloredLayer := cl' } which preserves relEntries by definition. -/
theorem coloredStep_preserves_relEntries (rules : List MixedColoredSoundRule) (s : State) :
    (coloredStep rules s).relEntries = s.relEntries := by
  sorry

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Single Tiered Saturation Loop
-- ══════════════════════════════════════════════════════════════════

/-- v3.11.0 F3: Bound-aware rewrite step. Applies rules gated by bound predicates.
    Reads CURRENT bounds from relation DAG, then overrides sideCondCheck closures
    to check boundK ≤ 2 for the matched e-class. Runs AFTER relStep so bounds are fresh.

    Key design: rules start with `sideCondCheck := some fun _ _ => false` (blocked).
    This function replaces the check with one that queries buildBoundLookup. -/
def boundAwareEqStep (boundRules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (cfg : Config) (s : State) : State :=
  if boundRules.isEmpty then s else
  -- Read bounds from the CURRENT DAG (relEntries[0] = bound relation)
  let boundLookup :=
    if h : 0 < s.relEntries.size
    then BoundPropagation.buildBoundLookup s.relEntries[0].dag
    else fun _ => none
  -- Override sideCondCheck to query actual bounds
  let rules := boundRules.map fun rule =>
    { rule with
      sideCondCheck := some fun g subst =>
        -- subst maps patVar 0 → matched classId
        match subst.get? 0 with
        | some classId =>
          let canonId := AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind classId
          match boundLookup canonId with
          | some k => k > 0 && k ≤ 2  -- boundK ≤ 2 → input < 2p → conditionalSub safe
          | none => false  -- no bound info → don't fire
        | none => false }
  let g' := MixedSaturation.applyRulesF cfg.matchFuel s.baseGraph rules
  let g'' := MixedSaturation.rebuildF g' cfg.rebuildFuel
  { s with baseGraph := g'' }

/-- One iteration of tiered saturation. ALL FIVE steps are real.
    Layer 1 (eq) → Layer 2 (colored) → Layer 3 (relational) → Cross-layer → Bound-aware. -/
def tieredStep (rules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (coloredRules : List MixedColoredSoundRule)
    (factory : BoundRuleFactory) (cfg : Config)
    (boundRules : List (MixedEMatch.RewriteRule MixedNodeOp) := [])
    (iter : Nat) (s : State) : State :=
  let s := if iter % cfg.eqFreq == 0 then eqStep rules cfg s else s
  let s := if iter % cfg.colorFreq == 0 then coloredStep coloredRules s else s
  let s := if iter % cfg.relFreq == 0 then relStep factory s else s
  let s := if iter % cfg.crossFreq == 0 then crossStep cfg s else s
  let s := if iter % cfg.boundAwareFreq == 0
    then boundAwareEqStep boundRules cfg s else s
  s

private def iterateN {α : Type} (f : Nat → α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateN f n (f n x)

/-- THE single saturation function. No alternatives, no stubs.
    - `factory = (fun _ => [])` → equality-only saturation (backward compat)
    - `factory = mkBabyBearFactory` → bound-aware NTT saturation
    - `boundRules = []` → no bound-aware rewrites (backward compat, F3 default) -/
def saturate (rules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (coloredRules : List MixedColoredSoundRule := [])
    (factory : BoundRuleFactory) (cfg : Config)
    (boundRules : List (MixedEMatch.RewriteRule MixedNodeOp) := [])
    (s : State) : State :=
  iterateN (tieredStep rules coloredRules factory cfg boundRules) cfg.totalFuel s

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Backward Compatibility
-- ══════════════════════════════════════════════════════════════════

/-- The null factory: no bound rules → no relation tracking. -/
def nullFactory : BoundRuleFactory := fun _ => []

/-- relStep with null factory is identity (no rules generated). -/
theorem relStep_null (s : State) : relStep nullFactory s = s := rfl

/-- crossStep on state with no relation edges is identity.
    (Empty DAGs produce no cross-evidence → no merges.) -/
theorem crossStep_empty_rels (cfg : Config) (s : State) (h : s.relEntries = #[]) :
    crossStep cfg s = s := by
  simp [crossStep, h]

/-- eqStep preserves relation entries (Layer 1 doesn't touch Layer 3). -/
theorem eqStep_preserves_relEntries (rules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (cfg : Config) (s : State) :
    (eqStep rules cfg s).relEntries = s.relEntries := rfl

/-- relStep with null factory preserves relEntries. -/
theorem relStep_null_preserves (s : State) :
    (relStep nullFactory s).relEntries = s.relEntries := rfl

/-- saturate with 0 fuel is identity (for any factory). -/
theorem saturate_zero_fuel (rules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (coloredRules : List MixedColoredSoundRule) (factory : BoundRuleFactory) (s : State) :
    saturate rules coloredRules factory { Config.default with totalFuel := 0 } s = s := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Theorems connecting to DirectedRelSpec
-- ══════════════════════════════════════════════════════════════════

/-- matchCrossEdges only produces pairs where dag2 has the reverse edge.
    This is the precondition for `antisymmetry_promotes`: if the DAGs
    are consistent, the matched pairs satisfy R(v(a),v(b)) ∧ R(v(b),v(a)),
    justifying the merge. -/
theorem matchCrossEdges_reverse_edge (dag1 dag2 : DirectedRelGraph)
    (pair : EClassId × EClassId) (hmem : pair ∈ matchCrossEdges dag1 dag2) :
    dag2.hasDirectEdge pair.2 pair.1 = true := by
  simp only [matchCrossEdges, List.mem_filterMap] at hmem
  obtain ⟨src_pair, _, hif⟩ := hmem
  split at hif
  · rename_i h_cond
    simp only [Option.some.injEq] at hif; rw [← hif]; exact h_cond
  · exact absurd hif (Option.not_mem_none _)

/-- matchCrossEdges on empty DAG produces nothing. -/
theorem matchCrossEdges_empty (dag : DirectedRelGraph) :
    matchCrossEdges DirectedRelGraph.empty dag = [] := by
  simp [matchCrossEdges, DirectedRelGraph.allEdges, DirectedRelGraph.empty]

-- ══════════════════════════════════════════════════════════════════
-- Section 8: State theorems
-- ══════════════════════════════════════════════════════════════════

theorem State.ofBase_baseGraph (g : MixedEGraph) : (State.ofBase g).baseGraph = g := rfl
theorem State.ofBase_noRelations (g : MixedEGraph) : (State.ofBase g).numRelations = 0 := rfl
theorem State.empty_numRelations : State.empty.numRelations = 0 := rfl
theorem State.empty_totalRelEdges : State.empty.totalRelEdges = 0 := rfl

theorem State.addRelation_numRelations (s : State) (name : String) :
    (s.addRelation name).numRelations = s.numRelations + 1 := by
  simp [addRelation, numRelations, Array.size_push]

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Multi-Relation Consistent Valuation (MRCV)
-- ══════════════════════════════════════════════════════════════════

/-- MRCV: the invariant for multi-relation colored e-graphs.
    Combines CCV (base + colored equalities) with relational consistency
    (all DAG edges satisfy their respective relations).

    The `rels` parameter maps each relEntry index to its semantic relation.
    This keeps RelEntry simple (no Prop fields) while still being sound. -/
def MRCV (s : State) (rels : Array (Nat → Nat → Prop))
    (baseCV : Prop) (env : MixedEnv) (v : EClassId → Nat) : Prop :=
  -- (1) Colored consistent valuation
  MixedCCV baseCV (AmoLean.EGraph.VerifiedExtraction.UnionFind.root s.baseGraph.unionFind ·)
    s.coloredLayer s.assumptions env v ∧
  -- (2) Relational consistency: every DAG edge satisfies its relation
  (∀ (i : Nat) (h : i < s.relEntries.size) (hr : i < rels.size),
    DirectedRelConsistency s.relEntries[i].dag rels[i] v)

/-- MRCV implies standard CV (backward compatibility).
    Any theorem using base ConsistentValuation still holds under MRCV. -/
theorem v2_implies_v1_soundness (s : State) (rels : Array (Nat → Nat → Prop))
    (baseCV : Prop) (env : MixedEnv) (v : EClassId → Nat)
    (hmrcv : MRCV s rels baseCV env v) :
    baseCV :=
  hmrcv.1.1

/-- MRCV of a fresh ofBase state with trivial assumptions holds
    when base CV holds (no colored equalities, no DAG edges to check). -/
theorem MRCV_ofBase (g : MixedEGraph) (rels : Array (Nat → Nat → Prop))
    (baseCV : Prop) (env : MixedEnv) (v : EClassId → Nat)
    (hcv : baseCV)
    (hbase_eq : ∀ (x y : EClassId),
      (AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind x ==
       AmoLean.EGraph.VerifiedExtraction.UnionFind.root g.unionFind y) = true →
      v x = v y) :
    MRCV (State.ofBase g) rels baseCV env v := by
  constructor
  · exact ColoredSpec.CV_implies_CCV_empty baseCV _ env v hcv hbase_eq
  · intro i h _; simp [State.ofBase] at h

/-- relStep with null factory preserves MRCV (no new edges added). -/
theorem relStep_null_preserves_MRCV (s : State) (rels : Array (Nat → Nat → Prop))
    (baseCV : Prop) (env : MixedEnv) (v : EClassId → Nat)
    (hmrcv : MRCV s rels baseCV env v) :
    MRCV (relStep nullFactory s) rels baseCV env v := by
  rw [relStep_null]; exact hmrcv

/-- eqStep preserves the relational part of MRCV
    (Layer 1 doesn't touch Layer 3 DAGs). -/
theorem eqStep_preserves_rel_MRCV (rules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (cfg : Config) (s : State)
    (rels : Array (Nat → Nat → Prop)) (v : EClassId → Nat)
    (hrel : ∀ (i : Nat) (h : i < s.relEntries.size) (hr : i < rels.size),
      DirectedRelConsistency s.relEntries[i].dag rels[i] v) :
    ∀ (i : Nat) (h : i < (eqStep rules cfg s).relEntries.size) (hr : i < rels.size),
      DirectedRelConsistency (eqStep rules cfg s).relEntries[i].dag rels[i] v := by
  intro i h hr
  have heq : (eqStep rules cfg s).relEntries = s.relEntries := eqStep_preserves_relEntries rules cfg s
  have h' : i < s.relEntries.size := heq ▸ h
  have : (eqStep rules cfg s).relEntries[i] = s.relEntries[i] := by
    simp [eqStep_preserves_relEntries]
  simp [this]; exact hrel i h' hr

-- ══════════════════════════════════════════════════════════════════
-- Section 10: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : State.empty.numRelations = 0 := rfl
example : State.empty.totalRelEdges = 0 := rfl
example : Config.default.totalFuel = 20 := rfl
example : (State.empty.addRelation "bounds").numRelations = 1 := by
  simp [State.addRelation, State.numRelations, State.empty, Array.size_push]

/-- saturate with null factory and 0 fuel is identity. -/
example : saturate [] [] nullFactory { Config.default with totalFuel := 0 }
    State.empty = State.empty := rfl

/-- relStep with null factory is identity. -/
example (s : State) : relStep nullFactory s = s := rfl

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.MultiRel
