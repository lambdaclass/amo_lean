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
import AmoLean.EGraph.Verified.Bitwise.MixedPipeline
import AmoLean.EGraph.Verified.Bitwise.MixedSaturation

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.MultiRel

open AmoLean.EGraph.VerifiedExtraction (EGraph EClassId)
open MixedPipeline (MixedEGraph)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: State
-- ══════════════════════════════════════════════════════════════════

structure RelEntry where
  dag : DirectedRelGraph
  name : String := "unnamed"

structure State where
  baseGraph : MixedEGraph
  relEntries : Array RelEntry := #[]

instance : Inhabited State where
  default := { baseGraph := default, relEntries := #[] }

def State.ofBase (g : MixedEGraph) : State where baseGraph := g
def State.empty : State where baseGraph := default
def State.numNodes (s : State) : Nat := s.baseGraph.numNodes
def State.numClasses (s : State) : Nat := s.baseGraph.numClasses
def State.numRelations (s : State) : Nat := s.relEntries.size
def State.totalRelEdges (s : State) : Nat :=
  s.relEntries.foldl (fun acc e => acc + e.dag.numEdges) 0

def State.addRelation (s : State) (name : String) : State where
  baseGraph := s.baseGraph
  relEntries := s.relEntries.push { dag := DirectedRelGraph.empty, name }

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
-- Section 5: Single Tiered Saturation Loop
-- ══════════════════════════════════════════════════════════════════

/-- One iteration of tiered saturation. All three steps are real. -/
def tieredStep (rules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (factory : BoundRuleFactory) (cfg : Config)
    (iter : Nat) (s : State) : State :=
  let s := if iter % cfg.eqFreq == 0 then eqStep rules cfg s else s
  let s := if iter % cfg.relFreq == 0 then relStep factory s else s
  let s := if iter % cfg.crossFreq == 0 then crossStep cfg s else s
  s

private def iterateN {α : Type} (f : Nat → α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateN f n (f n x)

/-- THE single saturation function. No alternatives, no stubs.
    - `factory = (fun _ => [])` → equality-only saturation (backward compat)
    - `factory = mkBabyBearFactory` → bound-aware NTT saturation -/
def saturate (rules : List (MixedEMatch.RewriteRule MixedNodeOp))
    (factory : BoundRuleFactory) (cfg : Config) (s : State) : State :=
  iterateN (tieredStep rules factory cfg) cfg.totalFuel s

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
    (factory : BoundRuleFactory) (s : State) :
    saturate rules factory { Config.default with totalFuel := 0 } s = s := rfl

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
-- Section 9: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : State.empty.numRelations = 0 := rfl
example : State.empty.totalRelEdges = 0 := rfl
example : Config.default.totalFuel = 20 := rfl
example : (State.empty.addRelation "bounds").numRelations = 1 := by
  simp [State.addRelation, State.numRelations, State.empty, Array.size_push]

/-- saturate with null factory and 0 fuel is identity. -/
example : saturate [] nullFactory { Config.default with totalFuel := 0 }
    State.empty = State.empty := rfl

/-- relStep with null factory is identity. -/
example (s : State) : relStep nullFactory s = s := rfl

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.MultiRel
