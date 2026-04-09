/-
  AMO-Lean Ultra — Phase 22: BoundPropagation
  Domain-specific bound rules for NTT field arithmetic.

  Provides `BoundRuleFactory` constructors that generate FRESH
  bound rules each iteration, reading the CURRENT DAG state.

  Key exports:
  - `mkFieldFactory`: creates a BoundRuleFactory for a given field prime
  - `ReductionChoice`: solinasFold | montgomery | harvey | lazy
  - `stageBoundFactor`: compute output bound after a reduction
  - Theorems: reduce_bound, add_bound_prop, harvey_1br, etc.
-/
import AmoLean.EGraph.Verified.Bitwise.MultiRelMixed

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.BoundProp

open AmoLean.EGraph.VerifiedExtraction (EGraph EClassId ENode EClass)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp DirectedRelGraph BoundedByKP)
open AmoLean.EGraph.Verified.Bitwise.MultiRel (State BoundRule BoundRuleFactory)
open MixedPipeline (MixedEGraph)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Core Bound Theorems
-- ══════════════════════════════════════════════════════════════════

def reductionBoundFactor : MixedNodeOp → Nat
  | .reduceGate _ _ => 1
  | .montyReduce _ _ _ => 1
  | .barrettReduce _ _ _ => 1
  | .harveyReduce _ _ => 1  -- Harvey output < p (harveyReduceSpec postcondition)
  | _ => 0

theorem reduce_bound (x p : Nat) (hp : 0 < p) : x % p < 1 * p := by
  rw [Nat.one_mul]; exact Nat.mod_lt x hp

theorem add_bound_prop (a b p k₁ k₂ : Nat) (ha : a < k₁ * p) (hb : b < k₂ * p) :
    a + b < (k₁ + k₂) * p := BoundedByKP_add ha hb

theorem mul_bound_prop (a b p k₁ k₂ : Nat) (ha : a < k₁ * p) (hb : b < k₂ * p) :
    a * b < (k₁ * p) * (k₂ * p) := Nat.mul_lt_mul_of_lt_of_lt ha hb

theorem sub_bound_prop (a b p k : Nat) (ha : a < k * p) : a - b < k * p :=
  Nat.lt_of_le_of_lt (Nat.sub_le a b) ha

theorem ct_sum_bound (a wb p k₁ k₂ : Nat) (ha : a < k₁ * p) (hwb : wb < k₂ * p) :
    a + wb < (k₁ + k₂) * p := add_bound_prop a wb p k₁ k₂ ha hwb

theorem harvey_1br (x p : Nat) (hx : x < 2 * p) (hp : 0 < p) :
    (if x ≥ p then x - p else x) < p := by split <;> omega

theorem harvey_2br (x p : Nat) (hx : x < 2 * p) (hge : x ≥ p) : x - p < p := by omega

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Sentinel Encoding
-- ══════════════════════════════════════════════════════════════════

/-- Sentinel base for encoding bound factors in edge targets. -/
def sentinelBase : Nat := 1000000

def encodeBoundFactor (k : Nat) : EClassId := sentinelBase + k

def decodeBoundFactor (sentinel : EClassId) : Option Nat :=
  if sentinel ≥ sentinelBase then some (sentinel - sentinelBase) else none

theorem decode_encode (k : Nat) : decodeBoundFactor (encodeBoundFactor k) = some k := by
  simp [decodeBoundFactor, encodeBoundFactor, sentinelBase]

/-- Build a bound lookup from a relation DAG's sentinel edges. -/
def buildBoundLookup (dag : DirectedRelGraph) : EClassId → Option Nat :=
  fun classId =>
    dag.successors classId |>.foldl (fun best dst =>
      match decodeBoundFactor dst with
      | some k => match best with
        | some bestK => if k < bestK then some k else some bestK
        | none => some k
      | none => best
    ) none

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Concrete BoundRule Constructors
-- ══════════════════════════════════════════════════════════════════

def isReductionOp : MixedNodeOp → Bool
  | .reduceGate _ _ | .montyReduce _ _ _ | .barrettReduce _ _ _ | .harveyReduce _ _ => true
  | _ => false

/-- Scan e-graph for reduction nodes, add sentinel edges encoding their bounds. -/
def mkReductionBoundRule (p : Nat) (relIdx : Nat) : BoundRule where
  name := s!"reduction_bound_p{p}"
  relIdx := relIdx
  apply := fun g =>
    g.classes.toList.foldl (fun acc (classId, eclass) =>
      let bestK := eclass.nodes.foldl (fun best node =>
        let k := reductionBoundFactor node.op
        if k > 0 && (best == 0 || k < best) then k else best
      ) 0
      if bestK > 0 then acc ++ [(classId, encodeBoundFactor bestK)]
      else acc
    ) []

/-- Scan e-graph for add nodes where both children have known bounds.
    The bound lookup is passed in, but it's created from the CURRENT
    DAG state by the factory — not frozen at initialization. -/
def mkAddBoundRule (relIdx : Nat) (lookup : EClassId → Option Nat) : BoundRule where
  name := "add_bound_propagation"
  relIdx := relIdx
  apply := fun g =>
    g.classes.toList.foldl (fun acc (classId, eclass) =>
      let result := eclass.nodes.foldl (fun best node =>
        match node.op with
        | .addGate child1 child2 =>
          match lookup child1, lookup child2 with
          | some k1, some k2 => some (k1 + k2)
          | _, _ => best
        | _ => best
      ) (none : Option Nat)
      match result with
      | some k => acc ++ [(classId, encodeBoundFactor k)]
      | none => acc
    ) []

-- ══════════════════════════════════════════════════════════════════
-- Section 4: BoundRuleFactory Constructors
-- ══════════════════════════════════════════════════════════════════

/-- Create a BoundRuleFactory for a given field prime.
    The factory reads the CURRENT DAG state each time it's called,
    so mkAddBoundRule always sees the latest bounds. -/
def mkFieldFactory (p : Nat) (relIdx : Nat := 0) : BoundRuleFactory := fun s =>
  let currentLookup :=
    if h : relIdx < s.relEntries.size
    then buildBoundLookup s.relEntries[relIdx].dag
    else fun _ => none
  [mkReductionBoundRule p relIdx, mkAddBoundRule relIdx currentLookup]

def babyBearFactory : BoundRuleFactory := mkFieldFactory 2013265921
def mersenne31Factory : BoundRuleFactory := mkFieldFactory 2147483647
def goldilocksFactory : BoundRuleFactory := mkFieldFactory 18446744069414584321

-- ══════════════════════════════════════════════════════════════════
-- Section 5: ReductionChoice + Stage Analysis
-- ══════════════════════════════════════════════════════════════════

inductive ReductionChoice where
  | solinasFold | montgomery | harvey | lazy
  deriving Repr, BEq, DecidableEq, Inhabited

def boundAfterReduction : ReductionChoice → Nat
  | .solinasFold => 2 | .montgomery => 1 | .harvey => 1 | .lazy => 0

def stageBoundFactor (inputK : Nat) (reduction : ReductionChoice) : Nat :=
  match reduction with
  | .lazy => inputK + 1
  | r => boundAfterReduction r

def lazyReductionSafe (currentK : Nat) (p : Nat) : Bool :=
  (currentK + 1) * p < 2 ^ 64

def computeStageBounds (stages : List ReductionChoice) (initialK : Nat) : List Nat :=
  stages.scanl stageBoundFactor initialK

-- ══════════════════════════════════════════════════════════════════
-- Section 6: relStep Soundness (N27.9 GATE)
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise.MultiRel (MRCV relStep)

/-- A sound factory: every edge it generates satisfies the relation.
    This is the interface contract for BoundRuleFactory — the factory
    must only produce edges where R(v(src), v(dst)) holds. -/
def SoundFactory (factory : BoundRuleFactory) (rels : Array (Nat → Nat → Prop))
    (v : EClassId → Nat) : Prop :=
  ∀ (s : State),
  ∀ rule ∈ factory s,
  ∀ (hr : rule.relIdx < rels.size),
  ∀ pair ∈ rule.apply s.baseGraph,
    rels[rule.relIdx] (v pair.1) (v pair.2)

/-- relStep only modifies relEntries (not baseGraph, coloredLayer, assumptions). -/
theorem relStep_preserves_baseGraph (factory : BoundRuleFactory) (s : State) :
    (relStep factory s).baseGraph = s.baseGraph := by
  simp only [relStep]
  -- foldl over rules: each rule.apply only adds edges, not changes baseGraph
  -- addBoundEdge preserves baseGraph by definition
  suffices h : ∀ (rules : List BoundRule) (s' : State),
    s'.baseGraph = s.baseGraph →
    (rules.foldl (fun s' rule =>
      (rule.apply s'.baseGraph).foldl (fun s'' (src, dst) =>
        s''.addBoundEdge rule.relIdx src dst) s') s').baseGraph = s.baseGraph by
    exact h (factory s) s rfl
  intro rules; induction rules with
  | nil => intro s' h; exact h
  | cons rule rest ih =>
    intro s' hbase
    apply ih
    -- After inner foldl, baseGraph is unchanged (addBoundEdge preserves it)
    suffices h : ∀ (edges : List (EClassId × EClassId)) (s'' : State),
      s''.baseGraph = s.baseGraph →
      (edges.foldl (fun s'' (src, dst) => s''.addBoundEdge rule.relIdx src dst) s'').baseGraph = s.baseGraph by
      exact h (rule.apply s'.baseGraph) s' hbase
    intro edges; induction edges with
    | nil => intro s'' h; exact h
    | cons e rest ih2 =>
      intro s'' hbase2; apply ih2
      simp [State.addBoundEdge]; split <;> simp [*]

theorem relStep_preserves_coloredLayer (factory : BoundRuleFactory) (s : State) :
    (relStep factory s).coloredLayer = s.coloredLayer := by
  simp only [relStep]
  suffices h : ∀ (rules : List BoundRule) (s' : State),
    s'.coloredLayer = s.coloredLayer →
    (rules.foldl (fun s' rule =>
      (rule.apply s'.baseGraph).foldl (fun s'' (src, dst) =>
        s''.addBoundEdge rule.relIdx src dst) s') s').coloredLayer = s.coloredLayer by
    exact h (factory s) s rfl
  intro rules; induction rules with
  | nil => intro s' h; exact h
  | cons rule rest ih =>
    intro s' hcl; apply ih
    suffices h : ∀ (edges : List (EClassId × EClassId)) (s'' : State),
      s''.coloredLayer = s.coloredLayer →
      (edges.foldl (fun s'' (src, dst) => s''.addBoundEdge rule.relIdx src dst) s'').coloredLayer = s.coloredLayer by
      exact h (rule.apply s'.baseGraph) s' hcl
    intro edges; induction edges with
    | nil => intro s'' h; exact h
    | cons e rest ih2 => intro s'' h; apply ih2; simp [State.addBoundEdge]; split <;> simp [*]

theorem relStep_preserves_assumptions (factory : BoundRuleFactory) (s : State) :
    (relStep factory s).assumptions = s.assumptions := by
  simp only [relStep]
  suffices h : ∀ (rules : List BoundRule) (s' : State),
    s'.assumptions = s.assumptions →
    (rules.foldl (fun s' rule =>
      (rule.apply s'.baseGraph).foldl (fun s'' (src, dst) =>
        s''.addBoundEdge rule.relIdx src dst) s') s').assumptions = s.assumptions by
    exact h (factory s) s rfl
  intro rules; induction rules with
  | nil => intro s' h; exact h
  | cons rule rest ih =>
    intro s' ha; apply ih
    suffices h : ∀ (edges : List (EClassId × EClassId)) (s'' : State),
      s''.assumptions = s.assumptions →
      (edges.foldl (fun s'' (src, dst) => s''.addBoundEdge rule.relIdx src dst) s'').assumptions = s.assumptions by
      exact h (rule.apply s'.baseGraph) s' ha
    intro edges; induction edges with
    | nil => intro s'' h; exact h
    | cons e rest ih2 => intro s'' h; apply ih2; simp [State.addBoundEdge]; split <;> simp [*]

/-- addBoundEdge preserves relEntries.size. -/
theorem addBoundEdge_size (s : State) (idx src dst : EClassId) :
    (s.addBoundEdge idx src dst).relEntries.size = s.relEntries.size := by
  unfold State.addBoundEdge; split
  · simp [Array.size_set]
  · rfl

/-- addBoundEdge preserves baseGraph. -/
theorem addBoundEdge_base (s : State) (idx src dst : EClassId) :
    (s.addBoundEdge idx src dst).baseGraph = s.baseGraph := by
  unfold State.addBoundEdge; split <;> rfl

/-- addBoundEdge preserves relational consistency at every index.
    For idx=i (in-bounds): uses addEdge_preserves_consistency.
    For idx≠i or out-of-bounds: DAG unchanged. -/
private theorem addBoundEdge_preserves_rel_at (s : State)
    (rels : Array (Nat → Nat → Prop)) (v : EClassId → Nat)
    (idx src dst : EClassId)
    (hrel : ∀ (i : Nat) (h : i < s.relEntries.size) (hr : i < rels.size),
      DirectedRelConsistency s.relEntries[i].dag rels[i] v)
    (hsound : ∀ (hr : idx < rels.size), rels[idx] (v src) (v dst)) :
    ∀ (i : Nat) (h : i < (s.addBoundEdge idx src dst).relEntries.size)
      (hr : i < rels.size),
    DirectedRelConsistency (s.addBoundEdge idx src dst).relEntries[i].dag rels[i] v := by
  intro i hi hir
  -- Rewrite using addBoundEdge_size to get the index bound
  have hsize' := addBoundEdge_size s idx src dst
  have hsize : i < s.relEntries.size := hsize' ▸ hi
  -- Case split: is idx in-bounds?
  unfold State.addBoundEdge
  split
  · rename_i hidx
    -- idx in bounds: Array.set modifies one entry
    simp only [Array.getElem_set]
    split
    · -- idx = i: DAG gets addEdge
      rename_i heq; subst heq
      exact addEdge_preserves_consistency _ _ v src dst (hrel idx hidx hir) (hsound hir)
    · -- idx ≠ i: DAG unchanged
      exact hrel i hsize hir
  · -- idx out of bounds: identity
    exact hrel i hsize hir

/-- Inner foldl (over edges) preserves relational consistency. -/
private theorem inner_foldl_preserves_rel
    (edges : List (EClassId × EClassId)) (s' : State)
    (origBase : MixedEGraph) (origSize : Nat)
    (rels : Array (Nat → Nat → Prop)) (v : EClassId → Nat)
    (relIdx : Nat)
    (hbase₀ : s'.baseGraph = origBase)
    (hsize₀ : s'.relEntries.size = origSize)
    (hrel : ∀ (i : Nat) (h : i < s'.relEntries.size) (hr : i < rels.size),
      DirectedRelConsistency s'.relEntries[i].dag rels[i] v)
    (hsound : ∀ pair ∈ edges, ∀ (hr : relIdx < rels.size), rels[relIdx] (v pair.1) (v pair.2)) :
    let s'' := edges.foldl (fun acc (p : EClassId × EClassId) =>
      acc.addBoundEdge relIdx p.1 p.2) s'
    (s''.baseGraph = origBase) ∧
    (s''.relEntries.size = origSize) ∧
    (∀ (i : Nat) (h : i < s''.relEntries.size) (hr : i < rels.size),
      DirectedRelConsistency s''.relEntries[i].dag rels[i] v) := by
  induction edges generalizing s' with
  | nil => exact ⟨hbase₀, hsize₀, hrel⟩
  | cons e rest ih =>
    simp only [List.foldl]
    apply ih
    · rw [addBoundEdge_base]; exact hbase₀
    · rw [addBoundEdge_size]; exact hsize₀
    · intro i hi' hir'
      exact addBoundEdge_preserves_rel_at s' rels v relIdx e.1 e.2 hrel
        (fun hr => hsound e (.head rest) hr) i hi' hir'
    · intro pair hmem
      exact hsound pair (.tail e hmem)

/-- relStep preserves MRCV when the factory is sound.
    THE GATE THEOREM: connects computational relStep to formal MRCV. -/
theorem relStepMixed_preserves_MRCV (factory : BoundRuleFactory)
    (rels : Array (Nat → Nat → Prop))
    (baseCV : Prop) (env : MixedEnv) (v : EClassId → Nat)
    (s : State) (hmrcv : MRCV s rels baseCV env v)
    (hsound : SoundFactory factory rels v) :
    MRCV (relStep factory s) rels baseCV env v := by
  constructor
  · -- CCV part: relStep doesn't change baseGraph or coloredLayer
    have hb := relStep_preserves_baseGraph factory s
    have hcl := relStep_preserves_coloredLayer factory s
    have ha := relStep_preserves_assumptions factory s
    simp only [MRCV] at hmrcv ⊢
    rw [hb, hcl, ha]; exact hmrcv.1
  · -- Relational part: nested foldl induction (N28.5)
    simp only [relStep]
    -- Outer foldl over rules from factory s
    suffices h : ∀ (rules : List BoundRule) (s' : State),
        (∀ rule ∈ rules, ∀ (hr : rule.relIdx < rels.size),
          ∀ pair ∈ rule.apply s.baseGraph, rels[rule.relIdx] (v pair.1) (v pair.2)) →
        s'.baseGraph = s.baseGraph →
        s'.relEntries.size = s.relEntries.size →
        (∀ (i : Nat) (h : i < s'.relEntries.size) (hr : i < rels.size),
          DirectedRelConsistency s'.relEntries[i].dag rels[i] v) →
        ∀ (i : Nat) (h : i < (rules.foldl (fun s' rule =>
          (rule.apply s'.baseGraph).foldl (fun s'' (p : EClassId × EClassId) =>
            s''.addBoundEdge rule.relIdx p.1 p.2) s') s').relEntries.size)
          (hr : i < rels.size),
        DirectedRelConsistency (rules.foldl (fun s' rule =>
          (rule.apply s'.baseGraph).foldl (fun s'' (p : EClassId × EClassId) =>
            s''.addBoundEdge rule.relIdx p.1 p.2) s') s').relEntries[i].dag rels[i] v by
      exact h (factory s) s
        (fun rule hmem hr pair hpair => hsound s rule hmem hr pair hpair)
        rfl rfl hmrcv.2
    intro rules
    induction rules with
    | nil => intro s' _ _ _ hrel i hi hr; exact hrel i hi hr
    | cons rule rest ih =>
      intro s' hrules hbase hsize hrel
      simp only [List.foldl]
      -- Apply inner foldl lemma for this rule
      have hinnerBase : s'.baseGraph = s.baseGraph := hbase
      have hedges := inner_foldl_preserves_rel
        (rule.apply s'.baseGraph) s' s.baseGraph s.relEntries.size rels v rule.relIdx
        hinnerBase hsize hrel
        (fun pair hmem hr =>
          hrules rule (.head rest) hr pair (hinnerBase ▸ hmem))
      -- After inner foldl: extract compound invariant
      let s'' := (rule.apply s'.baseGraph).foldl
        (fun acc (p : EClassId × EClassId) => acc.addBoundEdge rule.relIdx p.1 p.2) s'
      have hbase' : s''.baseGraph = s.baseGraph := hedges.1
      have hsize' : s''.relEntries.size = s.relEntries.size := hedges.2.1
      have hrel' := hedges.2.2
      -- Delegate to outer IH
      exact ih s''
        (fun r hmem => hrules r (.tail rule hmem))
        hbase' hsize' hrel'

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : 17 % 5 < 1 * 5 := reduce_bound 17 5 (by omega)
example : 3 + 4 < (1 + 1) * 5 := by native_decide
example : lazyReductionSafe 100 2013265921 = true := by native_decide
example : computeStageBounds [.lazy, .lazy, .solinasFold] 1 = [1, 2, 3, 2] := by native_decide
example : decodeBoundFactor (encodeBoundFactor 3) = some 3 := by native_decide
example : reductionBoundFactor (.montyReduce 0 0 0) = 1 := rfl
example : reductionBoundFactor (.harveyReduce 0 0) = 1 := rfl

/-- Factory produces non-empty rules for a state with a bounds DAG. -/
example : (babyBearFactory (State.empty.addRelation "bounds")).length = 2 := rfl

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.BoundProp
