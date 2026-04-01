/-
  AMO-Lean Ultra — Phase 22: DirectedRelSpec
  Soundness specification for directed relation graphs.

  Every theorem here is USED by MultiRelMixed.lean to maintain
  the consistency invariant during saturation. No orphan specs.

  Key results:
  - `DirectedRelConsistency`: edges in DAG imply relation holds
  - `addEdge_preserves_consistency`: adding sound edges is safe
  - `antisymmetry_promotes`: a≤b ∧ b≤a → v(a)=v(b) (justifies merge)
  - `BoundRelConsistency`: specialized for NTT bound tracking
-/
import AmoLean.EGraph.Verified.Bitwise.RelationTypes

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified (EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: DirectedRelConsistency
-- ══════════════════════════════════════════════════════════════════

/-- Semantic consistency: every edge (a,b) in the DAG implies R(v(a), v(b)).
    USED BY: MultiRelMixed.relStep to verify new edges are sound.
    USED BY: MultiRelMixed.crossStep to justify merges. -/
def DirectedRelConsistency {Val : Type} (drg : DirectedRelGraph)
    (R : Val → Val → Prop) (v : EClassId → Val) : Prop :=
  ∀ a b, drg.hasDirectEdge a b → R (v a) (v b)

/-- Empty graph is trivially consistent.
    USED BY: MultiRelMixed.State.ofBase (initial state has empty DAGs). -/
theorem empty_consistent_rel {Val : Type} (R : Val → Val → Prop) (v : EClassId → Val) :
    DirectedRelConsistency DirectedRelGraph.empty R v := by
  intro a b h
  simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors,
        DirectedRelGraph.empty] at h

/-- Adding an edge preserves consistency if the relation holds.
    USED BY: MultiRelMixed.relStep (each new edge passes this check). -/
theorem addEdge_preserves_consistency {Val : Type} (drg : DirectedRelGraph)
    (R : Val → Val → Prop) (v : EClassId → Val) (a b : EClassId)
    (hcon : DirectedRelConsistency drg R v) (h_sound : R (v a) (v b)) :
    DirectedRelConsistency (drg.addEdge a b) R v := by
  intro x y hxy
  simp [DirectedRelGraph.addEdge, DirectedRelGraph.hasDirectEdge,
        DirectedRelGraph.successors] at hxy
  rw [Std.HashMap.getD_insert] at hxy
  split at hxy
  · rename_i heq
    have hxa : a = x := eq_of_beq heq
    subst hxa
    simp [List.mem_cons] at hxy
    rcases hxy with rfl | hmem
    · exact h_sound
    · exact hcon a y (by simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors, hmem])
  · exact hcon x y (by simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors, hxy])

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Relation Properties
-- ══════════════════════════════════════════════════════════════════

def IsReflexive {Val : Type} (R : Val → Val → Prop) : Prop := ∀ x, R x x
def IsTransitive {Val : Type} (R : Val → Val → Prop) : Prop := ∀ x y z, R x y → R y z → R x z
def IsAntisymmetric {Val : Type} (R : Val → Val → Prop) : Prop := ∀ x y, R x y → R y x → x = y
def IsPreorder {Val : Type} (R : Val → Val → Prop) : Prop := IsReflexive R ∧ IsTransitive R
def IsPartialOrder {Val : Type} (R : Val → Val → Prop) : Prop := IsPreorder R ∧ IsAntisymmetric R

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Path Transitivity
-- ══════════════════════════════════════════════════════════════════

private theorem go_implies_relation {Val : Type} (drg : DirectedRelGraph)
    (R : Val → Val → Prop) (v : EClassId → Val)
    (hcon : DirectedRelConsistency drg R v)
    (htrans : IsTransitive R)
    (hrefl : IsReflexive R)
    (b : EClassId) :
    ∀ (fuel : Nat) (queue : List EClassId) (visited : Std.HashSet EClassId),
    DirectedRelGraph.hasPath.go drg b queue visited fuel = true →
    ∃ c ∈ queue, R (v c) (v b) := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue visited hgo
    cases queue <;> simp_all [DirectedRelGraph.hasPath.go]
  | succ n ih =>
    intro queue visited hgo
    match hq : queue with
    | [] => simp [DirectedRelGraph.hasPath.go] at hgo
    | cur :: rest =>
      unfold DirectedRelGraph.hasPath.go at hgo
      by_cases hcur : cur == b
      · have := beq_iff_eq.mp hcur
        subst this
        exact ⟨cur, .head rest, hrefl (v cur)⟩
      · simp [hcur] at hgo
        split at hgo
        · obtain ⟨c, hc_mem, hcR⟩ := ih rest visited hgo
          exact ⟨c, List.mem_cons_of_mem _ hc_mem, hcR⟩
        · obtain ⟨c, hc_mem, hcR⟩ := ih (rest ++ drg.successors cur) (visited.insert cur) hgo
          rw [List.mem_append] at hc_mem
          rcases hc_mem with hc_rest | hc_succ
          · exact ⟨c, List.mem_cons_of_mem _ hc_rest, hcR⟩
          · have hedge : drg.hasDirectEdge cur c := by
              simp [DirectedRelGraph.hasDirectEdge, hc_succ]
            exact ⟨cur, .head rest,
              htrans (v cur) (v c) (v b) (hcon cur c hedge) hcR⟩

/-- If R is transitive+reflexive and the graph is R-consistent, then a path
    from a to b implies R(v(a), v(b)). -/
theorem hasPath_implies_relation {Val : Type} (drg : DirectedRelGraph)
    (R : Val → Val → Prop) (v : EClassId → Val)
    (hcon : DirectedRelConsistency drg R v)
    (htrans : IsTransitive R)
    (hrefl : IsReflexive R)
    (a b : EClassId) (fuel : Nat)
    (hpath : drg.hasPath a b fuel = true) :
    R (v a) (v b) := by
  simp only [DirectedRelGraph.hasPath] at hpath
  obtain ⟨c, hc_mem, hcR⟩ := go_implies_relation drg R v hcon htrans hrefl b fuel [a] {} hpath
  simp at hc_mem
  subst hc_mem
  exact hcR

/-- Combining bidirectional paths with antisymmetry: a→b ∧ b→a → v(a) = v(b). -/
theorem bidirectional_path_implies_eq {Val : Type} (drg : DirectedRelGraph)
    (R : Val → Val → Prop) (v : EClassId → Val)
    (hcon : DirectedRelConsistency drg R v)
    (hpo : IsPartialOrder R)
    (a b : EClassId) (fuel : Nat)
    (hab : drg.hasPath a b fuel = true)
    (hba : drg.hasPath b a fuel = true) :
    v a = v b := by
  have hrefl := hpo.1.1
  have htrans := hpo.1.2
  have hanti := hpo.2
  exact hanti (v a) (v b)
    (hasPath_implies_relation drg R v hcon htrans hrefl a b fuel hab)
    (hasPath_implies_relation drg R v hcon htrans hrefl b a fuel hba)

/-- Equality implies any reflexive relation. Layer 1 informs Layer 3. -/
theorem equality_implies_relation {Val : Type}
    (R : Val → Val → Prop) (v : EClassId → Val)
    (hrefl : IsReflexive R) (a b : EClassId)
    (heq : v a = v b) :
    R (v a) (v b) := by
  rw [heq]; exact hrefl (v b)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Antisymmetry Promotion (Cross-Layer Rule)
-- ══════════════════════════════════════════════════════════════════

/-- If R is antisymmetric and we have R(v(a),v(b)) and R(v(b),v(a)),
    then v(a) = v(b). This justifies merging a and b in Layer 1.
    USED BY: MultiRelMixed.crossStep (promote DAG evidence → UF merge). -/
theorem antisymmetry_promotes {Val : Type}
    (R : Val → Val → Prop) (v : EClassId → Val)
    (hanti : ∀ x y, R x y → R y x → x = y)
    (a b : EClassId) (h_ab : R (v a) (v b)) (h_ba : R (v b) (v a)) :
    v a = v b :=
  hanti (v a) (v b) h_ab h_ba

-- ══════════════════════════════════════════════════════════════════
-- Section 3: BoundRelConsistency (NTT-specific)
-- ══════════════════════════════════════════════════════════════════

/-- Bound-specific consistency: edges encode "class has bounded value".
    USED BY: BoundPropagation rules to track x < k*p. -/
def BoundRelConsistency (p k : Nat) (drg : DirectedRelGraph) (v : EClassId → Nat) : Prop :=
  ∀ a b, drg.hasDirectEdge a b → v a < k * p

theorem bound_empty_consistent (p k : Nat) (v : EClassId → Nat) :
    BoundRelConsistency p k DirectedRelGraph.empty v := by
  intro a b h
  simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors,
        DirectedRelGraph.empty] at h

theorem bound_addEdge_preserves (p k : Nat) (drg : DirectedRelGraph)
    (v : EClassId → Nat) (a sentinel : EClassId)
    (hcon : BoundRelConsistency p k drg v) (h_bound : v a < k * p) :
    BoundRelConsistency p k (drg.addEdge a sentinel) v := by
  intro x y hxy
  simp [DirectedRelGraph.addEdge, DirectedRelGraph.hasDirectEdge,
        DirectedRelGraph.successors] at hxy
  rw [Std.HashMap.getD_insert] at hxy
  split at hxy
  · rename_i heq; have := eq_of_beq heq; subst this; exact h_bound
  · exact hcon x y (by simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors, hxy])

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : DirectedRelConsistency DirectedRelGraph.empty (fun (a b : Nat) => a ≤ b)
    (fun _ => 0) := empty_consistent_rel _ _

example : ∀ (a b : Nat), a ≤ b → b ≤ a → a = b :=
  fun a b h1 h2 => antisymmetry_promotes (fun a b => a ≤ b) id
    (fun x y h1 h2 => Nat.le_antisymm h1 h2) a b h1 h2

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise
