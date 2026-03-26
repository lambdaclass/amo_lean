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
-- Section 2: Antisymmetry Promotion (Cross-Layer Rule)
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
