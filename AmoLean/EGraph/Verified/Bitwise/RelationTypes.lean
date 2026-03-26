/-
  AMO-Lean Ultra — Phase 22: Relation Types
  Foundation types for the relational saturation layer.

  Provides:
  - `DirectedRelGraph`: adjacency-list DAG for directed relations
  - `BoundedByKP`: the key relation for NTT bound propagation (x < k*p)
  - `MixedSoundRelationRule`: generalized rewrite rule for arbitrary relations
-/
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules
import Std.Data.HashMap
import Std.Data.HashSet

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified (EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Directed Relation Graph
-- ══════════════════════════════════════════════════════════════════

/-- A directed graph storing relation edges between e-class IDs.
    Edge (a, b) means "R(value_at_a, value_at_b)" for the associated relation. -/
structure DirectedRelGraph where
  edges : Std.HashMap EClassId (List EClassId) := {}
  numEdges : Nat := 0

namespace DirectedRelGraph

def empty : DirectedRelGraph := {}

def addEdge (g : DirectedRelGraph) (src dst : EClassId) : DirectedRelGraph where
  edges := g.edges.insert src (dst :: g.edges.getD src [])
  numEdges := g.numEdges + 1

def successors (g : DirectedRelGraph) (src : EClassId) : List EClassId :=
  g.edges.getD src []

def hasDirectEdge (g : DirectedRelGraph) (src dst : EClassId) : Bool :=
  (g.successors src).contains dst

def allEdges (g : DirectedRelGraph) : List (EClassId × EClassId) :=
  (g.edges.toList.map fun (src, dsts) => dsts.map fun dst => (src, dst)).flatten

def canonicalize (g : DirectedRelGraph) (find : EClassId → EClassId) : DirectedRelGraph :=
  g.allEdges.foldl (fun acc (src, dst) =>
    let src' := find src
    let dst' := find dst
    if acc.hasDirectEdge src' dst' then acc
    else acc.addEdge src' dst') DirectedRelGraph.empty

theorem empty_noEdges : DirectedRelGraph.empty.numEdges = 0 := rfl

theorem addEdge_numEdges (g : DirectedRelGraph) (src dst : EClassId) :
    (g.addEdge src dst).numEdges = g.numEdges + 1 := rfl

end DirectedRelGraph

-- ══════════════════════════════════════════════════════════════════
-- Section 2: BoundedByKP — The Key Relation for NTT
-- ══════════════════════════════════════════════════════════════════

/-- `BoundedByKP p x k` means `x < k * p`.
    - After Solinas fold: k = 2 (output in [0, 2p))
    - After Montgomery:   k = 1 (output in [0, p))
    - After add of bounded values: k₁ + k₂ -/
def BoundedByKP (p : Nat) (x k : Nat) : Prop := x < k * p

theorem BoundedByKP_mono {p x k₁ k₂ : Nat} (hk : k₁ ≤ k₂)
    (hx : BoundedByKP p x k₁) : BoundedByKP p x k₂ := by
  unfold BoundedByKP at *
  exact Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right p hk)

theorem BoundedByKP_add {p a b k₁ k₂ : Nat}
    (ha : BoundedByKP p a k₁) (hb : BoundedByKP p b k₂) :
    BoundedByKP p (a + b) (k₁ + k₂) := by
  unfold BoundedByKP at *
  calc a + b < k₁ * p + k₂ * p := Nat.add_lt_add ha hb
    _ = (k₁ + k₂) * p := (Nat.add_mul k₁ k₂ p).symm

theorem BoundedByKP_lt_pow {p x k : Nat} (hx : BoundedByKP p x k)
    (hkp : k * p < 2 ^ 64) : x < 2 ^ 64 :=
  Nat.lt_trans hx hkp

theorem mod_BoundedByKP (x p : Nat) (hp : 0 < p) : BoundedByKP p (x % p) 1 := by
  unfold BoundedByKP; have := Nat.mod_lt x hp; omega

-- ══════════════════════════════════════════════════════════════════
-- Section 3: MixedSoundRelationRule — Generalized Rewrite Rules
-- ══════════════════════════════════════════════════════════════════

/-- A sound relation rule: R holds between evaluations of LHS and RHS.
    When R = Eq, reduces to `MixedSoundRule`. -/
structure MixedSoundRelationRule (R : Nat → Nat → Prop) where
  name : String
  lhsEval : MixedEnv → (EClassId → Nat) → Nat
  rhsEval : MixedEnv → (EClassId → Nat) → Nat
  soundness : ∀ (env : MixedEnv) (v : EClassId → Nat),
    R (lhsEval env v) (rhsEval env v)

/-- Convert MixedSoundRule (equality) to MixedSoundRelationRule Eq. -/
def MixedSoundRule.toRelationRule (r : MixedSoundRule) : MixedSoundRelationRule Eq where
  name := r.name
  lhsEval := r.lhsEval
  rhsEval := r.rhsEval
  soundness := r.soundness

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : DirectedRelGraph.empty.numEdges = 0 := rfl
example : (DirectedRelGraph.empty.addEdge 1 2).numEdges = 1 := rfl
example : BoundedByKP 3 5 2 := by unfold BoundedByKP; omega
example : BoundedByKP 5 (3 + 4) (1 + 1) :=
  BoundedByKP_add (by unfold BoundedByKP; omega) (by unfold BoundedByKP; omega)
example : BoundedByKP 5 (17 % 5) 1 := mod_BoundedByKP 17 5 (by omega)

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise
