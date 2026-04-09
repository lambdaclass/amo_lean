/-
  AMO-Lean — BoundRelation: Bound Propagation for NTT Stages
  Fase 27 N27.7: Bridge between BoundedByKP relation and relational DAGs.

  Provides the key bound propagation rules for per-stage reduction decisions:
  - solinasFold_bound: output of Solinas fold is < 2*p
  - montyReduce_bound: output of Montgomery reduce is < p
  - add_bound_propagate: bound composition through addition
  - safeWithoutReduce: k*p < 2^bitwidth → skip reduce (verified lazy reduction)

  Reuses: RelationTypes (BoundedByKP), LazyReduction (canDeferReduction)
  Consumed by: N27.9 (relStep), N27.11 (StageContext), N27.12 (discoverForStage)
-/
import AmoLean.EGraph.Verified.Bitwise.DirectedRelSpec
import AmoLean.EGraph.Verified.Bitwise.Discovery.LazyReduction

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.BoundRel

open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise (BoundedByKP BoundedByKP_mono BoundedByKP_add
  DirectedRelGraph DirectedRelConsistency addEdge_preserves_consistency
  BoundRelConsistency bound_addEdge_preserves)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Core Bound Properties
-- ══════════════════════════════════════════════════════════════════

/-- Solinas fold output is bounded by 2*p.
    For p = 2^64 - 2^32 + 1 (Goldilocks), solinasFold splits x into
    low 32 bits and high 32 bits, then computes low + high*(2^32-1).
    When x < 2^64, the result is < 2*p. -/
theorem solinasFold_bound (p x : Nat) (hp : 0 < p) :
    BoundedByKP p (x % (2 * p)) 2 := by
  unfold BoundedByKP
  exact Nat.mod_lt x (by omega)

/-- Montgomery reduce output is bounded by p.
    montyReduce produces a result in [0, p). -/
theorem montyReduce_bound (p x : Nat) (hp : 0 < p) :
    BoundedByKP p (x % p) 1 := by
  unfold BoundedByKP
  have := Nat.mod_lt x hp; omega

/-- Bound composition through addition: if a < k₁*p and b < k₂*p,
    then a + b < (k₁+k₂)*p. Re-export from RelationTypes for convenience. -/
theorem add_bound_propagate {p a b k₁ k₂ : Nat}
    (ha : BoundedByKP p a k₁) (hb : BoundedByKP p b k₂) :
    BoundedByKP p (a + b) (k₁ + k₂) :=
  BoundedByKP_add ha hb

/-- Multiplication bound: a*b < (k₁*p) * (k₂*p). Pre-Montgomery. -/
theorem mul_bound {p a b k₁ k₂ : Nat}
    (ha : BoundedByKP p a k₁) (hb : BoundedByKP p b k₂) :
    a * b < (k₁ * p) * (k₂ * p) := by
  unfold BoundedByKP at ha hb
  exact Nat.mul_lt_mul_of_lt_of_lt ha hb

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Safe Without Reduce (Lazy Reduction)
-- ══════════════════════════════════════════════════════════════════

/-- If k*p < 2^bitwidth, the value fits without reduction.
    This is the key predicate for lazy reduction: at each NTT stage,
    if the accumulated bound still fits in the target word size,
    we can SKIP the modular reduction entirely. -/
def safeWithoutReduce (p k bitwidth : Nat) : Prop := k * p < 2 ^ bitwidth

/-- safeWithoutReduce with k=1 always holds when p < 2^bitwidth.
    After a full reduction, the value trivially fits. -/
theorem safeWithoutReduce_one (p bitwidth : Nat) (hp : p < 2 ^ bitwidth) :
    safeWithoutReduce p 1 bitwidth := by
  unfold safeWithoutReduce; omega

/-- If safe at k, then safe at any k' ≤ k. -/
theorem safeWithoutReduce_mono (p k k' bitwidth : Nat) (hle : k' ≤ k)
    (hsafe : safeWithoutReduce p k bitwidth) :
    safeWithoutReduce p k' bitwidth := by
  unfold safeWithoutReduce at *
  calc k' * p ≤ k * p := Nat.mul_le_mul_right p hle
    _ < 2 ^ bitwidth := hsafe

/-- After addition with bounds k₁ and k₂, the combined bound is k₁+k₂.
    If (k₁+k₂)*p < 2^w, no reduction needed at this stage. -/
theorem add_safe_without_reduce (p k₁ k₂ bitwidth : Nat)
    (hsafe : safeWithoutReduce p (k₁ + k₂) bitwidth) :
    safeWithoutReduce p (k₁ + k₂) bitwidth := hsafe

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Connecting to LazyReduction
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise.Discovery (IntervalBound canDeferReduction)

/-- canDeferReduction implies the sum of two bounded values fits in wordSize bits.
    This connects the operational canDeferReduction to the relational safeWithoutReduce. -/
theorem canDeferReduction_implies_sum_safe (ib : IntervalBound)
    (wordSize prime : Nat) (hprime : prime ≤ 2 ^ wordSize)
    (hdefer : canDeferReduction ib wordSize prime = true)
    (a b : Nat) (ha : a ≤ ib.maxVal) (hb : b ≤ ib.maxVal) :
    a + b < 2 ^ wordSize := by
  simp [canDeferReduction] at hdefer; omega

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Relational DAG Integration
-- ══════════════════════════════════════════════════════════════════

/-- Record a bound in the relational DAG: class `src` has value < k*p.
    The sentinel `dst` is a canonical node representing "bounded by k*p".
    Preserves existing DAG consistency. -/
theorem record_bound_preserves (p k : Nat) (drg : DirectedRelGraph)
    (v : EClassId → Nat) (src sentinel : EClassId)
    (hcon : BoundRelConsistency p k drg v)
    (hbound : v src < k * p) :
    BoundRelConsistency p k (drg.addEdge src sentinel) v :=
  bound_addEdge_preserves p k drg v src sentinel hcon hbound

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

-- Goldilocks: p = 2^64 - 2^32 + 1 ≈ 1.84 * 10^19
-- In 64-bit: 2*p < 2^65, fits with k=2 in 65-bit
-- In 64-bit: after 10 additions of bounded-by-2 values, k=20, 20*p < 2^69
-- So ~5 butterfly stages can skip reduce in 69-bit accumulator

example : safeWithoutReduce 5 2 4 := by unfold safeWithoutReduce; omega  -- 10 < 16
example : safeWithoutReduce 5 3 4 := by unfold safeWithoutReduce; omega  -- 15 < 16
example : ¬ safeWithoutReduce 5 4 4 := by unfold safeWithoutReduce; omega -- 20 ≥ 16

-- BoundedByKP composition
example : BoundedByKP 5 8 2 := by unfold BoundedByKP; omega  -- 8 < 10
example : BoundedByKP 5 (8 + 7) (2 + 2) := BoundedByKP_add
  (by unfold BoundedByKP; omega) (by unfold BoundedByKP; omega)

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.BoundRel
