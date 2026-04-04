/-
  AmoLean.EGraph.Verified.Bitwise.MixedUnionFind — Strong WF for VerifiedExtraction.UnionFind

  Adapts OptiSat's UnionFind verification to amo-lean's simpler VerifiedExtraction EGraph.
  KEY simplification: VerifiedExtraction's `union` does NOT use `find` (no path compression),
  so we do NOT need compressPath or find lemmas.

  Deliverables:
  - IsRootAt, ParentsBounded, IsAcyclic predicates
  - StrongWF = ParentsBounded ∧ IsAcyclic
  - StrongWF → UFWF (the weak WellFormed from VerifiedExtraction.Core)
  - rootD lemmas: fuel_extra, fuel_add, bounded, parent_step, compose
  - Set lemmas: rootD_set_not_in_class, rootD_set_other_class, rootD_set_same_class
  - pigeonhole, cycle_contradicts_wf, rootD_depth_bound
  - rootD_union_step, rootD_set_root_to_root
  - union_preserves_strongWF (simple union without find)
  - union_root_cases
  - union_size
-/
import AmoLean.EGraph.Verified.Bitwise.MixedNodeOp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AmoLean.EGraph.Verified.Bitwise.MixedUnionFind

-- Direct abbreviations (avoid circular dep with MixedCoreSpec)
abbrev MUF  := AmoLean.EGraph.VerifiedExtraction.UnionFind
abbrev CId  := AmoLean.EGraph.VerifiedExtraction.EClassId
abbrev UFWF := AmoLean.EGraph.VerifiedExtraction.UnionFind.WellFormed

open AmoLean.EGraph.VerifiedExtraction (EClassId)
open AmoLean.EGraph.VerifiedExtraction.UnionFind (rootD root size root_oob)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Predicates
-- ══════════════════════════════════════════════════════════════════

/-- A node is a root: its parent is itself. -/
def IsRootAt (parent : Array CId) (i : CId) : Prop :=
  ∃ h : i < parent.size, parent[i]'h = i

/-- All parent pointers within bounds. -/
def ParentsBounded (uf : MUF) : Prop :=
  ∀ i, (h : i < uf.parent.size) → uf.parent[i]'h < uf.parent.size

/-- Every node reaches a root within size steps (implies acyclicity). -/
def IsAcyclic (uf : MUF) : Prop :=
  ∀ i, i < uf.parent.size → IsRootAt uf.parent (rootD uf.parent i uf.parent.size)

/-- Strong well-formedness = bounded + acyclic. -/
def StrongWF (uf : MUF) : Prop := ParentsBounded uf ∧ IsAcyclic uf

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Basic rootD lemmas
-- ══════════════════════════════════════════════════════════════════

@[simp] theorem rootD_zero_fuel {parent : Array CId} {id : CId} :
    rootD parent id 0 = id := rfl

theorem rootD_succ_oob {parent : Array CId} {id : CId} {fuel : Nat}
    (h : ¬(id < parent.size)) :
    rootD parent id (fuel + 1) = id := by
  simp only [rootD, dif_neg h]

theorem rootD_of_isRoot {parent : Array CId} {i : CId} {fuel : Nat}
    (hroot : IsRootAt parent i) (hfuel : 0 < fuel) :
    rootD parent i fuel = i := by
  obtain ⟨hlt, hself⟩ := hroot
  match fuel with
  | 0 => omega
  | n + 1 =>
    unfold rootD
    rw [dif_pos hlt]
    have hbeq : (parent[i]'hlt == i) = true := beq_iff_eq.mpr hself
    simp [hbeq]

theorem rootD_bounded {parent : Array CId} {id : CId} {fuel : Nat}
    (hbnd : ∀ j, (hj : j < parent.size) → parent[j]'hj < parent.size)
    (hid : id < parent.size) :
    rootD parent id fuel < parent.size := by
  induction fuel generalizing id with
  | zero => simpa [rootD]
  | succ n ih =>
    simp only [rootD, dif_pos hid]
    split
    · exact hid
    · exact ih (hbnd id hid)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Fuel monotonicity
-- ══════════════════════════════════════════════════════════════════

theorem rootD_fuel_extra {parent : Array CId} {id : CId} {fuel : Nat}
    (hbnd : ∀ j, (hj : j < parent.size) → parent[j]'hj < parent.size)
    (hid : id < parent.size)
    (hroot : IsRootAt parent (rootD parent id fuel)) :
    rootD parent id (fuel + 1) = rootD parent id fuel := by
  induction fuel generalizing id with
  | zero =>
    simp only [rootD_zero_fuel] at hroot
    exact rootD_of_isRoot hroot (by omega)
  | succ n ih =>
    unfold rootD
    rw [dif_pos hid, dif_pos hid]
    cases hc : parent[id]'hid == id
    · simp
      have hroot' : IsRootAt parent (rootD parent (parent[id]'hid) n) := by
        unfold rootD at hroot; rw [dif_pos hid] at hroot; simp [hc] at hroot; exact hroot
      exact ih (hbnd id hid) hroot'
    · rfl

theorem rootD_fuel_add {parent : Array CId} {id : CId} {fuel : Nat}
    (hbnd : ∀ j, (hj : j < parent.size) → parent[j]'hj < parent.size)
    (hid : id < parent.size)
    (hroot : IsRootAt parent (rootD parent id fuel))
    (extra : Nat) :
    rootD parent id (fuel + extra) = rootD parent id fuel := by
  induction extra with
  | zero => rfl
  | succ n ih =>
    have hroot' : IsRootAt parent (rootD parent id (fuel + n)) := ih ▸ hroot
    rw [show fuel + (n + 1) = (fuel + n) + 1 from by omega]
    rw [rootD_fuel_extra hbnd hid hroot']
    exact ih

-- ══════════════════════════════════════════════════════════════════
-- Section 4: StrongWF → UFWF
-- ══════════════════════════════════════════════════════════════════

theorem root_idempotent_of_strong {uf : MUF} (hwf : StrongWF uf)
    {id : CId} (hid : id < uf.parent.size) :
    root uf (root uf id) = root uf id := by
  have hacyclic := hwf.2 id hid
  have hpos : 0 < uf.parent.size := Nat.lt_of_le_of_lt (Nat.zero_le id) hid
  simp only [root]
  exact rootD_of_isRoot hacyclic hpos

/-- StrongWF implies the weak WellFormed from VerifiedExtraction.Core. -/
theorem strongWF_implies_UFWF {uf : MUF} (hwf : StrongWF uf) : UFWF uf where
  root_idempotent := fun i hi => root_idempotent_of_strong hwf hi
  root_bounded := fun i hi => rootD_bounded hwf.1 hi

-- ══════════════════════════════════════════════════════════════════
-- Section 4b: Push lemmas (adapted from OptiSat UnionFind.lean)
-- Used by add_node_consistent to prove StrongWF after UF.add
-- ══════════════════════════════════════════════════════════════════

/-- A root in the original array stays a root after push. -/
theorem IsRootAt_push {parent : Array CId} {v : CId} {i : CId}
    (hroot : IsRootAt parent i) :
    IsRootAt (parent.push v) i := by
  obtain ⟨hlt, hself⟩ := hroot
  have h' : i < (parent.push v).size := by simp [Array.size_push]; exact Nat.lt_succ_of_lt hlt
  refine ⟨h', ?_⟩
  have : (parent.push v)[i]'h' = parent[i]'hlt := by
    rw [Array.getElem_push]; split
    · rfl
    · rename_i hne; exact absurd hlt hne
  rw [this, hself]

/-- rootD on a pushed array equals rootD on the original for in-bounds IDs.
    Key lemma: push doesn't affect the parent chain of existing elements. -/
theorem rootD_push {parent : Array CId} {v : CId} {id : CId} {fuel : Nat}
    (hbnd : ∀ j, (hj : j < parent.size) → parent[j]'hj < parent.size)
    (hid : id < parent.size) :
    rootD (parent.push v) id fuel = rootD parent id fuel := by
  induction fuel generalizing id with
  | zero => rfl
  | succ n ih =>
    have hid' : id < (parent.push v).size := by simp [Array.size_push]; exact Nat.lt_succ_of_lt hid
    have hget : (parent.push v)[id]'hid' = parent[id]'hid := by
      rw [Array.getElem_push]; split
      · rfl
      · rename_i hne; exact absurd hid hne
    unfold rootD
    rw [dif_pos hid', dif_pos hid, hget]
    cases hc : parent[id]'hid == id
    · simp; exact ih (hbnd id hid)
    · simp

/-- UnionFind.add (push self-root) preserves StrongWF.
    Adapted from OptiSat add_wf. -/
theorem push_preserves_strongWF {uf : MUF} (hwf : StrongWF uf) :
    StrongWF ⟨uf.parent.push uf.parent.size⟩ := by
  constructor
  · -- ParentsBounded
    intro i h
    simp only [Array.size_push] at h
    show (uf.parent.push uf.parent.size)[i] < (uf.parent.push uf.parent.size).size
    rw [Array.size_push, Array.getElem_push]
    split
    · rename_i hlt; exact Nat.lt_succ_of_lt (hwf.1 i hlt)
    · exact Nat.lt_succ_of_le (Nat.le_refl _)
  · -- IsAcyclic
    intro i hi
    simp only [Array.size_push] at hi
    show IsRootAt (uf.parent.push uf.parent.size)
      (rootD (uf.parent.push uf.parent.size) i ((uf.parent.push uf.parent.size).size))
    rw [Array.size_push]
    by_cases hlt : i < uf.parent.size
    · -- Old element: rootD on extended array = rootD on original
      rw [rootD_push hwf.1 hlt, rootD_fuel_extra hwf.1 hlt (hwf.2 i hlt)]
      exact IsRootAt_push (hwf.2 i hlt)
    · -- New element: self-root
      have heq : i = uf.parent.size := by omega
      subst heq
      have hisRoot : IsRootAt (uf.parent.push uf.parent.size) uf.parent.size :=
        ⟨by simp [Array.size_push], Array.getElem_push_eq⟩
      rw [rootD_of_isRoot hisRoot (by omega)]
      exact hisRoot

/-- root in pushed UF = root in original UF for ALL IDs.
    Adapted from OptiSat CoreSpec.lean root_push_all_eq. -/
theorem root_push_all_eq {uf : MUF} (hwf : StrongWF uf) (k : CId) :
    AmoLean.EGraph.VerifiedExtraction.UnionFind.root ⟨uf.parent.push uf.parent.size⟩ k =
    AmoLean.EGraph.VerifiedExtraction.UnionFind.root uf k := by
  simp only [AmoLean.EGraph.VerifiedExtraction.UnionFind.root, Array.size_push]
  by_cases hk : k < uf.parent.size
  · rw [rootD_push hwf.1 hk, rootD_fuel_extra hwf.1 hk (hwf.2 k hk)]
  · -- k ≥ uf.parent.size: pushed rootD = k, original rootD = k
    -- pushed: rootD (push size) k (size+1) = k (k ≥ size, so if k=size → self-root, k>size → oob)
    -- original: rootD parent k size = k (k ≥ size → oob for succ fuel, rfl for zero fuel)
    -- Both sides = k when k ≥ uf.parent.size
    -- LHS: rootD of pushed array, RHS: rootD of original array
    have hrhs : rootD uf.parent k uf.parent.size = k := by
      cases hs : uf.parent.size with
      | zero => rfl  -- fuel = 0 → rootD = k
      | succ n => exact rootD_succ_oob (by omega)  -- k ≥ n+1 → oob
    by_cases hke : k = uf.parent.size
    · -- k = size: new self-root in pushed array
      subst hke
      rw [rootD_of_isRoot
        ⟨by simp [Array.size_push], Array.getElem_push_eq⟩
        (by omega), hrhs]
    · -- k > size: oob in both arrays
      have hgt : uf.parent.size < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hk) (Ne.symm hke)
      have hoob : ¬(k < (uf.parent.push uf.parent.size).size) := by
        simp [Array.size_push]; omega
      rw [rootD_succ_oob hoob, hrhs]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Parent step and set lemmas
-- ══════════════════════════════════════════════════════════════════

/-- Following one parent step preserves the root (for in-bounds, non-root nodes). -/
theorem rootD_parent_step {parent : Array CId} {j : CId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hj : j < parent.size) (hnotroot : (parent[j]'hj == j) = false) :
    rootD parent (parent[j]'hj) parent.size = rootD parent j parent.size := by
  have hfe : rootD parent j (parent.size + 1) = rootD parent j parent.size :=
    rootD_fuel_extra hbnd hj (hacyc j hj)
  conv at hfe => lhs; unfold rootD
  rw [dif_pos hj] at hfe
  simp [hnotroot] at hfe
  exact hfe

/-- If rt is a root and rt ≠ k, then rt stays a root after setting parent[k]. -/
theorem IsRootAt_set_ne {parent : Array CId} {k : CId} {v : CId} {rt : CId}
    (hroot : IsRootAt parent rt) (hne : rt ≠ k) (hk : k < parent.size) :
    IsRootAt (parent.set k v) rt := by
  obtain ⟨hlt, hself⟩ := hroot
  have hlt' : rt < (parent.set k v).size := by rw [Array.size_set]; exact hlt
  refine ⟨hlt', ?_⟩
  rw [Array.getElem_set, if_neg (Ne.symm hne)]
  exact hself

/-- If j is NOT in k's equivalence class, set k → rt preserves rootD. -/
theorem rootD_set_not_in_class {parent : Array CId} {k rt j : CId} {fuel : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hk : k < parent.size)
    (hrt_eq : rootD parent k parent.size = rt)
    (hj_ne : rootD parent j parent.size ≠ rt) :
    rootD (parent.set k rt) j fuel = rootD parent j fuel := by
  induction fuel generalizing j with
  | zero => rfl
  | succ n ih =>
    have hsz : (parent.set k rt).size = parent.size := Array.size_set ..
    have hjk : j ≠ k := fun heq => by subst heq; exact hj_ne hrt_eq
    unfold rootD
    by_cases hj : j < parent.size
    · have hj' : j < (parent.set k rt).size := hsz ▸ hj
      rw [dif_pos hj', dif_pos hj]
      have hget : (parent.set k rt)[j]'hj' = parent[j]'hj := by
        simp [Array.getElem_set, Ne.symm hjk]
      rw [hget]
      cases hc : parent[j]'hj == j
      · simp
        apply ih
        intro heq; exact hj_ne (rootD_parent_step hbnd hacyc hj hc ▸ heq)
      · simp
    · rw [dif_neg (by rw [hsz]; exact hj), dif_neg hj]

/-- If j is NOT in k's class, set k → v (arbitrary v) preserves rootD. -/
theorem rootD_set_other_class {parent : Array CId} {k v j : CId} {fuel : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hk : k < parent.size)
    (hj_ne : rootD parent j parent.size ≠ rootD parent k parent.size) :
    rootD (parent.set k v) j fuel = rootD parent j fuel := by
  induction fuel generalizing j with
  | zero => rfl
  | succ n ih =>
    have hsz : (parent.set k v).size = parent.size := Array.size_set ..
    have hjk : j ≠ k := fun heq => by subst heq; exact hj_ne rfl
    unfold rootD
    by_cases hj : j < parent.size
    · have hj' : j < (parent.set k v).size := hsz ▸ hj
      rw [dif_pos hj', dif_pos hj]
      have hget : (parent.set k v)[j]'hj' = parent[j]'hj := by
        simp [Array.getElem_set, Ne.symm hjk]
      rw [hget]
      cases hc : parent[j]'hj == j
      · simp
        apply ih
        intro heq; exact hj_ne (rootD_parent_step hbnd hacyc hj hc ▸ heq)
      · simp
    · rw [dif_neg (by rw [hsz]; exact hj), dif_neg hj]

/-- If j IS in k's equivalence class (root = rt), then rootD on modified array = rt. -/
theorem rootD_set_same_class {parent : Array CId} {k rt j : CId} {fuel : Nat}
    (_hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (_hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hk : k < parent.size)
    (hrt_root : IsRootAt parent rt)
    (_hrt_eq : rootD parent k parent.size = rt)
    (hjfuel : rootD parent j fuel = rt) :
    rootD (parent.set k rt) j fuel = rt := by
  induction fuel generalizing j with
  | zero => simpa using hjfuel
  | succ n ih =>
    have hsz : (parent.set k rt).size = parent.size := Array.size_set ..
    unfold rootD
    by_cases hj : j < parent.size
    · have hj' : j < (parent.set k rt).size := hsz ▸ hj
      rw [dif_pos hj']
      by_cases hjk : j = k
      · -- j = k: (parent.set k rt)[j] = rt
        have hget : (parent.set k rt)[j]'hj' = rt := by
          rw [Array.getElem_set, if_pos hjk.symm]
        rw [hget]
        cases hrtj : rt == j
        · -- rt ≠ j: follow to rt, which is a root in modified array
          simp
          have hrtne : rt ≠ k := by
            intro h; simp [BEq.beq, h, hjk] at hrtj
          have hrt_mod : IsRootAt (parent.set k rt) rt := IsRootAt_set_ne hrt_root hrtne hk
          cases n with
          | zero => rfl
          | succ m => exact rootD_of_isRoot hrt_mod (by omega)
        · exact (beq_iff_eq.mp hrtj).symm
      · -- j ≠ k: parent[j] is unchanged
        have hget : (parent.set k rt)[j]'hj' = parent[j]'hj := by
          simp [Array.getElem_set, Ne.symm hjk]
        rw [hget]
        cases hc : parent[j]'hj == j
        · simp; apply ih
          have : rootD parent j (n + 1) = rt := hjfuel
          unfold rootD at this; rw [dif_pos hj] at this; simp [hc] at this; exact this
        · simp
          have : rootD parent j (n + 1) = rt := hjfuel
          unfold rootD at this; rw [dif_pos hj] at this; simp [hc] at this; exact this
    · rw [dif_neg (by rw [hsz]; exact hj)]
      have : rootD parent j (n + 1) = rt := hjfuel
      rw [rootD_succ_oob hj] at this; exact this

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Composition, pigeonhole, cycle contradiction, depth bound
-- ══════════════════════════════════════════════════════════════════

/-- Composition: rootD parent j (a + b) = rootD parent (rootD parent j a) b. -/
private theorem rootD_compose {parent : Array CId} {j : CId} {a b : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hj : j < parent.size) :
    rootD parent j (a + b) = rootD parent (rootD parent j a) b := by
  induction a generalizing j with
  | zero => simp [rootD]
  | succ n ih =>
    rw [show n + 1 + b = (n + b) + 1 from by omega]
    by_cases hc : (parent[j]'hj == j) = true
    · have hroot : IsRootAt parent j := ⟨hj, beq_iff_eq.mp hc⟩
      rw [rootD_of_isRoot hroot (by omega), rootD_of_isRoot hroot (by omega)]
      cases b with
      | zero => rfl
      | succ b => exact (rootD_of_isRoot hroot (by omega)).symm
    · have hs1 : rootD parent j (n + b + 1) = rootD parent (parent[j]'hj) (n + b) := by
        conv => lhs; unfold rootD; rw [dif_pos hj]; simp [hc]
      have hs2 : rootD parent j (n + 1) = rootD parent (parent[j]'hj) n := by
        conv => lhs; unfold rootD; rw [dif_pos hj]; simp [hc]
      rw [hs1, hs2]
      exact ih (hbnd j hj)

/-- Pigeonhole principle: n+1 values from {0,...,n-1} must have a duplicate. -/
private theorem pigeonhole : ∀ (n : Nat) (f : Nat → Nat),
    (∀ k, k ≤ n → f k < n) →
    ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  intro n; induction n with
  | zero => intro f hf; exact absurd (hf 0 (Nat.le_refl _)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro f hf
    rcases Classical.em (∃ k, k ≤ n ∧ f k = f (n + 1)) with ⟨k, hk, heq⟩ | hno
    · exact ⟨k, n + 1, Nat.lt_succ_of_le hk, Nat.le_refl _, heq⟩
    · have hne : ∀ k, k ≤ n → f k ≠ f (n + 1) := fun k hk h => hno ⟨k, hk, h⟩
      let g := fun k => if f k < f (n + 1) then f k else f k - 1
      have hg : ∀ k, k ≤ n → g k < n := by
        intro k hk; simp only [g]
        have hfk : f k < n + 1 := hf k (Nat.le_succ_of_le hk)
        have hne' : f k ≠ f (n + 1) := hne k hk
        have hfn1 : f (n + 1) < n + 1 := hf (n + 1) (Nat.le_refl _)
        split <;> omega
      obtain ⟨i, j, hij, hj, hgij⟩ := ih g hg
      refine ⟨i, j, hij, Nat.le_succ_of_le hj, ?_⟩
      simp only [g] at hgij
      have hne_i : f i ≠ f (n + 1) := hne i (Nat.le_trans (Nat.le_of_lt hij) hj)
      have hne_j : f j ≠ f (n + 1) := hne j hj
      have hfi : f i < n + 1 := hf i (Nat.le_succ_of_le (Nat.le_trans (Nat.le_of_lt hij) hj))
      have hfj : f j < n + 1 := hf j (Nat.le_succ_of_le hj)
      split at hgij <;> split at hgij <;> omega

/-- A cycle at a non-root contradicts WF acyclicity. -/
private theorem cycle_contradicts_wf {parent : Array CId} {v : CId} {c : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hv : v < parent.size) (hc : c ≥ 1) (hcyc : rootD parent v c = v)
    (hnotroot : ¬IsRootAt parent v) : False := by
  have hmul : ∀ m, rootD parent v (m * c) = v := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [show (m + 1) * c = m * c + c from Nat.succ_mul m c]
      rw [rootD_compose hbnd hv, ih, hcyc]
  have hroot := hacyc v hv
  have key := rootD_fuel_add hbnd hv hroot (parent.size * c - parent.size)
  rw [show parent.size + (parent.size * c - parent.size) = parent.size * c from by
    have : parent.size * c ≥ parent.size := Nat.le_mul_of_pos_right _ hc; omega] at key
  rw [hmul] at key; rw [← key] at hroot; exact hnotroot hroot

/-- Depth bound: rootD parent j (parent.size - 1) = r2 when root(j) = r2.
    By pigeonhole, at most n-1 steps are needed (n = parent.size). -/
private theorem rootD_depth_bound {parent : Array CId} {r2 j : CId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (_hr2 : IsRootAt parent r2)
    (hj : j < parent.size) (hj_class : rootD parent j parent.size = r2) :
    rootD parent j (parent.size - 1) = r2 := by
  by_cases hroot : IsRootAt parent (rootD parent j (parent.size - 1))
  · have hps : 0 < parent.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
    have hfe := rootD_fuel_extra hbnd hj hroot
    rw [show (parent.size - 1) + 1 = parent.size from by omega] at hfe
    exact hfe.symm.trans hj_class
  · exfalso
    obtain ⟨p, q, hpq, hq, hcoll⟩ := pigeonhole parent.size
      (fun k => rootD parent j k) (fun _ _ => rootD_bounded hbnd hj)
    have hv_bnd : rootD parent j p < parent.size := rootD_bounded hbnd hj
    have hcycle : rootD parent (rootD parent j p) (q - p) = rootD parent j p := by
      have hcomp := rootD_compose hbnd hj (a := p) (b := q - p)
      rw [show p + (q - p) = q from by omega] at hcomp
      rw [← hcomp]; exact hcoll.symm
    by_cases hv_root : IsRootAt parent (rootD parent j p)
    · have hfa := rootD_fuel_add hbnd hj hv_root (parent.size - 1 - p)
      rw [show p + (parent.size - 1 - p) = parent.size - 1 from by omega] at hfa
      rw [hfa] at hroot; exact hroot hv_root
    · exact cycle_contradicts_wf hbnd hacyc hv_bnd (by omega) hcycle hv_root

-- ══════════════════════════════════════════════════════════════════
-- Section 7: rootD_union_step, rootD_set_root_to_root
-- ══════════════════════════════════════════════════════════════════

/-- After setting r2 → r1, rootD from j reaches r1 in m steps (where m > depth(j→r2)). -/
private theorem rootD_union_step {parent : Array CId} {r1 r2 j : CId}
    {k : Nat} {m : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hr2 : IsRootAt parent r2) (hne : r1 ≠ r2)
    (hr1_fix : ∀ fuel, rootD (parent.set r2 r1 hr2.1) r1 fuel = r1)
    (hj : j < parent.size)
    (hjk : rootD parent j k = r2) (hm : m ≥ k + 1) :
    rootD (parent.set r2 r1 hr2.1) j m = r1 := by
  induction k generalizing j m with
  | zero =>
    simp only [rootD] at hjk; rw [hjk]
    cases m with
    | zero => omega
    | succ m' =>
      unfold rootD
      have hr2' : r2 < (parent.set r2 r1 hr2.1).size := by rw [Array.size_set]; exact hr2.1
      rw [dif_pos hr2']
      have hget : (parent.set r2 r1 hr2.1)[r2]'hr2' = r1 := by
        rw [Array.getElem_set, if_pos rfl]
      rw [hget]
      have hbeq : (r1 == r2) = false := by
        cases h : r1 == r2; rfl; exact absurd (beq_iff_eq.mp h) hne
      simp [hbeq]
      exact hr1_fix m'
  | succ n ih =>
    unfold rootD at hjk; rw [dif_pos hj] at hjk
    by_cases hc : parent[j]'hj == j
    · -- j is a root = r2
      simp [hc] at hjk; rw [hjk]
      cases m with
      | zero => omega
      | succ m' =>
        unfold rootD
        have hr2' : r2 < (parent.set r2 r1 hr2.1).size := by rw [Array.size_set]; exact hr2.1
        rw [dif_pos hr2']
        have hget : (parent.set r2 r1 hr2.1)[r2]'hr2' = r1 := by
          rw [Array.getElem_set, if_pos rfl]
        rw [hget]
        have hbeq : (r1 == r2) = false := by
          cases h : r1 == r2; rfl; exact absurd (beq_iff_eq.mp h) hne
        simp [hbeq]
        exact hr1_fix m'
    · -- parent[j] ≠ j, recurse
      simp [hc] at hjk
      have hjr2 : j ≠ r2 := by
        intro heq; subst heq; exact absurd (beq_iff_eq.mpr hr2.2) (by simp [hc])
      have hpj := hbnd j hj
      cases m with
      | zero => omega
      | succ m' =>
        have hj' : j < (parent.set r2 r1 hr2.1).size := by rw [Array.size_set]; exact hj
        conv => lhs; unfold rootD
        rw [dif_pos hj']
        have hget : (parent.set r2 r1 hr2.1)[j]'hj' = parent[j]'hj := by
          simp [Array.getElem_set, Ne.symm hjr2]
        rw [hget]
        simp [hc]
        exact ih hpj hjk (by omega)

/-- After setting parent[r2] := r1 (where both are roots), rootD j size = r1
    for any j whose original root was r2. -/
private theorem rootD_set_root_to_root {parent : Array CId} {r1 r2 j : CId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hr1 : IsRootAt parent r1) (hr2 : IsRootAt parent r2) (hne : r1 ≠ r2)
    (hj : j < parent.size) (hj_class : rootD parent j parent.size = r2) :
    rootD (parent.set r2 r1 hr2.1) j parent.size = r1 := by
  have hps : 0 < parent.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hdb := rootD_depth_bound hbnd hacyc hr2 hj hj_class
  have hr1_fix : ∀ fuel, rootD (parent.set r2 r1 hr2.1) r1 fuel = r1 := by
    intro fuel; cases fuel with
    | zero => rfl
    | succ f => exact rootD_of_isRoot (IsRootAt_set_ne hr1 hne hr2.1) (by omega)
  exact rootD_union_step hbnd hr2 hne hr1_fix hj hdb (by omega)

-- ══════════════════════════════════════════════════════════════════
-- Section 8: union inline lemma and union_size
-- ══════════════════════════════════════════════════════════════════

/-- Union beta-reduces to an if-then-else (eliminates let bindings). -/
theorem union_eq (uf : MUF) (id1 id2 : CId) :
    uf.union id1 id2 =
    (if root uf id1 == root uf id2 then uf
     else if root uf id2 < uf.parent.size then ⟨uf.parent.set! (root uf id2) (root uf id1)⟩
     else uf) := by
  show AmoLean.EGraph.VerifiedExtraction.UnionFind.union uf id1 id2 = _
  unfold AmoLean.EGraph.VerifiedExtraction.UnionFind.union
  rfl

/-- Union preserves parent array size (no WF precondition needed). -/
theorem union_size (uf : MUF) (id1 id2 : CId) :
    (uf.union id1 id2).parent.size = uf.parent.size := by
  rw [union_eq]; split
  · rfl
  · split
    · simp [Array.set!, Array.size_setIfInBounds]
    · rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 9: union_preserves_strongWF
-- ══════════════════════════════════════════════════════════════════

/-- Helper: IsAcyclic is preserved after setting r2 → r1 (both roots, distinct). -/
private theorem isAcyclic_after_set {parent : Array CId} {r1 r2 : CId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hr1_root : IsRootAt parent r1) (hr2_root : IsRootAt parent r2)
    (hne : r1 ≠ r2) (i : CId) (hi : i < parent.size) :
    IsRootAt (parent.set r2 r1 hr2_root.1)
      (rootD (parent.set r2 r1 hr2_root.1) i parent.size) := by
  have hr2_self : rootD parent r2 parent.size = r2 :=
    rootD_of_isRoot hr2_root (Nat.lt_of_le_of_lt (Nat.zero_le _) hr2_root.1)
  by_cases hi_class : rootD parent i parent.size = r2
  · rw [rootD_set_root_to_root hbnd hacyc hr1_root hr2_root hne hi hi_class]
    exact IsRootAt_set_ne hr1_root hne hr2_root.1
  · have hj_ne : rootD parent i parent.size ≠ rootD parent r2 parent.size := by
      rwa [hr2_self]
    rw [rootD_set_other_class hbnd hacyc hr2_root.1 hj_ne]
    exact IsRootAt_set_ne (hacyc i hi) hi_class hr2_root.1

/-- The simple union (without find) preserves StrongWF.
    Key: after parent.set! root2 root1 where root1, root2 are distinct roots,
    ParentsBounded holds because root1 is bounded, and
    IsAcyclic holds because nodes in r2's class now reach r1. -/
theorem union_preserves_strongWF (uf : MUF) (id1 id2 : CId)
    (hwf : StrongWF uf) (h1 : id1 < uf.parent.size) (h2 : id2 < uf.parent.size) :
    StrongWF (uf.union id1 id2) := by
  rw [union_eq]
  by_cases heq : (root uf id1 == root uf id2) = true
  · simp [heq]; exact hwf
  · simp [heq]
    have hne : root uf id1 ≠ root uf id2 := fun h => heq (beq_iff_eq.mpr h)
    have hr2_bnd : root uf id2 < uf.parent.size := rootD_bounded hwf.1 h2
    simp [hr2_bnd]
    have hr1_root : IsRootAt uf.parent (root uf id1) := hwf.2 id1 h1
    have hr2_root : IsRootAt uf.parent (root uf id2) := hwf.2 id2 h2
    have hconv : uf.parent.setIfInBounds (root uf id2) (root uf id1) =
        uf.parent.set (root uf id2) (root uf id1) hr2_root.1 := by
      simp [Array.setIfInBounds, hr2_bnd, Array.set]
    -- ParentsBounded + IsAcyclic on ⟨parent.setIfInBounds r2 r1⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · -- ParentsBounded
      have hi' : i < uf.parent.size := by
        simp only [Array.size_setIfInBounds] at hi; exact hi
      simp only [Array.size_setIfInBounds]
      rw [Array.getElem_setIfInBounds hi']
      split
      · exact rootD_bounded hwf.1 h1
      · exact hwf.1 i hi'
    · -- IsAcyclic
      have hi' : i < uf.parent.size := by
        simp only [Array.size_setIfInBounds] at hi; exact hi
      -- Rewrite .parent access and sizes
      rw [show (⟨uf.parent.setIfInBounds (root uf id2) (root uf id1)⟩ : MUF).parent =
          uf.parent.setIfInBounds (root uf id2) (root uf id1) from rfl]
      rw [Array.size_setIfInBounds, hconv]
      exact isAcyclic_after_set hwf.1 hwf.2 hr1_root hr2_root hne i hi'

-- ══════════════════════════════════════════════════════════════════
-- Section 10: union_root_cases
-- ══════════════════════════════════════════════════════════════════

/-- After union, every element's root is either preserved or becomes root(id1).
    In the redirected case, the element was originally in id2's equivalence class. -/
theorem union_root_cases (uf : MUF) (id1 id2 j : CId)
    (hwf : StrongWF uf) (h1 : id1 < uf.parent.size) (h2 : id2 < uf.parent.size) :
    root (uf.union id1 id2) j = root uf j ∨
    (root (uf.union id1 id2) j = root uf id1 ∧ root uf j = root uf id2) := by
  rw [union_eq]
  by_cases heq : (root uf id1 == root uf id2) = true
  · simp [heq]
  · simp [heq]
    have hne : root uf id1 ≠ root uf id2 := fun h => heq (beq_iff_eq.mpr h)
    have hr2_bnd : root uf id2 < uf.parent.size := rootD_bounded hwf.1 h2
    simp [hr2_bnd]
    have hr1_root : IsRootAt uf.parent (root uf id1) := hwf.2 id1 h1
    have hr2_root : IsRootAt uf.parent (root uf id2) := hwf.2 id2 h2
    have hr2_self : rootD uf.parent (root uf id2) uf.parent.size = root uf id2 :=
      rootD_of_isRoot hr2_root (Nat.lt_of_le_of_lt (Nat.zero_le _) hr2_bnd)
    have hconv : uf.parent.setIfInBounds (root uf id2) (root uf id1) =
        uf.parent.set (root uf id2) (root uf id1) hr2_root.1 := by
      simp [Array.setIfInBounds, hr2_bnd, Array.set]
    by_cases hj : j < uf.parent.size
    · by_cases hj_class : root uf j = root uf id2
      · -- j in r2's class → redirected to r1
        right; constructor
        · show rootD (uf.parent.set! (root uf id2) (root uf id1)) j
              (uf.parent.set! (root uf id2) (root uf id1)).size = root uf id1
          simp only [Array.set!, hconv, Array.size_set]
          exact rootD_set_root_to_root hwf.1 hwf.2 hr1_root hr2_root hne hj hj_class
        · exact hj_class
      · -- j NOT in r2's class → root preserved
        left
        show rootD (uf.parent.set! (root uf id2) (root uf id1)) j
            (uf.parent.set! (root uf id2) (root uf id1)).size = root uf j
        simp only [Array.set!, hconv, Array.size_set]
        have hj_ne : rootD uf.parent j uf.parent.size ≠
            rootD uf.parent (root uf id2) uf.parent.size := by rwa [hr2_self]
        exact rootD_set_other_class hwf.1 hwf.2 hr2_root.1 hj_ne
    · -- j out of bounds → root preserved
      left
      show rootD (uf.parent.set! (root uf id2) (root uf id1)) j
          (uf.parent.set! (root uf id2) (root uf id1)).size = root uf j
      simp only [Array.set!, hconv, Array.size_set]
      rw [AmoLean.EGraph.VerifiedExtraction.UnionFind.rootD_oob _ _
          (by rw [Array.size_set]; exact hj),
          root_oob uf j hj]

end AmoLean.EGraph.Verified.Bitwise.MixedUnionFind
