/-
  AMO-Lean — Verified Union-Find Data Structure
  Ported from VR1CS-Lean (Fase 6 Subfase 2: Path A)

  Total implementation (no partial) with formal verification.
  Key properties: root_idempotent, find_eq_root, union_creates, compression_correct.

  References:
  - Charguéraud & Pottier, "Verifying the Correctness and Amortized Complexity
    of a Union-Find Implementation" (JAR 2019) pp.8-9, 21-29
  - Stevens & Ghidini (2025) pp.3-12
-/

namespace AmoLean.EGraph.Verified

/-- Identifier for an equivalence class (index into array). -/
abbrev EClassId := Nat

/-- Union-Find with path compression.
    Stores the parent of each ID. If parent[i] = i, then i is a root. -/
structure UnionFind where
  parent : Array EClassId
  deriving Inhabited

namespace UnionFind

/-! ### Core Operations -/

def empty : UnionFind := ⟨#[]⟩

def init (n : Nat) : UnionFind := ⟨Array.range n⟩

/-- Add a new element (becomes its own root). Returns (newId, updatedUF). -/
def add (uf : UnionFind) : (EClassId × UnionFind) :=
  let newId := uf.parent.size
  (newId, ⟨uf.parent.push newId⟩)

def size (uf : UnionFind) : Nat := uf.parent.size

/-! ### Root Finding (Specification) -/

/-- Find root by following parent pointers without compression.
    Fuel ensures totality; parent.size suffices for well-formed (acyclic) UFs. -/
def rootD (parent : Array EClassId) (id : EClassId) : Nat → EClassId
  | 0 => id
  | fuel + 1 =>
    if h : id < parent.size then
      if parent[id]'h == id then id
      else rootD parent (parent[id]'h) fuel
    else id

/-- Canonical root using parent.size as default fuel. -/
@[inline] def root (uf : UnionFind) (id : EClassId) : EClassId :=
  rootD uf.parent id uf.parent.size

/-! ### Path Compression -/

/-- Compress the path from id to rt, making intermediate nodes point to rt. -/
def compressPath (parent : Array EClassId) (id rt : EClassId) : Nat → Array EClassId
  | 0 => parent
  | fuel + 1 =>
    if h : id < parent.size then
      if parent[id]'h == rt || parent[id]'h == id then parent
      else compressPath (parent.set id rt) (parent[id]'h) rt fuel
    else parent

/-- Find the canonical root with path compression. Total (non-partial).
    Returns (root, updated union-find with compressed paths). -/
def find (uf : UnionFind) (id : EClassId) : (EClassId × UnionFind) :=
  let rt := root uf id
  (rt, ⟨compressPath uf.parent id rt uf.parent.size⟩)

/-- Union two classes. The second root becomes a child of the first root. -/
def union (uf : UnionFind) (id1 id2 : EClassId) : UnionFind :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  if root1 == root2 then uf2
  else if root2 < uf2.parent.size then
    ⟨uf2.parent.set! root2 root1⟩
  else uf2

/-- Check if two IDs are in the same equivalence class. -/
def equiv (uf : UnionFind) (id1 id2 : EClassId) : (Bool × UnionFind) :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  (root1 == root2, uf2)

/-! ### Well-Formedness Predicates -/

/-- A node is a root: its parent is itself. -/
def IsRootAt (parent : Array EClassId) (i : EClassId) : Prop :=
  ∃ h : i < parent.size, parent[i]'h = i

/-- All parent pointers within bounds. -/
def ParentsBounded (uf : UnionFind) : Prop :=
  ∀ i, (h : i < uf.parent.size) → uf.parent[i]'h < uf.parent.size

/-- Every node reaches a root within size steps (implies acyclicity). -/
def IsAcyclic (uf : UnionFind) : Prop :=
  ∀ i, i < uf.parent.size → IsRootAt uf.parent (rootD uf.parent i uf.parent.size)

/-- Well-formed = bounded + acyclic. -/
def WellFormed (uf : UnionFind) : Prop :=
  ParentsBounded uf ∧ IsAcyclic uf

/-! ### rootD Lemmas -/

@[simp] theorem rootD_zero_fuel {parent : Array EClassId} {id : EClassId} :
    rootD parent id 0 = id := rfl

theorem rootD_succ_oob {parent : Array EClassId} {id : EClassId} {fuel : Nat}
    (h : ¬(id < parent.size)) :
    rootD parent id (fuel + 1) = id := by
  simp only [rootD, dif_neg h]

theorem rootD_of_isRoot {parent : Array EClassId} {i : EClassId} {fuel : Nat}
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

/-! ### compressPath Size Preservation -/

theorem compressPath_size (parent : Array EClassId) (id rt : EClassId) (fuel : Nat) :
    (compressPath parent id rt fuel).size = parent.size := by
  induction fuel generalizing parent id with
  | zero => rfl
  | succ n ih =>
    unfold compressPath
    split -- dite on id < parent.size
    · rename_i h
      split -- if parent[id] == rt || parent[id] == id
      · rfl
      · rw [ih]; exact Array.size_set h
    · rfl

/-! ### find Lemmas -/

theorem find_fst_eq_root (uf : UnionFind) (id : EClassId) :
    (find uf id).1 = root uf id := rfl

theorem find_snd_size (uf : UnionFind) (id : EClassId) :
    (find uf id).2.parent.size = uf.parent.size := by
  simp only [find]
  exact compressPath_size uf.parent id (root uf id) uf.parent.size

/-! ### root Idempotent -/

theorem root_idempotent (uf : UnionFind) (id : EClassId)
    (hwf : WellFormed uf) (hid : id < uf.parent.size) :
    root uf (root uf id) = root uf id := by
  have hacyclic := hwf.2 id hid
  have hpos : 0 < uf.parent.size := Nat.lt_of_le_of_lt (Nat.zero_le id) hid
  simp only [root]
  exact rootD_of_isRoot hacyclic hpos

/-- Out-of-bounds IDs are their own root. -/
theorem root_oob (uf : UnionFind) (j : EClassId) (hj : ¬(j < uf.parent.size)) :
    root uf j = j := by
  simp only [root]
  match uf.parent.size with
  | 0 => rfl
  | _ + 1 => exact rootD_succ_oob (by omega)

/-! ### WellFormed Preservation -/

theorem empty_wf : WellFormed empty :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem init_wf (n : Nat) : WellFormed (init n) := by
  refine ⟨fun i h => ?_, fun i hi => ?_⟩
  · -- ParentsBounded: (Array.range n)[i] < (Array.range n).size
    show (Array.range n)[i] < (Array.range n).size
    rw [Array.getElem_range]; exact h
  · -- IsAcyclic: rootD reaches a root
    show IsRootAt (Array.range n) (rootD (Array.range n) i (Array.range n).size)
    have hisRoot : IsRootAt (Array.range n) i :=
      ⟨hi, Array.getElem_range hi⟩
    have hpos : 0 < (Array.range n).size := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
    rw [rootD_of_isRoot hisRoot hpos]
    exact hisRoot

/-! ### Helper lemmas for push (used by add_wf) -/

theorem IsRootAt_push {parent : Array EClassId} {v : EClassId} {i : EClassId}
    (hroot : IsRootAt parent i) :
    IsRootAt (parent.push v) i := by
  obtain ⟨hlt, hself⟩ := hroot
  have h' : i < (parent.push v).size := by
    rw [Array.size_push]; exact Nat.lt_succ_of_lt ‹_›
  refine ⟨h', ?_⟩
  have : (parent.push v)[i]'h' = parent[i]'hlt := by
    rw [Array.getElem_push]; split
    · rfl
    · rename_i hne; exact absurd hlt hne
  rw [this, hself]

theorem rootD_push {parent : Array EClassId} {v : EClassId} {id : EClassId} {fuel : Nat}
    (hbnd : ∀ j, (hj : j < parent.size) → parent[j]'hj < parent.size)
    (hid : id < parent.size) :
    rootD (parent.push v) id fuel = rootD parent id fuel := by
  induction fuel generalizing id with
  | zero => rfl
  | succ n ih =>
    have hid' : id < (parent.push v).size := by
      rw [Array.size_push]; exact Nat.lt_succ_of_lt ‹_›
    have hget : (parent.push v)[id]'hid' = parent[id]'hid := by
      rw [Array.getElem_push]; split
      · rfl
      · rename_i hne; exact absurd hid hne
    unfold rootD
    rw [dif_pos hid', dif_pos hid, hget]
    cases hc : parent[id]'hid == id
    · simp [hc]; exact ih (hbnd id hid)
    · simp [hc]

theorem rootD_fuel_extra {parent : Array EClassId} {id : EClassId} {fuel : Nat}
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
    · simp [hc]
      have hroot' : IsRootAt parent (rootD parent (parent[id]'hid) n) := by
        unfold rootD at hroot; rw [dif_pos hid] at hroot; simp [hc] at hroot; exact hroot
      exact ih (hbnd id hid) hroot'
    · rfl

theorem add_wf (uf : UnionFind) (hwf : WellFormed uf) :
    WellFormed (uf.add).2 := by
  -- Force Lean to unfold add so hypotheses use (parent.push n).size, not add.snd.parent.size
  show WellFormed ⟨uf.parent.push uf.parent.size⟩
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
    · -- Old element: rootD on extended array equals rootD on original
      rw [rootD_push hwf.1 hlt]
      have hacyc := hwf.2 i hlt
      rw [rootD_fuel_extra hwf.1 hlt hacyc]
      exact IsRootAt_push hacyc
    · -- New element: i = uf.parent.size, it's its own root
      have heq : i = uf.parent.size := by omega
      subst heq
      have hisRoot : IsRootAt (uf.parent.push uf.parent.size) uf.parent.size :=
        ⟨by simp [Array.size_push], Array.getElem_push_eq⟩
      rw [rootD_of_isRoot hisRoot (by omega)]
      exact hisRoot

/-! ### rootD extra fuel -/

theorem rootD_fuel_add {parent : Array EClassId} {id : EClassId} {fuel : Nat}
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

/-! ### rootD Bounded -/

theorem rootD_bounded {parent : Array EClassId} {id : EClassId} {fuel : Nat}
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

/-! ### Set-to-root helper lemmas (for find_preserves_roots) -/

theorem IsRootAt_set_ne {parent : Array EClassId} {k : EClassId} {v : EClassId} {rt : EClassId}
    (hroot : IsRootAt parent rt) (hne : rt ≠ k) (hk : k < parent.size) :
    IsRootAt (parent.set k v) rt := by
  obtain ⟨hlt, hself⟩ := hroot
  have hlt' : rt < (parent.set k v).size := by rw [Array.size_set]; exact hlt
  refine ⟨hlt', ?_⟩
  have hkne : ¬(k = rt) := fun h => hne h.symm
  rw [Array.getElem_set, if_neg hkne]
  exact hself

/-- Following one parent step preserves the root (for in-bounds, non-root nodes).
    Key trick: rootD j (size+1) = rootD j size by fuel_extra, then unfold LHS once. -/
theorem rootD_parent_step {parent : Array EClassId} {j : EClassId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hj : j < parent.size) (hnotroot : (parent[j]'hj == j) = false) :
    rootD parent (parent[j]'hj) parent.size = rootD parent j parent.size := by
  have hfe : rootD parent j (parent.size + 1) = rootD parent j parent.size :=
    rootD_fuel_extra hbnd hj (hacyc j hj)
  -- Unfold only the LHS rootD (which has explicit +1 fuel)
  conv at hfe => lhs; unfold rootD
  rw [dif_pos hj] at hfe
  simp [hnotroot] at hfe
  exact hfe

/-- If j is NOT in k's equivalence class, set k → rt preserves rootD at any fuel.
    Key insight: j ≠ k at every step (since root(j) ≠ root(k)), so parent[j] is unchanged. -/
theorem rootD_set_not_in_class {parent : Array EClassId} {k rt j : EClassId} {fuel : Nat}
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
      · simp [hc]
        apply ih
        intro heq; exact hj_ne (rootD_parent_step hbnd hacyc hj hc ▸ heq)
      · simp [hc]
    · rw [dif_neg (by rw [hsz]; exact hj), dif_neg hj]

/-- Generalization: if j is NOT in k's class, set k → v (arbitrary v) preserves rootD.
    The set value v is never read since j ≠ k at every step of the path. -/
theorem rootD_set_other_class {parent : Array EClassId} {k v j : EClassId} {fuel : Nat}
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
      · simp [hc]
        apply ih
        intro heq; exact hj_ne (rootD_parent_step hbnd hacyc hj hc ▸ heq)
      · simp [hc]
    · rw [dif_neg (by rw [hsz]; exact hj), dif_neg hj]

/-- If j IS in k's equivalence class (root = rt), then rootD on modified array = rt.
    Uses fuel induction with sufficiency condition: rootD parent j fuel = rt. -/
theorem rootD_set_same_class {parent : Array EClassId} {k rt j : EClassId} {fuel : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hk : k < parent.size)
    (hrt_root : IsRootAt parent rt)
    (hrt_eq : rootD parent k parent.size = rt)
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
      · -- j = k: (parent.set k rt)[j] = rt (since j = k)
        have hget : (parent.set k rt)[j]'hj' = rt := by
          rw [Array.getElem_set, if_pos hjk.symm]
        rw [hget]
        cases hrtj : rt == j
        · -- rt ≠ j: follow to rt, which is a root in modified array
          simp [hrtj]
          have hrtne : rt ≠ k := by
            intro h; simp [BEq.beq, h, hjk] at hrtj
          have hrt_mod : IsRootAt (parent.set k rt) rt := IsRootAt_set_ne hrt_root hrtne hk
          cases n with
          | zero => rfl
          | succ m => exact rootD_of_isRoot hrt_mod (by omega)
        · -- rt = j: j is its own root, result is j = rt
          exact (beq_iff_eq.mp hrtj).symm
      · -- j ≠ k: parent[j] is unchanged
        have hget : (parent.set k rt)[j]'hj' = parent[j]'hj := by
          simp [Array.getElem_set, Ne.symm hjk]
        rw [hget]
        cases hc : parent[j]'hj == j
        · -- parent[j] ≠ j: recurse
          simp [hc]
          apply ih
          -- Need: rootD parent (parent[j]) n = rt
          -- From hjfuel: rootD parent j (n+1) = rt, unfolding gives rootD parent (parent[j]) n = rt
          have : rootD parent j (n + 1) = rt := hjfuel
          unfold rootD at this
          rw [dif_pos hj] at this; simp [hc] at this
          exact this
        · -- parent[j] = j: j is a root, so j = rt
          simp [hc]
          -- hjfuel: rootD parent j (n+1) = rt. Since parent[j] = j, rootD returns j. So j = rt.
          have : rootD parent j (n + 1) = rt := hjfuel
          unfold rootD at this; rw [dif_pos hj] at this; simp [hc] at this
          exact this
    · -- j ≥ parent.size: OOB, rootD returns j
      rw [dif_neg (by rw [hsz]; exact hj)]
      -- hjfuel: rootD parent j (n+1) = rt. OOB means j = rt.
      have hj2 : ¬(j < parent.size) := hj
      have : rootD parent j (n + 1) = rt := hjfuel
      rw [rootD_succ_oob hj2] at this
      exact this

/-- Setting parent[k] := root(k) preserves rootD for ALL elements.
    This is THE one-step lemma: case split on whether j is in k's class. -/
theorem rootD_set_to_root {parent : Array EClassId} {k rt j : EClassId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hk : k < parent.size)
    (hrt_root : IsRootAt parent rt)
    (hrt_eq : rootD parent k parent.size = rt) :
    rootD (parent.set k rt) j parent.size = rootD parent j parent.size := by
  by_cases hclass : rootD parent j parent.size = rt
  · -- j is in k's class: rootD (modified) j size = rt = rootD parent j size
    rw [rootD_set_same_class hbnd hacyc hk hrt_root hrt_eq hclass, hclass]
  · -- j is NOT in k's class: rootD is unchanged
    exact rootD_set_not_in_class hbnd hacyc hk hrt_eq hclass

/-- compressPath preserves rootD for all elements.
    Induction on compressPath fuel, using rootD_set_to_root at each step.
    Main challenge: re-establishing WF invariants for the modified array at each step. -/
theorem compressPath_preserves_rootD {parent : Array EClassId} {id rt j : EClassId} {cpFuel : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hrt_root : IsRootAt parent rt)
    (hrt_eq : rootD parent id parent.size = rt) :
    rootD (compressPath parent id rt cpFuel) j parent.size = rootD parent j parent.size := by
  induction cpFuel generalizing parent id with
  | zero => rfl
  | succ n ih =>
    unfold compressPath
    split
    · rename_i hid
      split
      · rfl
      · -- Recursive: compressPath (parent.set id rt) (parent[id]) rt n
        rename_i hcond
        -- Extract: parent[id] ≠ rt AND parent[id] ≠ id from hcond
        have hcond_false : (parent[id]'hid == rt || parent[id]'hid == id) = false := by
          cases h : (parent[id]'hid == rt || parent[id]'hid == id)
          · rfl
          · exact absurd h hcond
        have hnotrt : (parent[id]'hid == rt) = false := by
          cases h : (parent[id]'hid == rt)
          · rfl
          · simp [h] at hcond_false
        have hnotid : (parent[id]'hid == id) = false := by
          cases h : (parent[id]'hid == id)
          · rfl
          · simp [h] at hcond_false
        -- One-step lemma: rootD on parent.set id rt = rootD on parent
        have hstep : ∀ x, rootD (parent.set id rt) x parent.size =
            rootD parent x parent.size :=
          fun x => rootD_set_to_root hbnd hacyc hid hrt_root hrt_eq
        -- Size preservation
        have hsz : (parent.set id rt).size = parent.size := Array.size_set ..
        -- Re-establish WF for parent.set id rt:
        -- (1) Bounded
        have hbnd' : ∀ i, (hi' : i < (parent.set id rt).size) →
            (parent.set id rt)[i]'hi' < (parent.set id rt).size := by
          intro i hi'
          simp only [hsz] at hi' ⊢
          by_cases hik : id = i
          · simp [Array.getElem_set, hik]; exact hrt_root.1
          · simp [Array.getElem_set, hik]; exact hbnd i hi'
        -- (2) Acyclic
        have hacyc' : ∀ i, i < (parent.set id rt).size →
            IsRootAt (parent.set id rt)
              (rootD (parent.set id rt) i (parent.set id rt).size) := by
          intro i hi'
          simp only [hsz] at hi' ⊢
          rw [hstep i]
          have hr := hacyc i hi'
          obtain ⟨hlt_r, hself_r⟩ := hr
          by_cases hrid : id = rootD parent i parent.size
          · -- The root r = id. Since rootD parent i _ is always a root (by hacyc),
            -- id is a root, so rootD parent id _ = id, hence rt = id.
            have hid_root : IsRootAt parent id := hrid ▸ hacyc i hi'
            have hid_self : rootD parent id parent.size = id :=
              rootD_of_isRoot hid_root (Nat.lt_of_le_of_lt (Nat.zero_le i) hi')
            have hrt_is_r : rt = rootD parent i parent.size := by
              rw [hid_self] at hrt_eq
              calc rt = id := hrt_eq.symm
                _ = rootD parent i parent.size := hrid
            rw [← hrt_is_r]
            obtain ⟨hlt_rt, hself_rt⟩ := hrt_root
            refine ⟨by simp [hsz]; exact hlt_rt, ?_⟩
            by_cases hrt_eq_id : id = rt
            · simp [Array.getElem_set, hrt_eq_id]
            · simp [Array.getElem_set, hrt_eq_id]; exact hself_rt
          · -- The root r ≠ id; it's unchanged in modified array
            refine ⟨by simp [hsz]; exact hlt_r, ?_⟩
            simp [Array.getElem_set, hrid]; exact hself_r
        -- (3) rt is still a root in modified array
        have hrt_root' : IsRootAt (parent.set id rt) rt := by
          by_cases hrtid : rt = id
          · obtain ⟨hlt_rt, hself_rt⟩ := hrt_root
            refine ⟨by simp [hsz]; exact hlt_rt, ?_⟩
            simp [Array.getElem_set, hrtid.symm]
          · exact IsRootAt_set_ne hrt_root hrtid hid
        -- (4) rootD (modified) (parent[id]) = rt
        have hrt_eq' : rootD (parent.set id rt) (parent[id]'hid)
            (parent.set id rt).size = rt := by
          simp only [hsz]
          rw [hstep, rootD_parent_step hbnd hacyc hid hnotid, hrt_eq]
        -- Apply IH, then chain with one-step
        have ih_result := ih hbnd' hacyc' hrt_root' hrt_eq'
        simp only [hsz] at ih_result
        rw [ih_result, hstep j]
    · rfl

/-- compressPath preserves parent bounds (all entries < size). -/
theorem compressPath_bounded {parent : Array EClassId} {id rt : EClassId} {fuel : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hrt_bnd : rt < parent.size) :
    ∀ i, (hi : i < (compressPath parent id rt fuel).size) →
      (compressPath parent id rt fuel)[i]'hi < (compressPath parent id rt fuel).size := by
  induction fuel generalizing parent id with
  | zero => exact hbnd
  | succ n ih =>
    unfold compressPath
    split
    · rename_i hid
      split
      · exact hbnd
      · -- parent.set id rt, then recurse
        exact ih
          (fun i hi => by
            simp only [Array.size_set] at hi ⊢
            by_cases hik : id = i
            · simp [Array.getElem_set, hik]; exact hrt_bnd
            · simp [Array.getElem_set, hik]; exact hbnd i hi)
          (by simp [Array.size_set]; exact hrt_bnd)
    · exact hbnd

/-- compressPath preserves root entries (if parent[r] = r, then compressed[r] = r). -/
theorem compressPath_preserves_root_entry {parent : Array EClassId} {id rt r : EClassId} {fuel : Nat}
    (hroot : IsRootAt parent r) :
    IsRootAt (compressPath parent id rt fuel) r := by
  induction fuel generalizing parent id with
  | zero => exact hroot
  | succ n ih =>
    unfold compressPath
    split
    · rename_i hid
      split
      · exact hroot
      · -- Need: IsRootAt (parent.set id rt) r, then IH gives the rest
        rename_i hcond
        apply ih
        obtain ⟨hlt, hself⟩ := hroot
        -- id ≠ r: from hcond, parent[id] ≠ id, but parent[r] = r (hroot), so id ≠ r
        have hid_ne : id ≠ r := by
          intro heq; subst heq; simp [BEq.beq, hself] at hcond
        refine ⟨by rw [Array.size_set]; exact hlt, ?_⟩
        simp [Array.getElem_set, hid_ne]; exact hself
    · exact hroot

/-- find preserves WellFormed. -/
theorem find_preserves_wf (uf : UnionFind) (id : EClassId) (hwf : WellFormed uf) :
    WellFormed (uf.find id).2 := by
  show WellFormed ⟨compressPath uf.parent id (root uf id) uf.parent.size⟩
  have hsz : (compressPath uf.parent id (root uf id) uf.parent.size).size =
      uf.parent.size := compressPath_size ..
  constructor
  · -- ParentsBounded
    intro i hi
    by_cases hid : id < uf.parent.size
    · exact compressPath_bounded hwf.1 (rootD_bounded hwf.1 hid) i hi
    · have hcp : compressPath uf.parent id (root uf id) uf.parent.size = uf.parent := by
        cases hn : uf.parent.size with
        | zero => rfl
        | succ n => simp only [root, hn]; unfold compressPath; rw [dif_neg hid]
      simp only [hcp]; exact hwf.1 i (hcp ▸ hi)
  · -- IsAcyclic
    intro i hi
    rw [hsz]
    by_cases hid : id < uf.parent.size
    · have hrootD : rootD (compressPath uf.parent id (root uf id) uf.parent.size) i
          uf.parent.size = rootD uf.parent i uf.parent.size :=
        compressPath_preserves_rootD hwf.1 hwf.2 (hwf.2 id hid) rfl
      rw [hrootD]
      exact compressPath_preserves_root_entry (hwf.2 i (hsz ▸ hi))
    · have hcp : compressPath uf.parent id (root uf id) uf.parent.size = uf.parent := by
        cases hn : uf.parent.size with
        | zero => rfl
        | succ n => simp only [root, hn]; unfold compressPath; rw [dif_neg hid]
      simp only [hcp]; exact hwf.2 i (hcp ▸ hi)

/-! ### Key Theorems -/

/-- find with compression returns the same root as root (without compression). -/
theorem find_eq_root (uf : UnionFind) (id : EClassId) :
    (uf.find id).1 = root uf id := rfl

/-- Path compression preserves the root of every element.
    Core property: compression only shortcuts paths — doesn't change roots.
    Proof strategy: setting parent[id] := rt where rt = root(id) doesn't change
    any element's root, since every path through id already reaches rt. -/
theorem find_preserves_roots (uf : UnionFind) (id j : EClassId)
    (hwf : WellFormed uf) :
    root (uf.find id).2 j = root uf j := by
  simp only [find, root]
  rw [compressPath_size]
  by_cases hid : id < uf.parent.size
  · exact compressPath_preserves_rootD hwf.1 hwf.2 (hwf.2 id hid) rfl
  · -- id ≥ parent.size: compressPath does nothing, rootD returns id
    -- compressPath parent id rt fuel returns parent when id ≥ parent.size
    have : compressPath uf.parent id (rootD uf.parent id uf.parent.size) uf.parent.size =
        uf.parent := by
      cases hf : uf.parent.size
      · rfl
      · rename_i n; unfold compressPath; rw [dif_neg hid]
    rw [this]

/-- If r1 is a root and r1 ≠ r2, root of r1 in setIfInBounds r2 r1 is still r1. -/
private theorem root_setIfInBounds_root_self {parent : Array EClassId} {r1 r2 : EClassId}
    (hr1 : IsRootAt parent r1) (hne : r1 ≠ r2) :
    root ⟨parent.setIfInBounds r2 r1⟩ r1 = r1 := by
  obtain ⟨hlt, hself⟩ := hr1
  simp only [root, Array.size_setIfInBounds]
  exact rootD_of_isRoot
    ⟨by rw [Array.size_setIfInBounds]; exact hlt,
     by rw [Array.getElem_setIfInBounds hlt, if_neg (Ne.symm hne)]; exact hself⟩
    (Nat.lt_of_le_of_lt (Nat.zero_le r1) hlt)

/-- If r1, r2 are distinct roots, root of r2 in setIfInBounds r2 r1 equals r1. -/
private theorem root_setIfInBounds_target {parent : Array EClassId} {r1 r2 : EClassId}
    (hr1 : IsRootAt parent r1) (hr2 : IsRootAt parent r2) (hne : r1 ≠ r2) :
    root ⟨parent.setIfInBounds r2 r1⟩ r2 = r1 := by
  obtain ⟨hlt1, hself1⟩ := hr1
  obtain ⟨hlt2, hself2⟩ := hr2
  -- r1 is a root in the modified array (r1 ≠ r2 so its entry is unchanged)
  have hr1_mod : IsRootAt (parent.setIfInBounds r2 r1) r1 := by
    refine ⟨by rw [Array.size_setIfInBounds]; exact hlt1, ?_⟩
    simp only [Array.getElem_setIfInBounds hlt1, if_neg (Ne.symm hne)]
    exact hself1
  simp only [root, Array.size_setIfInBounds]
  -- Unfold rootD one step: parent[r2] = r1, then r1 is a root
  cases hn : parent.size with
  | zero => exact absurd (hn ▸ hlt2) (Nat.not_lt_zero _)
  | succ n =>
    unfold rootD
    simp only [Array.size_setIfInBounds, dif_pos hlt2]
    simp only [Array.getElem_setIfInBounds hlt2, ite_true]
    cases hrc : (r1 == r2) with
    | false =>
      -- Debug: what is the goal?
      show rootD (parent.setIfInBounds r2 r1) r1 n = r1
      have hfuel : 0 < n := by
        simp only [EClassId] at hlt1 hlt2 hne
        omega
      exact rootD_of_isRoot hr1_mod hfuel
    | true =>
      exact absurd (beq_iff_eq.mp hrc) hne

/-! ### Union helper lemmas (for union_preserves_equiv) -/

/-- rootD from j never visits r1 when root(j) = r2 and r1 ≠ r2 are both roots. -/
private theorem rootD_avoids_root {parent : Array EClassId} {r1 r2 j : EClassId} {fuel : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hr1 : IsRootAt parent r1) (hne : r1 ≠ r2)
    (hj : j < parent.size) (hj_class : rootD parent j parent.size = r2) :
    rootD parent j fuel ≠ r1 := by
  induction fuel generalizing j with
  | zero =>
    simp only [rootD]; intro heq
    rw [heq, rootD_of_isRoot hr1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)] at hj_class
    exact hne hj_class
  | succ n ih =>
    unfold rootD; rw [dif_pos hj]
    cases hc : parent[j]'hj == j
    · simp [hc]
      apply ih (hbnd j hj)
      rw [rootD_parent_step hbnd hacyc hj hc]; exact hj_class
    · simp [hc]; intro heq
      rw [heq, rootD_of_isRoot hr1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)] at hj_class
      exact hne hj_class

/-- Unfold rootD one step when not a root. -/
private theorem rootD_step {parent : Array EClassId} {id : EClassId} {fuel : Nat}
    (h : id < parent.size) (hc : ¬((parent[id]'h == id) = true)) :
    rootD parent id (fuel + 1) = rootD parent (parent[id]'h) fuel := by
  conv => lhs; unfold rootD
  rw [dif_pos h]; simp [hc]

/-- Composition: rootD parent j (a + b) = rootD parent (rootD parent j a) b. -/
private theorem rootD_compose {parent : Array EClassId} {j : EClassId} {a b : Nat}
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
    · rw [rootD_step hj hc, rootD_step hj hc]
      exact ih (hbnd j hj)

/-- Key lemma: setting a root r2 to point to r1, rootD reaches r1 with fuel ≥ k+1.
    By induction on fuel_budget k (the depth witness). -/
private theorem rootD_union_step {parent : Array EClassId} {r1 r2 j : EClassId}
    {k : Nat} {m : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hr2 : IsRootAt parent r2) (hne : r1 ≠ r2)
    (hr1_fix : ∀ fuel, rootD (parent.set r2 r1 hr2.1) r1 fuel = r1)
    (hj : j < parent.size)
    (hjk : rootD parent j k = r2) (hm : m ≥ k + 1) :
    rootD (parent.set r2 r1 hr2.1) j m = r1 := by
  induction k generalizing j m with
  | zero =>
    simp only [rootD] at hjk -- hjk : j = r2
    rw [hjk]
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
        cases h : r1 == r2
        · rfl
        · exact absurd (beq_iff_eq.mp h) hne
      simp [hbeq]
      exact hr1_fix m'
  | succ n ih =>
    unfold rootD at hjk
    rw [dif_pos hj] at hjk
    by_cases hc : parent[j]'hj == j
    · -- j is a root = r2, same as base case
      simp [hc] at hjk -- hjk : j = r2
      rw [hjk]
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
          cases h : r1 == r2
          · rfl
          · exact absurd (beq_iff_eq.mp h) hne
        simp [hbeq]
        exact hr1_fix m'
    · -- parent[j] ≠ j, rootD parent (parent[j]) n = r2
      simp [hc] at hjk
      have hjr2 : j ≠ r2 := by
        intro heq; subst heq; exact absurd (beq_iff_eq.mpr hr2.2) (by simp [hc])
      have hpj := hbnd j hj
      cases m with
      | zero => omega
      | succ m' =>
        have hj' : j < (parent.set r2 r1 hr2.1).size := by rw [Array.size_set]; exact hj
        rw [rootD_step hj' (by
          intro h_eq
          have : (parent.set r2 r1 hr2.1)[j]'hj' = parent[j]'hj := by
            simp [Array.getElem_set, Ne.symm hjr2]
          rw [this] at h_eq; exact hc h_eq)]
        have hget : (parent.set r2 r1 hr2.1)[j]'hj' = parent[j]'hj := by
          simp [Array.getElem_set, Ne.symm hjr2]
        rw [hget]
        exact ih hpj hjk (by omega)

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
private theorem cycle_contradicts_wf {parent : Array EClassId} {v : EClassId} {c : Nat}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hv : v < parent.size) (hc : c ≥ 1) (hcyc : rootD parent v c = v)
    (hnotroot : ¬IsRootAt parent v) : False := by
  have hmul : ∀ m, rootD parent v (m * c) = v := by
    intro m; induction m with
    | zero => simp [rootD]
    | succ m ih =>
      have : (m + 1) * c = m * c + c := Nat.succ_mul m c
      rw [this, rootD_compose hbnd hv, ih, hcyc]
  have hroot := hacyc v hv
  have key := rootD_fuel_add hbnd hv hroot (parent.size * c - parent.size)
  rw [show parent.size + (parent.size * c - parent.size) = parent.size * c from by
    have : parent.size * c ≥ parent.size := Nat.le_mul_of_pos_right _ hc; omega] at key
  rw [hmul] at key; rw [← key] at hroot; exact hnotroot hroot

/-- Depth bound: rootD parent j (parent.size - 1) = r2 when root(j) = r2.
    The path visits ≤ n distinct nodes; by pigeonhole, n-1 steps suffice. -/
private theorem rootD_depth_bound {parent : Array EClassId} {r2 j : EClassId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hr2 : IsRootAt parent r2)
    (hj : j < parent.size) (hj_class : rootD parent j parent.size = r2) :
    rootD parent j (parent.size - 1) = r2 := by
  by_cases hroot : IsRootAt parent (rootD parent j (parent.size - 1))
  · -- rootD j (n-1) is a root → by fuel_extra, equals rootD j n = r2
    have hps : 0 < parent.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
    have hfe := rootD_fuel_extra hbnd hj hroot
    rw [show (parent.size - 1) + 1 = parent.size from by omega] at hfe
    exact hfe.symm.trans hj_class
  · -- rootD j (n-1) is NOT a root → exfalso via pigeonhole
    exfalso
    -- n+1 values rootD parent j k for k = 0,...,n, all < n → collision
    obtain ⟨p, q, hpq, hq, hcoll⟩ := pigeonhole parent.size
      (fun k => rootD parent j k) (fun _ _ => rootD_bounded hbnd hj)
    have hv_bnd : rootD parent j p < parent.size := rootD_bounded hbnd hj
    -- Collision implies cycle: rootD parent (rootD parent j p) (q-p) = rootD parent j p
    have hcycle : rootD parent (rootD parent j p) (q - p) = rootD parent j p := by
      have hcomp := rootD_compose hbnd hj (a := p) (b := q - p)
      rw [show p + (q - p) = q from by omega] at hcomp
      rw [← hcomp]; exact hcoll.symm
    by_cases hv_root : IsRootAt parent (rootD parent j p)
    · -- Collision value is a root → rootD j (n-1) equals it → contradiction
      have hfa := rootD_fuel_add hbnd hj hv_root (parent.size - 1 - p)
      rw [show p + (parent.size - 1 - p) = parent.size - 1 from by omega] at hfa
      rw [hfa] at hroot; exact hroot hv_root
    · -- Collision value is not a root with cycle → contradicts WF
      exact cycle_contradicts_wf hbnd hacyc hv_bnd (by omega) hcycle hv_root

/-- For j in r2's class, root in the union array equals r1.
    Combines depth_bound (rootD parent j (n-1) = r2) with union_step. -/
private theorem rootD_set_root_to_root {parent : Array EClassId} {r1 r2 j : EClassId}
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

/-- Like rootD_set_root_to_root but when r1 is out of bounds (not a root). -/
private theorem rootD_set_root_to_oob {parent : Array EClassId} {r1 r2 j : EClassId}
    (hbnd : ∀ i, (hi : i < parent.size) → parent[i]'hi < parent.size)
    (hacyc : ∀ i, i < parent.size → IsRootAt parent (rootD parent i parent.size))
    (hr2 : IsRootAt parent r2) (hne : r1 ≠ r2) (hr1_oob : ¬(r1 < parent.size))
    (hj : j < parent.size) (hj_class : rootD parent j parent.size = r2) :
    rootD (parent.set r2 r1 hr2.1) j parent.size = r1 := by
  have hps : 0 < parent.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have hdb := rootD_depth_bound hbnd hacyc hr2 hj hj_class
  have hr1_fix : ∀ fuel, rootD (parent.set r2 r1 hr2.1) r1 fuel = r1 := by
    intro fuel; cases fuel with
    | zero => rfl
    | succ f => exact rootD_succ_oob (by rw [Array.size_set]; exact hr1_oob)
  exact rootD_union_step hbnd hr2 hne hr1_fix hj hdb (by omega)

/-- After union, the roots of the two merged classes become equal. -/
theorem union_creates_equiv (uf : UnionFind) (id1 id2 : EClassId)
    (hwf : WellFormed uf) (h1 : id1 < uf.parent.size) (h2 : id2 < uf.parent.size) :
    root (uf.union id1 id2) (root uf id1) =
    root (uf.union id1 id2) (root uf id2) := by
  -- Key properties
  have hwf1 := find_preserves_wf uf id1 hwf
  have hfpr1 : ∀ j, root (uf.find id1).2 j = root uf j :=
    fun j => find_preserves_roots uf id1 j hwf
  have hfpr2 : ∀ j, root ((uf.find id1).2.find id2).2 j = root uf j :=
    fun j => by rw [find_preserves_roots _ id2 j hwf1, hfpr1]
  have hsz2 : ((uf.find id1).2.find id2).2.parent.size = uf.parent.size := by
    rw [find_snd_size, find_snd_size]
  -- Unfold: union uf id1 id2 depends on whether roots are equal
  unfold union
  simp only [find_fst_eq_root]
  -- root1 = root uf id1, root2 = root (uf.find id1).2 id2
  -- root (uf.find id1).2 id2 = root uf id2 by hfpr1
  rw [show root (uf.find id1).2 id2 = root uf id2 from hfpr1 id2]
  -- Case split on root uf id1 == root uf id2
  by_cases heq : (root uf id1 == root uf id2) = true
  · -- Equal roots: union returns uf2
    simp [heq]
    have : root uf id1 = root uf id2 := beq_iff_eq.mp heq
    rw [this]
  · -- Different roots: set root2 → root1
    simp [heq]
    -- root uf id2 < uf2.parent.size (always true for WF)
    have hr2_in : root uf id2 < ((uf.find id1).2.find id2).2.parent.size := by
      rw [hsz2]; exact rootD_bounded hwf.1 h2
    simp [hr2_in]
    -- r1 ≠ r2
    have hne : root uf id1 ≠ root uf id2 := by intro h; exact heq (beq_iff_eq.mpr h)
    -- r1 and r2 are roots in uf2 (compressPath preserves root entries)
    have hr1_isroot : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id1) :=
      compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id1 h1))
    have hr2_isroot : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id2) :=
      compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id2 h2))
    -- Both sides equal root uf id1
    rw [root_setIfInBounds_root_self hr1_isroot hne,
        root_setIfInBounds_target hr1_isroot hr2_isroot hne]

/-- Union preserves existing equivalences. -/
theorem union_preserves_equiv (uf : UnionFind) (id1 id2 a b : EClassId)
    (hwf : WellFormed uf) (heq_ab : root uf a = root uf b) :
    root (uf.union id1 id2) a = root (uf.union id1 id2) b := by
  have hwf1 := find_preserves_wf uf id1 hwf
  have hwf2 := find_preserves_wf _ id2 hwf1
  have hfpr1 : ∀ j, root (uf.find id1).2 j = root uf j :=
    fun j => find_preserves_roots uf id1 j hwf
  have hfpr2 : ∀ j, root ((uf.find id1).2.find id2).2 j = root uf j :=
    fun j => by rw [find_preserves_roots _ id2 j hwf1, hfpr1]
  have hsz2 : ((uf.find id1).2.find id2).2.parent.size = uf.parent.size := by
    rw [find_snd_size, find_snd_size]
  unfold union
  simp only [find_fst_eq_root]
  rw [show root (uf.find id1).2 id2 = root uf id2 from hfpr1 id2]
  by_cases heq : (root uf id1 == root uf id2) = true
  · simp [heq]; rw [hfpr2 a, hfpr2 b, heq_ab]
  · simp [heq]
    have hne : root uf id1 ≠ root uf id2 := by intro h; exact heq (beq_iff_eq.mpr h)
    by_cases hr2_in : root uf id2 < ((uf.find id1).2.find id2).2.parent.size
    · simp [hr2_in]
      -- Abbreviate uf2 = ((uf.find id1).2.find id2).2
      -- r1 = root uf id1, r2 = root uf id2
      -- Derive id2 < uf.parent.size from hr2_in
      have hid2 : id2 < uf.parent.size := by
        rcases Nat.lt_or_ge id2 uf.parent.size with h | h
        · exact h
        · exfalso
          have hge : ¬(id2 < uf.parent.size) := Nat.not_lt_of_le h
          have : rootD uf.parent id2 uf.parent.size = id2 := by
            cases uf.parent.size with
            | zero => rfl
            | succ n => exact rootD_succ_oob hge
          simp only [root] at hr2_in; rw [this, hsz2] at hr2_in
          exact absurd h (Nat.not_le_of_lt hr2_in)
      -- r2 is a root in uf2
      have hr2_isroot : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id2) :=
        compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id2 hid2))
      -- WF components for uf2
      have hbnd2 := hwf2.1
      have hacyc2 := hwf2.2
      -- Step 1: Convert setIfInBounds to set (before root unfolds)
      have hset_eq : ((uf.find id1).2.find id2).2.parent.setIfInBounds (root uf id2) (root uf id1) =
          ((uf.find id1).2.find id2).2.parent.set (root uf id2) (root uf id1) hr2_isroot.1 := by
        simp [Array.setIfInBounds, hr2_in]
      simp only [hset_eq]
      -- Goal: root ⟨uf2.parent.set r2 r1 h⟩ a = root ⟨uf2.parent.set r2 r1 h⟩ b
      -- Both a,b have same root in uf2
      have heq_uf2 : root ((uf.find id1).2.find id2).2 a =
          root ((uf.find id1).2.find id2).2 b := by
        rw [hfpr2 a, hfpr2 b, heq_ab]
      -- Helper: rootD for out-of-bounds → identity
      have rootD_oob : ∀ (p : Array EClassId) (x : EClassId), ¬(x < p.size) →
          rootD p x p.size = x := by
        intro p x hx; cases p.size with
        | zero => rfl
        | succ n => exact rootD_succ_oob hx
      -- Bounds derivation helper
      have bnd_of_class : ∀ x, root ((uf.find id1).2.find id2).2 x = root uf id2 →
          x < ((uf.find id1).2.find id2).2.parent.size := by
        intro x hx
        rcases Nat.lt_or_ge x ((uf.find id1).2.find id2).2.parent.size with h | h
        · exact h
        · exfalso
          have : root ((uf.find id1).2.find id2).2 x = x := rootD_oob _ _ (Nat.not_lt_of_le h)
          rw [this] at hx; rw [hx] at h
          exact absurd hr2_in (Nat.not_lt_of_le h)
      -- Case split: is root(a) in r2's class?
      by_cases ha_class : root ((uf.find id1).2.find id2).2 a = root uf id2
      · -- Both a,b in r2's class → both map to r1
        have hb_class : root ((uf.find id1).2.find id2).2 b = root uf id2 :=
          heq_uf2 ▸ ha_class
        have ha_bnd := bnd_of_class a ha_class
        have hb_bnd := bnd_of_class b hb_class
        -- Both sides equal root uf id1
        suffices ∀ x, x < ((uf.find id1).2.find id2).2.parent.size →
            root ((uf.find id1).2.find id2).2 x = root uf id2 →
            root ⟨((uf.find id1).2.find id2).2.parent.set (root uf id2) (root uf id1) hr2_isroot.1⟩ x = root uf id1 by
          rw [this a ha_bnd ha_class, this b hb_bnd hb_class]
        intro x hx hx_class
        -- Unfold root to rootD, simplify size
        show rootD _ x _ = _
        rw [Array.size_set]
        by_cases hid1 : id1 < uf.parent.size
        · have hr1_isroot : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id1) :=
            compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id1 hid1))
          exact rootD_set_root_to_root hbnd2 hacyc2 hr1_isroot hr2_isroot hne hx hx_class
        · have hr1_oob : ¬(root uf id1 < ((uf.find id1).2.find id2).2.parent.size) := by
            rw [hsz2]; intro h; exact hid1 ((rootD_oob _ _ (Nat.not_lt_of_le (Nat.le_of_not_lt hid1))) ▸ h)
          exact rootD_set_root_to_oob hbnd2 hacyc2 hr2_isroot hne hr1_oob hx hx_class
      · -- Both a,b NOT in r2's class → rootD unchanged
        have hb_class : ¬(root ((uf.find id1).2.find id2).2 b = root uf id2) := by
          rwa [← heq_uf2]
        -- root after set = root before set (for elements not in r2's class)
        suffices ∀ x, ¬(root ((uf.find id1).2.find id2).2 x = root uf id2) →
            root ⟨((uf.find id1).2.find id2).2.parent.set (root uf id2) (root uf id1) hr2_isroot.1⟩ x =
            root ((uf.find id1).2.find id2).2 x by
          rw [this a ha_class, this b hb_class, heq_uf2]
        intro x hx
        show rootD _ x _ = rootD _ x _
        rw [Array.size_set]
        have hr2_self : rootD ((uf.find id1).2.find id2).2.parent (root uf id2)
            ((uf.find id1).2.find id2).2.parent.size = root uf id2 :=
          rootD_of_isRoot hr2_isroot (by rw [hsz2]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hid2)
        have hx_ne : rootD ((uf.find id1).2.find id2).2.parent x
            ((uf.find id1).2.find id2).2.parent.size ≠
            rootD ((uf.find id1).2.find id2).2.parent (root uf id2)
            ((uf.find id1).2.find id2).2.parent.size := by rwa [hr2_self]
        exact rootD_set_other_class hbnd2 hacyc2 hr2_isroot.1 hx_ne
    · simp [hr2_in]; rw [hfpr2 a, hfpr2 b, heq_ab]

/-- Union preserves parent array size (no WF precondition needed). -/
theorem union_size (uf : UnionFind) (id1 id2 : EClassId) :
    (uf.union id1 id2).parent.size = uf.parent.size := by
  unfold union; simp only [find_fst_eq_root]
  split -- root1 == root2
  · rw [find_snd_size, find_snd_size]
  · split -- root2 < uf2.parent.size
    · simp [find_snd_size]
    · rw [find_snd_size, find_snd_size]

/-- Union preserves WellFormed when the first argument is in bounds. -/
theorem union_preserves_wf (uf : UnionFind) (id1 id2 : EClassId)
    (hwf : WellFormed uf) (h1 : id1 < uf.parent.size) :
    WellFormed (uf.union id1 id2) := by
  have hwf1 := find_preserves_wf uf id1 hwf
  have hwf2 := find_preserves_wf _ id2 hwf1
  have hfpr1 : ∀ j, root (uf.find id1).2 j = root uf j :=
    fun j => find_preserves_roots uf id1 j hwf
  have hsz2 : ((uf.find id1).2.find id2).2.parent.size = uf.parent.size := by
    rw [find_snd_size, find_snd_size]
  unfold union
  simp only [find_fst_eq_root]
  rw [show root (uf.find id1).2 id2 = root uf id2 from hfpr1 id2]
  by_cases heq : (root uf id1 == root uf id2) = true
  · simp [heq]; exact hwf2
  · simp [heq]
    have hne : root uf id1 ≠ root uf id2 := by intro h; exact heq (beq_iff_eq.mpr h)
    by_cases hr2_in : root uf id2 < ((uf.find id1).2.find id2).2.parent.size
    · simp [hr2_in]
      -- Derive id2 < uf.parent.size from hr2_in
      have hid2 : id2 < uf.parent.size := by
        rcases Nat.lt_or_ge id2 uf.parent.size with h | h
        · exact h
        · exfalso
          have hge : ¬(id2 < uf.parent.size) := Nat.not_lt_of_le h
          have : rootD uf.parent id2 uf.parent.size = id2 := by
            cases uf.parent.size with
            | zero => rfl
            | succ n => exact rootD_succ_oob hge
          simp only [root] at hr2_in; rw [this, hsz2] at hr2_in
          exact absurd h (Nat.not_le_of_lt hr2_in)
      -- Roots are roots in uf2
      have hr1_isroot : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id1) :=
        compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id1 h1))
      have hr2_isroot : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id2) :=
        compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id2 hid2))
      -- WF components for uf2
      have hbnd2 := hwf2.1
      have hacyc2 := hwf2.2
      -- Convert setIfInBounds to set
      have hset_eq : ((uf.find id1).2.find id2).2.parent.setIfInBounds (root uf id2) (root uf id1) =
          ((uf.find id1).2.find id2).2.parent.set (root uf id2) (root uf id1) hr2_isroot.1 := by
        simp [Array.setIfInBounds, hr2_in]
      simp only [hset_eq]
      constructor
      · -- ParentsBounded
        intro i hi
        simp only [Array.size_set] at hi ⊢
        simp only [Array.getElem_set]
        split
        · -- i = root2 → parent'[i] = root1 < parent.size
          rw [hsz2]; exact rootD_bounded hwf.1 h1
        · -- i ≠ root2 → parent'[i] unchanged
          exact hbnd2 i hi
      · -- IsAcyclic
        intro i hi
        simp only [Array.size_set] at hi ⊢
        have hr2_self : rootD ((uf.find id1).2.find id2).2.parent (root uf id2)
            ((uf.find id1).2.find id2).2.parent.size = root uf id2 :=
          rootD_of_isRoot hr2_isroot (Nat.lt_of_le_of_lt (Nat.zero_le _) hr2_in)
        by_cases hi_class : rootD ((uf.find id1).2.find id2).2.parent i
            ((uf.find id1).2.find id2).2.parent.size = root uf id2
        · -- i in root2's class → rootD goes to root1
          rw [rootD_set_root_to_root hbnd2 hacyc2 hr1_isroot hr2_isroot hne hi hi_class]
          exact IsRootAt_set_ne hr1_isroot hne hr2_isroot.1
        · -- i not in root2's class → rootD unchanged
          have hj_ne : rootD ((uf.find id1).2.find id2).2.parent i
              ((uf.find id1).2.find id2).2.parent.size ≠
              rootD ((uf.find id1).2.find id2).2.parent (root uf id2)
              ((uf.find id1).2.find id2).2.parent.size := by rwa [hr2_self]
          rw [rootD_set_other_class hbnd2 hacyc2 hr2_isroot.1 hj_ne]
          exact IsRootAt_set_ne (hacyc2 i hi) hi_class hr2_isroot.1
    · simp [hr2_in]; exact hwf2

/-- After union, every element's root is either preserved or becomes root(id1).
    In the redirected case, the element was originally in id2's equivalence class. -/
theorem union_root_cases (uf : UnionFind) (id1 id2 j : EClassId)
    (hwf : WellFormed uf) (h1 : id1 < uf.parent.size) (h2 : id2 < uf.parent.size) :
    root (uf.union id1 id2) j = root uf j ∨
    (root (uf.union id1 id2) j = root uf id1 ∧ root uf j = root uf id2) := by
  have hwf1 := find_preserves_wf uf id1 hwf
  have hfpr1 : ∀ k, root (uf.find id1).2 k = root uf k :=
    fun k => find_preserves_roots uf id1 k hwf
  have hwf2 := find_preserves_wf _ id2 hwf1
  have hfpr2 : ∀ k, root ((uf.find id1).2.find id2).2 k = root uf k :=
    fun k => by rw [find_preserves_roots _ id2 k hwf1, hfpr1]
  have hsz2 : ((uf.find id1).2.find id2).2.parent.size = uf.parent.size := by
    rw [find_snd_size, find_snd_size]
  unfold union; simp only [find_fst_eq_root]
  rw [show root (uf.find id1).2 id2 = root uf id2 from hfpr1 id2]
  by_cases heq : (root uf id1 == root uf id2) = true
  · simp [heq]; exact Or.inl (hfpr2 j)
  · simp [heq]
    have hne : root uf id1 ≠ root uf id2 := fun h => heq (beq_iff_eq.mpr h)
    have hr2_in : root uf id2 < ((uf.find id1).2.find id2).2.parent.size :=
      hsz2 ▸ rootD_bounded hwf.1 h2
    simp [hr2_in]
    have hr1_rt : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id1) :=
      compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id1 h1))
    have hr2_rt : IsRootAt ((uf.find id1).2.find id2).2.parent (root uf id2) :=
      compressPath_preserves_root_entry (compressPath_preserves_root_entry (hwf.2 id2 h2))
    have hset_eq : ((uf.find id1).2.find id2).2.parent.setIfInBounds (root uf id2) (root uf id1) =
        ((uf.find id1).2.find id2).2.parent.set (root uf id2) (root uf id1) hr2_rt.1 := by
      simp [Array.setIfInBounds, hr2_in]
    simp only [hset_eq]
    by_cases hj : j < uf.parent.size
    · have hj2 : j < ((uf.find id1).2.find id2).2.parent.size := hsz2 ▸ hj
      by_cases hj_class : root uf j = root uf id2
      · -- j in id2's class → redirected to root(id1)
        right; constructor
        · simp only [root, Array.size_set]
          have : rootD ((uf.find id1).2.find id2).2.parent j
              ((uf.find id1).2.find id2).2.parent.size = root uf id2 := by
            change root ((uf.find id1).2.find id2).2 j = root uf id2
            rw [hfpr2]; exact hj_class
          exact rootD_set_root_to_root hwf2.1 hwf2.2 hr1_rt hr2_rt hne hj2 this
        · exact hj_class
      · -- j NOT in id2's class → root preserved
        left
        suffices root ⟨((uf.find id1).2.find id2).2.parent.set (root uf id2) (root uf id1)
            hr2_rt.1⟩ j = root ((uf.find id1).2.find id2).2 j by rw [this, hfpr2]
        simp only [root, Array.size_set]
        have hr2_self : rootD ((uf.find id1).2.find id2).2.parent (root uf id2)
            ((uf.find id1).2.find id2).2.parent.size = root uf id2 :=
          rootD_of_isRoot hr2_rt (Nat.lt_of_le_of_lt (Nat.zero_le _) hr2_in)
        have hj_ne : rootD ((uf.find id1).2.find id2).2.parent j
            ((uf.find id1).2.find id2).2.parent.size ≠
            rootD ((uf.find id1).2.find id2).2.parent (root uf id2)
            ((uf.find id1).2.find id2).2.parent.size := by
          rw [hr2_self]
          change root ((uf.find id1).2.find id2).2 j ≠ root uf id2
          rw [hfpr2]; exact hj_class
        exact rootD_set_other_class hwf2.1 hwf2.2 hr2_rt.1 hj_ne
    · -- j out of bounds → root preserved
      left
      have h1 : root ⟨((uf.find id1).2.find id2).2.parent.set (root uf id2) (root uf id1)
          hr2_rt.1⟩ j = j := root_oob _ j (by intro h; apply hj; rwa [Array.size_set, hsz2] at h)
      have h2 : root uf j = j := root_oob uf j hj
      rw [h1, h2]

end UnionFind

end AmoLean.EGraph.Verified
