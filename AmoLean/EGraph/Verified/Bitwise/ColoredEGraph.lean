/-
  AMO-Lean — Colored E-Graph Foundation: SmallUF + ColoredLayer + Coarsening
  Fase 27 N27.2: Ported from OptiSat v2 ColorTypes.lean + ColoredMerge.lean.

  Colored e-graphs maintain multiple congruence relations in a single structure.
  Each "color" represents an assumption under which additional equalities hold.
  Colors form a hierarchy: every color is a coarsening of its parent
  (≅ ⊆ ≅_c for every color c).

  Key types:
  - `SmallUF`: delta union-find storing additional merges on top of parent layer
  - `ColoredLayer`: hierarchy + per-color SmallUFs + worklists
  - `compositeFind`: compositional find through ancestor chain

  Key theorem: `compositeFind_coarsening` — descendant colors automatically
  see parent merges (L-704, via foldl_append).

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)
             Singher, "Easter Egg" (FMCAD 2024)

  Consumes: EClassId from UnionFind
  Consumed by: ColoredSpec (N27.3), MultiRelMixed (N27.5), HardwareColors (N27.8)
-/
import AmoLean.EGraph.Verified.UnionFind
import Std.Data.HashMap

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Colored

open AmoLean.EGraph.Verified (EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Color Identifiers
-- ══════════════════════════════════════════════════════════════════

abbrev ColorId := Nat

def colorRoot : ColorId := 0

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Color Hierarchy
-- ══════════════════════════════════════════════════════════════════

/-- Tree of colors. Each non-root color has exactly one parent.
    The hierarchy defines coarsening: ≅_{parent(c)} ⊆ ≅_c for all c.
    Invariant: the parent graph is acyclic and every path leads to root. -/
structure ColorHierarchy where
  parentOf : Std.HashMap ColorId ColorId := {}
  numColors : Nat := 1
  deriving Repr, Inhabited

namespace ColorHierarchy

def empty : ColorHierarchy := {}

def addColor (h : ColorHierarchy) (par : ColorId) : ColorId × ColorHierarchy :=
  let newId := h.numColors
  (newId, { parentOf := h.parentOf.insert newId par
            numColors := h.numColors + 1 })

def getParent (h : ColorHierarchy) (c : ColorId) : ColorId :=
  if c == colorRoot then colorRoot
  else h.parentOf.getD c colorRoot

def isAncestor (h : ColorHierarchy) (c ancestor : ColorId) : Bool :=
  go c h.numColors
where
  go (current : ColorId) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      if current == ancestor then true
      else if current == colorRoot then false
      else go (h.getParent current) fuel

def ancestors (h : ColorHierarchy) (c : ColorId) : List ColorId :=
  go c h.numColors []
where
  go (current : ColorId) : Nat → List ColorId → List ColorId
    | 0, acc => acc.reverse
    | fuel + 1, acc =>
      let acc' := current :: acc
      if current == colorRoot then acc'.reverse
      else go (h.getParent current) fuel acc'

def getChildren (h : ColorHierarchy) (c : ColorId) : List ColorId :=
  h.parentOf.toList.filterMap fun (child, par) =>
    if par == c then some child else none

def descendants (h : ColorHierarchy) (c : ColorId) : List ColorId :=
  go [c] [] h.numColors
where
  go : List ColorId → List ColorId → Nat → List ColorId
    | [], acc, _ => acc.reverse
    | _, acc, 0 => acc.reverse
    | cur :: rest, acc, fuel + 1 =>
      let kids := h.getChildren cur
      go (rest ++ kids) (cur :: acc) fuel

end ColorHierarchy

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Small (Delta) Union-Find
-- ══════════════════════════════════════════════════════════════════

/-- Delta union-find: stores only ADDITIONAL merges on top of a parent layer.
    The full equivalence for a color c is:
      `find_c(e) = deltaFind(c, parentLayerFind(e))`
    where parentLayerFind resolves through ancestor colors down to the base UF. -/
structure SmallUF where
  delta : Std.HashMap EClassId EClassId := {}
  deriving Repr, Inhabited

namespace SmallUF

def empty : SmallUF := {}

def size (suf : SmallUF) : Nat := suf.delta.size

def deltaFind (suf : SmallUF) (id : EClassId) : Nat → EClassId
  | 0 => id
  | fuel + 1 =>
    match suf.delta.get? id with
    | none => id
    | some par =>
      if par == id then id
      else deltaFind suf par fuel

def find (suf : SmallUF) (parentFind : EClassId → EClassId) (id : EClassId)
    (fuel : Nat := 100) : EClassId :=
  deltaFind suf (parentFind id) fuel

def merge (suf : SmallUF) (a b : EClassId) (fuel : Nat := 100) : SmallUF :=
  let repA := deltaFind suf a fuel
  let repB := deltaFind suf b fuel
  if repA == repB then suf
  else { delta := suf.delta.insert repA repB }

def equiv (suf : SmallUF) (parentFind : EClassId → EClassId) (a b : EClassId)
    (fuel : Nat := 100) : Bool :=
  find suf parentFind a fuel == find suf parentFind b fuel

end SmallUF

-- ══════════════════════════════════════════════════════════════════
-- Section 4: SmallUF Well-Formedness and Theorems
-- ══════════════════════════════════════════════════════════════════

def SmallUF.WellFormed (suf : SmallUF) : Prop :=
  ∀ id, SmallUF.deltaFind suf id suf.size = SmallUF.deltaFind suf id (suf.size + 1)

theorem SmallUF.empty_wellFormed : SmallUF.empty.WellFormed := by
  intro id
  simp [SmallUF.empty, SmallUF.deltaFind, SmallUF.size]

theorem SmallUF.deltaFind_zero (suf : SmallUF) (id : EClassId) :
    SmallUF.deltaFind suf id 0 = id := by
  rfl

theorem SmallUF.deltaFind_root (suf : SmallUF) (id : EClassId) (fuel : Nat)
    (h : suf.delta.get? id = none) :
    SmallUF.deltaFind suf id (fuel + 1) = id := by
  simp only [SmallUF.deltaFind, h]

theorem ColorHierarchy.getParent_root (h : ColorHierarchy) :
    h.getParent colorRoot = colorRoot := by
  simp [ColorHierarchy.getParent, colorRoot]

theorem SmallUF.empty_deltaFind (id : EClassId) :
    ∀ fuel, SmallUF.empty.deltaFind id fuel = id
  | 0 => rfl
  | _ + 1 => by simp [SmallUF.deltaFind, SmallUF.empty]

theorem SmallUF.deltaFind_insert_preserves_val {Val : Type}
    (suf : SmallUF) (repA repB : EClassId) (v : EClassId → Val)
    (hroot : suf.delta.get? repA = none)
    (hrootB : suf.delta.get? repB = none)
    (hab : v repA = v repB)
    (hold : ∀ id fuel, v (suf.deltaFind id fuel) = v id) :
    ∀ id fuel, v ({ delta := suf.delta.insert repA repB : SmallUF }.deltaFind id fuel) = v id
  | _, 0 => rfl
  | id, fuel + 1 => by
    unfold SmallUF.deltaFind
    show v (match ({ delta := suf.delta.insert repA repB : SmallUF }).delta.get? id with
      | none => id | some par => if par == id then id
        else SmallUF.deltaFind { delta := suf.delta.insert repA repB } par fuel) = v id
    by_cases hid : repA = id
    · subst hid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true,
                  ↓reduceIte]
      by_cases hbeq : repB == repA
      · simp [hbeq]
      · simp [hbeq]
        have hrootB' : ({ delta := suf.delta.insert repA repB : SmallUF }).delta.get? repB = none := by
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_eq_false_iff_ne.mpr (fun h => hbeq (beq_iff_eq.mpr h.symm))]
          simp only [Bool.false_eq_true, ↓reduceIte, ← Std.HashMap.get?_eq_getElem?, hrootB]
        have := deltaFind_insert_preserves_val suf repA repB v hroot hrootB hab hold repB fuel
        exact this.trans hab.symm
    · have hinsert_ne : (suf.delta.insert repA repB).get? id = suf.delta.get? id := by
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        simp [beq_eq_false_iff_ne.mpr hid]
      show v (match (suf.delta.insert repA repB).get? id with
        | none => id | some par => if par == id then id
          else SmallUF.deltaFind { delta := suf.delta.insert repA repB } par fuel) = v id
      rw [hinsert_ne]
      match hget : suf.delta.get? id with
      | none => rfl
      | some par =>
        simp only []
        split
        · rfl
        · rename_i hpar_ne_id
          have hrec := deltaFind_insert_preserves_val suf repA repB v hroot hrootB hab hold par fuel
          have h2 := hold id (fuel + 1)
          have h1 := hold par fuel
          have hstep : v (suf.deltaFind id (fuel + 1)) = v (suf.deltaFind par fuel) := by
            congr 1; show (match suf.delta.get? id with
              | none => id
              | some par => if par == id then id else suf.deltaFind par fuel) = _
            rw [hget]; simp [hpar_ne_id]
          exact hrec.trans (h1.symm.trans (hstep.symm ▸ h2))

-- ══════════════════════════════════════════════════════════════════
-- Section 5: ColoredLayer
-- ══════════════════════════════════════════════════════════════════

/-- The colored layer of a colored e-graph.
    Manages per-color SmallUFs and worklists.
    Layer 1 (base EGraph) is separate and untouched. -/
structure ColoredLayer where
  colorUFs : Std.HashMap ColorId SmallUF := {}
  hierarchy : ColorHierarchy := ColorHierarchy.empty
  worklists : Std.HashMap ColorId (List EClassId) := {}
  deriving Repr, Inhabited

namespace ColoredLayer

def empty : ColoredLayer :=
  { colorUFs := {}, hierarchy := ColorHierarchy.empty, worklists := {} }

def getUF (cl : ColoredLayer) (c : ColorId) : SmallUF :=
  cl.colorUFs.getD c SmallUF.empty

def setUF (cl : ColoredLayer) (c : ColorId) (suf : SmallUF) : ColoredLayer :=
  { cl with colorUFs := cl.colorUFs.insert c suf }

def getWorklist (cl : ColoredLayer) (c : ColorId) : List EClassId :=
  cl.worklists.getD c []

def addToWorklist (cl : ColoredLayer) (c : ColorId) (ids : List EClassId) :
    ColoredLayer :=
  let current := cl.getWorklist c
  { cl with worklists := cl.worklists.insert c (current ++ ids) }

def clearWorklist (cl : ColoredLayer) (c : ColorId) : ColoredLayer :=
  { cl with worklists := cl.worklists.insert c [] }

def addColor (cl : ColoredLayer) (parent : ColorId) : ColorId × ColoredLayer :=
  let (newId, newHier) := cl.hierarchy.addColor parent
  (newId, { cl with hierarchy := newHier })

end ColoredLayer

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Composite Find
-- ══════════════════════════════════════════════════════════════════

/-- Compute the representative of `id` under color `c` by composing
    delta finds through the ancestor chain.

    Given ancestors = [root, c1, c2, ..., c]:
    result = deltaFind_c(deltaFind_c2(...(deltaFind_c1(baseFind(id)))...))

    The root color's "delta" is empty, so its find is the identity.
    The `baseFind` resolves through the base (black) union-find. -/
def compositeFind (colorUFs : Std.HashMap ColorId SmallUF) (ancestors : List ColorId)
    (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) : EClassId :=
  ancestors.foldl (fun acc c =>
    (colorUFs.getD c SmallUF.empty).deltaFind acc fuel
  ) (baseFind id)

def ColoredLayer.findUnderColor (cl : ColoredLayer)
    (baseFind : EClassId → EClassId) (c : ColorId) (id : EClassId)
    (fuel : Nat := 100) : EClassId :=
  let anc := (cl.hierarchy.ancestors c).reverse
  compositeFind cl.colorUFs anc baseFind fuel id

def ColoredLayer.equivUnderColor (cl : ColoredLayer)
    (baseFind : EClassId → EClassId) (c : ColorId) (a b : EClassId)
    (fuel : Nat := 100) : Bool :=
  cl.findUnderColor baseFind c a fuel == cl.findUnderColor baseFind c b fuel

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Merge Under Color
-- ══════════════════════════════════════════════════════════════════

/-- Merge two e-classes under a specific color.
    No propagation to descendants needed: descendant colors compose
    their find through this color's SmallUF, so they automatically see the merge. -/
def ColoredLayer.mergeUnderColor (cl : ColoredLayer)
    (baseFind : EClassId → EClassId) (c : ColorId) (a b : EClassId)
    (fuel : Nat := 100) : ColoredLayer × Bool :=
  let repA := cl.findUnderColor baseFind c a fuel
  let repB := cl.findUnderColor baseFind c b fuel
  if repA == repB then
    (cl, false)
  else
    let suf := cl.getUF c
    let suf' := suf.merge repA repB fuel
    let cl' := cl.setUF c suf'
    let cl'' := cl'.addToWorklist c [repA, repB]
    (cl'', true)

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Coarsening Invariant + Key Theorems
-- ══════════════════════════════════════════════════════════════════

/-- The coarsening invariant: if two e-classes are equivalent under
    a parent color, they are also equivalent under any descendant color.
    This is the central safety property of colored e-graphs. -/
def CoarseningInvariant (colorUFs : Std.HashMap ColorId SmallUF)
    (hierarchy : ColorHierarchy) (baseFind : EClassId → EClassId) (fuel : Nat) : Prop :=
  ∀ (child parent : ColorId) (a b : EClassId),
    hierarchy.getParent child = parent →
    compositeFind colorUFs (hierarchy.ancestors parent).reverse baseFind fuel a =
    compositeFind colorUFs (hierarchy.ancestors parent).reverse baseFind fuel b →
    compositeFind colorUFs (hierarchy.ancestors child).reverse baseFind fuel a =
    compositeFind colorUFs (hierarchy.ancestors child).reverse baseFind fuel b

theorem deltaFind_preserves_eq (suf : SmallUF) (x y : EClassId) (fuel : Nat)
    (h : x = y) : suf.deltaFind x fuel = suf.deltaFind y fuel := by
  rw [h]

/-- Key "coarsening for free" result: extending the ancestor chain preserves equality. -/
theorem compositeFind_extend_preserves_eq (colorUFs : Std.HashMap ColorId SmallUF)
    (parentChain : List ColorId) (child : ColorId) (baseFind : EClassId → EClassId)
    (fuel : Nat) (a b : EClassId)
    (h : compositeFind colorUFs parentChain baseFind fuel a =
         compositeFind colorUFs parentChain baseFind fuel b) :
    compositeFind colorUFs (parentChain ++ [child]) baseFind fuel a =
    compositeFind colorUFs (parentChain ++ [child]) baseFind fuel b := by
  simp [compositeFind, List.foldl_append] at *
  rw [h]

/-- Coarsening is inherent in the compositional architecture:
    any extension of the ancestor chain preserves equivalences. -/
theorem compositeFind_coarsening (colorUFs : Std.HashMap ColorId SmallUF)
    (parentChain suffix : List ColorId) (baseFind : EClassId → EClassId)
    (fuel : Nat) (a b : EClassId)
    (h : compositeFind colorUFs parentChain baseFind fuel a =
         compositeFind colorUFs parentChain baseFind fuel b) :
    compositeFind colorUFs (parentChain ++ suffix) baseFind fuel a =
    compositeFind colorUFs (parentChain ++ suffix) baseFind fuel b := by
  simp [compositeFind, List.foldl_append] at *
  rw [h]

theorem mergeUnderColor_idempotent
    (cl : ColoredLayer) (baseFind : EClassId → EClassId)
    (c : ColorId) (a b : EClassId) (fuel : Nat)
    (h_equiv : cl.equivUnderColor baseFind c a b fuel = true) :
    (cl.mergeUnderColor baseFind c a b fuel).2 = false := by
  simp only [ColoredLayer.mergeUnderColor, ColoredLayer.equivUnderColor] at *
  simp [h_equiv]

theorem compositeFind_nil (colorUFs : Std.HashMap ColorId SmallUF)
    (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) :
    compositeFind colorUFs [] baseFind fuel id = baseFind id := by
  simp [compositeFind]

theorem compositeFind_singleton (colorUFs : Std.HashMap ColorId SmallUF)
    (c : ColorId) (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) :
    compositeFind colorUFs [c] baseFind fuel id =
    (colorUFs.getD c SmallUF.empty).deltaFind (baseFind id) fuel := by
  simp [compositeFind]

theorem compositeFind_empty_colorUFs (ancestors : List ColorId)
    (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) :
    compositeFind (∅ : Std.HashMap ColorId SmallUF) ancestors baseFind fuel id =
    baseFind id := by
  simp only [compositeFind]
  induction ancestors with
  | nil => simp [List.foldl]
  | cons c rest ih =>
    simp only [List.foldl]
    have hget : (∅ : Std.HashMap ColorId SmallUF).getD c SmallUF.empty = SmallUF.empty :=
      Std.HashMap.getD_empty
    rw [hget, SmallUF.empty_deltaFind]
    exact ih

theorem equivUnderColor_empty_layer
    (baseFind : EClassId → EClassId)
    (c : ColorId) (a b : EClassId) (fuel : Nat) :
    ColoredLayer.equivUnderColor ColoredLayer.empty baseFind c a b fuel =
    (baseFind a == baseFind b) := by
  simp only [ColoredLayer.equivUnderColor, ColoredLayer.findUnderColor, ColoredLayer.empty]
  congr 1 <;> exact compositeFind_empty_colorUFs _ baseFind fuel _

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

example : ColorHierarchy.empty.numColors = 1 := by rfl

example : SmallUF.empty.size = 0 := by native_decide

example : SmallUF.deltaFind SmallUF.empty 42 10 = 42 := by native_decide

#eval do
  let cl : ColoredLayer := ColoredLayer.empty
  let (c1, cl1) := cl.addColor colorRoot
  let baseFind := fun id => id
  let (cl2, changed) := cl1.mergeUnderColor baseFind c1 10 20 100
  let eq := cl2.equivUnderColor baseFind c1 10 20 100
  return s!"color={c1}, merged={changed}, equiv={eq}"

#eval do
  let cl : ColoredLayer := ColoredLayer.empty
  let (c1, cl1) := cl.addColor colorRoot
  let baseFind := fun id => id
  let (cl2, _) := cl1.mergeUnderColor baseFind c1 10 20 100
  let eqRoot := cl2.equivUnderColor baseFind colorRoot 10 20 100
  let eqC1 := cl2.equivUnderColor baseFind c1 10 20 100
  return s!"root_equiv={eqRoot}, c1_equiv={eqC1}"

#eval do
  let cl : ColoredLayer := ColoredLayer.empty
  let (c1, cl1) := cl.addColor colorRoot
  let (c2, cl2) := cl1.addColor c1
  let baseFind := fun id => id
  let (cl3, _) := cl2.mergeUnderColor baseFind c1 10 20 100
  let eqC2 := cl3.equivUnderColor baseFind c2 10 20 100
  return s!"child_c2_sees_parent_merge={eqC2}"

end AmoLean.EGraph.Verified.Bitwise.Colored
