/-
  AmoLean.EGraph.VerifiedExtraction.Core — Generic E-Graph Types for Verified Extraction

  Minimal e-graph type definitions needed by extraction algorithms.
  Unifies SuperTensor-lean's ENodeOps and OptiSat's NodeOps into a single
  parametric interface. No mutation operations (add/merge/rebuild) — only
  read access needed for extraction.

  Adapted from VerifiedExtraction library (copy/adapt, never import).
-/
import Std.Data.HashMap

namespace AmoLean.EGraph.VerifiedExtraction

/-! ## EClassId -/

/-- Identifier for an equivalence class (index into union-find array). -/
abbrev EClassId := Nat

/-! ## NodeOps — Unified Typeclass -/

/-- Typeclass for e-graph node operations.
    Unifies SuperTensor's `ENodeOps` and OptiSat's `NodeOps`.
    Any domain-specific node type must implement this interface. -/
class NodeOps (Op : Type) where
  /-- Extract child e-class IDs from an operation. -/
  children : Op → List EClassId
  /-- Apply a function to all child e-class IDs. -/
  mapChildren : (EClassId → EClassId) → Op → Op
  /-- Replace children positionally with new IDs. -/
  replaceChildren : Op → List EClassId → Op
  /-- Local cost of an operation (not including children). -/
  localCost : Op → Nat
  /-- Law: mapChildren distributes over children extraction. -/
  mapChildren_children : ∀ (f : EClassId → EClassId) (op : Op),
    children (mapChildren f op) = (children op).map f
  /-- Law: mapChildren with identity is identity. -/
  mapChildren_id : ∀ (op : Op), mapChildren id op = op
  /-- Law: replaceChildren yields the given children when lengths match. -/
  replaceChildren_children : ∀ (op : Op) (ids : List EClassId),
    ids.length = (children op).length →
    children (replaceChildren op ids) = ids
  /-- Law: replaceChildren preserves the operator skeleton. -/
  replaceChildren_sameShape : ∀ (op : Op) (ids : List EClassId),
    ids.length = (children op).length →
    mapChildren (fun _ => (0 : EClassId)) (replaceChildren op ids) =
      mapChildren (fun _ => (0 : EClassId)) op

/-! ## UnionFind — Minimal for Extraction -/

/-- Union-Find with path compression.
    Stores the parent of each ID. If parent[i] = i, then i is a root. -/
structure UnionFind where
  parent : Array EClassId
  deriving Inhabited

namespace UnionFind

def empty : UnionFind := ⟨#[]⟩

def size (uf : UnionFind) : Nat := uf.parent.size

/-- Find root by following parent pointers without compression.
    Fuel ensures totality; parent.size suffices for well-formed UFs. -/
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

/-- Add a new element (becomes its own root). Returns (newId, updatedUF). -/
def add (uf : UnionFind) : (EClassId × UnionFind) :=
  let newId := uf.parent.size
  (newId, ⟨uf.parent.push newId⟩)

/-- Union two classes. The second root becomes a child of the first root. -/
def union (uf : UnionFind) (id1 id2 : EClassId) : UnionFind :=
  let root1 := root uf id1
  let root2 := root uf id2
  if root1 == root2 then uf
  else if root2 < uf.parent.size then
    ⟨uf.parent.set! root2 root1⟩
  else uf

end UnionFind

/-! ## ENode, EClass, EGraph -/

/-- An e-node wraps a domain-specific operation. -/
@[ext]
structure ENode (Op : Type) where
  op : Op

namespace ENode

instance [BEq Op] : BEq (ENode Op) where
  beq a b := a.op == b.op

instance [Hashable Op] : Hashable (ENode Op) where
  hash e := hash e.op

instance [Inhabited Op] : Inhabited (ENode Op) where
  default := ⟨default⟩

instance [DecidableEq Op] : DecidableEq (ENode Op) := fun a b =>
  match decEq a.op b.op with
  | isTrue h => isTrue (ENode.ext h)
  | isFalse h => isFalse (fun heq => h (congrArg ENode.op heq))

instance instLawfulBEqENode [BEq Op] [LawfulBEq Op] : LawfulBEq (ENode Op) where
  eq_of_beq h := ENode.ext (eq_of_beq h)
  rfl {x} := by
    have h : (x.op == x.op) = true := ReflBEq.rfl
    exact h

instance [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op] :
    LawfulHashable (ENode Op) where
  hash_eq {a b} h := by
    have : a.op = b.op := eq_of_beq h
    show hash a.op = hash b.op
    rw [this]

variable {Op : Type} [NodeOps Op]

def children (node : ENode Op) : List EClassId := NodeOps.children node.op

def mapChildren (f : EClassId → EClassId) (node : ENode Op) : ENode Op :=
  ⟨NodeOps.mapChildren f node.op⟩

def replaceChildren (node : ENode Op) (ids : List EClassId) : ENode Op :=
  ⟨NodeOps.replaceChildren node.op ids⟩

def localCost (node : ENode Op) : Nat := NodeOps.localCost node.op

@[simp] theorem mapChildren_children_eq (f : EClassId → EClassId) (node : ENode Op) :
    (node.mapChildren f).children = node.children.map f := by
  simp [children, mapChildren, NodeOps.mapChildren_children]

end ENode

private def infinityCost : Nat := 1000000000

/-- An equivalence class: array of equivalent e-nodes + best cost tracking. -/
structure EClass (Op : Type) where
  nodes    : Array (ENode Op) := #[]
  bestCost : Nat := infinityCost
  bestNode : Option (ENode Op) := none
  deriving Inhabited

namespace EClass

variable {Op : Type} [BEq Op]

def singleton (node : ENode Op) : EClass Op where
  nodes := #[node]
  bestCost := infinityCost
  bestNode := some node

def addNode (ec : EClass Op) (node : ENode Op) : EClass Op :=
  if ec.nodes.contains node then ec
  else { ec with nodes := ec.nodes.push node }

def updateBest (ec : EClass Op) (node : ENode Op) (cost : Nat) : EClass Op :=
  if cost < ec.bestCost then
    { ec with bestCost := cost, bestNode := some node }
  else ec

def union (ec1 ec2 : EClass Op) : EClass Op :=
  let merged := ec2.nodes.foldl (fun acc n =>
    if acc.contains n then acc else acc.push n) ec1.nodes
  { nodes := merged
  , bestCost := min ec1.bestCost ec2.bestCost
  , bestNode := if ec1.bestCost ≤ ec2.bestCost then ec1.bestNode else ec2.bestNode }

def size (ec : EClass Op) : Nat := ec.nodes.size

end EClass

/-- The main e-graph, parameterized by operation type Op. -/
structure EGraph (Op : Type) [BEq Op] [Hashable Op] where
  unionFind : UnionFind := .empty
  hashcons  : Std.HashMap (ENode Op) EClassId := Std.HashMap.ofList []
  classes   : Std.HashMap EClassId (EClass Op) := Std.HashMap.ofList []
  worklist  : List EClassId := []
  deriving Inhabited

namespace EGraph

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

def empty : EGraph Op := {}

def numClasses (g : EGraph Op) : Nat := g.classes.size
def numNodes (g : EGraph Op) : Nat := g.hashcons.size

/-- Find the canonical root of a class (read-only, no path compression). -/
def findRoot (g : EGraph Op) (id : EClassId) : EClassId :=
  UnionFind.root g.unionFind id

/-- Get the e-class for a canonical ID. -/
def getClass (g : EGraph Op) (id : EClassId) : Option (EClass Op) :=
  g.classes.get? id

/-- Add a node to the e-graph. Returns (newId, updatedEGraph). -/
def add (g : EGraph Op) (node : ENode Op) : (EClassId × EGraph Op) :=
  let cs := node.children
  let canonNode := if cs.isEmpty then node
    else node.mapChildren (fun c => UnionFind.root g.unionFind c)
  match g.hashcons.get? canonNode with
  | some existingId => (UnionFind.root g.unionFind existingId, g)
  | none =>
    let (newId, uf') := g.unionFind.add
    let newClass := EClass.singleton canonNode
    (newId, { g with
      unionFind := uf'
      hashcons := g.hashcons.insert canonNode newId
      classes := g.classes.insert newId newClass })

/-- Merge two e-classes. -/
def merge (g : EGraph Op) (id1 id2 : EClassId) : EGraph Op :=
  let root1 := UnionFind.root g.unionFind id1
  let root2 := UnionFind.root g.unionFind id2
  if root1 == root2 then g
  else
    let uf' := g.unionFind.union root1 root2
    let class1 := g.classes.get? root1 |>.getD default
    let class2 := g.classes.get? root2 |>.getD default
    let mergedClass := class1.union class2
    { g with
      unionFind := uf'
      classes := g.classes.insert root1 mergedClass
      worklist := root2 :: g.worklist }

/-- Compute costs for all classes (greedy best-node selection). -/
def computeCostsF (g : EGraph Op)
    (costFn : ENode Op → Nat := fun n => n.localCost)
    (fuel : Nat := 100) : EGraph Op :=
  match fuel with
  | 0 => g
  | fuel + 1 =>
    let g' := g.classes.fold (init := g) fun acc classId eclass =>
      eclass.nodes.foldl (init := acc) fun acc2 node =>
        let nodeCost := costFn node +
          node.children.foldl (fun sum childId =>
            let canonId := UnionFind.root acc2.unionFind childId
            sum + (acc2.classes.get? canonId |>.map (·.bestCost) |>.getD infinityCost)
          ) 0
        match acc2.classes.get? classId with
        | some ec =>
          let ec' := ec.updateBest node nodeCost
          { acc2 with classes := acc2.classes.insert classId ec' }
        | none => acc2
    computeCostsF g' costFn fuel

end EGraph

/-! ## Semantic Interface -/

/-- Typeclass for semantic evaluation of node operations.
    `Env` is the environment type for external inputs.
    `Val` is the semantic domain (e.g., ZMod p, TensorVal, Nat). -/
class NodeSemantics (Op : Type) (Env Val : Type) [NodeOps Op] where
  /-- Evaluate an operation given an environment and a class-value mapping. -/
  evalOp : Op → Env → (EClassId → Val) → Val
  /-- `evalOp` depends on `v` only through the children of `op`. -/
  evalOp_ext : ∀ (op : Op) (env : Env) (v v' : EClassId → Val),
    (∀ c ∈ NodeOps.children op, v c = v' c) → evalOp op env v = evalOp op env v'

/-- Semantic evaluation of an ENode: delegates to `NodeSemantics.evalOp`. -/
def NodeEval {Op Env Val : Type} [NodeOps Op] [NodeSemantics Op Env Val]
    (node : ENode Op) (env : Env) (v : EClassId → Val) : Val :=
  NodeSemantics.evalOp node.op env v

/-! ## UnionFind Well-Formedness -/

namespace UnionFind

/-- rootD on an out-of-bounds ID returns the ID itself. -/
theorem rootD_oob (parent : Array EClassId) (id : EClassId)
    (h : ¬(id < parent.size)) : ∀ fuel, rootD parent id fuel = id
  | 0 => rfl
  | _ + 1 => by unfold rootD; exact dif_neg h

/-- Out-of-bounds IDs are their own root. -/
theorem root_oob (uf : UnionFind) (id : EClassId) (h : ¬(id < uf.parent.size)) :
    root uf id = id :=
  rootD_oob uf.parent id h uf.parent.size

/-- Abstract well-formedness for UnionFind.
    Project adaptors prove this for their specific UF implementations. -/
structure WellFormed (uf : UnionFind) : Prop where
  /-- Root of a root is itself. -/
  root_idempotent : ∀ i, i < uf.parent.size → root uf (root uf i) = root uf i
  /-- Root stays in bounds. -/
  root_bounded : ∀ i, i < uf.parent.size → root uf i < uf.parent.size

end UnionFind

/-! ## ConsistentValuation -/

/-- A valuation `v : EClassId → Val` is consistent with an e-graph `g`
    under environment `env` if:
    (1) UF-equivalent class IDs have the same value, and
    (2) every node in a class evaluates to that class's value. -/
structure ConsistentValuation {Op Env Val : Type}
    [NodeOps Op] [BEq Op] [Hashable Op] [NodeSemantics Op Env Val]
    (g : EGraph Op) (env : Env) (v : EClassId → Val) : Prop where
  /-- Equivalent IDs map to the same value. -/
  equiv_same_val : ∀ i j,
    UnionFind.root g.unionFind i = UnionFind.root g.unionFind j → v i = v j
  /-- Every node evaluates to its class's value. -/
  node_consistent : ∀ classId eclass,
    g.classes.get? classId = some eclass →
    ∀ node, node ∈ eclass.nodes.toList →
      NodeEval node env v = v classId

/-- v(root id) = v id, for in-bounds IDs. -/
theorem consistent_root_eq {Op Env Val : Type}
    [NodeOps Op] [BEq Op] [Hashable Op] [NodeSemantics Op Env Val]
    {g : EGraph Op} {env : Env} {v : EClassId → Val}
    (hcv : ConsistentValuation g env v) (hwf : UnionFind.WellFormed g.unionFind)
    {id : EClassId} (hid : id < g.unionFind.parent.size) :
    v (UnionFind.root g.unionFind id) = v id :=
  hcv.equiv_same_val _ _ (hwf.root_idempotent id hid)

/-- v(root id) = v id, handling both in-bounds and out-of-bounds. -/
theorem consistent_root_eq' {Op Env Val : Type}
    [NodeOps Op] [BEq Op] [Hashable Op] [NodeSemantics Op Env Val]
    {g : EGraph Op} {env : Env} {v : EClassId → Val}
    (hcv : ConsistentValuation g env v) (hwf : UnionFind.WellFormed g.unionFind)
    (id : EClassId) :
    v (UnionFind.root g.unionFind id) = v id := by
  by_cases hid : id < g.unionFind.parent.size
  · exact consistent_root_eq hcv hwf hid
  · rw [UnionFind.root_oob g.unionFind id hid]

/-- Every bestNode is in its class's nodes array. -/
def BestNodeInv {Op : Type} [BEq Op] [Hashable Op]
    (classes : Std.HashMap EClassId (EClass Op)) : Prop :=
  ∀ cid cls nd, classes.get? cid = some cls →
    cls.bestNode = some nd → nd ∈ cls.nodes.toList

end AmoLean.EGraph.VerifiedExtraction
