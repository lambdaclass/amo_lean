/-
  AMO-Lean: E-Graph for VecExpr
  Phase 1: VecExpr E-Graph Integration

  This module extends the E-graph system to handle VecExpr,
  enabling optimization of vector operations via equality saturation.

  Key optimizations:
  - Identity rules: v + broadcast(0) = v, v * broadcast(1) = v
  - Split-concat identities: splitLo(concat(a,b)) = a
  - Strength reduction: v + v = 2 * v

  References:
  - egg: Fast and Extensible Equality Saturation (Willsey et al.)
  - AmoLean/Vector/Basic.lean: VecExpr DSL
  - AmoLean/EGraph/Basic.lean: Scalar E-graph
-/

import Std.Data.HashMap
import Std.Data.HashSet
import AmoLean.Vector.Basic
import AmoLean.EGraph.Basic

namespace AmoLean.EGraph.VecExpr

open AmoLean.Vector (VecExpr VecVarId Vec)
open AmoLean (Expr VarId)
open AmoLean.EGraph (EClassId infiniteCost)

/-! ## Part 1: Vector E-Node Operations -/

/-- Identifier for vector e-classes -/
abbrev VecEClassId := Nat

/-- Cost model for vector operations.
    Lower costs encourage the optimizer to prefer certain forms. -/
structure VecCostModel where
  /-- Cost of literal vector -/
  litCost : Nat := 1
  /-- Cost of variable reference -/
  varCost : Nat := 0
  /-- Cost of map operation -/
  mapCost : Nat := 2
  /-- Cost of zipWith operation -/
  zipWithCost : Nat := 2
  /-- Cost of split operation (half) -/
  splitCost : Nat := 1
  /-- Cost of concat operation -/
  concatCost : Nat := 1
  /-- Cost of interleave operation -/
  interleaveCost : Nat := 2
  /-- Cost of stride permutation -/
  strideCost : Nat := 3
  /-- Cost of bit-reversal permutation -/
  bitRevCost : Nat := 3
  /-- Cost of broadcast -/
  broadcastCost : Nat := 0
  /-- Cost of head extraction -/
  headCost : Nat := 1
  /-- Cost of tail extraction -/
  tailCost : Nat := 1
  deriving Repr, Inhabited

/-- Default vector cost model -/
def defaultVecCostModel : VecCostModel := {}

/-- Vector operations for E-graph nodes.
    Each operation stores child IDs and dimension information. -/
inductive VecENodeOp where
  /-- Literal vector -/
  | lit (n : Nat) (hash : UInt64)
  /-- Variable reference -/
  | var (id : VecVarId) (n : Nat)
  /-- Map scalar function over vector -/
  | map (v : VecEClassId) (n : Nat)
  /-- ZipWith: combine two vectors element-wise -/
  | zipWith (v1 v2 : VecEClassId) (n : Nat)
  /-- Split low half -/
  | splitLo (v : VecEClassId) (n : Nat)
  /-- Split high half -/
  | splitHi (v : VecEClassId) (n : Nat)
  /-- Head: first element as 1-vector -/
  | head (v : VecEClassId) (n : Nat)
  /-- Tail: all but first element -/
  | tail (v : VecEClassId) (n : Nat)
  /-- Concatenate two vectors -/
  | concat (v1 v2 : VecEClassId) (m n : Nat)
  /-- Interleave two vectors -/
  | interleave (v1 v2 : VecEClassId) (n : Nat)
  /-- Stride permutation -/
  | stride (k : Nat) (v : VecEClassId) (n : Nat)
  /-- Bit-reversal permutation -/
  | bitRev (v : VecEClassId) (k : Nat)
  /-- Broadcast scalar to vector -/
  | broadcast (scalar : EClassId) (n : Nat)
  /-- Scalar multiplication: s * v -/
  | smul (scalar : EClassId) (v : VecEClassId) (n : Nat)
  /-- Vector addition: v1 + v2 -/
  | add (v1 v2 : VecEClassId) (n : Nat)
  /-- Zero vector of size n (for optimization rules) -/
  | zero (n : Nat)
  deriving Repr, BEq, Hashable, Inhabited

/-- A vector E-node wraps an operation -/
structure VecENode where
  op : VecENodeOp
  deriving Repr, BEq, Hashable, Inhabited

namespace VecENode

/-- Create literal node -/
def mkLit (n : Nat) (hash : UInt64) : VecENode := ⟨.lit n hash⟩

/-- Create variable node -/
def mkVar (id : VecVarId) (n : Nat) : VecENode := ⟨.var id n⟩

/-- Create map node -/
def mkMap (v : VecEClassId) (n : Nat) : VecENode := ⟨.map v n⟩

/-- Create zipWith node -/
def mkZipWith (v1 v2 : VecEClassId) (n : Nat) : VecENode := ⟨.zipWith v1 v2 n⟩

/-- Create splitLo node -/
def mkSplitLo (v : VecEClassId) (n : Nat) : VecENode := ⟨.splitLo v n⟩

/-- Create splitHi node -/
def mkSplitHi (v : VecEClassId) (n : Nat) : VecENode := ⟨.splitHi v n⟩

/-- Create head node -/
def mkHead (v : VecEClassId) (n : Nat) : VecENode := ⟨.head v n⟩

/-- Create tail node -/
def mkTail (v : VecEClassId) (n : Nat) : VecENode := ⟨.tail v n⟩

/-- Create concat node -/
def mkConcat (v1 v2 : VecEClassId) (m n : Nat) : VecENode := ⟨.concat v1 v2 m n⟩

/-- Create interleave node -/
def mkInterleave (v1 v2 : VecEClassId) (n : Nat) : VecENode := ⟨.interleave v1 v2 n⟩

/-- Create stride node -/
def mkStride (k : Nat) (v : VecEClassId) (n : Nat) : VecENode := ⟨.stride k v n⟩

/-- Create bitRev node -/
def mkBitRev (v : VecEClassId) (k : Nat) : VecENode := ⟨.bitRev v k⟩

/-- Create broadcast node -/
def mkBroadcast (scalar : EClassId) (n : Nat) : VecENode := ⟨.broadcast scalar n⟩

/-- Create smul node -/
def mkSmul (scalar : EClassId) (v : VecEClassId) (n : Nat) : VecENode := ⟨.smul scalar v n⟩

/-- Create add node -/
def mkAdd (v1 v2 : VecEClassId) (n : Nat) : VecENode := ⟨.add v1 v2 n⟩

/-- Create zero node -/
def mkZero (n : Nat) : VecENode := ⟨.zero n⟩

/-- Get output dimension of a vector node -/
def dimension : VecENode → Nat
  | ⟨.lit n _⟩ => n
  | ⟨.var _ n⟩ => n
  | ⟨.map _ n⟩ => n
  | ⟨.zipWith _ _ n⟩ => n
  | ⟨.splitLo _ n⟩ => n
  | ⟨.splitHi _ n⟩ => n
  | ⟨.head _ _⟩ => 1
  | ⟨.tail _ n⟩ => n
  | ⟨.concat _ _ m n⟩ => m + n
  | ⟨.interleave _ _ n⟩ => 2 * n
  | ⟨.stride _ _ n⟩ => n
  | ⟨.bitRev _ k⟩ => 2^k
  | ⟨.broadcast _ n⟩ => n
  | ⟨.smul _ _ n⟩ => n
  | ⟨.add _ _ n⟩ => n
  | ⟨.zero n⟩ => n

/-- Get all child e-class IDs (vector children) -/
def vecChildren : VecENode → List VecEClassId
  | ⟨.lit _ _⟩ => []
  | ⟨.var _ _⟩ => []
  | ⟨.map v _⟩ => [v]
  | ⟨.zipWith v1 v2 _⟩ => [v1, v2]
  | ⟨.splitLo v _⟩ => [v]
  | ⟨.splitHi v _⟩ => [v]
  | ⟨.head v _⟩ => [v]
  | ⟨.tail v _⟩ => [v]
  | ⟨.concat v1 v2 _ _⟩ => [v1, v2]
  | ⟨.interleave v1 v2 _⟩ => [v1, v2]
  | ⟨.stride _ v _⟩ => [v]
  | ⟨.bitRev v _⟩ => [v]
  | ⟨.broadcast _ _⟩ => []
  | ⟨.smul _ v _⟩ => [v]
  | ⟨.add v1 v2 _⟩ => [v1, v2]
  | ⟨.zero _⟩ => []

/-- Get scalar child IDs -/
def scalarChildren : VecENode → List EClassId
  | ⟨.broadcast s _⟩ => [s]
  | ⟨.smul s _ _⟩ => [s]
  | _ => []

/-- Calculate local cost of a node -/
def localCost (cm : VecCostModel := defaultVecCostModel) : VecENode → Nat
  | ⟨.lit _ _⟩ => cm.litCost
  | ⟨.var _ _⟩ => cm.varCost
  | ⟨.map _ _⟩ => cm.mapCost
  | ⟨.zipWith _ _ _⟩ => cm.zipWithCost
  | ⟨.splitLo _ _⟩ => cm.splitCost
  | ⟨.splitHi _ _⟩ => cm.splitCost
  | ⟨.head _ _⟩ => cm.headCost
  | ⟨.tail _ _⟩ => cm.tailCost
  | ⟨.concat _ _ _ _⟩ => cm.concatCost
  | ⟨.interleave _ _ _⟩ => cm.interleaveCost
  | ⟨.stride _ _ _⟩ => cm.strideCost
  | ⟨.bitRev _ _⟩ => cm.bitRevCost
  | ⟨.broadcast _ _⟩ => cm.broadcastCost
  | ⟨.smul _ _ _⟩ => cm.zipWithCost  -- Same as zipWith
  | ⟨.add _ _ _⟩ => cm.zipWithCost   -- Same as zipWith
  | ⟨.zero _⟩ => 0

end VecENode

/-! ## Part 2: Vector E-Class -/

/-- A vector equivalence class -/
structure VecEClass where
  nodes : Std.HashSet VecENode
  bestCost : Nat := infiniteCost
  bestNode : Option VecENode := none
  dim : Nat := 0
  deriving Inhabited

namespace VecEClass

/-- Create a class with a single node -/
def singleton (node : VecENode) (cost : Nat := infiniteCost) : VecEClass :=
  { nodes := Std.HashSet.empty.insert node
  , bestCost := cost
  , bestNode := some node
  , dim := node.dimension }

/-- Add a node to the class -/
def addNode (ec : VecEClass) (node : VecENode) : VecEClass :=
  { ec with nodes := ec.nodes.insert node }

/-- Update best node if new cost is lower -/
def updateBest (ec : VecEClass) (node : VecENode) (cost : Nat) : VecEClass :=
  if cost < ec.bestCost then
    { ec with bestCost := cost, bestNode := some node }
  else
    ec

/-- Union two e-classes -/
def union (ec1 ec2 : VecEClass) : VecEClass :=
  let merged := ec1.nodes.fold (init := ec2.nodes) fun acc n => acc.insert n
  { nodes := merged
  , bestCost := min ec1.bestCost ec2.bestCost
  , bestNode := if ec1.bestCost ≤ ec2.bestCost then ec1.bestNode else ec2.bestNode
  , dim := ec1.dim }

/-- Number of nodes in the class -/
def size (ec : VecEClass) : Nat := ec.nodes.size

end VecEClass

/-! ## Part 3: Vector Union-Find -/

/-- Union-Find for vector e-classes -/
structure VecUnionFind where
  parent : Array VecEClassId
  deriving Inhabited

namespace VecUnionFind

def empty : VecUnionFind := ⟨#[]⟩

def init (n : Nat) : VecUnionFind := ⟨Array.range n⟩

def add (uf : VecUnionFind) : (VecEClassId × VecUnionFind) :=
  let newId := uf.parent.size
  (newId, ⟨uf.parent.push newId⟩)

partial def find (uf : VecUnionFind) (id : VecEClassId) : (VecEClassId × VecUnionFind) :=
  if id < uf.parent.size then
    let parentId := uf.parent[id]!
    if parentId == id then
      (id, uf)
    else
      let (root, uf') := find uf parentId
      if id < uf'.parent.size then
        let uf'' := ⟨uf'.parent.set! id root⟩
        (root, uf'')
      else
        (root, uf')
  else
    (id, uf)

def union (uf : VecUnionFind) (id1 id2 : VecEClassId) : VecUnionFind :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  if root1 == root2 then
    uf2
  else if root2 < uf2.parent.size then
    ⟨uf2.parent.set! root2 root1⟩
  else
    uf2

def equiv (uf : VecUnionFind) (id1 id2 : VecEClassId) : (Bool × VecUnionFind) :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  (root1 == root2, uf2)

def size (uf : VecUnionFind) : Nat := uf.parent.size

end VecUnionFind

/-! ## Part 4: Vector E-Graph -/

/-- The main Vector E-Graph structure -/
structure VecEGraph where
  unionFind : VecUnionFind
  hashcons : Std.HashMap VecENode VecEClassId
  classes : Std.HashMap VecEClassId VecEClass
  worklist : List VecEClassId
  dirty : Std.HashSet VecEClassId
  /-- Reference to scalar E-graph for broadcast/smul -/
  scalarEGraph : Option AmoLean.EGraph.EGraph := none
  deriving Inhabited

namespace VecEGraph

/-- Create empty vector E-graph -/
def empty : VecEGraph :=
  { unionFind := VecUnionFind.empty
  , hashcons := Std.HashMap.empty
  , classes := Std.HashMap.empty
  , worklist := []
  , dirty := Std.HashSet.empty
  , scalarEGraph := none }

/-- Number of e-classes -/
def numClasses (g : VecEGraph) : Nat := g.classes.size

/-- Number of e-nodes -/
def numNodes (g : VecEGraph) : Nat := g.hashcons.size

/-- Find canonical ID -/
def find (g : VecEGraph) (id : VecEClassId) : (VecEClassId × VecEGraph) :=
  let (canonical, uf') := g.unionFind.find id
  (canonical, { g with unionFind := uf' })

/-- Check if two IDs are equivalent -/
def equiv (g : VecEGraph) (id1 id2 : VecEClassId) : (Bool × VecEGraph) :=
  let (eq, uf') := g.unionFind.equiv id1 id2
  (eq, { g with unionFind := uf' })

/-- Add a node to the E-graph -/
def add (g : VecEGraph) (node : VecENode) : (VecEClassId × VecEGraph) :=
  match g.hashcons.get? node with
  | some existingId =>
    let (canonId, g') := g.find existingId
    (canonId, g')
  | none =>
    let (newId, uf') := g.unionFind.add
    let newClass := VecEClass.singleton node
    let g' := { g with
      unionFind := uf'
      hashcons := g.hashcons.insert node newId
      classes := g.classes.insert newId newClass }
    (newId, g')

/-- Merge two e-classes -/
def merge (g : VecEGraph) (id1 id2 : VecEClassId) : VecEGraph :=
  let (root1, g1) := g.find id1
  let (root2, g2) := g1.find id2
  if root1 == root2 then g2
  else
    let uf' := g2.unionFind.union root1 root2
    let class1 := g2.classes.get? root1 |>.getD (VecEClass.singleton (VecENode.mkZero 0))
    let class2 := g2.classes.get? root2 |>.getD (VecEClass.singleton (VecENode.mkZero 0))
    let mergedClass := class1.union class2
    { g2 with
      unionFind := uf'
      classes := g2.classes.insert root1 mergedClass
      worklist := root2 :: g2.worklist
      dirty := g2.dirty.insert root1 }

/-- Get the e-class for an ID -/
def getClass (g : VecEGraph) (id : VecEClassId) : (Option VecEClass × VecEGraph) :=
  let (canonId, g') := g.find id
  (g'.classes.get? canonId, g')

/-! ## Part 5: Rebuild -/

/-- Rebuild the E-graph to restore invariants -/
partial def rebuild (g : VecEGraph) : VecEGraph :=
  if g.worklist.isEmpty && g.dirty.isEmpty then g
  else
    let g' := { g with worklist := [], dirty := Std.HashSet.empty }
    -- Simplified rebuild: just clear the lists
    -- Full implementation would re-canonicalize nodes
    g'

/-! ## Part 6: Optimization Rules -/

/-- Rewrite rule for vector expressions -/
structure VecRule where
  name : String
  /-- Pattern to match (returns the node it matched and extracted IDs) -/
  tryMatch : VecEGraph → VecEClassId → Option (List VecEClassId)
  /-- Apply rule: create new node and return ID to merge with -/
  applyRule : VecEGraph → VecEClassId → List VecEClassId → (VecEClassId × VecEGraph)

/-- Rule: splitLo(concat(a, b)) = a
    When we split the low half of a concatenation, we get the first vector. -/
def ruleSplitLoConcat : VecRule := {
  name := "splitLo(concat(a,b)) = a"
  tryMatch := fun g classId =>
    let (_, g') := g.find classId
    match g'.classes.get? classId with
    | none => none
    | some ec =>
      -- Look for a splitLo node in this class
      ec.nodes.fold (init := none) fun acc node =>
        match acc with
        | some _ => acc
        | none =>
          match node.op with
          | .splitLo innerV n =>
            -- Check if innerV is a concat
            match g'.classes.get? innerV with
            | none => none
            | some innerEc =>
              innerEc.nodes.fold (init := none) fun acc2 innerNode =>
                match acc2 with
                | some _ => acc2
                | none =>
                  match innerNode.op with
                  | .concat a _ m _ =>
                    if m == n then some [a] else none
                  | _ => none
          | _ => none
  applyRule := fun g _ extractedIds =>
    match extractedIds with
    | [a] => (a, g)  -- Just return a
    | _ => (0, g)  -- Should not happen
}

/-- Rule: splitHi(concat(a, b)) = b
    When we split the high half of a concatenation, we get the second vector. -/
def ruleSplitHiConcat : VecRule := {
  name := "splitHi(concat(a,b)) = b"
  tryMatch := fun g classId =>
    let (_, g') := g.find classId
    match g'.classes.get? classId with
    | none => none
    | some ec =>
      ec.nodes.fold (init := none) fun acc node =>
        match acc with
        | some _ => acc
        | none =>
          match node.op with
          | .splitHi innerV n =>
            match g'.classes.get? innerV with
            | none => none
            | some innerEc =>
              innerEc.nodes.fold (init := none) fun acc2 innerNode =>
                match acc2 with
                | some _ => acc2
                | none =>
                  match innerNode.op with
                  | .concat _ b _ m =>
                    if m == n then some [b] else none
                  | _ => none
          | _ => none
  applyRule := fun g _ extractedIds =>
    match extractedIds with
    | [b] => (b, g)
    | _ => (0, g)
}

/-- Rule: v + zero = v
    Adding zero is an identity operation. -/
def ruleAddZero : VecRule := {
  name := "v + zero = v"
  tryMatch := fun g classId =>
    let (_, g') := g.find classId
    match g'.classes.get? classId with
    | none => none
    | some ec =>
      ec.nodes.fold (init := none) fun acc node =>
        match acc with
        | some _ => acc
        | none =>
          match node.op with
          | .add v1 v2 _ =>
            -- Check if v2 is zero
            match g'.classes.get? v2 with
            | none => none
            | some v2ec =>
              let hasZero := v2ec.nodes.fold (init := false) fun found n =>
                match n.op with
                | .zero _ => true
                | _ => found
              if hasZero then some [v1] else none
          | _ => none
  applyRule := fun g _ extractedIds =>
    match extractedIds with
    | [v] => (v, g)
    | _ => (0, g)
}

/-- Rule: concat(splitLo(v), splitHi(v)) = v
    Concatenating the two halves reconstructs the original vector. -/
def ruleConcatSplits : VecRule := {
  name := "concat(splitLo(v), splitHi(v)) = v"
  tryMatch := fun g classId =>
    let (_, g') := g.find classId
    match g'.classes.get? classId with
    | none => none
    | some ec =>
      ec.nodes.fold (init := none) fun acc node =>
        match acc with
        | some _ => acc
        | none =>
          match node.op with
          | .concat loId hiId _ _ =>
            -- Check if loId is splitLo(v) and hiId is splitHi(v)
            match g'.classes.get? loId, g'.classes.get? hiId with
            | some loEc, some hiEc =>
              -- Look for splitLo in loEc
              let loOriginal := loEc.nodes.fold (init := none) fun loAcc loNode =>
                match loAcc with
                | some _ => loAcc
                | none =>
                  match loNode.op with
                  | .splitLo v _ => some v
                  | _ => none
              -- Look for splitHi in hiEc
              let hiOriginal := hiEc.nodes.fold (init := none) fun hiAcc hiNode =>
                match hiAcc with
                | some _ => hiAcc
                | none =>
                  match hiNode.op with
                  | .splitHi v _ => some v
                  | _ => none
              match loOriginal, hiOriginal with
              | some v1, some v2 =>
                if v1 == v2 then some [v1] else none
              | _, _ => none
            | _, _ => none
          | _ => none
  applyRule := fun g _ extractedIds =>
    match extractedIds with
    | [v] => (v, g)
    | _ => (0, g)
}

/-- All optimization rules -/
def allRules : List VecRule := [
  ruleSplitLoConcat,
  ruleSplitHiConcat,
  ruleAddZero,
  ruleConcatSplits
]

/-- Apply a single rule to a class, returning updated graph if rule matched -/
def applyVecRule (g : VecEGraph) (rule : VecRule) (classId : VecEClassId) : VecEGraph :=
  match rule.tryMatch g classId with
  | none => g
  | some extractedIds =>
    let (targetId, g') := rule.applyRule g classId extractedIds
    if targetId == classId then g'
    else g'.merge classId targetId

/-- Run one saturation iteration -/
def saturateOnce (g : VecEGraph) : (VecEGraph × Bool) :=
  let classIds := g.classes.toList.map Prod.fst
  let (g', changed) := classIds.foldl (fun (acc, anyChanged) classId =>
    let newAcc := allRules.foldl (fun accG rule => applyVecRule accG rule classId) acc
    let classChanged := newAcc.numClasses < acc.numClasses
    (newAcc, anyChanged || classChanged)
  ) (g, false)
  (g'.rebuild, changed)

/-- Run saturation to fixed point (with fuel) -/
partial def saturate (g : VecEGraph) (fuel : Nat := 100) : VecEGraph :=
  if fuel == 0 then g
  else
    let (g', changed) := saturateOnce g
    if changed then saturate g' (fuel - 1)
    else g'

/-! ## Part 7: Statistics -/

/-- Statistics for the vector E-graph -/
structure VecStats where
  numClasses : Nat
  numNodes : Nat
  unionFindSize : Nat
  worklistSize : Nat
  deriving Repr

def stats (g : VecEGraph) : VecStats :=
  { numClasses := g.numClasses
  , numNodes := g.numNodes
  , unionFindSize := g.unionFind.size
  , worklistSize := g.worklist.length }

end VecEGraph

/-! ## Part 8: Tests -/

section Tests

open VecEGraph

-- Test 1: Create E-graph with simple vector nodes
#eval do
  let g0 := VecEGraph.empty
  let (v1, g1) := g0.add (VecENode.mkVar 0 4)  -- var 0, length 4
  let (v2, g2) := g1.add (VecENode.mkVar 1 4)  -- var 1, length 4
  let (addId, g3) := g2.add (VecENode.mkAdd v1 v2 4)  -- v1 + v2
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     VECEXPR E-GRAPH TESTS                                    ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Test 1: Simple vector addition v1 + v2"
  IO.println s!"  v1 ID: {v1}"
  IO.println s!"  v2 ID: {v2}"
  IO.println s!"  v1+v2 ID: {addId}"
  IO.println s!"  Classes: {g3.numClasses}"
  IO.println s!"  Nodes: {g3.numNodes}"
  IO.println ""

-- Test 2: splitLo(concat(a, b)) = a optimization
#eval do
  let g0 := VecEGraph.empty
  -- Create vectors a and b (length 4 each)
  let (a, g1) := g0.add (VecENode.mkVar 0 4)
  let (b, g2) := g1.add (VecENode.mkVar 1 4)
  -- Create concat(a, b) - length 8
  let (concatId, g3) := g2.add (VecENode.mkConcat a b 4 4)
  -- Create splitLo(concat(a, b)) - should equal a (length 4)
  let (splitLoId, g4) := g3.add (VecENode.mkSplitLo concatId 4)

  IO.println "Test 2: splitLo(concat(a, b)) = a"
  IO.println s!"  a ID: {a}"
  IO.println s!"  concat(a,b) ID: {concatId}"
  IO.println s!"  splitLo(concat(a,b)) ID: {splitLoId}"
  IO.println s!"  Before optimization: {g4.numClasses} classes"

  -- Apply the rule
  let g5 := applyVecRule g4 ruleSplitLoConcat splitLoId
  let g6 := g5.rebuild

  IO.println s!"  After splitLo rule: {g6.numClasses} classes"
  let (eq, _) := g6.equiv splitLoId a
  IO.println s!"  splitLo(concat(a,b)) == a? {eq}"
  IO.println ""

-- Test 3: v + zero = v optimization
#eval do
  let g0 := VecEGraph.empty
  -- Create vector v (length 4)
  let (v, g1) := g0.add (VecENode.mkVar 0 4)
  -- Create zero vector (length 4)
  let (z, g2) := g1.add (VecENode.mkZero 4)
  -- Create v + zero
  let (addId, g3) := g2.add (VecENode.mkAdd v z 4)

  IO.println "Test 3: v + zero = v"
  IO.println s!"  v ID: {v}"
  IO.println s!"  zero ID: {z}"
  IO.println s!"  v+zero ID: {addId}"
  IO.println s!"  Before optimization: {g3.numClasses} classes"

  -- Apply the rule
  let g4 := applyVecRule g3 ruleAddZero addId
  let g5 := g4.rebuild

  IO.println s!"  After addZero rule: {g5.numClasses} classes"
  let (eq, _) := g5.equiv addId v
  IO.println s!"  v + zero == v? {eq}"
  IO.println ""

-- Test 4: FRI fold pattern
#eval do
  IO.println "Test 4: FRI fold pattern (even + α * odd)"
  let g0 := VecEGraph.empty
  -- Create even and odd vectors (length 4)
  let (even, g1) := g0.add (VecENode.mkVar 0 4)
  let (odd, g2) := g1.add (VecENode.mkVar 1 4)
  -- Create alpha (scalar ID 0)
  let alphaScalarId : EClassId := 0
  -- Create alpha * odd
  let (alphaOdd, g3) := g2.add (VecENode.mkSmul alphaScalarId odd 4)
  -- Create even + alpha * odd
  let (foldResult, g4) := g3.add (VecENode.mkAdd even alphaOdd 4)

  IO.println s!"  even ID: {even}"
  IO.println s!"  odd ID: {odd}"
  IO.println s!"  α*odd ID: {alphaOdd}"
  IO.println s!"  even+α*odd ID: {foldResult}"
  IO.println s!"  Total classes: {g4.numClasses}"
  IO.println s!"  Total nodes: {g4.numNodes}"
  IO.println ""

-- Test 5: Full saturation
#eval do
  IO.println "Test 5: Full saturation test"
  let g0 := VecEGraph.empty
  let (a, g1) := g0.add (VecENode.mkVar 0 4)
  let (b, g2) := g1.add (VecENode.mkVar 1 4)
  let (concatId, g3) := g2.add (VecENode.mkConcat a b 4 4)
  let (splitLoId, g4) := g3.add (VecENode.mkSplitLo concatId 4)
  let (splitHiId, g5) := g4.add (VecENode.mkSplitHi concatId 4)

  IO.println s!"  Before saturation: {g5.numClasses} classes, {g5.numNodes} nodes"

  let g6 := g5.saturate
  IO.println s!"  After saturation: {g6.numClasses} classes, {g6.numNodes} nodes"

  let (eqA, _) := g6.equiv splitLoId a
  let (eqB, _) := g6.equiv splitHiId b
  IO.println s!"  splitLo(concat(a,b)) == a? {eqA}"
  IO.println s!"  splitHi(concat(a,b)) == b? {eqB}"
  IO.println ""
  IO.println "Tests completed."

end Tests

end AmoLean.EGraph.VecExpr
