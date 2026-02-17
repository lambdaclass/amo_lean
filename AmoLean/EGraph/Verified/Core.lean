/-
  AMO-Lean — Verified EGraph Core Structures
  Ported from VR1CS-Lean (Phase 3 Subphase 1-2).
  CircuitNodeOp preserved for now; will be generalized to Expr α in Subfase 8d.
-/
import Lean
import AmoLean.EGraph.Verified.UnionFind

namespace AmoLean.EGraph.Verified

private def infinityCost : Nat := 1000000000

/-- Operations supported in the circuit E-graph. -/
inductive CircuitNodeOp where
  | constGate  : Nat → CircuitNodeOp
  | witness    : Nat → CircuitNodeOp
  | pubInput   : Nat → CircuitNodeOp
  | addGate    : EClassId → EClassId → CircuitNodeOp
  | mulGate    : EClassId → EClassId → CircuitNodeOp
  | negGate    : EClassId → CircuitNodeOp
  | smulGate   : Nat → EClassId → CircuitNodeOp
  deriving Repr, Hashable, Inhabited, DecidableEq

instance : BEq CircuitNodeOp := instBEqOfDecidableEq

/-- An E-node wraps a circuit operation. -/
structure ENode where
  op : CircuitNodeOp
  deriving Repr, Hashable, Inhabited, DecidableEq

instance : BEq ENode := instBEqOfDecidableEq

namespace ENode

def mkConst (c : Nat) : ENode := ⟨.constGate c⟩
def mkWitness (i : Nat) : ENode := ⟨.witness i⟩
def mkPubInput (i : Nat) : ENode := ⟨.pubInput i⟩
def mkAdd (a b : EClassId) : ENode := ⟨.addGate a b⟩
def mkMul (a b : EClassId) : ENode := ⟨.mulGate a b⟩
def mkNeg (a : EClassId) : ENode := ⟨.negGate a⟩
def mkSmul (c : Nat) (a : EClassId) : ENode := ⟨.smulGate c a⟩

def children : ENode → List EClassId
  | ⟨.constGate _⟩   => []
  | ⟨.witness _⟩      => []
  | ⟨.pubInput _⟩     => []
  | ⟨.addGate a b⟩    => [a, b]
  | ⟨.mulGate a b⟩    => [a, b]
  | ⟨.negGate a⟩      => [a]
  | ⟨.smulGate _ a⟩   => [a]

def mapChildren (f : EClassId → EClassId) : ENode → ENode
  | ⟨.constGate c⟩   => ⟨.constGate c⟩
  | ⟨.witness i⟩      => ⟨.witness i⟩
  | ⟨.pubInput i⟩     => ⟨.pubInput i⟩
  | ⟨.addGate a b⟩    => ⟨.addGate (f a) (f b)⟩
  | ⟨.mulGate a b⟩    => ⟨.mulGate (f a) (f b)⟩
  | ⟨.negGate a⟩      => ⟨.negGate (f a)⟩
  | ⟨.smulGate c a⟩   => ⟨.smulGate c (f a)⟩

def localCost : ENode → Nat
  | ⟨.mulGate _ _⟩ => 1
  | _               => 0

end ENode

/-- An equivalence class: array of equivalent e-nodes + best cost tracking. -/
structure EClass where
  nodes    : Array ENode := #[]
  bestCost : Nat := infinityCost
  bestNode : Option ENode := none
  deriving Repr, Inhabited

namespace EClass

def singleton (node : ENode) : EClass where
  nodes := #[node]
  bestCost := infinityCost
  bestNode := some node

def addNode (ec : EClass) (node : ENode) : EClass :=
  if ec.nodes.contains node then ec
  else { ec with nodes := ec.nodes.push node }

def updateBest (ec : EClass) (node : ENode) (cost : Nat) : EClass :=
  if cost < ec.bestCost then
    { ec with bestCost := cost, bestNode := some node }
  else ec

def union (ec1 ec2 : EClass) : EClass :=
  let merged := ec2.nodes.foldl (fun acc n =>
    if acc.contains n then acc else acc.push n) ec1.nodes
  { nodes := merged
  , bestCost := min ec1.bestCost ec2.bestCost
  , bestNode := if ec1.bestCost ≤ ec2.bestCost then ec1.bestNode else ec2.bestNode }

def size (ec : EClass) : Nat := ec.nodes.size

end EClass

/-- The main E-graph for circuit expressions. -/
structure EGraph where
  unionFind : UnionFind := .empty
  hashcons  : Std.HashMap ENode EClassId := Std.HashMap.ofList []
  classes   : Std.HashMap EClassId EClass := Std.HashMap.ofList []
  worklist  : List EClassId := []
  dirtyArr  : Array EClassId := #[]
  deriving Inhabited

namespace EGraph

def empty : EGraph := {}

def numClasses (g : EGraph) : Nat := g.classes.size
def numNodes (g : EGraph) : Nat := g.hashcons.size

def find (g : EGraph) (id : EClassId) : (EClassId × EGraph) :=
  let (canonical, uf') := g.unionFind.find id
  (canonical, { g with unionFind := uf' })

def canonicalize (g : EGraph) (node : ENode) : (ENode × EGraph) :=
  let children := node.children
  if children.isEmpty then (node, g)
  else
    let rec go (cs : List EClassId) (g : EGraph) (pairs : List (EClassId × EClassId)) :
        (List (EClassId × EClassId) × EGraph) :=
      match cs with
      | [] => (pairs, g)
      | c :: rest =>
        let (canonId, g') := g.find c
        go rest g' ((c, canonId) :: pairs)
    let (pairs, g') := go children g []
    let f : EClassId → EClassId := fun id =>
      match pairs.find? (fun (old, _) => old == id) with
      | some (_, new_) => new_
      | none => id
    (node.mapChildren f, g')

def add (g : EGraph) (node : ENode) : (EClassId × EGraph) :=
  let (canonNode, g1) := g.canonicalize node
  match g1.hashcons.get? canonNode with
  | some existingId =>
    let (canonId, g2) := g1.find existingId
    (canonId, g2)
  | none =>
    let (newId, uf') := g1.unionFind.add
    let newClass := EClass.singleton canonNode
    (newId, { g1 with
      unionFind := uf'
      hashcons := g1.hashcons.insert canonNode newId
      classes := g1.classes.insert newId newClass })

def merge (g : EGraph) (id1 id2 : EClassId) : EGraph :=
  let (root1, g1) := g.find id1
  let (root2, g2) := g1.find id2
  if root1 == root2 then g2
  else
    let uf' := g2.unionFind.union root1 root2
    let class1 := g2.classes.get? root1 |>.getD default
    let class2 := g2.classes.get? root2 |>.getD default
    let mergedClass := class1.union class2
    { g2 with
      unionFind := uf'
      classes := g2.classes.insert root1 mergedClass
      worklist := root2 :: g2.worklist
      dirtyArr := if g2.dirtyArr.contains root1 then g2.dirtyArr
                  else g2.dirtyArr.push root1 }

def processClass (g : EGraph) (classId : EClassId) :
    (EGraph × List (EClassId × EClassId)) :=
  let (canonId, g1) := g.find classId
  match g1.classes.get? canonId with
  | none => (g1, [])
  | some eclass =>
    eclass.nodes.foldl (init := (g1, [])) fun (acc, merges) node =>
      let (canonNode, acc1) := acc.canonicalize node
      if canonNode == node then
        (acc1, merges)
      else
        let hashcons1 := acc1.hashcons.erase node
        match hashcons1.get? canonNode with
        | some existingId =>
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc1 with hashcons := hashcons2 }, (canonId, existingId) :: merges)
        | none =>
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc1 with hashcons := hashcons2 }, merges)

partial def rebuild (g : EGraph) : EGraph :=
  if g.worklist.isEmpty && g.dirtyArr.isEmpty then g
  else
    let toProcess := g.worklist ++ g.dirtyArr.toList
    let g1 : EGraph := { g with worklist := [], dirtyArr := #[] }
    let (g2, pendingMerges) := toProcess.foldl (fun (acc, merges) classId =>
      let (acc', newMerges) := processClass acc classId
      (acc', newMerges ++ merges)
    ) (g1, [])
    let g3 := pendingMerges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g2
    if g3.worklist.isEmpty && g3.dirtyArr.isEmpty then g3
    else rebuild g3

partial def computeCosts (g : EGraph) (costFn : ENode → Nat := ENode.localCost) : EGraph :=
  let getCost (classes : Std.HashMap EClassId EClass) (id : EClassId) : Nat :=
    let (canonId, _) := g.unionFind.find id
    match classes.get? canonId with
    | some ec => ec.bestCost
    | none => infinityCost
  let iterate (classes : Std.HashMap EClassId EClass) :
      (Std.HashMap EClassId EClass × Bool) :=
    classes.fold (fun (acc, changed) classId eclass =>
      let (bestCost, bestNode, nodeChanged) := eclass.nodes.foldl
        (init := (eclass.bestCost, eclass.bestNode, false))
        fun (curBest, curNode, curChanged) node =>
          let childCosts := node.children.foldl
            (fun sum cid => sum + getCost acc cid) 0
          let cost := costFn node + childCosts
          if cost < curBest then (cost, some node, true)
          else (curBest, curNode, curChanged)
      if nodeChanged then
        let updatedClass := { eclass with bestCost := bestCost, bestNode := bestNode }
        (acc.insert classId updatedClass, true)
      else
        (acc, changed)) (classes, false)
  let rec loop (classes : Std.HashMap EClassId EClass) (fuel : Nat) :
      Std.HashMap EClassId EClass :=
    if fuel == 0 then classes
    else
      let (classes', changed) := iterate classes
      if changed then loop classes' (fuel - 1)
      else classes'
  { g with classes := loop g.classes 100 }

def getClass (g : EGraph) (id : EClassId) : (Option EClass × EGraph) :=
  let (canonId, g1) := g.find id
  (g1.classes.get? canonId, g1)

structure Stats where
  numClasses : Nat
  numNodes : Nat
  unionFindSize : Nat
  worklistSize : Nat
  deriving Repr

def stats (g : EGraph) : Stats where
  numClasses := g.numClasses
  numNodes := g.numNodes
  unionFindSize := g.unionFind.size
  worklistSize := g.worklist.length

end EGraph

end AmoLean.EGraph.Verified
