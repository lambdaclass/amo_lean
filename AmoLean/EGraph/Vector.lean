/-
  AMO-Lean: E-Graph Extension for Kronecker Products
  Phase 5.4 - Matrix Expression E-Graph

  This module extends the E-graph to handle MatExpr nodes with Kronecker
  products as first-class citizens. The key insight from SPIRAL is that
  FFT can be represented with O(log N) nodes using Kronecker formulas:

    DFT_{mn} = (DFT_m ⊗ I_n) · T^{mn}_n · (I_m ⊗ DFT_n) · L^{mn}_m

  Design principles:
  - MatENodeOp stores matrix operations with child IDs (not recursive structures)
  - Dimensions (m, n) are stored in the nodes for type safety
  - Kronecker products are NOT expanded - they remain symbolic
  - E-graph saturation operates on this compact representation

  References:
  - SPIRAL: "Efficient SIMD Vectorization for Hashing in OpenSSL"
  - egg: Fast and Extensible Equality Saturation (Willsey et al.)
-/

import Std.Data.HashMap
import Std.Data.HashSet
import AmoLean.Matrix.Basic
import AmoLean.EGraph.Basic

namespace AmoLean.EGraph.Matrix

open AmoLean.Matrix (Perm MatExpr)
open AmoLean.EGraph (EClassId infiniteCost)

/-! ## Part 1: Matrix E-Node Operations -/

/-- Identifier for matrix e-classes (separate namespace from scalar e-classes) -/
abbrev MatEClassId := Nat

/-- Cost model for matrix/vector operations (SIMD-aware).
    Based on VectorCostModel from Matrix.Basic but for E-graph use. -/
structure MatCostModel where
  /-- SIMD vector width (4 for AVX2, 8 for AVX-512) -/
  simdWidth : Nat := 4

  /-- Cost of identity matrix (zero - it's free) -/
  identityCost : Nat := 0

  /-- Cost of symbolic DFT (zero - not expanded) -/
  dftSymbolicCost : Nat := 0

  /-- Cost of symbolic NTT (zero - not expanded) -/
  nttSymbolicCost : Nat := 0

  /-- Cost of twiddle factor multiplication (per element / simdWidth) -/
  twiddleCost : Nat := 1

  /-- Cost of permutation (data movement) -/
  permCost : Nat := 2

  /-- Cost of Kronecker product (zero - symbolic, not expanded) -/
  kronCost : Nat := 0

  /-- Cost of matrix composition -/
  composeCost : Nat := 1

  /-- Cost of matrix addition -/
  addCost : Nat := 1

  /-- Cost of scalar multiplication -/
  smulCost : Nat := 1

  /-- Cost of transpose -/
  transposeCost : Nat := 2

  /-- Penalty for scalar fallback (discourages expansion) -/
  scalarPenalty : Nat := 1000

  deriving Repr, Inhabited

/-- Default cost model for AVX2 -/
def defaultMatCostModel : MatCostModel := {}

/-- Permutation type for E-graph storage.
    Simplified representation that can be hashed and compared. -/
inductive PermOp where
  /-- Identity permutation on n elements -/
  | identity (n : Nat)
  /-- Stride permutation L^{mn}_n -/
  | stride (m n : Nat)
  /-- Bit-reversal permutation on 2^k elements -/
  | bitRev (k : Nat)
  /-- Swap (2 elements) -/
  | swap
  /-- Composition of two permutations -/
  | compose (p1 p2 : MatEClassId)
  /-- Inverse of a permutation -/
  | inverse (p : MatEClassId)
  /-- Tensor product of permutations -/
  | tensor (p1 p2 : MatEClassId)
  deriving Repr, BEq, Hashable, Inhabited

/-- Matrix operations for E-graph nodes.
    Each operation stores its dimensions for type safety.

    Key design: Kronecker products are first-class, NOT expanded.
    This keeps the E-graph size O(log N) for FFT of size N. -/
inductive MatENodeOp where
  /-- Identity matrix I_n -/
  | identity (n : Nat)

  /-- Zero matrix m×n -/
  | zero (m n : Nat)

  /-- Symbolic DFT matrix of size n -/
  | dft (n : Nat)

  /-- Symbolic NTT matrix in Z_p of size n -/
  | ntt (n p : Nat)

  /-- Twiddle factor matrix T^n_k (diagonal) -/
  | twiddle (n k : Nat)

  /-- Permutation matrix from permutation operation -/
  | perm (p : PermOp)

  /-- Kronecker product A ⊗ B
      Stores dimensions: (m₁, n₁) for A, (m₂, n₂) for B
      Result dimensions: (m₁*m₂, n₁*n₂) -/
  | kron (a b : MatEClassId) (m₁ n₁ m₂ n₂ : Nat)

  /-- Matrix composition A · B (apply B first, then A)
      Stores dimensions: A is m×k, B is k×n -/
  | compose (a b : MatEClassId) (m k n : Nat)

  /-- Matrix addition A + B (same dimensions m×n) -/
  | add (a b : MatEClassId) (m n : Nat)

  /-- Scalar multiplication c · A -/
  | smul (scalar : MatEClassId) (a : MatEClassId) (m n : Nat)

  /-- Transpose of a matrix -/
  | transpose (a : MatEClassId) (m n : Nat)

  /-- Conjugate transpose (for complex matrices) -/
  | conjTranspose (a : MatEClassId) (m n : Nat)

  deriving Repr, BEq, Hashable, Inhabited

/-- A matrix E-node wraps an operation. -/
structure MatENode where
  op : MatENodeOp
  deriving Repr, BEq, Hashable, Inhabited

namespace MatENode

/-- Create identity matrix node -/
def mkIdentity (n : Nat) : MatENode := ⟨.identity n⟩

/-- Create zero matrix node -/
def mkZero (m n : Nat) : MatENode := ⟨.zero m n⟩

/-- Create DFT matrix node -/
def mkDFT (n : Nat) : MatENode := ⟨.dft n⟩

/-- Create NTT matrix node -/
def mkNTT (n p : Nat) : MatENode := ⟨.ntt n p⟩

/-- Create twiddle factor node -/
def mkTwiddle (n k : Nat) : MatENode := ⟨.twiddle n k⟩

/-- Create permutation node -/
def mkPerm (p : PermOp) : MatENode := ⟨.perm p⟩

/-- Create stride permutation node -/
def mkStridePerm (m n : Nat) : MatENode := ⟨.perm (.stride m n)⟩

/-- Create bit-reversal permutation node -/
def mkBitRevPerm (k : Nat) : MatENode := ⟨.perm (.bitRev k)⟩

/-- Create Kronecker product node -/
def mkKron (a b : MatEClassId) (m₁ n₁ m₂ n₂ : Nat) : MatENode :=
  ⟨.kron a b m₁ n₁ m₂ n₂⟩

/-- Create composition node -/
def mkCompose (a b : MatEClassId) (m k n : Nat) : MatENode :=
  ⟨.compose a b m k n⟩

/-- Create addition node -/
def mkAdd (a b : MatEClassId) (m n : Nat) : MatENode :=
  ⟨.add a b m n⟩

/-- Create scalar multiplication node -/
def mkSmul (scalar a : MatEClassId) (m n : Nat) : MatENode :=
  ⟨.smul scalar a m n⟩

/-- Create transpose node -/
def mkTranspose (a : MatEClassId) (m n : Nat) : MatENode :=
  ⟨.transpose a m n⟩

/-- Get the output dimensions of a matrix node (rows, cols) -/
def dimensions : MatENode → (Nat × Nat)
  | ⟨.identity n⟩ => (n, n)
  | ⟨.zero m n⟩ => (m, n)
  | ⟨.dft n⟩ => (n, n)
  | ⟨.ntt n _⟩ => (n, n)
  | ⟨.twiddle n _⟩ => (n, n)
  | ⟨.perm (.identity n)⟩ => (n, n)
  | ⟨.perm (.stride m n)⟩ => (m * n, m * n)
  | ⟨.perm (.bitRev k)⟩ => (2^k, 2^k)
  | ⟨.perm .swap⟩ => (2, 2)
  | ⟨.perm (.compose _ _)⟩ => (0, 0)  -- Need class lookup for exact dims
  | ⟨.perm (.inverse _)⟩ => (0, 0)
  | ⟨.perm (.tensor _ _)⟩ => (0, 0)
  | ⟨.kron _ _ m₁ n₁ m₂ n₂⟩ => (m₁ * m₂, n₁ * n₂)
  | ⟨.compose _ _ m _ n⟩ => (m, n)
  | ⟨.add _ _ m n⟩ => (m, n)
  | ⟨.smul _ _ m n⟩ => (m, n)
  | ⟨.transpose _ m n⟩ => (n, m)  -- Note: transposed
  | ⟨.conjTranspose _ m n⟩ => (n, m)

/-- Get all child e-class IDs of a node -/
def children : MatENode → List MatEClassId
  | ⟨.identity _⟩ => []
  | ⟨.zero _ _⟩ => []
  | ⟨.dft _⟩ => []
  | ⟨.ntt _ _⟩ => []
  | ⟨.twiddle _ _⟩ => []
  | ⟨.perm (.identity _)⟩ => []
  | ⟨.perm (.stride _ _)⟩ => []
  | ⟨.perm (.bitRev _)⟩ => []
  | ⟨.perm .swap⟩ => []
  | ⟨.perm (.compose p1 p2)⟩ => [p1, p2]
  | ⟨.perm (.inverse p)⟩ => [p]
  | ⟨.perm (.tensor p1 p2)⟩ => [p1, p2]
  | ⟨.kron a b _ _ _ _⟩ => [a, b]
  | ⟨.compose a b _ _ _⟩ => [a, b]
  | ⟨.add a b _ _⟩ => [a, b]
  | ⟨.smul s a _ _⟩ => [s, a]
  | ⟨.transpose a _ _⟩ => [a]
  | ⟨.conjTranspose a _ _⟩ => [a]

/-- Map a function over child IDs -/
def mapChildren (f : MatEClassId → MatEClassId) : MatENode → MatENode
  | ⟨.identity n⟩ => ⟨.identity n⟩
  | ⟨.zero m n⟩ => ⟨.zero m n⟩
  | ⟨.dft n⟩ => ⟨.dft n⟩
  | ⟨.ntt n p⟩ => ⟨.ntt n p⟩
  | ⟨.twiddle n k⟩ => ⟨.twiddle n k⟩
  | ⟨.perm (.identity n)⟩ => ⟨.perm (.identity n)⟩
  | ⟨.perm (.stride m n)⟩ => ⟨.perm (.stride m n)⟩
  | ⟨.perm (.bitRev k)⟩ => ⟨.perm (.bitRev k)⟩
  | ⟨.perm .swap⟩ => ⟨.perm .swap⟩
  | ⟨.perm (.compose p1 p2)⟩ => ⟨.perm (.compose (f p1) (f p2))⟩
  | ⟨.perm (.inverse p)⟩ => ⟨.perm (.inverse (f p))⟩
  | ⟨.perm (.tensor p1 p2)⟩ => ⟨.perm (.tensor (f p1) (f p2))⟩
  | ⟨.kron a b m₁ n₁ m₂ n₂⟩ => ⟨.kron (f a) (f b) m₁ n₁ m₂ n₂⟩
  | ⟨.compose a b m k n⟩ => ⟨.compose (f a) (f b) m k n⟩
  | ⟨.add a b m n⟩ => ⟨.add (f a) (f b) m n⟩
  | ⟨.smul s a m n⟩ => ⟨.smul (f s) (f a) m n⟩
  | ⟨.transpose a m n⟩ => ⟨.transpose (f a) m n⟩
  | ⟨.conjTranspose a m n⟩ => ⟨.conjTranspose (f a) m n⟩

/-- Calculate local cost of a node (without counting children) -/
def localCost (cm : MatCostModel := defaultMatCostModel) : MatENode → Nat
  | ⟨.identity _⟩ => cm.identityCost
  | ⟨.zero _ _⟩ => 0
  | ⟨.dft _⟩ => cm.dftSymbolicCost
  | ⟨.ntt _ _⟩ => cm.nttSymbolicCost
  | ⟨.twiddle n _⟩ => (n / cm.simdWidth) * cm.twiddleCost
  | ⟨.perm _⟩ => cm.permCost
  | ⟨.kron _ _ _ _ _ _⟩ => cm.kronCost
  | ⟨.compose _ _ _ _ _⟩ => cm.composeCost
  | ⟨.add _ _ _ _⟩ => cm.addCost
  | ⟨.smul _ _ _ _⟩ => cm.smulCost
  | ⟨.transpose _ _ _⟩ => cm.transposeCost
  | ⟨.conjTranspose _ _ _⟩ => cm.transposeCost

end MatENode

/-! ## Part 2: Matrix E-Class -/

/-- A matrix equivalence class contains:
    - nodes: set of equivalent matrix e-nodes
    - bestCost: minimum known cost
    - bestNode: node with minimum cost
    - dims: dimensions (rows, cols) of matrices in this class -/
structure MatEClass where
  nodes : Std.HashSet MatENode
  bestCost : Nat := infiniteCost
  bestNode : Option MatENode := none
  dims : Nat × Nat := (0, 0)
  deriving Inhabited

namespace MatEClass

/-- Create a class with a single node -/
def singleton (node : MatENode) (cost : Nat := infiniteCost) : MatEClass :=
  { nodes := Std.HashSet.empty.insert node
  , bestCost := cost
  , bestNode := some node
  , dims := node.dimensions }

/-- Add a node to the class -/
def addNode (ec : MatEClass) (node : MatENode) : MatEClass :=
  { ec with nodes := ec.nodes.insert node }

/-- Update best node if new cost is lower -/
def updateBest (ec : MatEClass) (node : MatENode) (cost : Nat) : MatEClass :=
  if cost < ec.bestCost then
    { ec with bestCost := cost, bestNode := some node }
  else
    ec

/-- Union two e-classes -/
def union (ec1 ec2 : MatEClass) : MatEClass :=
  let merged := ec1.nodes.fold (init := ec2.nodes) fun acc n => acc.insert n
  { nodes := merged
  , bestCost := min ec1.bestCost ec2.bestCost
  , bestNode := if ec1.bestCost ≤ ec2.bestCost then ec1.bestNode else ec2.bestNode
  , dims := ec1.dims }

/-- Number of nodes in the class -/
def size (ec : MatEClass) : Nat := ec.nodes.size

end MatEClass

/-! ## Part 3: Matrix Union-Find -/

/-- Union-Find for matrix e-classes (same structure as scalar) -/
structure MatUnionFind where
  parent : Array MatEClassId
  deriving Inhabited

namespace MatUnionFind

def empty : MatUnionFind := ⟨#[]⟩

def init (n : Nat) : MatUnionFind := ⟨Array.range n⟩

def add (uf : MatUnionFind) : (MatEClassId × MatUnionFind) :=
  let newId := uf.parent.size
  (newId, ⟨uf.parent.push newId⟩)

partial def find (uf : MatUnionFind) (id : MatEClassId) : (MatEClassId × MatUnionFind) :=
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

def union (uf : MatUnionFind) (id1 id2 : MatEClassId) : MatUnionFind :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  if root1 == root2 then
    uf2
  else if root2 < uf2.parent.size then
    ⟨uf2.parent.set! root2 root1⟩
  else
    uf2

def equiv (uf : MatUnionFind) (id1 id2 : MatEClassId) : (Bool × MatUnionFind) :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  (root1 == root2, uf2)

def size (uf : MatUnionFind) : Nat := uf.parent.size

end MatUnionFind

/-! ## Part 4: Matrix E-Graph -/

/-- The main Matrix E-Graph structure.

    Similar to scalar EGraph but for matrix expressions with Kronecker products.
    Key feature: Kronecker products remain symbolic, keeping size O(log N). -/
structure MatEGraph where
  unionFind : MatUnionFind
  hashcons : Std.HashMap MatENode MatEClassId
  classes : Std.HashMap MatEClassId MatEClass
  worklist : List MatEClassId
  dirty : Std.HashSet MatEClassId
  deriving Inhabited

namespace MatEGraph

/-- Create empty matrix E-graph -/
def empty : MatEGraph :=
  { unionFind := MatUnionFind.empty
  , hashcons := Std.HashMap.empty
  , classes := Std.HashMap.empty
  , worklist := []
  , dirty := Std.HashSet.empty }

/-- Number of e-classes -/
def numClasses (g : MatEGraph) : Nat := g.classes.size

/-- Number of e-nodes -/
def numNodes (g : MatEGraph) : Nat := g.hashcons.size

/-- Find canonical ID -/
def find (g : MatEGraph) (id : MatEClassId) : (MatEClassId × MatEGraph) :=
  let (canonical, uf') := g.unionFind.find id
  (canonical, { g with unionFind := uf' })

/-- Check if two IDs are equivalent -/
def equiv (g : MatEGraph) (id1 id2 : MatEClassId) : (Bool × MatEGraph) :=
  let (eq, uf') := g.unionFind.equiv id1 id2
  (eq, { g with unionFind := uf' })

/-- Canonicalize a node (replace children with canonical IDs) -/
def canonicalize (g : MatEGraph) (node : MatENode) : (MatENode × MatEGraph) :=
  let children := node.children
  if children.isEmpty then
    (node, g)
  else
    let (canonChildren, g') := children.foldl
      (fun (acc, gr) childId =>
        let (canonId, gr') := gr.find childId
        (acc ++ [canonId], gr'))
      ([], g)
    -- Rebuild node with canonical children
    let canonNode := match node.op, canonChildren with
      | .kron _ _ m₁ n₁ m₂ n₂, [a, b] => MatENode.mkKron a b m₁ n₁ m₂ n₂
      | .compose _ _ m k n, [a, b] => MatENode.mkCompose a b m k n
      | .add _ _ m n, [a, b] => MatENode.mkAdd a b m n
      | .smul _ _ m n, [s, a] => MatENode.mkSmul s a m n
      | .transpose _ m n, [a] => MatENode.mkTranspose a m n
      | .conjTranspose _ m n, [a] => ⟨.conjTranspose a m n⟩
      | .perm (.compose _ _), [p1, p2] => ⟨.perm (.compose p1 p2)⟩
      | .perm (.inverse _), [p] => ⟨.perm (.inverse p)⟩
      | .perm (.tensor _ _), [p1, p2] => ⟨.perm (.tensor p1 p2)⟩
      | _, _ => node  -- No change for other cases
    (canonNode, g')

/-- Add a node to the E-graph. Returns the e-class ID. -/
def add (g : MatEGraph) (node : MatENode) : (MatEClassId × MatEGraph) :=
  let (canonNode, g1) := g.canonicalize node
  match g1.hashcons.get? canonNode with
  | some existingId =>
    let (canonId, g2) := g1.find existingId
    (canonId, g2)
  | none =>
    let (newId, uf') := g1.unionFind.add
    let newClass := MatEClass.singleton canonNode
    let g2 := { g1 with
      unionFind := uf'
      hashcons := g1.hashcons.insert canonNode newId
      classes := g1.classes.insert newId newClass }
    (newId, g2)

/-- Merge two e-classes -/
def merge (g : MatEGraph) (id1 id2 : MatEClassId) : MatEGraph :=
  let (root1, g1) := g.find id1
  let (root2, g2) := g1.find id2
  if root1 == root2 then g2
  else
    let uf' := g2.unionFind.union root1 root2
    let class1 := g2.classes.get? root1 |>.getD (MatEClass.singleton (MatENode.mkIdentity 0))
    let class2 := g2.classes.get? root2 |>.getD (MatEClass.singleton (MatENode.mkIdentity 0))
    let mergedClass := class1.union class2
    { g2 with
      unionFind := uf'
      classes := g2.classes.insert root1 mergedClass
      worklist := root2 :: g2.worklist
      dirty := g2.dirty.insert root1 }

/-- Get the e-class for an ID -/
def getClass (g : MatEGraph) (id : MatEClassId) : (Option MatEClass × MatEGraph) :=
  let (canonId, g1) := g.find id
  (g1.classes.get? canonId, g1)

/-! ## Part 5: Rebuild -/

private def processClass (g : MatEGraph) (classId : MatEClassId) : (MatEGraph × List (MatEClassId × MatEClassId)) :=
  let (canonId, g1) := g.find classId
  match g1.classes.get? canonId with
  | none => (g1, [])
  | some eclass =>
    eclass.nodes.fold (init := (g1, [])) fun (acc, merges) node =>
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

/-- Rebuild the E-graph to restore invariants -/
partial def rebuild (g : MatEGraph) : MatEGraph :=
  if g.worklist.isEmpty && g.dirty.isEmpty then g
  else
    let toProcess := g.worklist ++ g.dirty.toList
    let g1 := { g with worklist := [], dirty := Std.HashSet.empty }
    let (g2, pendingMerges) := toProcess.foldl (fun (acc, merges) classId =>
      let (acc', newMerges) := processClass acc classId
      (acc', newMerges ++ merges)
    ) (g1, [])
    let g3 := pendingMerges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g2
    if g3.worklist.isEmpty && g3.dirty.isEmpty then g3
    else rebuild g3

/-! ## Part 6: Add MatExpr to E-Graph -/

/-- Convert Perm to PermOp.
    Uses explicit pattern matching to handle dependent types correctly. -/
def permToPermOp (n : Nat) (p : Perm n) : PermOp :=
  match p with
  | .identity => .identity n
  | .stride m n' => .stride m n'
  | .bitRev k => .bitRev k
  | .swap => .swap
  | .compose _ _ => .identity n  -- Simplified for now
  | .inverse _ => .identity n
  | .tensor _ _ => .identity n  -- Simplified for now

/-- Add a MatExpr to the E-graph recursively.
    Note: This handles the symbolic representation without expanding Kronecker products.

    The function takes explicit dimension parameters to avoid dependent type issues. -/
def addMatExpr (g : MatEGraph) (m n : Nat) : MatExpr α m n → (MatEClassId × MatEGraph)
  | .identity n' => g.add (MatENode.mkIdentity n')
  | .zero m' n' => g.add (MatENode.mkZero m' n')
  | .dft n' => g.add (MatENode.mkDFT n')
  | .ntt n' p => g.add (MatENode.mkNTT n' p)
  | .twiddle n' k => g.add (MatENode.mkTwiddle n' k)
  | .perm p => g.add (MatENode.mkPerm (permToPermOp n p))
  | @MatExpr.kron _ m₁ n₁ m₂ n₂ a b =>
    let (idA, g1) := addMatExpr g m₁ n₁ a
    let (idB, g2) := addMatExpr g1 m₂ n₂ b
    g2.add (MatENode.mkKron idA idB m₁ n₁ m₂ n₂)
  | @MatExpr.compose _ m' k n' a b =>
    let (idA, g1) := addMatExpr g m' k a
    let (idB, g2) := addMatExpr g1 k n' b
    g2.add (MatENode.mkCompose idA idB m' k n')
  | @MatExpr.add _ m' n' a b =>
    let (idA, g1) := addMatExpr g m' n' a
    let (idB, g2) := addMatExpr g1 m' n' b
    g2.add (MatENode.mkAdd idA idB m' n')
  | @MatExpr.smul _ m' n' _ a =>
    let (idA, g1) := addMatExpr g m' n' a
    let (scalarId, g2) := g1.add (MatENode.mkIdentity 1)
    g2.add (MatENode.mkSmul scalarId idA m' n')
  | @MatExpr.transpose _ m' n' a =>
    let (idA, g1) := addMatExpr g m' n' a
    g1.add (MatENode.mkTranspose idA m' n')
  | @MatExpr.conjTranspose _ m' n' a =>
    let (idA, g1) := addMatExpr g m' n' a
    g1.add ⟨.conjTranspose idA m' n'⟩
  | .diag _ =>
    g.add (MatENode.mkIdentity n)
  | .scalar _ =>
    g.add (MatENode.mkIdentity 1)

/-- Create a MatEGraph from a MatExpr -/
def fromMatExpr (e : MatExpr α m n) : (MatEClassId × MatEGraph) :=
  addMatExpr empty m n e

/-! ## Part 7: Cost Calculation -/

/-- Calculate cost of a node given child costs -/
def nodeCost (cm : MatCostModel) (childCosts : MatEClassId → Nat) : MatENode → Nat
  | node =>
    let localCost := node.localCost cm
    let childCost := node.children.foldl (fun acc id => acc + childCosts id) 0
    localCost + childCost

/-- Compute costs for all e-classes (bottom-up) -/
partial def computeCosts (g : MatEGraph) (cm : MatCostModel := defaultMatCostModel) : MatEGraph :=
  let getCost (classes : Std.HashMap MatEClassId MatEClass) (id : MatEClassId) : Nat :=
    let (canonId, _) := g.unionFind.find id
    match classes.get? canonId with
    | some ec => ec.bestCost
    | none => infiniteCost

  let iterate (classes : Std.HashMap MatEClassId MatEClass) : (Std.HashMap MatEClassId MatEClass × Bool) :=
    classes.fold (init := (classes, false)) fun (acc, changed) classId eclass =>
      let (bestCost, bestNode, nodeChanged) := eclass.nodes.fold
        (init := (eclass.bestCost, eclass.bestNode, false))
        fun (curBest, curNode, curChanged) node =>
          let cost := nodeCost cm (getCost acc) node
          if cost < curBest then (cost, some node, true)
          else (curBest, curNode, curChanged)
      if nodeChanged then
        let updatedClass := { eclass with bestCost := bestCost, bestNode := bestNode }
        (acc.insert classId updatedClass, true)
      else
        (acc, changed)

  let rec loop (classes : Std.HashMap MatEClassId MatEClass) (fuel : Nat) : Std.HashMap MatEClassId MatEClass :=
    if fuel == 0 then classes
    else
      let (classes', changed) := iterate classes
      if changed then loop classes' (fuel - 1)
      else classes'

  { g with classes := loop g.classes 100 }

/-! ## Part 8: Statistics -/

/-- Statistics for the matrix E-graph -/
structure MatStats where
  numClasses : Nat
  numNodes : Nat
  unionFindSize : Nat
  worklistSize : Nat
  deriving Repr

def stats (g : MatEGraph) : MatStats :=
  { numClasses := g.numClasses
  , numNodes := g.numNodes
  , unionFindSize := g.unionFind.size
  , worklistSize := g.worklist.length }

end MatEGraph

/-! ## Part 9: Tests -/

section Tests

open MatEGraph

-- Test 1: Create E-graph with identity matrix
#eval do
  let (id, g) := MatEGraph.empty.add (MatENode.mkIdentity 4)
  IO.println s!"Test 1: Identity matrix I_4"
  IO.println s!"  Root ID: {id}"
  IO.println s!"  Classes: {g.numClasses}"
  IO.println s!"  Nodes: {g.numNodes}"

-- Test 2: Create DFT matrix
#eval do
  let (id, g) := MatEGraph.empty.add (MatENode.mkDFT 8)
  IO.println s!"Test 2: DFT_8"
  IO.println s!"  Root ID: {id}"
  IO.println s!"  Classes: {g.numClasses}"

-- Test 3: Kronecker product DFT_2 ⊗ I_4
#eval do
  let g0 := MatEGraph.empty
  let (dft2Id, g1) := g0.add (MatENode.mkDFT 2)
  let (i4Id, g2) := g1.add (MatENode.mkIdentity 4)
  let (kronId, g3) := g2.add (MatENode.mkKron dft2Id i4Id 2 2 4 4)
  IO.println s!"Test 3: DFT_2 ⊗ I_4"
  IO.println s!"  DFT_2 ID: {dft2Id}"
  IO.println s!"  I_4 ID: {i4Id}"
  IO.println s!"  Kron ID: {kronId}"
  IO.println s!"  Total Classes: {g3.numClasses}"
  IO.println s!"  Total Nodes: {g3.numNodes}"

-- Test 4: FFT Cooley-Tukey structure (DFT_8 decomposition)
#eval do
  let g0 := MatEGraph.empty
  -- Build: (DFT_2 ⊗ I_4) · T · (I_2 ⊗ DFT_4) · L
  let (dft2, g1) := g0.add (MatENode.mkDFT 2)
  let (i4, g2) := g1.add (MatENode.mkIdentity 4)
  let (kron1, g3) := g2.add (MatENode.mkKron dft2 i4 2 2 4 4)  -- DFT_2 ⊗ I_4

  let (twiddle, g4) := g3.add (MatENode.mkTwiddle 8 4)  -- T^8_4

  let (i2, g5) := g4.add (MatENode.mkIdentity 2)
  let (dft4, g6) := g5.add (MatENode.mkDFT 4)
  let (kron2, g7) := g6.add (MatENode.mkKron i2 dft4 2 2 4 4)  -- I_2 ⊗ DFT_4

  let (stride, g8) := g7.add (MatENode.mkStridePerm 2 4)  -- L^8_4

  -- Compose: (kron1) · (twiddle · (kron2 · stride))
  let (comp1, g9) := g8.add (MatENode.mkCompose kron2 stride 8 8 8)
  let (comp2, g10) := g9.add (MatENode.mkCompose twiddle comp1 8 8 8)
  let (comp3, g11) := g10.add (MatENode.mkCompose kron1 comp2 8 8 8)

  IO.println s!"Test 4: FFT Cooley-Tukey DFT_8 = (DFT_2 ⊗ I_4) · T · (I_2 ⊗ DFT_4) · L"
  IO.println s!"  Final composition ID: {comp3}"
  IO.println s!"  Total Classes: {g11.numClasses}"
  IO.println s!"  Total Nodes: {g11.numNodes}"
  IO.println s!"  (Expected: O(log N) ≈ 10 nodes for N=8)"

-- Test 5: Merge test - DFT_8 should equal its Cooley-Tukey decomposition
#eval do
  let g0 := MatEGraph.empty
  -- Add DFT_8 directly
  let (dft8, g1) := g0.add (MatENode.mkDFT 8)

  -- Add Cooley-Tukey decomposition
  let (dft2, g2) := g1.add (MatENode.mkDFT 2)
  let (i4, g3) := g2.add (MatENode.mkIdentity 4)
  let (kron1, g4) := g3.add (MatENode.mkKron dft2 i4 2 2 4 4)
  let (twiddle, g5) := g4.add (MatENode.mkTwiddle 8 4)
  let (i2, g6) := g5.add (MatENode.mkIdentity 2)
  let (dft4, g7) := g6.add (MatENode.mkDFT 4)
  let (kron2, g8) := g7.add (MatENode.mkKron i2 dft4 2 2 4 4)
  let (stride, g9) := g8.add (MatENode.mkStridePerm 2 4)
  let (comp1, g10) := g9.add (MatENode.mkCompose kron2 stride 8 8 8)
  let (comp2, g11) := g10.add (MatENode.mkCompose twiddle comp1 8 8 8)
  let (cooleyTukey, g12) := g11.add (MatENode.mkCompose kron1 comp2 8 8 8)

  IO.println s!"Test 5: Merge DFT_8 with Cooley-Tukey decomposition"
  IO.println s!"  DFT_8 ID: {dft8}"
  IO.println s!"  Cooley-Tukey ID: {cooleyTukey}"
  IO.println s!"  Before merge: {g12.numClasses} classes"

  -- Merge: assert DFT_8 = Cooley-Tukey decomposition
  let g13 := g12.merge dft8 cooleyTukey
  let g14 := g13.rebuild

  IO.println s!"  After merge+rebuild: {g14.numClasses} classes"
  let (eq, _) := g14.equiv dft8 cooleyTukey
  IO.println s!"  Are they equivalent? {eq}"

end Tests

end AmoLean.EGraph.Matrix
