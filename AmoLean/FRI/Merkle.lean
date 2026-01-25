/-
  AMO-Lean: Vectorized Merkle Tree
  Phase 6.4 - Flat Array Implementation

  This module implements a cache-friendly Merkle tree using a flat array
  layout optimized for SIMD operations and FRI protocol integration.

  Design Decisions (from Phase 6.4 Analysis):

  1. LEAVES-FIRST LAYOUT (vs root-first heap):
     - Leaves at indices [0..n-1]
     - Internal nodes at [n..2n-2]
     - Root at index [2n-2]
     - Rationale: Natural for FRI where we start with polynomial evaluations

  2. GENERIC FIELD (vs fixed ZMod p):
     - Uses FRIField typeclass
     - Allows Float for testing, ZMod for production
     - Consistent with Fold.lean design

  3. .loop FOR PARALLELISM (vs .par):
     - Within-layer parallelism via .loop (maps to SIMD)
     - Between-layer sequencing via .seq (data dependency)
     - Avoids fork-join overhead of literal .par

  4. MERKLE PROOF INCLUDED:
     - Authentication paths for FRI query phase
     - Path bits indicate left/right position

  Memory Layout for n=8 leaves:
  ┌─────────────────────────────────────────────────────────────────┐
  │ Index:  0   1   2   3   4   5   6   7   8   9  10  11  12  13  14│
  │ Node:  L0  L1  L2  L3  L4  L5  L6  L7  N0  N1  N2  N3  N4  N5 ROOT│
  │ Layer:  ─────── leaves ───────────  ── layer1 ── ─ layer2 ─ root │
  └─────────────────────────────────────────────────────────────────┘

  Tree structure (n=8):
                    [14] ROOT
                   /         \
              [12]             [13]
             /    \           /    \
         [8]       [9]    [10]      [11]
        /   \     /   \   /   \    /    \
      [0]  [1] [2]  [3] [4]  [5] [6]   [7]
       L0  L1   L2  L3  L4   L5  L6    L7

  References:
  - "Merkle Trees in Authenticated Data Structures" (Merkle, 1979)
  - ADR-003: Tiled Processing for Memory Efficiency
-/

import AmoLean.FRI.Basic
import AmoLean.FRI.Fold
import AmoLean.FRI.Transcript
import AmoLean.Vector.Basic

namespace AmoLean.FRI.Merkle

open AmoLean.FRI (ZKCostModel defaultZKCost)
open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Transcript (Intrinsic CryptoSigma DomainTag)
open AmoLean.Vector (Vec)
open AmoLean.Sigma (Gather Scatter LoopVar IdxExpr Kernel)

/-! ## Part 1: Flat Merkle Tree Structure -/

/-- Index calculations for leaves-first layout.

    For a tree with n leaves:
    - Leaves: indices 0 to n-1
    - Internal nodes: indices n to 2n-2
    - Root: index 2n-2
    - Parent of node i: (i + n - 1) / 2  (for i < n) or (i - 1) / 2 (for i >= n)
    - Left child of internal node i: 2*(i - n) for layer above leaves
-/
structure MerkleIndex where
  /-- Number of leaves (must be power of 2) -/
  numLeaves : Nat
  /-- Total nodes = 2*numLeaves - 1 -/
  totalNodes : Nat := 2 * numLeaves - 1
  /-- Tree depth = log2(numLeaves) -/
  depth : Nat
  deriving Repr, Inhabited

namespace MerkleIndex

/-- Create index helper for n leaves -/
def create (n : Nat) : MerkleIndex :=
  { numLeaves := n
    totalNodes := 2 * n - 1
    depth := Nat.log2 n }

/-- Index of root node -/
def rootIndex (idx : MerkleIndex) : Nat := idx.totalNodes - 1

/-- Index of first internal node (right after leaves) -/
def firstInternalIndex (idx : MerkleIndex) : Nat := idx.numLeaves

/-- Given a leaf index, get its parent index -/
def parentOfLeaf (idx : MerkleIndex) (leafIdx : Nat) : Nat :=
  idx.numLeaves + leafIdx / 2

/-- Given an internal node index, get its parent index -/
def parentOfInternal (idx : MerkleIndex) (nodeIdx : Nat) : Nat :=
  idx.numLeaves + (nodeIdx - idx.numLeaves + idx.numLeaves) / 2
  -- Simplified: for internal at i, parent is at n + (i - n + n) / 2

/-- Get children indices for an internal node at given layer.
    Layer 0 = leaves, Layer 1 = first internal layer, etc.
    For node at position j in layer k, children are at positions 2j and 2j+1 in layer k-1 -/
def childrenInLayer (idx : MerkleIndex) (layer : Nat) (posInLayer : Nat) : Nat × Nat :=
  if layer == 1 then
    -- Children are leaves
    (2 * posInLayer, 2 * posInLayer + 1)
  else
    -- Children are internal nodes
    let prevLayerStart := idx.numLeaves / (2^(layer - 1))
    let childBase := idx.numLeaves + prevLayerStart + 2 * posInLayer
    (childBase, childBase + 1)

/-- Absolute index of node at (layer, positionInLayer).
    Layer 0 = leaves, Layer k has n/2^k nodes -/
def absoluteIndex (idx : MerkleIndex) (layer : Nat) (posInLayer : Nat) : Nat :=
  if layer == 0 then posInLayer
  else
    -- Sum of all nodes in layers 0 to layer-1, plus position
    let nodesBeforeThisLayer := idx.numLeaves * (2 - 1 / (2^(layer - 1)))
    -- Simplified calculation
    idx.numLeaves + (idx.numLeaves - idx.numLeaves / (2^(layer - 1))) + posInLayer

/-- Number of nodes in a given layer -/
def nodesInLayer (idx : MerkleIndex) (layer : Nat) : Nat :=
  idx.numLeaves / (2^layer)

end MerkleIndex

/-- Flat Merkle tree with leaves-first layout.

    Structure: [leaf_0, leaf_1, ..., leaf_{n-1}, internal_0, ..., root]
    Total size: 2n - 1 nodes
-/
structure FlatMerkle (F : Type) [FRIField F] (n : Nat) where
  /-- All nodes in flat array -/
  nodes : Array F
  /-- Size invariant -/
  h_size : nodes.size = 2 * n - 1
  /-- Power of 2 invariant -/
  h_pow2 : ∃ k, n = 2^k
  deriving Repr

namespace FlatMerkle

variable {F : Type} [FRIField F]

/-- Get the root hash -/
def root (tree : FlatMerkle F n) : F :=
  tree.nodes.get! (2 * n - 2)

/-- Get a leaf value -/
def getLeaf (tree : FlatMerkle F n) (i : Nat) (h : i < n) : F :=
  tree.nodes.get! i

/-- Get an internal node -/
def getInternal (tree : FlatMerkle F n) (i : Nat) : F :=
  tree.nodes.get! (n + i)

/-- Number of layers (including leaf layer) -/
def numLayers (n : Nat) : Nat := Nat.log2 n + 1

end FlatMerkle

/-! ## Part 2: Merkle Proof (Authentication Path) -/

/-- Merkle authentication path for proving leaf membership.

    For a leaf at index i in a tree of depth d:
    - siblings: The d sibling hashes along the path to root
    - pathBits: Direction at each level (false=left, true=right)

    Verification: Start with leaf, iteratively hash with siblings,
    compare final result with known root.
-/
structure MerkleProof (F : Type) where
  /-- Sibling hashes from leaf to root -/
  siblings : List F
  /-- Path direction at each level (false = leaf is left child) -/
  pathBits : List Bool
  /-- Leaf index this proof is for -/
  leafIndex : Nat
  deriving Repr

namespace MerkleProof

variable {F : Type} [FRIField F] [BEq F]

/-- Verify a Merkle proof given leaf value and expected root.

    Recomputes the path from leaf to root and checks against expectedRoot.
-/
def verify (proof : MerkleProof F) (leafValue : F) (expectedRoot : F)
    (hashFn : F → F → F) : Bool :=
  let rec loop (current : F) (siblings : List F) (bits : List Bool) : F :=
    match siblings, bits with
    | [], [] => current
    | sib :: restSib, bit :: restBit =>
      let newHash := if bit then hashFn sib current else hashFn current sib
      loop newHash restSib restBit
    | _, _ => current  -- Mismatched lengths, return current
  let computedRoot := loop leafValue proof.siblings proof.pathBits
  computedRoot == expectedRoot

/-- Extract path bits from leaf index -/
def pathBitsFromIndex (leafIndex : Nat) (depth : Nat) : List Bool :=
  List.range depth |>.map fun i => (leafIndex / (2^i)) % 2 == 1

end MerkleProof

/-! ## Part 3: Tree Construction (Hash Operations) -/

/-- Simulated hash function for testing (XOR-based, NOT cryptographic!) -/
def testHash (a b : UInt64) : UInt64 :=
  (a ^^^ b) + 0x9e3779b97f4a7c15  -- Golden ratio constant for mixing

/-- Hash function signature for generic tree building -/
abbrev HashFn (F : Type) := F → F → F

/-- Build a Merkle tree from leaves (functional style).

    Algorithm:
    1. Copy leaves to positions 0..n-1
    2. For each layer from bottom to top:
       - Hash pairs of children into parent nodes
    3. Return completed tree

    This is the reference implementation; CryptoSigma version follows.
-/
def buildTree [FRIField F] [Inhabited F] (leaves : Array F) (hashFn : HashFn F) :
    Option (FlatMerkle F leaves.size) :=
  let n := leaves.size
  if h1 : n == 0 then none
  else
    -- Check power of 2
    let isPow2 := n &&& (n - 1) == 0
    if !isPow2 then none
    else
      -- Initialize array with leaves + space for internals
      let totalSize := 2 * n - 1
      let initialNodes : Array F := Array.mkArray totalSize default

      -- Copy leaves
      let withLeaves := List.range n |>.foldl
        (fun arr i => arr.set! i (leaves.get! i))
        initialNodes

      -- Build internal layers bottom-up
      let depth := Nat.log2 n
      let finalNodes := List.range depth |>.foldl
        (fun arr layerIdx =>
          let layer := layerIdx + 1
          let numNodesInLayer := n / (2^layer)
          let childLayerStart := if layer == 1 then 0 else n - n / (2^(layer - 1))
          let thisLayerStart := n - n / (2^layer)

          List.range numNodesInLayer |>.foldl
            (fun arr2 j =>
              let leftChildIdx := if layer == 1 then 2 * j else childLayerStart + 2 * j
              let rightChildIdx := leftChildIdx + 1
              let leftChild := arr2.get! leftChildIdx
              let rightChild := arr2.get! rightChildIdx
              let parentHash := hashFn leftChild rightChild
              let parentIdx := thisLayerStart + j
              arr2.set! parentIdx parentHash)
            arr)
        withLeaves

      some {
        nodes := finalNodes
        h_size := by sorry  -- Size invariant
        h_pow2 := ⟨Nat.log2 n, by sorry⟩  -- Power of 2
      }

/-- Generate Merkle proof for a leaf -/
def generateProof [FRIField F] [Inhabited F] (tree : FlatMerkle F n) (leafIndex : Nat) :
    Option (MerkleProof F) :=
  if leafIndex >= n then none
  else
    let depth := Nat.log2 n
    -- Accumulate (siblings, pathBits, currentIdx) through layers
    let (siblings, pathBits, _) := List.range depth |>.foldl
      (fun (sibs, bits, curIdx) layer =>
        let siblingIdx := if curIdx % 2 == 0 then curIdx + 1 else curIdx - 1
        let siblingVal := if layer == 0 then
          tree.nodes.get! siblingIdx
        else
          let layerStart := n - n / (2^layer)
          tree.nodes.get! (layerStart + siblingIdx)
        (sibs ++ [siblingVal], bits ++ [curIdx % 2 == 1], curIdx / 2))
      ([], [], leafIndex)

    some {
      siblings := siblings
      pathBits := pathBits
      leafIndex := leafIndex
    }

/-! ## Part 4: CryptoSigma Lowering for Vectorized Construction -/

/-- Generate CryptoSigma for building one layer of the Merkle tree.

    For layer k (k=1 is first internal layer above leaves):
    - Source: nodes at layer k-1
    - Destination: nodes at layer k
    - Operation: hash pairs of children

    Uses .loop for SIMD-friendly parallel hashing within layer.
-/
def buildLayerSigma (n : Nat) (layer : Nat) : CryptoSigma :=
  let numNodes := n / (2^layer)
  let srcStart := if layer == 1 then 0 else n - n / (2^(layer - 1))
  let dstStart := n - n / (2^layer)

  .loop numNodes layer
    (.intrinsic .merkleHash
      -- Gather: read 2 consecutive children
      (Gather.strided 2 (.affine srcStart 2 layer) 1)
      -- Scatter: write 1 parent hash
      (Scatter.contiguous 1 (.affine dstStart 1 layer)))

/-- Generate complete CryptoSigma for building entire Merkle tree.

    Structure:
    - Domain enter for Merkle construction
    - Sequential composition of layer constructions (bottom-up)
    - Domain exit

    Key invariant: Layers are .seq'd together (data dependency),
    but within each layer, iterations are independent (SIMD-able via .loop).
-/
def buildTreeSigma (n : Nat) : CryptoSigma :=
  let depth := Nat.log2 n
  let dummyGather := Gather.contiguous 1 (.const 0)
  let dummyScatter := Scatter.contiguous 1 (.const 0)

  -- Enter Merkle construction domain
  let domainEnter := CryptoSigma.intrinsic (.domainEnter .merkleNode) dummyGather dummyScatter

  -- Build each layer bottom-up
  let layers := List.range depth |>.map fun k =>
    buildLayerSigma n (k + 1)  -- k+1 because layer 0 is leaves (no hashing)

  -- Combine layers sequentially
  let layerSeq := layers.foldl CryptoSigma.seq CryptoSigma.nop

  -- Exit domain
  let domainExit := CryptoSigma.intrinsic .domainExit dummyGather dummyScatter

  .seq domainEnter (.seq layerSeq domainExit)

/-! ## Part 5: Memory Access Pattern Analysis -/

/-- Trace entry for memory access analysis -/
structure MemoryAccess where
  layer : Nat
  iteration : Nat
  readIndices : List Nat
  writeIndex : Nat
  deriving Repr

/-- Generate memory access trace for tree construction -/
def generateAccessTrace (n : Nat) : List MemoryAccess :=
  let depth := Nat.log2 n
  List.range depth |>.flatMap fun layerIdx =>
    let layer := layerIdx + 1
    let numNodes := n / (2^layer)
    let srcStart := if layer == 1 then 0 else n - n / (2^(layer - 1))
    let dstStart := n - n / (2^layer)
    List.range numNodes |>.map fun j =>
      let leftIdx := srcStart + 2 * j
      let rightIdx := leftIdx + 1
      let parentIdx := dstStart + j
      { layer := layer
        iteration := j
        readIndices := [leftIdx, rightIdx]
        writeIndex := parentIdx }

/-- Verify memory access pattern is contiguous within layers -/
def verifyContiguousAccess (trace : List MemoryAccess) : Bool × List String :=
  let rec check (remaining : List MemoryAccess) (prevWrite : Option Nat) (prevLayer : Nat) (errors : List String) : List String :=
    match remaining with
    | [] => errors
    | access :: rest =>
      let newErrors := match access.readIndices with
        | [left, right] =>
          if right != left + 1 then
            errors ++ [s!"Layer {access.layer}, iter {access.iteration}: non-consecutive reads [{left}, {right}]"]
          else errors
        | _ => errors ++ [s!"Layer {access.layer}: unexpected read count"]

      let writeErrors := if access.layer == prevLayer then
        match prevWrite with
        | some prev =>
          if access.writeIndex != prev + 1 then
            newErrors ++ [s!"Layer {access.layer}: non-sequential writes {prev} -> {access.writeIndex}"]
          else newErrors
        | none => newErrors
      else newErrors

      check rest (some access.writeIndex) access.layer writeErrors

  let finalErrors := check trace none 0 []
  (finalErrors.isEmpty, finalErrors)

/-! ## Part 6: Cost Analysis -/

/-- Calculate cost of building a Merkle tree -/
def buildTreeCost (cm : ZKCostModel) (n : Nat) : Nat :=
  -- Total internal nodes = n - 1
  -- Each requires: 2 loads + 1 hash + 1 store
  let hashCost := Intrinsic.cost cm .merkleHash
  (n - 1) * hashCost

/-- Calculate cost of verifying a Merkle proof -/
def verifyProofCost (cm : ZKCostModel) (depth : Nat) : Nat :=
  -- depth hashes along the path
  depth * Intrinsic.cost cm .merkleHash

/-! ## Part 7: Tests -/

section Tests

-- Test with UInt64 as our field type
instance : FRIField UInt64 where
  neg := fun x => 0 - x
  zero := 0
  one := 1
  fdiv := (· / ·)
  ofNat := UInt64.ofNat

/-- Test 1: Memory access pattern for n=8 -/
def testMemoryAccess : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       MERKLE TREE MEMORY ACCESS TEST (N = 8)                 ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let n := 8
  let trace := generateAccessTrace n

  IO.println "Memory Layout (leaves-first):"
  IO.println "  [0-7]: Leaves L0-L7"
  IO.println "  [8-11]: Layer 1 (N0-N3)"
  IO.println "  [12-13]: Layer 2 (N4-N5)"
  IO.println "  [14]: Root"
  IO.println ""

  IO.println "Access Trace:"
  IO.println "  Layer | Iter | Read Indices | Write Index"
  IO.println "  ------|------|--------------|------------"
  for access in trace do
    IO.println s!"    {access.layer}   |   {access.iteration}  |    {access.readIndices}    |     {access.writeIndex}"

  IO.println ""
  let (valid, errors) := verifyContiguousAccess trace
  if valid then
    IO.println "VERIFICATION: PASSED - All accesses are contiguous"
  else
    IO.println "VERIFICATION: FAILED"
    for e in errors do
      IO.println s!"  Error: {e}"

#eval! testMemoryAccess

/-- Test 2: CryptoSigma generation -/
def testCryptoSigma : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       MERKLE TREE CryptoSigma TEST (N = 8)                   ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let sigma := buildTreeSigma 8
  IO.println s!"Generated CryptoSigma:\n{sigma}"

  IO.println ""
  IO.println s!"Has intrinsics: {sigma.hasIntrinsics}"
  IO.println s!"Intrinsic count: {sigma.intrinsicCount}"

  let intrinsics := sigma.extractIntrinsicSequence
  IO.println s!"Intrinsic sequence: {intrinsics.map Intrinsic.toString}"

#eval! testCryptoSigma

/-- Test 3: Tree construction and proof generation -/
def testTreeConstruction : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       MERKLE TREE CONSTRUCTION TEST (N = 8)                  ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Create test leaves
  let leaves : Array UInt64 := #[1, 2, 3, 4, 5, 6, 7, 8]
  IO.println s!"Leaves: [1, 2, 3, 4, 5, 6, 7, 8]"

  match buildTree leaves testHash with
  | none => IO.println "Failed to build tree"
  | some tree =>
    IO.println s!"Tree size: {tree.nodes.size} nodes"
    IO.println s!"Root value: {tree.root}"

    -- Generate and display proof for leaf 3
    match generateProof tree 3 with
    | none => IO.println "Failed to generate proof"
    | some proof =>
      IO.println s!"\nProof for leaf 3:"
      IO.println s!"  Leaf index: {proof.leafIndex}"
      IO.println s!"  Path depth: {proof.siblings.length}"
      IO.println s!"  Path bits: {proof.pathBits}"

      -- Verify the proof
      let leafVal := leaves.get! 3
      let verified := proof.verify leafVal tree.root testHash
      IO.println s!"  Verification: {if verified then "PASSED" else "FAILED"}"

#eval! testTreeConstruction

/-- Test 4: Cost analysis -/
def testCostAnalysis : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       MERKLE TREE COST ANALYSIS                              ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let cm := defaultZKCost

  for n in [8, 64, 1024, 1048576] do
    let buildCost := buildTreeCost cm n
    let depth := Nat.log2 n
    let verifyCost := verifyProofCost cm depth
    IO.println s!"N = {n}:"
    IO.println s!"  Build cost: {buildCost}"
    IO.println s!"  Proof verify cost: {verifyCost}"
    IO.println s!"  Depth: {depth}"
    IO.println ""

#eval! testCostAnalysis

/-- Test 5: Index calculations verification -/
def testIndexCalculations : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       INDEX CALCULATIONS VERIFICATION (N = 8)                ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let idx := MerkleIndex.create 8
  IO.println s!"MerkleIndex for n=8:"
  IO.println s!"  numLeaves: {idx.numLeaves}"
  IO.println s!"  totalNodes: {idx.totalNodes}"
  IO.println s!"  depth: {idx.depth}"
  IO.println s!"  rootIndex: {idx.rootIndex}"
  IO.println s!"  firstInternalIndex: {idx.firstInternalIndex}"
  IO.println ""

  IO.println "Nodes per layer:"
  for layer in [0:4] do
    IO.println s!"  Layer {layer}: {idx.nodesInLayer layer} nodes"

#eval! testIndexCalculations

end Tests

/-! ## Part 8: Summary -/

def merkleSummary : String :=
  "Merkle Tree Module Summary (Phase 6.4):
   ======================================

   1. FlatMerkle: Leaves-first flat array layout
      - Leaves at [0..n-1]
      - Internal nodes at [n..2n-2]
      - Root at [2n-2]

   2. MerkleProof: Authentication path structure
      - siblings: Hashes along path to root
      - pathBits: Direction at each level

   3. Construction: Bottom-up layer-by-layer
      - Each layer hashes pairs from previous layer
      - .loop for SIMD parallelism within layer
      - .seq for data dependency between layers

   4. CryptoSigma Integration:
      - Uses Intrinsic.merkleHash for opaque hashing
      - Domain separation with domainEnter/Exit
      - Preserves security through optimization

   5. Memory Access Pattern:
      - Contiguous reads within layers
      - Sequential writes within layers
      - Optimal for AVX vectorization

   Key Properties:
   - Generic over field type (Float for testing, ZMod for production)
   - Proof generation and verification included
   - Cost analysis integrated with ZKCostModel"

#eval! IO.println merkleSummary

end AmoLean.FRI.Merkle
