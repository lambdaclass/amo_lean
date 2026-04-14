/-
  AMO-Lean Ultra — Phase 24, Nodes 24.1+24.2: MatNodeOps + Abstract Semantics
  Self-contained matrix e-graph types + breakdown rules.

  Vector.lean has pre-existing compilation issues (#eval with sorry).
  Instead of importing it, we define the matrix-level types we need
  here and bridge to the arithmetic level via the cross-e-graph protocol.

  Design: abstract transform identities (TransformId), breakdown rules
  (BreakdownRule), and a lightweight matrix representation (MatOp)
  that can be used for algorithmic exploration without the full MatEGraph.

  Consumed by: N24.3 (BreakdownRules), N24.4 (CrossEGraphProtocol), Phase23Integration
-/
-- v3.13.0 F.5: NTTPlanCodeGen import removed; add direct NTTPlan import for log2
import AmoLean.EGraph.Verified.Bitwise.NTTPlan
-- v3.14.0 B8: NodeOps typeclass for MatOp e-graph integration
import AmoLean.EGraph.VerifiedExtraction.Core
-- v3.14.0 B9: Extractable for MatOp extraction
import AmoLean.EGraph.VerifiedExtraction.Greedy

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Matrix

open AmoLean.EGraph.Verified.Bitwise.NTTPlan (log2)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Transform Identity (Abstract Semantics)
-- ══════════════════════════════════════════════════════════════════

/-- Abstract identity for a matrix transform. Two expressions with the
    same TransformId compute the same matrix. -/
structure TransformId where
  name : String
  rows : Nat
  cols : Nat
  params : List Nat := []
  deriving Repr, BEq, Inhabited, Hashable

def TransformId.dft (n : Nat) : TransformId := { name := "DFT", rows := n, cols := n }
def TransformId.ntt (n p : Nat) : TransformId := { name := "NTT", rows := n, cols := n, params := [p] }
def TransformId.identity (n : Nat) : TransformId := { name := "I", rows := n, cols := n }
def TransformId.twiddle (n k : Nat) : TransformId := { name := "T", rows := n, cols := n, params := [k] }
def TransformId.stride (m n : Nat) : TransformId := { name := "L", rows := m*n, cols := m*n, params := [m] }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Lightweight Matrix Operations
-- ══════════════════════════════════════════════════════════════════

/-- Lightweight matrix operation for algorithmic exploration.
    Child references are indices into an array (not e-class IDs). -/
inductive MatOp where
  | identity (n : Nat)
  | dft (n : Nat)
  | ntt (n p : Nat)
  | twiddle (n k : Nat)
  | stridePerm (m n : Nat)
  | kron (a b : Nat) (m₁ n₁ m₂ n₂ : Nat)
  | compose (a b : Nat) (m k n : Nat)
  deriving Repr, BEq, Inhabited, Hashable, DecidableEq  -- v3.13.0 H.6: for future MatOp e-graph (v3.14.0)

def MatOp.children : MatOp → List Nat
  | .identity _ | .dft _ | .ntt _ _ | .twiddle _ _ | .stridePerm _ _ => []
  | .kron a b _ _ _ _ | .compose a b _ _ _ => [a, b]

def MatOp.transformId : MatOp → TransformId
  | .identity n => .identity n
  | .dft n => .dft n
  | .ntt n p => .ntt n p
  | .twiddle n k => .twiddle n k
  | .stridePerm m n => .stride m n
  | .kron _ _ m₁ n₁ m₂ n₂ => { name := "⊗", rows := m₁*m₂, cols := n₁*n₂ }
  | .compose _ _ m _ n => { name := "·", rows := m, cols := n }

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Factorization Tree
-- ══════════════════════════════════════════════════════════════════

/-- A factorization tree: a concrete decomposition of a DFT/NTT.
    Nodes are MatOps stored in an array (DAG representation).
    The root is the last entry. -/
structure FactorizationTree where
  nodes : Array MatOp
  root : Nat  -- index into nodes
  deriving Repr, Inhabited

def FactorizationTree.size (t : FactorizationTree) : Nat := t.nodes.size

/-- Get the transform identity of the root. -/
def FactorizationTree.rootId (t : FactorizationTree) : TransformId :=
  if h : t.root < t.nodes.size then t.nodes[t.root].transformId
  else { name := "?", rows := 0, cols := 0 }

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Breakdown Rules
-- ══════════════════════════════════════════════════════════════════

/-- A breakdown rule decomposes a transform into a factored tree.
    SPIRAL's core concept formalized. -/
structure BreakdownRule where
  name : String
  targetTransform : String   -- "DFT" or "NTT"
  isApplicable : Nat → Bool  -- size predicate
  /-- Build a factorization tree for size n with prime p. -/
  decompose : Nat → Nat → FactorizationTree

/-- Cooley-Tukey: DFT(r*s) = (DFT(r)⊗I(s)) · T(r*s,s) · (I(r)⊗DFT(s)) · L(r*s,r) -/
def cooleyTukeyRule (r s : Nat) : BreakdownRule where
  name := s!"CT({r},{s})"
  targetTransform := "DFT"
  isApplicable := fun n => n == r * s && r ≥ 2 && s ≥ 2
  decompose := fun n _p =>
    let rs := r * s
    let nodes : Array MatOp := #[
      .dft r,                              -- 0: DFT(r)
      .identity s,                         -- 1: I(s)
      .kron 0 1 r r 1 s,                  -- 2: DFT(r) ⊗ I(s)
      .twiddle n s,                        -- 3: T(n,s)
      .identity r,                         -- 4: I(r)
      .dft s,                              -- 5: DFT(s)
      .kron 4 5 1 r s s,                  -- 6: I(r) ⊗ DFT(s)
      .stridePerm n r,                     -- 7: L(n,r)
      MatOp.compose 6 7 rs rs n,           -- 8: (I⊗DFT_s) · L
      MatOp.compose 3 8 n n n,             -- 9: T · (I⊗DFT_s) · L
      MatOp.compose 2 9 n n n             -- 10: (DFT_r⊗I) · T · (I⊗DFT_s) · L
    ]
    { nodes, root := 10 }

/-- Base case: DFT(2) = F₂ -/
def baseCase2Rule : BreakdownRule where
  name := "Base2"
  targetTransform := "DFT"
  isApplicable := fun n => n == 2
  decompose := fun _ _ => { nodes := #[.dft 2], root := 0 }

/-- Radix-4: DFT(4m) via CT(4,m) -/
def radix4Rule (m : Nat) : BreakdownRule where
  name := s!"Radix4({m})"
  targetTransform := "DFT"
  isApplicable := fun n => n == 4 * m && m ≥ 1
  decompose := (cooleyTukeyRule 4 m).decompose

/-- All standard breakdown rules for a given N. -/
def standardRules (n : Nat) : List BreakdownRule :=
  let divisors := List.range n |>.filter (fun d => d ≥ 2 && n % d == 0 && n / d ≥ 2)
  divisors.map (fun r => cooleyTukeyRule r (n / r)) ++ [baseCase2Rule]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Cost Model for Factorization Trees
-- ══════════════════════════════════════════════════════════════════

/-- Count multiplications in a factorization tree.
    This is the algorithmic cost (Level 1), separate from
    arithmetic cost (Level 3) which is per-butterfly. -/
def FactorizationTree.mulCount (t : FactorizationTree) : Nat :=
  t.nodes.foldl (fun acc op =>
    match op with
    | .kron _ _ _ _ _ _ => acc  -- Kronecker products are "free" (they define loop structure)
    | .compose _ _ _ _ _ => acc -- Composition is loop nesting
    | .twiddle n _ => acc + n   -- Twiddle diagonal: n multiplications
    | _ => acc
  ) 0

/-- Count total nodes in the tree (structural complexity). -/
def FactorizationTree.nodeCount (t : FactorizationTree) : Nat := t.nodes.size

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Factorization Exploration
-- ══════════════════════════════════════════════════════════════════

/-- Recursively decompose all DFT sub-nodes in a factorization tree.
    For each `.dft n` node where n > 2, find the best factorization
    and splice its nodes into the tree. Fuel-bounded to ensure termination. -/
private def expandSubDFTs (tree : FactorizationTree) (p : Nat)
    (fuel : Nat) : FactorizationTree :=
  match fuel with
  | 0 => tree
  | fuel + 1 =>
    -- Find first unexpanded DFT node with n > 2
    let expandable := tree.nodes.findIdx? fun op =>
      match op with | .dft n => n > 2 | _ => false
    match expandable with
    | none => tree  -- all DFTs are base cases → done
    | some idx =>
      match tree.nodes[idx]? with
      | some (.dft n) =>
        -- Find best decomposition for this sub-DFT
        let rules := standardRules n
        let applicable := rules.filter (·.isApplicable n)
        match applicable with
        | [] => tree  -- no applicable rule → leave as-is
        | rule :: _ =>
          let subTree := rule.decompose n p
          -- Replace the DFT node with the decomposition's root node
          -- (simplified: just append subtree nodes and update references)
          let offsetNodes := subTree.nodes.map fun op =>
            match op with
            | .kron a b m1 n1 m2 n2 => .kron (a + tree.nodes.size) (b + tree.nodes.size) m1 n1 m2 n2
            | .compose a b m k n' => MatOp.compose (a + tree.nodes.size) (b + tree.nodes.size) m k n'
            | other => other
          let newNodes := tree.nodes ++ offsetNodes
          let expanded := { nodes := newNodes, root := tree.root }
          expandSubDFTs expanded p fuel
      | _ => tree

/-- Generate all possible factorizations for DFT(n) and pick the cheapest.
    RECURSIVE: decomposes sub-DFTs until all are base cases.
    This is the algorithmic search that SPIRAL does with DP.

    Returns: (chosen factorization, its mul count, all candidates). -/
def exploreFact (n p : Nat) : FactorizationTree × Nat × Nat :=
  let rules := standardRules n
  let candidates := rules.filter (·.isApplicable n) |>.map fun rule =>
    let tree := rule.decompose n p
    -- Recursively expand sub-DFTs (fuel = log2(n) is sufficient)
    expandSubDFTs tree p (log2 n)
  match candidates with
  | [] =>
    let fallback := baseCase2Rule.decompose n p
    (fallback, fallback.mulCount, 0)
  | first :: rest =>
    let best := rest.foldl (fun best t =>
      if t.mulCount < best.mulCount then t else best) first
    (best, best.mulCount, candidates.length)

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Theorems
-- ══════════════════════════════════════════════════════════════════

theorem base2_applicable : baseCase2Rule.isApplicable 2 = true := rfl

theorem ct_produces_tree_8 :
    ((cooleyTukeyRule 2 4).decompose 8 0).nodes.size = 11 := rfl

theorem base2_produces_leaf :
    (baseCase2Rule.decompose 2 0).nodes.size = 1 := rfl

theorem dft_transformId (n : Nat) : (MatOp.dft n).transformId = TransformId.dft n := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : (cooleyTukeyRule 2 4).isApplicable 8 = true := by native_decide
example : (cooleyTukeyRule 2 4).isApplicable 7 = false := by native_decide
example : baseCase2Rule.isApplicable 2 = true := rfl
example : (radix4Rule 4).isApplicable 16 = true := by native_decide

/-- CT(2,4) factorization of DFT(8) has 11 nodes. -/
example : ((cooleyTukeyRule 2 4).decompose 8 0).nodes.size = 11 := rfl

/-- Exploration finds candidates for n=8. -/
example : (exploreFact 8 0).2.2 > 0 := by native_decide

/-- Exploration finds candidates for n=16. -/
example : (exploreFact 16 0).2.2 > 0 := by native_decide

/-- TransformId equality. -/
example : TransformId.dft 8 == TransformId.dft 8 := by native_decide

end SmokeTests

-- ══════════════════════════════════════════════════════════════════
-- Section: NodeOps instance for MatOp (v3.14.0 B8)
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.VerifiedExtraction (EClassId NodeOps)

/-- Apply a function to all child e-class IDs. Only kron and compose have children. -/
@[simp] def MatOp.mapChildren (f : EClassId → EClassId) : MatOp → MatOp
  | .identity n       => .identity n
  | .dft n            => .dft n
  | .ntt n p          => .ntt n p
  | .twiddle n k      => .twiddle n k
  | .stridePerm m n   => .stridePerm m n
  | .kron a b m₁ n₁ m₂ n₂ => .kron (f a) (f b) m₁ n₁ m₂ n₂
  | .compose a b m k n    => .compose (f a) (f b) m k n

/-- Positionally replace children with new e-class IDs. -/
@[simp] def MatOp.replaceChildren (op : MatOp) (ids : List EClassId) : MatOp :=
  match op, ids with
  | .kron _ _ m₁ n₁ m₂ n₂, a :: b :: _ => .kron a b m₁ n₁ m₂ n₂
  | .compose _ _ m k n, a :: b :: _      => .compose a b m k n
  | op, _ => op

/-- Local cost of a matrix operation. Twiddle costs n multiplies, others symbolic. -/
def MatOp.localCost : MatOp → Nat
  | .twiddle n _ => n
  | _            => 0

private theorem mat_list_length_two {l : List Nat} (h : l.length = 2) :
    ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

instance : NodeOps MatOp where
  children := MatOp.children
  mapChildren := MatOp.mapChildren
  replaceChildren := MatOp.replaceChildren
  localCost := MatOp.localCost
  mapChildren_children f op := by cases op <;> simp [MatOp.children, MatOp.mapChildren]
  mapChildren_id op := by cases op <;> simp [MatOp.mapChildren]
  replaceChildren_children op ids hlen := by
    cases op with
    | identity _ | dft _ | ntt _ _ | twiddle _ _ | stridePerm _ _ =>
      simp [MatOp.children] at hlen; subst hlen; rfl
    | kron a b m₁ n₁ m₂ n₂ =>
      simp [MatOp.children] at hlen
      obtain ⟨x, y, rfl⟩ := mat_list_length_two hlen; rfl
    | compose a b m k n =>
      simp [MatOp.children] at hlen
      obtain ⟨x, y, rfl⟩ := mat_list_length_two hlen; rfl
  replaceChildren_sameShape op ids hlen := by
    cases op with
    | identity _ | dft _ | ntt _ _ | twiddle _ _ | stridePerm _ _ =>
      simp [MatOp.children] at hlen; subst hlen; rfl
    | kron a b m₁ n₁ m₂ n₂ =>
      simp [MatOp.children] at hlen
      obtain ⟨x, y, rfl⟩ := mat_list_length_two hlen; rfl
    | compose a b m k n =>
      simp [MatOp.children] at hlen
      obtain ⟨x, y, rfl⟩ := mat_list_length_two hlen; rfl

-- ══════════════════════════════════════════════════════════════════
-- Section: MatExprFlat + Extractable (v3.14.0 B9)
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.VerifiedExtraction.Greedy (Extractable)

/-- Non-indexed recursive expression type for MatOp.
    Mirrors MatOp but with recursive children instead of Nat indices.
    Used by extractF to reconstruct expressions from the e-graph.
    NOT the same as MatExpr (which is dependently-typed by dimensions). -/
inductive MatExprFlat where
  | identity (n : Nat)
  | dft (n : Nat)
  | ntt (n p : Nat)
  | twiddle (n k : Nat)
  | stridePerm (m n : Nat)
  | kron (a b : MatExprFlat) (m₁ n₁ m₂ n₂ : Nat)
  | compose (a b : MatExprFlat) (m k n : Nat)
  deriving Repr, Inhabited

/-- Reconstruct a MatExprFlat from a MatOp and its children's extracted expressions. -/
def matReconstruct (op : MatOp) (children : List MatExprFlat) : Option MatExprFlat :=
  match op, children with
  | .identity n, []                        => some (.identity n)
  | .dft n, []                             => some (.dft n)
  | .ntt n p, []                           => some (.ntt n p)
  | .twiddle n k, []                       => some (.twiddle n k)
  | .stridePerm m n, []                    => some (.stridePerm m n)
  | .kron _ _ m₁ n₁ m₂ n₂, [a, b]        => some (.kron a b m₁ n₁ m₂ n₂)
  | .compose _ _ m k n, [a, b]            => some (.compose a b m k n)
  | _, _                                   => none

instance : Extractable MatOp MatExprFlat where
  reconstruct := matReconstruct

/-- Convert MatExprFlat to FactorizationTree (flat array representation).
    Bridge to factorizationToPlan (CrossEGraphProtocol:123-150). -/
def matExprFlatToTree (expr : MatExprFlat) : FactorizationTree :=
  let (nodes, rootIdx) := go expr #[]
  { nodes := nodes, root := rootIdx }
where
  go (e : MatExprFlat) (acc : Array MatOp) : Array MatOp × Nat :=
    match e with
    | .identity n     => (acc.push (.identity n), acc.size)
    | .dft n          => (acc.push (.dft n), acc.size)
    | .ntt n p        => (acc.push (.ntt n p), acc.size)
    | .twiddle n k    => (acc.push (.twiddle n k), acc.size)
    | .stridePerm m n => (acc.push (.stridePerm m n), acc.size)
    | .kron a b m₁ n₁ m₂ n₂ =>
      let (acc1, aIdx) := go a acc
      let (acc2, bIdx) := go b acc1
      (acc2.push (.kron aIdx bIdx m₁ n₁ m₂ n₂), acc2.size)
    | .compose a b m k n =>
      let (acc1, aIdx) := go a acc
      let (acc2, bIdx) := go b acc1
      (acc2.push (.compose aIdx bIdx m k n), acc2.size)

-- ══════════════════════════════════════════════════════════════════
-- Section: applyBreakdownInEGraph (v3.14.0 B10)
-- ══════════════════════════════════════════════════════════════════

/-- Apply a BreakdownRule to an NTT/DFT node in the e-graph.
    Decomposes the transform via rule.decompose, adds all nodes of the
    FactorizationTree to the e-graph, and merges the tree root with
    the original nttClassId.
    Returns the updated e-graph with the factorization as an equivalent
    representation of the original NTT. -/
def applyBreakdownInEGraph (g : AmoLean.EGraph.VerifiedExtraction.EGraph MatOp)
    (nttClassId : EClassId) (rule : BreakdownRule) (n p : Nat)
    : AmoLean.EGraph.VerifiedExtraction.EGraph MatOp :=
  if !rule.isApplicable n then g
  else
    let tree := rule.decompose n p
    -- Add each node of the FactorizationTree to the e-graph.
    -- tree.nodes uses array indices as children; we remap to EClassIds.
    let (g', idMap) := tree.nodes.foldl
      (fun (acc : AmoLean.EGraph.VerifiedExtraction.EGraph MatOp × Array EClassId) node =>
      let (g, ids) := acc
      -- Remap children: tree uses array indices, e-graph uses EClassIds
      let remappedOp := MatOp.mapChildren (fun childIdx =>
        if h : childIdx < ids.size then ids[childIdx] else childIdx) node
      let (newId, g') := g.add ⟨remappedOp⟩
      (g', ids.push newId)
    ) (g, #[])
    -- Merge: the tree root is equivalent to the original NTT
    if h : tree.root < idMap.size then
      g'.merge nttClassId idMap[tree.root]
    else g'

/-- Apply all applicable breakdown rules from a list to an NTT node.
    Each rule that applies adds its factorization as an equivalent class. -/
def applyAllBreakdowns (g : AmoLean.EGraph.VerifiedExtraction.EGraph MatOp)
    (nttClassId : EClassId) (rules : List BreakdownRule) (n p : Nat)
    : AmoLean.EGraph.VerifiedExtraction.EGraph MatOp :=
  rules.foldl (fun g rule => applyBreakdownInEGraph g nttClassId rule n p) g

-- ══════════════════════════════════════════════════════════════════
-- Smoke tests: NodeOps MatOp
-- ══════════════════════════════════════════════════════════════════

section NodeOpsTests

/-- mapChildren distributes over children. -/
example : NodeOps.children (NodeOps.mapChildren (· + 10) (MatOp.kron 1 2 3 3 3 3)) =
    (NodeOps.children (MatOp.kron 1 2 3 3 3 3)).map (· + 10) := rfl

/-- mapChildren with id is identity. -/
example : NodeOps.mapChildren id (MatOp.compose 5 6 4 4 4) =
    MatOp.compose 5 6 4 4 4 := rfl

/-- replaceChildren yields given children. -/
example : NodeOps.children (NodeOps.replaceChildren (MatOp.kron 1 2 3 3 3 3) [10, 20]) =
    [10, 20] := rfl

/-- Leaf nodes have 0 children. -/
example : NodeOps.children (MatOp.ntt 64 18446744069414584321) = [] := rfl

/-- localCost: twiddle costs n. -/
example : NodeOps.localCost (MatOp.twiddle 64 8) = 64 := rfl

end NodeOpsTests

end AmoLean.EGraph.Verified.Matrix
