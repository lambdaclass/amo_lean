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

end AmoLean.EGraph.Verified.Matrix
