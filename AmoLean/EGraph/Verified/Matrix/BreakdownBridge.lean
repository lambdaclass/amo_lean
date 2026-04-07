/-
  AmoLean.EGraph.Verified.Matrix.BreakdownBridge

  Bridges BreakdownRules (algorithmic factorization) with MatEGraph
  (e-graph-based optimization). Replaces the MatOp-based FactorizationTree
  approach with direct insertion of MatExpr factorizations into the MatEGraph.

  Architecture:
    1. BreakdownRule produces a MatExpr (e.g., fftCooleyTukey 2 (n/2))
    2. addMatExpr inserts it into the MatEGraph
    3. merge makes it equivalent to the original dft(n) e-class
    4. The e-graph explores all factorizations simultaneously with sharing
    5. extractMatExpr produces the optimal verified MatExpr

  This replaces: MatOp, FactorizationTree, exploreFact, expandSubDFTs.
-/
import AmoLean.EGraph.Vector
import AmoLean.Matrix.Basic

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Matrix.BreakdownBridge

open AmoLean.EGraph.Matrix (MatEGraph MatEClassId MatENode MatENodeOp)
open AmoLean.EGraph.Matrix.MatEGraph (addMatExpr extractMatExpr)
open AmoLean.Matrix (MatExpr Perm)

/-- A breakdown rule for the MatEGraph.
    Given an e-class containing dft(n), inserts the factorized MatExpr
    into the e-graph and merges it with the original e-class.
    The rule is sound if the factorized MatExpr evaluates identically
    to the original (via evalMatExprAlg). -/
structure EGraphBreakdownRule where
  /-- Rule name for identification. -/
  name : String
  /-- Check if the rule applies to a given DFT size. -/
  isApplicable : (n : Nat) → Bool
  /-- Produce the factorized MatExpr for DFT of size n.
      Returns an existential over dimensions. -/
  factorize : (n : Nat) → Σ' (m k : Nat), MatExpr Nat m k

/-- Apply a breakdown rule to a specific e-class in the MatEGraph.
    If the e-class contains a dft(n) and the rule applies:
    1. Create the factorized MatExpr
    2. Add it to the e-graph (reusing shared sub-expressions)
    3. Merge the new e-class with the original
    Returns the (possibly updated) e-graph. -/
def applyBreakdownRule (g : MatEGraph) (classId : MatEClassId)
    (n : Nat) (rule : EGraphBreakdownRule) : MatEGraph :=
  if rule.isApplicable n then
    let ⟨m, k, expr⟩ := rule.factorize n
    let (newId, g1) := addMatExpr g m k expr
    g1.merge classId newId
  else g

/-- Cooley-Tukey breakdown rule for the MatEGraph.
    DFT(2n) = (DFT(2) ⊗ I(n)) · T(2n, n) · (I(2) ⊗ DFT(n)) · L(2n, 2)
    Directly uses fftCooleyTukey from Matrix/Basic.lean. -/
def cooleyTukeyEGraphRule : EGraphBreakdownRule where
  name := "cooley_tukey_radix2"
  isApplicable := fun n => n > 2 && n % 2 == 0
  factorize := fun n =>
    let half := n / 2
    -- fftCooleyTukey 2 half : MatExpr Nat (2*half) (2*half)
    ⟨2 * half, 2 * half, MatExpr.fftCooleyTukey 2 half⟩

/-- Base case: DFT(2) = butterfly matrix (identity in the e-graph). -/
def baseCaseEGraphRule : EGraphBreakdownRule where
  name := "base_case_2"
  isApplicable := fun n => n == 2
  factorize := fun _ => ⟨2, 2, MatExpr.dft 2⟩  -- base case stays as dft(2)

/-- Radix-4 breakdown rule.
    DFT(4n) = (DFT(4) ⊗ I(n)) · T(4n, n) · (I(4) ⊗ DFT(n)) · L(4n, 4) -/
def radix4EGraphRule : EGraphBreakdownRule where
  name := "cooley_tukey_radix4"
  isApplicable := fun n => n > 4 && n % 4 == 0
  factorize := fun n =>
    let quarter := n / 4
    ⟨4 * quarter, 4 * quarter, MatExpr.fftCooleyTukey 4 quarter⟩

/-- All standard breakdown rules for NTT factorization. -/
def standardEGraphRules : List EGraphBreakdownRule :=
  [cooleyTukeyEGraphRule, radix4EGraphRule, baseCaseEGraphRule]

/-- Apply all applicable breakdown rules to a DFT e-class.
    This is the e-graph equivalent of exploreFact: instead of building a
    separate FactorizationTree, we insert all factorizations directly into
    the e-graph. The e-graph's equality saturation explores them all
    simultaneously with sharing of common sub-expressions. -/
def saturateBreakdowns (g : MatEGraph) (dftClassId : MatEClassId)
    (n : Nat) (rules : List EGraphBreakdownRule := standardEGraphRules) : MatEGraph :=
  rules.foldl (fun g' rule => applyBreakdownRule g' dftClassId n rule) g

/-- Create a MatEGraph with DFT(n) and all factorizations.
    This is the top-level entry point replacing the old MatOp pipeline:
    1. Create empty e-graph
    2. Add dft(n) as the root
    3. Apply all breakdown rules recursively
    4. Extract the optimal factorization as a verified MatExpr -/
def optimizeNTTFactorization (n : Nat) (fuel : Nat := 10) :
    Option (Σ' (m k : Nat), MatExpr Nat m k) :=
  let (rootId, g0) := MatEGraph.empty.add (MatENode.mkDFT n)
  -- Apply breakdown rules (limited by fuel to avoid infinite expansion)
  let g := applyBreakdownRulesRecursive g0 rootId n fuel
  -- Extract the best factorization
  extractMatExpr g rootId
where
  /-- Recursively apply breakdown rules to expand sub-DFTs.
      N27.14: Now iterates over sub-DFTs and expands them recursively. -/
  applyBreakdownRulesRecursive (g : MatEGraph) (rootId : MatEClassId)
      (n : Nat) (fuel : Nat) : MatEGraph :=
    match fuel with
    | 0 => g
    | fuel' + 1 =>
      let g1 := saturateBreakdowns g rootId n
      -- Extract sub-DFT sizes from the e-graph nodes
      let subDFTs := extractSubDFTSizes g1
      -- Recursively expand each sub-DFT
      subDFTs.foldl (fun g' (subId, subN) =>
        if subN > 1 then
          let g'' := saturateBreakdowns g' subId subN
          applyBreakdownRulesRecursive g'' subId subN fuel'
        else g'
      ) g1
  /-- Extract sub-DFT class IDs and their sizes from the e-graph. -/
  extractSubDFTSizes (g : MatEGraph) : List (MatEClassId × Nat) :=
    g.classes.toList.filterMap fun (cid, eclass) =>
      -- Check if any node in this class is a DFT node
      let dftSize := eclass.nodes.fold (fun acc node =>
        match node.op with
        | .dft n => if n > 1 then some n else acc
        | _ => acc
      ) (none : Option Nat)
      match dftSize with
      | some n => some (cid, n)
      | none => none

-- Smoke test: CT factorization of DFT(8)
#eval do
  let result := optimizeNTTFactorization 8
  match result with
  | some ⟨m, n, _⟩ => IO.println s!"Extracted: {m}x{n} MatExpr"
  | none => IO.println "Extraction failed"

end AmoLean.EGraph.Verified.Matrix.BreakdownBridge
