/-
  AMO-Lean — Bridge between Expr α and Verified EGraph Engine
  Subfase 8d (Option C): Adapter layer, zero modification to proven theorems.

  Maps AmoLean.Expr Int ↔ Verified CircuitNodeOp EGraph.
  The verified engine uses CircuitNodeOp internally; this bridge provides
  transparent conversion so downstream code works with Expr Int.

  Mapping:
    Expr.const c   → constGate c.toNat
    Expr.var v     → witness v
    Expr.add a b   → addGate idA idB
    Expr.mul a b   → mulGate idA idB
    Expr.pow e n   → chain of mulGate (repeated squaring)
-/
import AmoLean.Basic
import AmoLean.EGraph.Verified.Core
import AmoLean.EGraph.Verified.EMatch
import AmoLean.EGraph.Verified.Saturate

namespace AmoLean.EGraph.Verified.Bridge

open AmoLean (Expr VarId)
open AmoLean.EGraph.Verified

/-! ## Part 1: Expr → EGraph (embedding) -/

/-- Add an Expr Int to the verified e-graph recursively.
    Returns the root class ID and updated graph. -/
def addExpr (g : EGraph) : Expr Int → (EClassId × EGraph)
  | .const c  => g.add (ENode.mkConst c.toNat)
  | .var v    => g.add (ENode.mkWitness v)
  | .add a b  =>
    let (idA, g1) := addExpr g a
    let (idB, g2) := addExpr g1 b
    g2.add (ENode.mkAdd idA idB)
  | .mul a b  =>
    let (idA, g1) := addExpr g a
    let (idB, g2) := addExpr g1 b
    g2.add (ENode.mkMul idA idB)
  | .pow e n  =>
    match n with
    | 0 => g.add (ENode.mkConst 1)
    | 1 => addExpr g e
    | n + 2 =>
      -- e^(n+2) = e * e^(n+1)
      let (idBase, g1) := addExpr g e
      let (idRest, g2) := addExpr g1 (.pow e (n + 1))
      g2.add (ENode.mkMul idBase idRest)

/-- Create a verified e-graph from a single Expr Int. -/
def fromExpr (e : Expr Int) : (EClassId × EGraph) :=
  addExpr .empty e

/-! ## Part 2: EGraph → Expr Int (extraction) -/

/-- Extract the best Expr Int from an e-class (requires costs computed). -/
partial def extract (g : EGraph) (id : EClassId) : Option (Expr Int) :=
  let (canonId, g') := g.find id
  match g'.classes.get? canonId with
  | none => none
  | some eclass =>
    match eclass.bestNode with
    | none => none
    | some node =>
      match node.op with
      | .constGate c  => some (.const (Int.ofNat c))
      | .witness i    => some (.var i)
      | .pubInput i   => some (.var i)  -- map pubInput → var
      | .addGate a b  =>
        match extract g' a, extract g' b with
        | some ea, some eb => some (.add ea eb)
        | _, _ => none
      | .mulGate a b  =>
        match extract g' a, extract g' b with
        | some ea, some eb => some (.mul ea eb)
        | _, _ => none
      | .negGate a    =>
        -- neg a → mul (const (-1)) a
        match extract g' a with
        | some ea => some (.mul (.const (-1)) ea)
        | none => none
      | .smulGate c a =>
        -- smul c a → mul (const c) a
        match extract g' a with
        | some ea => some (.mul (.const (Int.ofNat c)) ea)
        | none => none

/-! ## Part 3: Pattern Bridge -/

/-- Convert an Expr-style pattern to a CircuitPattern for e-matching. -/
def exprPatternToCircuit : Expr Int → CircuitPattern
  | .const c  => .constPat c.toNat
  | .var v    => .patVar v   -- variables become pattern variables
  | .add a b  => .addPat (exprPatternToCircuit a) (exprPatternToCircuit b)
  | .mul a b  => .mulPat (exprPatternToCircuit a) (exprPatternToCircuit b)
  | .pow e n  =>
    match n with
    | 0 => .constPat 1
    | 1 => exprPatternToCircuit e
    | n + 2 =>
      let base := exprPatternToCircuit e
      let rest := exprPatternToCircuit (.pow e (n + 1))
      .mulPat base rest

/-- Create a RewriteRule from Expr-style LHS/RHS patterns. -/
def mkRule (name : String) (lhs rhs : Expr Int)
    (sideCond : Option (EGraph → Substitution → Bool) := none) : RewriteRule where
  name := name
  lhs := exprPatternToCircuit lhs
  rhs := exprPatternToCircuit rhs
  sideCondCheck := sideCond

/-! ## Part 4: End-to-End Pipeline -/

/-- Optimize an Expr Int using the verified e-graph engine.
    Steps: embed → saturate → compute costs → extract. -/
def optimize (expr : Expr Int) (rules : List RewriteRule)
    (config : SaturationConfig := {}) : Option (Expr Int) :=
  let (rootId, g0) := fromExpr expr
  let result := saturate g0 rules config
  let g1 := result.graph.computeCosts
  extract g1 rootId

/-- Optimize with Expr-style rules (convenience wrapper). -/
def optimizeWithRules (expr : Expr Int)
    (rules : List (String × Expr Int × Expr Int))
    (config : SaturationConfig := {}) : Option (Expr Int) :=
  let circuitRules := rules.map fun (name, lhs, rhs) => mkRule name lhs rhs
  optimize expr circuitRules config

end AmoLean.EGraph.Verified.Bridge
