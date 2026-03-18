/-
  AmoLean.EGraph.Verified.Bitwise.MixedEGraphBuilder — Build EGraph from MixedExpr

  Recursively converts a MixedExpr tree into EGraph nodes.
  Provides:
  - addMixedExpr: recursively add a MixedExpr to an EGraph
  - Helpers: addConst, addWitness, addPubInput, etc.
-/
import AmoLean.EGraph.Verified.Bitwise.MixedEMatch
import AmoLean.EGraph.Verified.Bitwise.MixedExtract

namespace MixedEGraphBuilder

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Leaf helpers
-- ══════════════════════════════════════════════════════════════════

/-- Add a constant gate node. -/
def addConst (g : EGraph MixedNodeOp) (n : Nat) : EClassId × EGraph MixedNodeOp :=
  g.add ⟨.constGate n⟩

/-- Add a witness node. -/
def addWitness (g : EGraph MixedNodeOp) (n : Nat) : EClassId × EGraph MixedNodeOp :=
  g.add ⟨.witness n⟩

/-- Add a public input node. -/
def addPubInput (g : EGraph MixedNodeOp) (n : Nat) : EClassId × EGraph MixedNodeOp :=
  g.add ⟨.pubInput n⟩

/-- Add a constant mask node (2^n - 1). -/
def addConstMask (g : EGraph MixedNodeOp) (n : Nat) : EClassId × EGraph MixedNodeOp :=
  g.add ⟨.constMask n⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Binary/Unary op helpers
-- ══════════════════════════════════════════════════════════════════

/-- Add a binary op node given two child class IDs. -/
def addBinaryOp (g : EGraph MixedNodeOp) (mkOp : EClassId → EClassId → MixedNodeOp)
    (a b : EClassId) : EClassId × EGraph MixedNodeOp :=
  g.add ⟨mkOp a b⟩

/-- Add a unary op node given one child class ID. -/
def addUnaryOp (g : EGraph MixedNodeOp) (mkOp : EClassId → MixedNodeOp)
    (a : EClassId) : EClassId × EGraph MixedNodeOp :=
  g.add ⟨mkOp a⟩

/-- Add a shift node given a child class ID and shift amount. -/
def addShift (g : EGraph MixedNodeOp) (mkOp : EClassId → Nat → MixedNodeOp)
    (a : EClassId) (n : Nat) : EClassId × EGraph MixedNodeOp :=
  g.add ⟨mkOp a n⟩

/-- Add a scalar multiply node. -/
def addSmul (g : EGraph MixedNodeOp) (n : Nat) (a : EClassId)
    : EClassId × EGraph MixedNodeOp :=
  g.add ⟨.smulGate n a⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 3: addMixedExpr — Recursive builder
-- ══════════════════════════════════════════════════════════════════

/-- Recursively add a MixedExpr tree to an EGraph. Returns the root class ID
    and the updated graph. All 13 MixedExpr constructors are handled. -/
def addMixedExpr (g : EGraph MixedNodeOp) (expr : MixedExpr)
    : EClassId × EGraph MixedNodeOp :=
  match expr with
  | .constE n       => addConst g n
  | .witnessE n     => addWitness g n
  | .pubInputE n    => addPubInput g n
  | .constMaskE n   => addConstMask g n
  | .addE a b =>
    let (aId, g1) := addMixedExpr g a
    let (bId, g2) := addMixedExpr g1 b
    addBinaryOp g2 .addGate aId bId
  | .mulE a b =>
    let (aId, g1) := addMixedExpr g a
    let (bId, g2) := addMixedExpr g1 b
    addBinaryOp g2 .mulGate aId bId
  | .negE a =>
    let (aId, g1) := addMixedExpr g a
    addUnaryOp g1 .negGate aId
  | .smulE n a =>
    let (aId, g1) := addMixedExpr g a
    addSmul g1 n aId
  | .shiftLeftE a n =>
    let (aId, g1) := addMixedExpr g a
    addShift g1 .shiftLeft aId n
  | .shiftRightE a n =>
    let (aId, g1) := addMixedExpr g a
    addShift g1 .shiftRight aId n
  | .bitAndE a b =>
    let (aId, g1) := addMixedExpr g a
    let (bId, g2) := addMixedExpr g1 b
    addBinaryOp g2 .bitAnd aId bId
  | .bitXorE a b =>
    let (aId, g1) := addMixedExpr g a
    let (bId, g2) := addMixedExpr g1 b
    addBinaryOp g2 .bitXor aId bId
  | .bitOrE a b =>
    let (aId, g1) := addMixedExpr g a
    let (bId, g2) := addMixedExpr g1 b
    addBinaryOp g2 .bitOr aId bId

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Convenience — build from scratch
-- ══════════════════════════════════════════════════════════════════

/-- Build a fresh EGraph from a MixedExpr. Returns (graph, rootId). -/
def buildEGraph (expr : MixedExpr) : EGraph MixedNodeOp × EClassId :=
  let (rootId, g) := addMixedExpr EGraph.empty expr
  (g, rootId)

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke test: adding a constant creates 1 class. -/
example : (addConst EGraph.empty 42).2.numClasses = 1 := by native_decide

/-- Smoke test: adding a binary op with two leaves creates 3 classes. -/
example :
    let (aId, g1) := addConst EGraph.empty 1
    let (bId, g2) := addConst g1 2
    (addBinaryOp g2 .addGate aId bId).2.numClasses = 3 := by native_decide

/-- Smoke test: building a simple expression. -/
example :
    let expr := MixedExpr.addE (.constE 1) (.constE 2)
    (buildEGraph expr).1.numClasses = 3 := by native_decide

/-- Smoke test: building bitAnd(witness(0), constMask(31)). -/
example :
    let expr := MixedExpr.bitAndE (.witnessE 0) (.constMaskE 31)
    (buildEGraph expr).1.numClasses = 3 := by native_decide

/-- Smoke test: shared subexpressions are deduplicated. -/
example :
    let w := MixedExpr.witnessE 0
    let expr := MixedExpr.bitAndE w w  -- both children are witness(0)
    (buildEGraph expr).1.numClasses = 2 := by native_decide
    -- Only 2 classes: witness(0) and bitAnd(w0, w0)

end MixedEGraphBuilder
