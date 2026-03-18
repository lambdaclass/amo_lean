/-
  AmoLean.EGraph.Verified.Bitwise.MixedSaturation — Saturation Core

  Adapted from OptiSat LambdaSat/SaturationSpec.lean (lines 320+) + SemanticSpec.lean (rebuild).
  Provides:
  - applyRuleAtF: fuel-based rule application at a class
  - applyRulesF: apply list of rules across all classes
  - processClass: re-canonicalize nodes and detect congruences
  - rebuildStepBody / rebuildF: fuel-based rebuild
  - saturateMixedF: main saturation loop (apply rules → rebuild → repeat)
-/
import AmoLean.EGraph.Verified.Bitwise.MixedEMatch

namespace MixedSaturation

open AmoLean.EGraph.VerifiedExtraction
open MixedEMatch (Pattern Substitution ematchF instantiateF RewriteRule sameShape)

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: applyRuleAtF — Apply a rewrite rule at a specific class
-- ══════════════════════════════════════════════════════════════════

/-- Apply a rewrite rule at a specific class. Ematch the LHS pattern,
    instantiate the RHS, and merge the result with the matched class.
    Adapted from OptiSat SaturationSpec.lean:325-341. -/
def applyRuleAtF (fuel : Nat) (g : EGraph Op) (rule : RewriteRule Op)
    (classId : EClassId) : EGraph Op :=
  let results := ematchF fuel g rule.lhs classId
  results.foldl (fun acc subst =>
    let condMet := match rule.sideCondCheck with
      | some check => check acc subst
      | none => true
    if !condMet then acc
    else
      match instantiateF fuel acc rule.rhs subst with
      | none => acc
      | some (rhsId, acc') =>
        let canonLhs := UnionFind.root acc'.unionFind classId
        let canonRhs := UnionFind.root acc'.unionFind rhsId
        if canonLhs == canonRhs then acc'
        else acc'.merge classId rhsId) g

/-- Apply a rule to all classes using fuel-based operations. -/
def applyRuleF (fuel : Nat) (g : EGraph Op) (rule : RewriteRule Op) : EGraph Op :=
  let allClasses := g.classes.toList.map (·.1)
  allClasses.foldl (fun acc classId => applyRuleAtF fuel acc rule classId) g

/-- Apply a list of rules once across the entire e-graph (fuel-based). -/
def applyRulesF (fuel : Nat) (g : EGraph Op) (rules : List (RewriteRule Op)) : EGraph Op :=
  rules.foldl (applyRuleF fuel) g

-- ══════════════════════════════════════════════════════════════════
-- Section 2: processClass + rebuild — Re-canonicalize and congruence closure
-- ══════════════════════════════════════════════════════════════════

/-- Re-canonicalize a node's children using the current union-find roots. -/
def canonicalizeNode (g : EGraph Op) (node : ENode Op) : ENode Op :=
  node.mapChildren (fun c => UnionFind.root g.unionFind c)

/-- Process a class: re-canonicalize all nodes and detect congruences.
    Returns the updated graph and a list of merges to perform.
    Adapted from OptiSat Core.lean:processClass. -/
def processClass (g : EGraph Op) (classId : EClassId) :
    (EGraph Op × List (EClassId × EClassId)) :=
  let canonId := UnionFind.root g.unionFind classId
  match g.classes.get? canonId with
  | none => (g, [])
  | some eclass =>
    eclass.nodes.foldl (init := (g, [])) fun (acc, merges) node =>
      let canonNode := canonicalizeNode acc node
      if canonNode == node then
        (acc, merges)
      else
        let hashcons1 := acc.hashcons.erase node
        match hashcons1.get? canonNode with
        | some existingId =>
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc with hashcons := hashcons2 }, (canonId, existingId) :: merges)
        | none =>
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc with hashcons := hashcons2 }, merges)

/-- Body of one rebuild iteration: process worklist, then apply pending merges. -/
def rebuildStepBody (g : EGraph Op) : EGraph Op :=
  let toProcess := g.worklist
  let g1 : EGraph Op := { g with worklist := [] }
  let (g2, pendingMerges) := toProcess.foldl (fun (acc, merges) classId =>
    let (acc', newMerges) := processClass acc classId
    (acc', newMerges ++ merges)
  ) (g1, [])
  pendingMerges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g2

/-- Fuel-based total version of rebuild. Iterates until worklist is empty or fuel runs out. -/
def rebuildF (g : EGraph Op) : Nat → EGraph Op
  | 0 => g
  | fuel + 1 =>
    if g.worklist.isEmpty then g
    else rebuildF (rebuildStepBody g) fuel

-- ══════════════════════════════════════════════════════════════════
-- Section 3: saturateMixedF — Main saturation loop
-- ══════════════════════════════════════════════════════════════════

/-- Total saturation loop. Applies rules for at most `maxIter` iterations.
    Each iteration: apply all rules, then rebuild.
    Uses `ematchFuel` for ematch/instantiate and `rebuildFuel` for rebuild.
    Adapted from OptiSat SaturationSpec.lean:358-367. -/
def saturateMixedF (ematchFuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op)) : EGraph Op :=
  match maxIter with
  | 0 => g
  | n + 1 =>
    let g' := applyRulesF ematchFuel g rules
    let g'' := rebuildF g' rebuildFuel
    if g''.numClasses == g.numClasses then g''
    else saturateMixedF ematchFuel n rebuildFuel g'' rules

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Counted variants (for UCB1 scoring feedback)
-- ══════════════════════════════════════════════════════════════════

/-- Apply a rule at a class and count how many merges occurred. -/
def applyRuleAtF_counted (fuel : Nat) (g : EGraph Op) (rule : RewriteRule Op)
    (classId : EClassId) : (EGraph Op × Nat) :=
  let results := ematchF fuel g rule.lhs classId
  results.foldl (fun (acc, count) subst =>
    let condMet := match rule.sideCondCheck with
      | some check => check acc subst
      | none => true
    if !condMet then (acc, count)
    else
      match instantiateF fuel acc rule.rhs subst with
      | none => (acc, count)
      | some (rhsId, acc') =>
        let canonLhs := UnionFind.root acc'.unionFind classId
        let canonRhs := UnionFind.root acc'.unionFind rhsId
        if canonLhs == canonRhs then (acc', count)
        else (acc'.merge classId rhsId, count + 1)) (g, 0)

/-- Apply a rule to all classes and count total merges. -/
def applyRuleF_counted (fuel : Nat) (g : EGraph Op) (rule : RewriteRule Op) :
    (EGraph Op × Nat) :=
  let allClasses := g.classes.toList.map (·.1)
  allClasses.foldl (fun (acc, count) classId =>
    let (acc', c) := applyRuleAtF_counted fuel acc rule classId
    (acc', count + c)) (g, 0)

/-- Apply a list of rules and collect per-rule merge counts. -/
def applyRulesF_counted (fuel : Nat) (g : EGraph Op)
    (rules : List (RewriteRule Op)) : (EGraph Op × List (String × Nat)) :=
  rules.foldl (fun (acc, stats) rule =>
    let (acc', count) := applyRuleF_counted fuel acc rule
    (acc', (rule.name, count) :: stats)) (g, [])

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp)

/-- Smoke test: saturating an empty graph with no rules returns an empty graph. -/
example : (saturateMixedF 10 5 3 (EGraph.empty : EGraph MixedNodeOp) []).numClasses = 0 := by
  native_decide

/-- Smoke test: rebuildF on empty graph is identity. -/
example : (rebuildF (EGraph.empty : EGraph MixedNodeOp) 10).numClasses = 0 := by
  native_decide

end SmokeTests

end MixedSaturation
