/-
  AMO-Lean — Verified — ILP Encoding for E-Graph Extraction
  Fase 8 Subfase 1: Encode e-graph → ILP problem

  Encodes the ILP formulation from TENSAT (Yang et al., 2021):
  - One nodeSelect variable per node in each class
  - One classActive variable per class
  - One level variable per class (for acyclicity)
  - Constraints: root activation, exactly-one, child dependency, acyclicity
-/
import AmoLean.EGraph.Verified.ILP

namespace AmoLean.EGraph.Verified.ILP

open AmoLean.EGraph.Verified UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Encoding: E-graph → ILP Problem
-- ══════════════════════════════════════════════════════════════════

/-- Get the canonical (root) class IDs for all children of a node. -/
private def canonicalChildren (g : EGraph) (node : ENode) : List EClassId :=
  node.children.map (root g.unionFind ·)

/-- Collect all canonical class IDs in the e-graph. -/
private def collectClasses (g : EGraph) : Array EClassId :=
  g.classes.fold (fun acc classId _ => acc.push classId) #[]

/-- Encode an e-graph extraction problem as an ILP problem.
    `rootId` is the class from which we extract.
    `costFn` maps nodes to their cost (default: mulGate=1, rest=0). -/
def encodeEGraph (g : EGraph) (rootId : EClassId)
    (costFn : ENode → Nat := ENode.localCost) : ILPProblem := Id.run do
  let canonRoot := root g.unionFind rootId
  let allClasses := collectClasses g
  let numC := allClasses.size
  let bigM : Int := (numC : Int) + 1

  -- Phase 1: Bounds
  let mut bounds : Array VarBound := #[]
  let mut nodeMap : Std.HashMap (EClassId × Nat) ENode := Std.HashMap.ofList []

  for classId in allClasses do
    bounds := bounds.push { var := .classActive classId, lo := 0, hi := 1 }
    bounds := bounds.push { var := .level classId, lo := 0, hi := numC }
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        let node := eclass.nodes[idx]
        bounds := bounds.push { var := .nodeSelect classId idx, lo := 0, hi := 1 }
        nodeMap := nodeMap.insert (classId, idx) node

  -- Phase 2: Objective — minimize Σ cost(n) · s_n
  let mut objective : Array ObjTerm := #[]
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        let node := eclass.nodes[idx]
        let cost := costFn node
        if cost > 0 then
          objective := objective.push { cost := cost, var := .nodeSelect classId idx }

  -- Phase 3: Constraints
  let mut constraints : Array ILPConstraint := #[]

  -- C1: Root activation: a_root = 1
  constraints := constraints.push {
    name := "root_active"
    terms := #[{ coeff := 1, var := .classActive canonRoot }]
    op := .eq
    rhs := 1
  }

  -- C2: Exactly-one per class: Σ s_n - a_c = 0
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      let mut terms : Array LinTerm := #[]
      for h : idx in [:eclass.nodes.size] do
        terms := terms.push { coeff := 1, var := .nodeSelect classId idx }
      terms := terms.push { coeff := -1, var := .classActive classId }
      constraints := constraints.push {
        name := s!"exactly_one_{classId}"
        terms := terms
        op := .eq
        rhs := 0
      }

  -- C3: Child dependency: s_n - a_{child} ≤ 0
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        let node := eclass.nodes[idx]
        let children := canonicalChildren g node
        for child in children do
          constraints := constraints.push {
            name := s!"child_dep_{classId}_{idx}_{child}"
            terms := #[
              { coeff := 1, var := .nodeSelect classId idx },
              { coeff := -1, var := .classActive child }
            ]
            op := .le
            rhs := 0
          }

  -- C4: Acyclicity: -L_c + L_child - M·s_n ≤ M - 1
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        let node := eclass.nodes[idx]
        let children := canonicalChildren g node
        for child in children do
          if child != classId then
            constraints := constraints.push {
              name := s!"acyclic_{classId}_{idx}_{child}"
              terms := #[
                { coeff := -1, var := .level classId },
                { coeff := 1, var := .level child },
                { coeff := -bigM, var := .nodeSelect classId idx }
              ]
              op := .le
              rhs := bigM - 1
            }

  return { bounds := bounds
         , objective := objective
         , constraints := constraints
         , numClasses := numC
         , rootClassId := canonRoot
         , nodeMap := nodeMap }

-- ══════════════════════════════════════════════════════════════════
-- Problem Statistics
-- ══════════════════════════════════════════════════════════════════

/-- Statistics about an encoded ILP problem. -/
structure ILPStats where
  numVars        : Nat
  numConstraints : Nat
  numClasses     : Nat
  numNodes       : Nat
  rootClassId    : EClassId
  deriving Repr, Inhabited

def ILPProblem.stats (p : ILPProblem) : ILPStats where
  numVars := p.numVars
  numConstraints := p.numConstraints
  numClasses := p.numClasses
  numNodes := p.nodeMap.size
  rootClassId := p.rootClassId

-- ══════════════════════════════════════════════════════════════════
-- Feasibility Checking (decidable, for certificate verification)
-- ══════════════════════════════════════════════════════════════════

/-- Evaluate a variable in a solution. -/
def evalVar (sol : ILPSolution) (var : ILPVar) : Int :=
  match var with
  | .nodeSelect classId nodeIdx =>
    match sol.selectedNodes.get? classId with
    | some idx => if idx == nodeIdx then 1 else 0
    | none => 0
  | .classActive classId =>
    if sol.isActive classId then 1 else 0
  | .level classId =>
    (sol.getLevel classId : Int)

/-- Evaluate the LHS of a constraint: Σ coeff_i · var_i. -/
def evalConstraintLHS (sol : ILPSolution) (terms : Array LinTerm) : Int :=
  terms.foldl (fun acc t => acc + t.coeff * evalVar sol t.var) 0

/-- Check if a single constraint is satisfied by the solution. -/
def checkConstraint (sol : ILPSolution) (c : ILPConstraint) : Bool :=
  let lhs := evalConstraintLHS sol c.terms
  match c.op with
  | .le => lhs ≤ c.rhs
  | .ge => lhs ≥ c.rhs
  | .eq => lhs == c.rhs

/-- Check if all bounds are satisfied. -/
def checkBounds (sol : ILPSolution) (bounds : Array VarBound) : Bool :=
  bounds.all fun b =>
    let val := evalVar sol b.var
    b.lo ≤ val && val ≤ b.hi

/-- Decidable feasibility check: does the solution satisfy all constraints and bounds? -/
def ILPSolution.isFeasible (sol : ILPSolution) (prob : ILPProblem) : Bool :=
  checkBounds sol prob.bounds && prob.constraints.all (checkConstraint sol ·)

-- ══════════════════════════════════════════════════════════════════
-- Solution from raw variable assignment
-- ══════════════════════════════════════════════════════════════════

/-- Build an ILPSolution from a raw variable→value map (for solver output parsing). -/
def ILPSolution.fromVarMap (varMap : Std.HashMap String Int)
    (prob : ILPProblem) : ILPSolution := Id.run do
  let mut selectedNodes : Std.HashMap EClassId Nat := Std.HashMap.ofList []
  let mut activatedClasses : Std.HashMap EClassId Bool := Std.HashMap.ofList []
  let mut levels : Std.HashMap EClassId Nat := Std.HashMap.ofList []
  let mut objValue : Nat := 0

  for bound in prob.bounds do
    let varName := toString bound.var
    let val := varMap.get? varName |>.getD 0
    match bound.var with
    | .nodeSelect classId nodeIdx =>
      if val > 0 then
        selectedNodes := selectedNodes.insert classId nodeIdx
    | .classActive classId =>
      activatedClasses := activatedClasses.insert classId (val > 0)
    | .level classId =>
      levels := levels.insert classId val.toNat

  for obj in prob.objective do
    let varName := toString obj.var
    let val := varMap.get? varName |>.getD 0
    if val > 0 then
      objValue := objValue + obj.cost

  return { selectedNodes := selectedNodes
         , activatedClasses := activatedClasses
         , levels := levels
         , objectiveValue := objValue }

end AmoLean.EGraph.Verified.ILP
