/-
  AMO-Lean — Verified — ILP Extraction Data Model
  Fase 8 Subfase 1: Types for ILP-based optimal e-graph extraction

  ILP formulation from TENSAT (Yang et al., 2021):
  Given e-graph G = (C, N, children) with root class r:

  Variables:
    s_n ∈ {0,1}     — select node n
    a_c ∈ {0,1}     — activate class c
    L_c ∈ [0,|C|]   — acyclicity level

  Objective: minimize Σ cost(n) · s_n

  Constraints:
    C1: a_root = 1                                    (root activation)
    C2: Σ_{n∈class(c)} s_n = a_c                      (exactly one per active class)
    C3: s_n ≤ a_{c_k} for each child c_k of n         (child dependency)
    C4: L_{c_n} ≥ L_{c_k} + 1 - M·(1 - s_n), M=|C|+1 (acyclicity)
-/
import AmoLean.EGraph.Verified.Core

namespace AmoLean.EGraph.Verified.ILP

open AmoLean.EGraph.Verified

-- ══════════════════════════════════════════════════════════════════
-- ILP Variable Types
-- ══════════════════════════════════════════════════════════════════

/-- ILP variable: either a node selection, class activation, or acyclicity level. -/
inductive ILPVar where
  /-- s_n: select node `nodeIdx` in class `classId` (binary) -/
  | nodeSelect  : (classId : EClassId) → (nodeIdx : Nat) → ILPVar
  /-- a_c: activate class `classId` (binary) -/
  | classActive : (classId : EClassId) → ILPVar
  /-- L_c: acyclicity level for class `classId` (integer, [0, |C|]) -/
  | level       : (classId : EClassId) → ILPVar
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : ToString ILPVar where
  toString
    | .nodeSelect cid nid => s!"s_{cid}_{nid}"
    | .classActive cid    => s!"a_{cid}"
    | .level cid          => s!"L_{cid}"

-- ══════════════════════════════════════════════════════════════════
-- ILP Constraint Types
-- ══════════════════════════════════════════════════════════════════

/-- A linear term: coefficient × variable. -/
structure LinTerm where
  coeff : Int
  var   : ILPVar
  deriving Repr, BEq, Inhabited

/-- Comparison operator for constraints. -/
inductive CmpOp where
  | le  -- ≤
  | ge  -- ≥
  | eq  -- =
  deriving Repr, BEq, Inhabited

/-- A linear constraint: Σ (coeff_i × var_i) op rhs. -/
structure ILPConstraint where
  name  : String
  terms : Array LinTerm
  op    : CmpOp
  rhs   : Int
  deriving Repr, Inhabited

/-- Variable bound. -/
structure VarBound where
  var : ILPVar
  lo  : Int
  hi  : Int
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- ILP Problem
-- ══════════════════════════════════════════════════════════════════

/-- Objective term: cost × variable (minimize). -/
structure ObjTerm where
  cost : Nat
  var  : ILPVar
  deriving Repr, Inhabited

/-- An ILP problem: minimize objective subject to constraints. -/
structure ILPProblem where
  /-- Variable declarations with bounds -/
  bounds       : Array VarBound
  /-- Objective: minimize Σ cost_i · var_i -/
  objective    : Array ObjTerm
  /-- Linear constraints -/
  constraints  : Array ILPConstraint
  /-- Number of e-classes (for big-M constant) -/
  numClasses   : Nat
  /-- Root e-class ID -/
  rootClassId  : EClassId
  /-- Map from (classId, nodeIdx) to the ENode -/
  nodeMap      : Std.HashMap (EClassId × Nat) ENode
  deriving Inhabited

namespace ILPProblem

def numVars (p : ILPProblem) : Nat := p.bounds.size
def numConstraints (p : ILPProblem) : Nat := p.constraints.size

end ILPProblem

-- ══════════════════════════════════════════════════════════════════
-- ILP Solution
-- ══════════════════════════════════════════════════════════════════

/-- An ILP solution: maps variables to values. -/
structure ILPSolution where
  /-- For each class, the index of the selected node (if active) -/
  selectedNodes   : Std.HashMap EClassId Nat
  /-- Active classes -/
  activatedClasses : Std.HashMap EClassId Bool
  /-- Acyclicity levels -/
  levels          : Std.HashMap EClassId Nat
  /-- Objective value achieved -/
  objectiveValue  : Nat
  deriving Inhabited

namespace ILPSolution

/-- Check if a class is activated in this solution. -/
def isActive (sol : ILPSolution) (classId : EClassId) : Bool :=
  sol.activatedClasses.get? classId |>.getD false

/-- Get the selected node index for a class (returns none if not active). -/
def getSelectedNodeIdx (sol : ILPSolution) (classId : EClassId) : Option Nat :=
  if sol.isActive classId then sol.selectedNodes.get? classId
  else none

/-- Get the level of a class. -/
def getLevel (sol : ILPSolution) (classId : EClassId) : Nat :=
  sol.levels.get? classId |>.getD 0

end ILPSolution

-- ══════════════════════════════════════════════════════════════════
-- Solver Configuration
-- ══════════════════════════════════════════════════════════════════

/-- Which ILP solver backend to use. -/
inductive SolverBackend where
  /-- External HiGHS solver via IO.Process -/
  | highs
  /-- Pure Lean branch-and-bound (for small instances) -/
  | internal
  /-- Auto-select based on problem size -/
  | auto
  deriving Repr, BEq, Inhabited

/-- ILP solver configuration. -/
structure SolverConfig where
  /-- Which solver backend to use -/
  backend          : SolverBackend := .auto
  /-- Timeout in milliseconds for external solver -/
  timeoutMs        : Nat := 30000
  /-- Threshold: use internal solver below this many classes -/
  internalThreshold : Nat := 50
  /-- HiGHS binary path -/
  higgsPath        : String := "highs"
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Extraction Mode
-- ══════════════════════════════════════════════════════════════════

/-- Extraction mode for the pipeline. -/
inductive ExtractionMode where
  /-- Greedy cost-guided extraction (existing, default) -/
  | greedy
  /-- ILP-based optimal extraction -/
  | ilp
  /-- Auto-select: ILP for large graphs, greedy for small -/
  | ilpAuto
  deriving Repr, BEq, Inhabited

end AmoLean.EGraph.Verified.ILP
