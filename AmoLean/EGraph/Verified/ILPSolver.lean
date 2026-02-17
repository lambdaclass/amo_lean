/-
  AMO-Lean — Verified — ILP Solver Interface
  Fase 8 Subfase 2: External (HiGHS) + Internal (Branch-and-Bound) solvers

  Architecture: external solver is TCB for *optimality* only.
  Solution correctness is verified in ILPCheck.lean (S3) via certificate checking.
  Pure Lean B&B fallback for small instances (<50 classes) or environments without HiGHS.
-/
import AmoLean.EGraph.Verified.ILPEncode

namespace AmoLean.EGraph.Verified.ILP

open AmoLean.EGraph.Verified

-- ══════════════════════════════════════════════════════════════════
-- MPS Format Export
-- ══════════════════════════════════════════════════════════════════

/-- Convert an ILP problem to MPS (Mathematical Programming System) format.
    MPS is the standard input format for HiGHS and most LP/ILP solvers. -/
def ILPProblem.toMPS (prob : ILPProblem) : String := Id.run do
  let mut lines : Array String := #[]

  -- Header
  lines := lines.push "NAME          VR1CS_ILP"
  lines := lines.push "ROWS"

  -- Objective row
  lines := lines.push " N  OBJ"

  -- Constraint rows
  for c in prob.constraints do
    let rowType := match c.op with
      | .le => "L"
      | .ge => "G"
      | .eq => "E"
    lines := lines.push s!" {rowType}  {c.name}"

  -- COLUMNS section
  lines := lines.push "COLUMNS"
  lines := lines.push "    MARKER    'MARKER'    'INTORG'"

  -- Collect all variables that appear in objective or constraints
  let mut varCoeffs : Std.HashMap String (Array (String × Int)) := Std.HashMap.ofList []

  -- Add objective coefficients
  for obj in prob.objective do
    let varName := toString obj.var
    let existing := varCoeffs.get? varName |>.getD #[]
    varCoeffs := varCoeffs.insert varName (existing.push ("OBJ", (obj.cost : Int)))

  -- Add constraint coefficients
  for c in prob.constraints do
    for t in c.terms do
      let varName := toString t.var
      let existing := varCoeffs.get? varName |>.getD #[]
      varCoeffs := varCoeffs.insert varName (existing.push (c.name, t.coeff))

  -- Write columns
  for bound in prob.bounds do
    let varName := toString bound.var
    match varCoeffs.get? varName with
    | none => pure ()
    | some coeffs =>
      for (rowName, coeff) in coeffs do
        let coeffStr := if coeff ≥ 0 then s!" {coeff}" else s!"{coeff}"
        lines := lines.push s!"    {varName}  {rowName}  {coeffStr}"

  lines := lines.push "    MARKER    'MARKER'    'INTEND'"

  -- RHS section
  lines := lines.push "RHS"
  for c in prob.constraints do
    if c.rhs != 0 then
      lines := lines.push s!"    RHS1  {c.name}  {c.rhs}"

  -- BOUNDS section
  lines := lines.push "BOUNDS"
  for b in prob.bounds do
    let varName := toString b.var
    match b.var with
    | .level _ =>
      -- Integer variable with bounds
      lines := lines.push s!" LO BND1  {varName}  {b.lo}"
      lines := lines.push s!" UP BND1  {varName}  {b.hi}"
    | _ =>
      -- Binary variable
      lines := lines.push s!" BV BND1  {varName}"

  lines := lines.push "ENDATA"
  "\n".intercalate lines.toList

-- ══════════════════════════════════════════════════════════════════
-- HiGHS Solution Parsing
-- ══════════════════════════════════════════════════════════════════

/-- Parse a HiGHS solution file into variable→value map. -/
private def parseHiGHSSolution (output : String) : Std.HashMap String Int := Id.run do
  let mut varMap : Std.HashMap String Int := Std.HashMap.ofList []
  let lines := output.splitOn "\n"
  let mut inColumns := false
  for line in lines do
    let trimmed := line.trim
    if trimmed.startsWith "Columns" then
      inColumns := true
    else if inColumns then
      -- Format: varName value
      let parts := trimmed.splitOn " " |>.filter (· != "")
      if parts.length ≥ 2 then
        match parts[0]!, parts[1]! with
        | varName, valStr =>
          -- Parse as float then round to int
          let val := valStr.toInt?.getD 0
          varMap := varMap.insert varName val
  return varMap

-- ══════════════════════════════════════════════════════════════════
-- External HiGHS Solver
-- ══════════════════════════════════════════════════════════════════

/-- Solve an ILP problem using external HiGHS solver.
    Writes MPS to temp file, runs HiGHS, parses solution. -/
def solveExternal (prob : ILPProblem) (config : SolverConfig := {}) :
    IO (Option ILPSolution) := do
  -- Write MPS file
  let mpsContent := prob.toMPS
  let tmpDir := "/tmp/vr1cs_ilp"
  IO.FS.createDirAll tmpDir
  let mpsPath := s!"{tmpDir}/problem.mps"
  let solPath := s!"{tmpDir}/solution.sol"
  IO.FS.writeFile ⟨mpsPath⟩ mpsContent

  -- Run HiGHS
  let timeLimit := config.timeoutMs / 1000
  let args := #[mpsPath, "--solution_file", solPath,
                "--time_limit", toString timeLimit]
  let child ← IO.Process.spawn {
    cmd := config.higgsPath
    args := args
    stdout := .piped
    stderr := .piped
  }
  let stdout ← child.stdout.readToEnd
  let exitCode ← child.wait

  if exitCode != 0 then
    return none

  -- Parse solution
  let solContent ← IO.FS.readFile ⟨solPath⟩
  let varMap := parseHiGHSSolution solContent

  -- Check if solver found optimal
  if (stdout.splitOn "ptimal").length > 1 then
    return some (ILPSolution.fromVarMap varMap prob)
  else
    return none

-- ══════════════════════════════════════════════════════════════════
-- Pure Lean Branch-and-Bound Solver
-- ══════════════════════════════════════════════════════════════════

/-- State for the branch-and-bound solver. -/
private structure BBState where
  bestSolution : Option ILPSolution
  bestObjective : Nat
  nodesExplored : Nat
  maxNodes : Nat
  deriving Inhabited

/-- Evaluate the objective function for a (partial) assignment. -/
private def evalObjective (prob : ILPProblem) (assignment : Std.HashMap String Int) : Nat :=
  prob.objective.foldl (fun acc obj =>
    let varName := toString obj.var
    let val := assignment.get? varName |>.getD 0
    if val > 0 then acc + obj.cost else acc) 0

/-- Check if a partial assignment violates any constraint. -/
private def checkPartialFeasibility (prob : ILPProblem)
    (assignment : Std.HashMap String Int) : Bool :=
  prob.constraints.all fun c =>
    -- Only check constraints where all variables are assigned
    let allAssigned := c.terms.all fun t => assignment.contains (toString t.var)
    if !allAssigned then true
    else
      let lhs := c.terms.foldl (fun acc t =>
        acc + t.coeff * (assignment.get? (toString t.var) |>.getD 0)) 0
      match c.op with
      | .le => lhs ≤ c.rhs
      | .ge => lhs ≥ c.rhs
      | .eq => lhs == c.rhs

/-- Simple branch-and-bound solver for small ILP instances.
    Enumerates binary variables with pruning. -/
partial def solveBranchAndBound (prob : ILPProblem) (maxNodes : Nat := 100000) :
    Option ILPSolution := Id.run do
  -- Collect binary variables (nodeSelect, classActive)
  let binaryVars := prob.bounds.filter fun b =>
    match b.var with
    | .level _ => false
    | _ => true

  if binaryVars.isEmpty then return none

  let mut state : BBState := {
    bestSolution := none
    bestObjective := 1000000000
    nodesExplored := 0
    maxNodes := maxNodes
  }

  -- Simple DFS over binary variable assignments
  let mut stack : Array (Std.HashMap String Int × Nat) := #[
    (Std.HashMap.ofList [], 0)
  ]

  while !stack.isEmpty do
    let (assignment, varIdx) := stack.back!
    stack := stack.pop

    state := { state with nodesExplored := state.nodesExplored + 1 }
    if state.nodesExplored > state.maxNodes then break

    -- Check feasibility of current partial assignment
    if !checkPartialFeasibility prob assignment then
      continue

    -- Compute lower bound (current objective)
    let currentObj := evalObjective prob assignment
    if currentObj ≥ state.bestObjective then
      continue  -- Prune

    if varIdx ≥ binaryVars.size then
      -- All binary variables assigned — check full feasibility
      -- Set unassigned level variables greedily
      let mut fullAssignment := assignment
      for b in prob.bounds do
        match b.var with
        | .level classId =>
          let varName := toString b.var
          if !fullAssignment.contains varName then
            -- Assign level = classId (simple topological ordering)
            fullAssignment := fullAssignment.insert varName (classId : Int)
        | _ => pure ()

      let sol := ILPSolution.fromVarMap fullAssignment prob
      if sol.isFeasible prob then
        if sol.objectiveValue < state.bestObjective then
          state := {
            bestSolution := some sol
            bestObjective := sol.objectiveValue
            nodesExplored := state.nodesExplored
            maxNodes := state.maxNodes
          }
    else
      -- Branch on next binary variable
      let bvar := binaryVars[varIdx]!
      let varName := toString bvar.var
      -- Try 0 first (tends to reduce cost), then 1
      stack := stack.push (assignment.insert varName 1, varIdx + 1)
      stack := stack.push (assignment.insert varName 0, varIdx + 1)

  return state.bestSolution

-- ══════════════════════════════════════════════════════════════════
-- Unified Solver Interface
-- ══════════════════════════════════════════════════════════════════

/-- Solve an ILP problem using the configured backend. -/
def solveILP (prob : ILPProblem) (config : SolverConfig := {}) :
    IO (Option ILPSolution) := do
  match config.backend with
  | .internal =>
    return solveBranchAndBound prob
  | .highs =>
    solveExternal prob config
  | .auto =>
    if prob.numClasses ≤ config.internalThreshold then
      return solveBranchAndBound prob
    else
      -- Try external first, fall back to internal
      let result ← solveExternal prob config
      match result with
      | some sol => return some sol
      | none => return solveBranchAndBound prob

-- ══════════════════════════════════════════════════════════════════
-- Solver Statistics
-- ══════════════════════════════════════════════════════════════════

/-- Results from a solver invocation. -/
structure SolverResult where
  solution   : Option ILPSolution
  backend    : String
  probStats  : ILPStats
  deriving Inhabited

/-- Solve and return detailed results. -/
def solveWithStats (prob : ILPProblem) (config : SolverConfig := {}) :
    IO SolverResult := do
  let backendName := match config.backend with
    | .internal => "internal_bb"
    | .highs => "highs"
    | .auto =>
      if prob.numClasses ≤ config.internalThreshold then "internal_bb (auto)"
      else "highs (auto)"
  let solution ← solveILP prob config
  return {
    solution := solution
    backend := backendName
    probStats := prob.stats
  }

end AmoLean.EGraph.Verified.ILP
