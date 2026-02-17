/-
  AMO-Lean — Verified — Parallel Saturation Loop
  Fase 8 Subfase 5: Parallel match → sequential apply → sequential rebuild

  Architecture:
  - Matching phase: embarrassingly parallel (read-only e-graph)
  - Apply phase: sequential (merge is not thread-safe)
  - Rebuild phase: sequential (maintains invariants)

  This preserves soundness: the final e-graph contains the same equivalences
  as sequential saturation (modulo merge ordering, which doesn't affect
  the fixpoint due to commutativity of union-find merge).
-/
import AmoLean.EGraph.Verified.ParallelMatch
import AmoLean.EGraph.Verified.Saturate

namespace AmoLean.EGraph.Verified

-- ══════════════════════════════════════════════════════════════════
-- Configuration
-- ══════════════════════════════════════════════════════════════════

/-- Configuration for parallel saturation. Extends SaturationConfig. -/
structure ParallelSatConfig where
  /-- Maximum iterations before stopping -/
  maxIterations   : Nat := 10
  /-- Maximum nodes in the e-graph -/
  maxNodes        : Nat := 500
  /-- Maximum classes in the e-graph -/
  maxClasses      : Nat := 200
  /-- Number of parallel tasks for matching -/
  numTasks        : Nat := 4
  /-- Minimum classes to enable parallelism (below = sequential) -/
  parallelThreshold : Nat := 20
  deriving Repr, Inhabited

/-- Convert to sequential SaturationConfig (for fallback). -/
def ParallelSatConfig.toSequential (c : ParallelSatConfig) : SaturationConfig where
  maxIterations := c.maxIterations
  maxNodes := c.maxNodes
  maxClasses := c.maxClasses

/-- Large parallel config for aggressive saturation. -/
def ParallelSatConfig.large : ParallelSatConfig where
  maxIterations := 30
  maxNodes := 10000
  maxClasses := 5000
  numTasks := 8
  parallelThreshold := 50

-- ══════════════════════════════════════════════════════════════════
-- Saturation Mode
-- ══════════════════════════════════════════════════════════════════

/-- Saturation mode for the pipeline. -/
inductive SaturationMode where
  /-- Sequential saturation (existing, default) -/
  | sequential
  /-- Parallel matching + sequential apply/rebuild -/
  | parallel
  deriving Repr, BEq, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Parallel Saturation Step
-- ══════════════════════════════════════════════════════════════════

/-- One step of parallel saturation:
    1. Match all rules in parallel (read-only e-graph)
    2. Apply all matches sequentially (mutation)
    3. Rebuild (sequential) -/
def parallelSaturateStep (g : EGraph) (rules : List RewriteRule)
    (numTasks : Nat) : IO EGraph := do
  -- Phase 1: Parallel matching
  let ruleMatches ← matchAllRulesParallel g rules numTasks
  -- Phase 2: Sequential apply
  -- Phase 3: Rebuild
  return applyAllMatchResultsAndRebuild g ruleMatches

private def checkLimitsIO (g : EGraph) (config : ParallelSatConfig) : Option String :=
  if g.numNodes > config.maxNodes then some s!"node limit ({config.maxNodes})"
  else if g.numClasses > config.maxClasses then some s!"class limit ({config.maxClasses})"
  else none

private def reachedFixpointIO (before after : EGraph) : Bool :=
  before.numNodes == after.numNodes && before.numClasses == after.numClasses

/-- Run parallel equality saturation with bounded iterations.
    Falls back to sequential for small graphs (below parallelThreshold). -/
partial def parallelSaturate (g : EGraph) (rules : List RewriteRule)
    (config : ParallelSatConfig := {}) : IO SaturationResult := do
  -- Check if graph is small enough for sequential fallback
  if g.numClasses < config.parallelThreshold then
    return saturate g rules config.toSequential

  let rec loop (current : EGraph) (iter : Nat) : IO SaturationResult := do
    if iter >= config.maxIterations then
      return { graph := current, iterations := iter, saturated := false,
               reason := "max iterations" }
    else
      match checkLimitsIO current config with
      | some reason =>
        return { graph := current, iterations := iter, saturated := false,
                 reason := reason }
      | none =>
        let next ← parallelSaturateStep current rules config.numTasks
        if reachedFixpointIO current next then
          return { graph := next, iterations := iter + 1, saturated := true,
                   reason := "fixpoint" }
        else
          loop next (iter + 1)
  loop g 0

-- ══════════════════════════════════════════════════════════════════
-- Unified Saturation Interface
-- ══════════════════════════════════════════════════════════════════

/-- Run saturation in the specified mode. -/
def saturateWithMode (g : EGraph) (rules : List RewriteRule)
    (mode : SaturationMode) (seqConfig : SaturationConfig := {})
    (parConfig : ParallelSatConfig := {}) : IO SaturationResult := do
  match mode with
  | .sequential => return saturate g rules seqConfig
  | .parallel => parallelSaturate g rules parConfig

end AmoLean.EGraph.Verified
