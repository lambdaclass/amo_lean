/-
  AMO-Lean — Verified Equality Saturation Loop
  Ported from VR1CS-Lean (Phase 3 Subphase 4).
  SaturationConfig, saturate loop with fixpoint detection.
-/
import AmoLean.EGraph.Verified.EMatch

namespace AmoLean.EGraph.Verified

structure SaturationConfig where
  maxIterations : Nat := 10
  maxNodes : Nat := 100
  maxClasses : Nat := 50
  deriving Repr, Inhabited

structure SaturationResult where
  graph : EGraph
  iterations : Nat
  saturated : Bool
  reason : String
  deriving Inhabited

structure IterationStats where
  nodesBefore : Nat
  nodesAfter : Nat
  classesBefore : Nat
  classesAfter : Nat
  rulesApplied : Nat
  deriving Repr

private def saturateStep (g : EGraph) (rules : List RewriteRule) : EGraph :=
  let g' := applyRules g rules
  g'.rebuild

private def checkLimits (g : EGraph) (config : SaturationConfig) : Option String :=
  if g.numNodes > config.maxNodes then some s!"node limit ({config.maxNodes})"
  else if g.numClasses > config.maxClasses then some s!"class limit ({config.maxClasses})"
  else none

private def reachedFixpoint (before after : EGraph) : Bool :=
  before.numNodes == after.numNodes && before.numClasses == after.numClasses

/-- Run equality saturation with bounded iterations. -/
partial def saturate (g : EGraph) (rules : List RewriteRule)
    (config : SaturationConfig := {}) : SaturationResult :=
  let rec loop (current : EGraph) (iter : Nat) : SaturationResult :=
    if iter >= config.maxIterations then
      { graph := current, iterations := iter, saturated := false,
        reason := "max iterations" }
    else
      match checkLimits current config with
      | some reason =>
        { graph := current, iterations := iter, saturated := false,
          reason := reason }
      | none =>
        let next := saturateStep current rules
        if reachedFixpoint current next then
          { graph := next, iterations := iter + 1, saturated := true,
            reason := "fixpoint" }
        else
          loop next (iter + 1)
  loop g 0

/-- Large configuration for more thorough saturation. -/
def SaturationConfig.large : SaturationConfig where
  maxIterations := 30
  maxNodes := 10000
  maxClasses := 5000

end AmoLean.EGraph.Verified
