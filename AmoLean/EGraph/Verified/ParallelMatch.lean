/-
  AMO-Lean — Verified — Parallel Pattern Matching Infrastructure
  Fase 8 Subfase 4: Parallel matching via Lean 4 Task API

  Key design: read-only e-graph during matching.
  - Use `root` (pure, no path compression) instead of `find` (mutating)
  - Collect all matches, then apply sequentially
  - Embarrassingly parallel: each class's ematch is independent
-/
import AmoLean.EGraph.Verified.EMatch

namespace AmoLean.EGraph.Verified

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Read-Only E-Matching (no path compression)
-- ══════════════════════════════════════════════════════════════════

/-- E-match using `root` instead of `find` (no mutation, safe for parallelism).
    The e-graph is not modified — we use UnionFind.root which is pure. -/
partial def ematchReadOnly (g : EGraph) (pattern : CircuitPattern) (classId : EClassId)
    (subst : Substitution := Substitution.empty) : MatchResult :=
  let canonId := root g.unionFind classId
  match pattern with
  | .patVar pv =>
    match subst.extend pv canonId with
    | some subst' => [subst']
    | none => []

  | .constPat c =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkConst c) then [subst] else []

  | .witnessPat i =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkWitness i) then [subst] else []

  | .pubInPat i =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkPubInput i) then [subst] else []

  | .addPat p1 p2 =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .addGate childA childB =>
          let ms := ematchReadOnly g p1 childA subst
          ms.foldl (fun acc2 subst1 =>
            acc2 ++ ematchReadOnly g p2 childB subst1) acc
        | _ => acc

  | .mulPat p1 p2 =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .mulGate childA childB =>
          let ms := ematchReadOnly g p1 childA subst
          ms.foldl (fun acc2 subst1 =>
            acc2 ++ ematchReadOnly g p2 childB subst1) acc
        | _ => acc

  | .negPat p1 =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .negGate childA =>
          acc ++ ematchReadOnly g p1 childA subst
        | _ => acc

  | .smulPat c p1 =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .smulGate nodeC childA =>
          if nodeC == c then acc ++ ematchReadOnly g p1 childA subst
          else acc
        | _ => acc

-- ══════════════════════════════════════════════════════════════════
-- Parallel Matching
-- ══════════════════════════════════════════════════════════════════

/-- A match result for a specific rule at a specific class. -/
structure RuleMatch where
  classId : EClassId
  subst   : Substitution
  deriving Inhabited

/-- Collect matches from ematchReadOnly into an array of RuleMatch. -/
private def collectMatches (g : EGraph) (pattern : CircuitPattern)
    (classId : EClassId) : Array RuleMatch :=
  let results := ematchReadOnly g pattern classId
  results.foldl (fun acc subst =>
    acc.push { classId := classId, subst := subst }) #[]

/-- Match a single rule against a chunk of class IDs (pure, read-only). -/
def matchRuleChunk (g : EGraph) (rule : RewriteRule) (classIds : Array EClassId) :
    Array RuleMatch :=
  classIds.foldl (init := #[]) fun acc classId =>
    acc ++ collectMatches g rule.lhs classId

/-- Split an array into `n` roughly equal chunks. -/
def splitIntoChunks {α : Type} (arr : Array α) (n : Nat) : Array (Array α) :=
  if n == 0 || arr.isEmpty then #[arr]
  else
    let chunkSize := max ((arr.size + n - 1) / n) 1
    Id.run do
      let mut result : Array (Array α) := #[]
      let mut start : Nat := 0
      for _ in [:n] do
        if start >= arr.size then break
        let endIdx := min (start + chunkSize) arr.size
        result := result.push (arr.extract start endIdx)
        start := endIdx
      return result

/-- Search for all instances of a pattern across all classes in parallel.
    Uses IO.asTask to run matching on chunks concurrently.
    The e-graph is read-only during matching (uses `root`, not `find`). -/
def searchPatternParallel (g : EGraph) (pattern : CircuitPattern) (numTasks : Nat := 4) :
    IO (Array RuleMatch) := do
  let allClassIds := g.classes.fold (fun acc classId _ => acc.push classId) (#[] : Array EClassId)
  if allClassIds.size ≤ 1 || numTasks ≤ 1 then
    -- Sequential fallback for tiny graphs
    return allClassIds.foldl (init := #[]) fun acc classId =>
      acc ++ collectMatches g pattern classId
  else
    let chunks := splitIntoChunks allClassIds numTasks
    let tasks ← chunks.mapM fun chunk => do
      IO.asTask (prio := .dedicated) do
        return chunk.foldl (init := #[]) fun acc classId =>
          acc ++ collectMatches g pattern classId
    let mut allResults : Array RuleMatch := #[]
    for task in tasks do
      let result ← IO.ofExcept (← IO.wait task)
      allResults := allResults ++ result
    return allResults

/-- Match all rules against the e-graph in parallel.
    Each rule is matched independently via IO.asTask. -/
def matchAllRulesParallel (g : EGraph) (rules : List RewriteRule) (numTasks : Nat := 4) :
    IO (Array (RewriteRule × Array RuleMatch)) := do
  let ruleArray := rules.toArray
  if ruleArray.size ≤ 1 || numTasks ≤ 1 then
    -- Sequential fallback
    let mut results : Array (RewriteRule × Array RuleMatch) := #[]
    for rule in ruleArray do
      let allClassIds := g.classes.fold (fun acc classId _ => acc.push classId) (#[] : Array EClassId)
      let ruleMatches := matchRuleChunk g rule allClassIds
      results := results.push (rule, ruleMatches)
    return results
  else
    let tasks ← ruleArray.mapM fun rule => do
      IO.asTask (prio := .dedicated) do
        let allClassIds := g.classes.fold (fun acc classId _ => acc.push classId) (#[] : Array EClassId)
        let ruleMatches := matchRuleChunk g rule allClassIds
        return (rule, ruleMatches)
    let mut results : Array (RewriteRule × Array RuleMatch) := #[]
    for task in tasks do
      let result ← IO.ofExcept (← IO.wait task)
      results := results.push result
    return results

-- ══════════════════════════════════════════════════════════════════
-- Sequential Apply (after parallel match)
-- ══════════════════════════════════════════════════════════════════

/-- Apply collected match results sequentially (merge is not thread-safe).
    Side conditions are re-checked at apply time since the e-graph may
    have changed between matching and applying. -/
def applyMatchResults (g : EGraph) (rule : RewriteRule)
    (ruleMatches : Array RuleMatch) : EGraph :=
  ruleMatches.foldl (init := g) fun acc m =>
    let condMet := match rule.sideCondCheck with
      | some check => check acc m.subst
      | none => true
    if !condMet then acc
    else
      match instantiate acc rule.rhs m.subst with
      | none => acc
      | some (rhsId, acc') =>
        let (canonLhs, acc'') := acc'.find m.classId
        let (canonRhs, acc''') := acc''.find rhsId
        if canonLhs == canonRhs then acc'''
        else acc'''.merge m.classId rhsId

/-- Apply all rule match results sequentially, then rebuild once. -/
def applyAllMatchResultsAndRebuild (g : EGraph)
    (allRuleMatches : Array (RewriteRule × Array RuleMatch)) : EGraph :=
  let g' := allRuleMatches.foldl (init := g) fun acc (rule, ruleMatches) =>
    applyMatchResults acc rule ruleMatches
  g'.rebuild

end AmoLean.EGraph.Verified
