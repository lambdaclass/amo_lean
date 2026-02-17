/-
  AMO-Lean — Verified E-Matching for Circuit Patterns
  Ported from VR1CS-Lean (Phase 3 Subphase 3).
  Pattern matching, substitution, ematch, instantiate, applyRules.
-/
import AmoLean.EGraph.Verified.Core

namespace AmoLean.EGraph.Verified

abbrev PatVarId := Nat

/-- Circuit pattern for e-matching (mirrors CircuitNodeOp but with pattern variables). -/
inductive CircuitPattern where
  | patVar    : PatVarId → CircuitPattern
  | constPat  : Nat → CircuitPattern
  | witnessPat : Nat → CircuitPattern
  | pubInPat  : Nat → CircuitPattern
  | addPat    : CircuitPattern → CircuitPattern → CircuitPattern
  | mulPat    : CircuitPattern → CircuitPattern → CircuitPattern
  | negPat    : CircuitPattern → CircuitPattern
  | smulPat   : Nat → CircuitPattern → CircuitPattern
  deriving Repr, BEq, Inhabited

abbrev Substitution := Std.HashMap PatVarId EClassId

namespace Substitution

def empty : Substitution := Std.HashMap.ofList []

def extend (subst : Substitution) (pv : PatVarId) (id : EClassId) : Option Substitution :=
  match subst.get? pv with
  | none => some (subst.insert pv id)
  | some existingId => if existingId == id then some subst else none

def lookup (subst : Substitution) (pv : PatVarId) : Option EClassId :=
  subst.get? pv

end Substitution

abbrev MatchResult := List Substitution

/-- E-match: find all substitutions making the pattern match a given class. -/
partial def ematch (g : EGraph) (pattern : CircuitPattern) (classId : EClassId)
    (subst : Substitution := Substitution.empty) : MatchResult :=
  let (canonId, g') := g.find classId
  match pattern with
  | .patVar pv =>
    match subst.extend pv canonId with
    | some subst' => [subst']
    | none => []

  | .constPat c =>
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkConst c) then [subst] else []

  | .witnessPat i =>
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkWitness i) then [subst] else []

  | .pubInPat i =>
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkPubInput i) then [subst] else []

  | .addPat p1 p2 =>
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .addGate childA childB =>
          let matches1 := ematch g' p1 childA subst
          matches1.foldl (fun acc2 subst1 =>
            acc2 ++ ematch g' p2 childB subst1) acc
        | _ => acc

  | .mulPat p1 p2 =>
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .mulGate childA childB =>
          let matches1 := ematch g' p1 childA subst
          matches1.foldl (fun acc2 subst1 =>
            acc2 ++ ematch g' p2 childB subst1) acc
        | _ => acc

  | .negPat p1 =>
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .negGate childA =>
          acc ++ ematch g' p1 childA subst
        | _ => acc

  | .smulPat c p1 =>
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        match node.op with
        | .smulGate nodeC childA =>
          if nodeC == c then acc ++ ematch g' p1 childA subst
          else acc
        | _ => acc

/-- Search for all instances of a pattern in the entire e-graph. -/
def searchPattern (g : EGraph) (pattern : CircuitPattern) : List (EClassId × Substitution) :=
  g.classes.fold (fun acc classId _ =>
    let results := ematch g pattern classId
    acc ++ results.map (classId, ·)) []

/-- A rewrite rule for the circuit e-graph.
    Optionally includes a side condition check that must pass before
    the rule fires. The check receives the e-graph and the substitution
    from pattern matching. If `sideCondCheck = none`, the rule is unconditional. -/
structure RewriteRule where
  name : String
  lhs : CircuitPattern
  rhs : CircuitPattern
  sideCondCheck : Option (EGraph → Substitution → Bool) := none

instance : Repr RewriteRule where
  reprPrec r _ := Repr.addAppParen s!"RewriteRule(\"{r.name}\")" 0

/-- Instantiate a pattern with a substitution, adding nodes to the e-graph. -/
partial def instantiate (g : EGraph) (pattern : CircuitPattern) (subst : Substitution)
    : Option (EClassId × EGraph) :=
  match pattern with
  | .patVar pv =>
    match subst.lookup pv with
    | some id => some (id, g)
    | none => none
  | .constPat c =>
    some (g.add (ENode.mkConst c))
  | .witnessPat i =>
    some (g.add (ENode.mkWitness i))
  | .pubInPat i =>
    some (g.add (ENode.mkPubInput i))
  | .addPat p1 p2 =>
    match instantiate g p1 subst with
    | none => none
    | some (id1, g1) =>
      match instantiate g1 p2 subst with
      | none => none
      | some (id2, g2) => some (g2.add (ENode.mkAdd id1 id2))
  | .mulPat p1 p2 =>
    match instantiate g p1 subst with
    | none => none
    | some (id1, g1) =>
      match instantiate g1 p2 subst with
      | none => none
      | some (id2, g2) => some (g2.add (ENode.mkMul id1 id2))
  | .negPat p1 =>
    match instantiate g p1 subst with
    | none => none
    | some (id1, g1) => some (g1.add (ENode.mkNeg id1))
  | .smulPat c p1 =>
    match instantiate g p1 subst with
    | none => none
    | some (id1, g1) => some (g1.add (ENode.mkSmul c id1))

/-- Apply a rewrite rule at a specific class.
    If the rule has a side condition check, it is verified for each
    substitution before the rule fires. -/
def applyRuleAt (g : EGraph) (rule : RewriteRule) (classId : EClassId) : EGraph :=
  let results := ematch g rule.lhs classId
  results.foldl (fun acc subst =>
    -- Check side condition if present
    let condMet := match rule.sideCondCheck with
      | some check => check acc subst
      | none => true
    if !condMet then acc
    else
      match instantiate acc rule.rhs subst with
      | none => acc
      | some (rhsId, acc') =>
        let (canonLhs, acc'') := acc'.find classId
        let (canonRhs, acc''') := acc''.find rhsId
        if canonLhs == canonRhs then acc'''
        else acc'''.merge classId rhsId
  ) g

/-- Apply a rule to all classes in the e-graph. -/
def applyRule (g : EGraph) (rule : RewriteRule) : EGraph :=
  let allClasses := g.classes.toList.map (·.1)
  allClasses.foldl (fun acc classId => applyRuleAt acc rule classId) g

/-- Apply a list of rules once across the entire e-graph. -/
def applyRules (g : EGraph) (rules : List RewriteRule) : EGraph :=
  rules.foldl applyRule g

end AmoLean.EGraph.Verified
