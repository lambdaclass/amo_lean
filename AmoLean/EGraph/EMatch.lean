/-
  AMO-Lean: E-Graph E-Matching

  E-matching: buscar todas las instancias de un patrón en el E-graph.
  Un patrón es como una expresión pero con "variables de patrón" que
  pueden matchear cualquier e-class.
-/

import AmoLean.EGraph.Basic

namespace AmoLean.EGraph

/-! ## Parte 1: Patrones -/

/-- Variable de patrón (diferente de variable de expresión) -/
abbrev PatVarId := Nat

/-- Patrón para E-matching.
    Similar a Expr pero con variables de patrón que pueden matchear cualquier e-class. -/
inductive Pattern where
  | patVar : PatVarId → Pattern              -- Variable de patrón (?a, ?b, etc.)
  | const : Int → Pattern                     -- Constante literal
  | var : Nat → Pattern                       -- Variable de expresión (x, y, etc.)
  | add : Pattern → Pattern → Pattern         -- Suma
  | mul : Pattern → Pattern → Pattern         -- Multiplicación
  deriving Repr, BEq, Inhabited

namespace Pattern

/-- Notación conveniente para variables de patrón -/
def pvar (n : Nat) : Pattern := patVar n

/-- Contar variables de patrón en un patrón -/
def numPatVars : Pattern → Nat
  | patVar n => n + 1
  | const _ => 0
  | var _ => 0
  | add p1 p2 => max (numPatVars p1) (numPatVars p2)
  | mul p1 p2 => max (numPatVars p1) (numPatVars p2)

end Pattern

/-! ## Parte 2: Sustituciones -/

/-- Una sustitución mapea variables de patrón a e-class IDs -/
abbrev Substitution := Std.HashMap PatVarId EClassId

namespace Substitution

/-- Sustitución vacía -/
def empty : Substitution := Std.HashMap.empty

/-- Intentar extender una sustitución con un nuevo binding.
    Falla si la variable ya está asignada a un ID diferente. -/
def extend (subst : Substitution) (pv : PatVarId) (id : EClassId) : Option Substitution :=
  match subst.get? pv with
  | none => some (subst.insert pv id)
  | some existingId => if existingId == id then some subst else none

/-- Obtener el binding de una variable de patrón -/
def lookup (subst : Substitution) (pv : PatVarId) : Option EClassId :=
  subst.get? pv

end Substitution

/-! ## Parte 3: E-Matching -/

/-- Resultado de E-matching: lista de sustituciones válidas -/
abbrev MatchResult := List Substitution

/-- E-match: encontrar todas las sustituciones que hacen que el patrón
    coincida con algún término representado por la e-class dada.

    Algoritmo:
    - Para patVar: asignar la e-class a la variable (o verificar consistencia)
    - Para const/var: verificar que existe un nodo correspondiente en la clase
    - Para add/mul: para cada nodo add/mul en la clase, recursivamente matchear hijos -/
partial def ematch (g : EGraph) (pattern : Pattern) (classId : EClassId)
    (subst : Substitution := Substitution.empty) : MatchResult :=
  let (canonId, g') := g.find classId
  match pattern with
  | .patVar pv =>
    -- Variable de patrón: intentar asignar esta clase
    match subst.extend pv canonId with
    | some subst' => [subst']
    | none => []

  | .const c =>
    -- Constante: verificar que existe un nodo const c en la clase
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkConst c) then [subst] else []

  | .var v =>
    -- Variable de expresión: verificar que existe un nodo var v en la clase
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      if eclass.nodes.contains (ENode.mkVar v) then [subst] else []

  | .add p1 p2 =>
    -- Suma: buscar nodos add en la clase y recursivamente matchear
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.fold (init := []) fun acc node =>
        match node.op with
        | .add childA childB =>
          -- Matchear p1 con childA y p2 con childB
          let matches1 := ematch g' p1 childA subst
          matches1.foldl (fun acc2 subst1 =>
            let matches2 := ematch g' p2 childB subst1
            acc2 ++ matches2
          ) acc
        | _ => acc

  | .mul p1 p2 =>
    -- Multiplicación: similar a suma
    match g'.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.fold (init := []) fun acc node =>
        match node.op with
        | .mul childA childB =>
          let matches1 := ematch g' p1 childA subst
          matches1.foldl (fun acc2 subst1 =>
            let matches2 := ematch g' p2 childB subst1
            acc2 ++ matches2
          ) acc
        | _ => acc

/-- Buscar todas las instancias de un patrón en todo el E-graph.
    Retorna lista de (EClassId, Substitution) para cada match. -/
def searchPattern (g : EGraph) (pattern : Pattern) : List (EClassId × Substitution) :=
  g.classes.fold (init := []) fun acc classId _ =>
    let results := ematch g pattern classId
    acc ++ results.map (classId, ·)

/-! ## Parte 4: Reglas de Reescritura para E-graph -/

/-- Una regla de reescritura: patrón LHS → patrón RHS.
    Cuando LHS matchea, se añade RHS al E-graph y se hace merge. -/
structure RewriteRule where
  name : String
  lhs : Pattern       -- Lado izquierdo (lo que buscamos)
  rhs : Pattern       -- Lado derecho (lo que añadimos)
  deriving Repr

namespace RewriteRule

/-- Crear una regla con nombre -/
def make (name : String) (lhs rhs : Pattern) : RewriteRule :=
  { name, lhs, rhs }

/-! ### Reglas algebraicas básicas -/

-- a + 0 → a
def addZeroRight : RewriteRule :=
  make "add_zero_right" (.add (.patVar 0) (.const 0)) (.patVar 0)

-- 0 + a → a
def addZeroLeft : RewriteRule :=
  make "add_zero_left" (.add (.const 0) (.patVar 0)) (.patVar 0)

-- a * 1 → a
def mulOneRight : RewriteRule :=
  make "mul_one_right" (.mul (.patVar 0) (.const 1)) (.patVar 0)

-- 1 * a → a
def mulOneLeft : RewriteRule :=
  make "mul_one_left" (.mul (.const 1) (.patVar 0)) (.patVar 0)

-- a * 0 → 0
def mulZeroRight : RewriteRule :=
  make "mul_zero_right" (.mul (.patVar 0) (.const 0)) (.const 0)

-- 0 * a → 0
def mulZeroLeft : RewriteRule :=
  make "mul_zero_left" (.mul (.const 0) (.patVar 0)) (.const 0)

-- a * (b + c) → a*b + a*c (distributividad izquierda)
def distribLeft : RewriteRule :=
  make "distrib_left"
    (.mul (.patVar 0) (.add (.patVar 1) (.patVar 2)))
    (.add (.mul (.patVar 0) (.patVar 1)) (.mul (.patVar 0) (.patVar 2)))

-- (a + b) * c → a*c + b*c (distributividad derecha)
def distribRight : RewriteRule :=
  make "distrib_right"
    (.mul (.add (.patVar 0) (.patVar 1)) (.patVar 2))
    (.add (.mul (.patVar 0) (.patVar 2)) (.mul (.patVar 1) (.patVar 2)))

-- a*b + a*c → a*(b+c) (factorización)
def factorLeft : RewriteRule :=
  make "factor_left"
    (.add (.mul (.patVar 0) (.patVar 1)) (.mul (.patVar 0) (.patVar 2)))
    (.mul (.patVar 0) (.add (.patVar 1) (.patVar 2)))

/-- Conjunto de reglas algebraicas básicas -/
def basicRules : List RewriteRule := [
  addZeroRight, addZeroLeft,
  mulOneRight, mulOneLeft,
  mulZeroRight, mulZeroLeft
]

/-- Reglas extendidas con distributividad -/
def extendedRules : List RewriteRule :=
  basicRules ++ [distribLeft, distribRight, factorLeft]

end RewriteRule

/-! ## Parte 5: Instanciación de Patrones -/

/-- Instanciar un patrón con una sustitución, añadiendo nodos al E-graph.
    Retorna el ID de la e-class resultante. -/
partial def instantiate (g : EGraph) (pattern : Pattern) (subst : Substitution)
    : Option (EClassId × EGraph) :=
  match pattern with
  | .patVar pv =>
    match subst.lookup pv with
    | some id => some (id, g)
    | none => none  -- Variable no asignada

  | .const c =>
    some (g.add (ENode.mkConst c))

  | .var v =>
    some (g.add (ENode.mkVar v))

  | .add p1 p2 =>
    match instantiate g p1 subst with
    | none => none
    | some (id1, g1) =>
      match instantiate g1 p2 subst with
      | none => none
      | some (id2, g2) =>
        some (g2.add (ENode.mkAdd id1 id2))

  | .mul p1 p2 =>
    match instantiate g p1 subst with
    | none => none
    | some (id1, g1) =>
      match instantiate g1 p2 subst with
      | none => none
      | some (id2, g2) =>
        some (g2.add (ENode.mkMul id1 id2))

/-! ## Parte 6: Aplicación de Reglas -/

/-- Aplicar una regla de reescritura en una e-class específica.
    Si el LHS matchea, instancia el RHS y hace merge. -/
def applyRuleAt (g : EGraph) (rule : RewriteRule) (classId : EClassId) : EGraph :=
  let results := ematch g rule.lhs classId
  results.foldl (fun acc subst =>
    match instantiate acc rule.rhs subst with
    | none => acc
    | some (rhsId, acc') =>
      -- Merge: el LHS (classId) es equivalente al RHS
      acc'.merge classId rhsId
  ) g

/-- Aplicar una regla en todo el E-graph. -/
def applyRule (g : EGraph) (rule : RewriteRule) : EGraph :=
  let allClasses := g.classes.toList.map (·.1)
  allClasses.foldl (fun acc classId =>
    applyRuleAt acc rule classId
  ) g

/-- Aplicar una lista de reglas una vez en todo el E-graph. -/
def applyRules (g : EGraph) (rules : List RewriteRule) : EGraph :=
  rules.foldl applyRule g

end AmoLean.EGraph
