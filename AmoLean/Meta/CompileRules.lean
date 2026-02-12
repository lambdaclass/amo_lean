/-
  AMO-Lean: Metaprogramación - Macro #compile_rules

  Este módulo implementa la extracción automática de reglas de reescritura
  desde teoremas de Mathlib usando metaprogramación de Lean 4.
-/

import Lean
import AmoLean.EGraph.EMatch

namespace AmoLean.Meta

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open AmoLean.EGraph

-- Alias para evitar conflictos con AmoLean.Expr
abbrev LeanExpr := Lean.Expr

/-! ## Parte 1: Conversión de Lean.Expr a Pattern -/

/-- Estado para tracking de variables durante la conversión -/
structure ConvertState where
  varMap : Std.HashMap FVarId Nat  -- Mapeo de FVarId a PatVarId
  nextVar : Nat                     -- Próximo PatVarId disponible
  deriving Inhabited

/-- Monad para conversión con estado -/
abbrev ConvertM := StateT ConvertState MetaM

/-- Obtener o crear un PatVarId para una variable libre -/
def getOrCreatePatVar (fvarId : FVarId) : ConvertM Nat := do
  let state ← get
  match state.varMap.get? fvarId with
  | some n => return n
  | none =>
    let n := state.nextVar
    set { state with varMap := state.varMap.insert fvarId n, nextVar := n + 1 }
    return n

/-- Intentar extraer un argumento de aplicación en posición dada -/
def getAppArg? (e : LeanExpr) (n : Nat) : Option LeanExpr :=
  let args := e.getAppArgs
  if h : n < args.size then some args[n] else none

/-- Detectar si es una aplicación de una función específica con al menos n argumentos -/
def isAppOfWithArity? (e : LeanExpr) (fn : Name) (minArity : Nat) : Option (Array LeanExpr) :=
  if e.isAppOf fn then
    let args := e.getAppArgs
    if args.size >= minArity then some args else none
  else
    none

/-- Convertir una expresión Lean a Pattern.
    Solo soporta: variables libres, literales Int, Add.add, HMul.hMul -/
partial def exprToPatternAux (e : LeanExpr) : ConvertM (Option Pattern) := do
  let e ← instantiateMVars e
  match e with
  -- Variable libre → PatVar
  | .fvar fvarId =>
    let n ← getOrCreatePatVar fvarId
    return some (.patVar n)

  -- Literal numérico
  | .lit (.natVal n) =>
    return some (.const (Int.ofNat n))

  -- Aplicación de función
  | .app .. =>
    -- Intentar detectar Add.add (4 args: tipo, instancia, lhs, rhs)
    if let some args := isAppOfWithArity? e ``Add.add 4 then
      let lhsP ← exprToPatternAux args[2]!
      let rhsP ← exprToPatternAux args[3]!
      match lhsP, rhsP with
      | some l, some r => return some (.add l r)
      | _, _ => return none
    -- Intentar detectar HAdd.hAdd (6 args)
    else if let some args := isAppOfWithArity? e ``HAdd.hAdd 6 then
      let lhsP ← exprToPatternAux args[4]!
      let rhsP ← exprToPatternAux args[5]!
      match lhsP, rhsP with
      | some l, some r => return some (.add l r)
      | _, _ => return none
    -- Intentar detectar Mul.mul (4 args)
    else if let some args := isAppOfWithArity? e ``Mul.mul 4 then
      let lhsP ← exprToPatternAux args[2]!
      let rhsP ← exprToPatternAux args[3]!
      match lhsP, rhsP with
      | some l, some r => return some (.mul l r)
      | _, _ => return none
    -- Intentar detectar HMul.hMul (6 args)
    else if let some args := isAppOfWithArity? e ``HMul.hMul 6 then
      let lhsP ← exprToPatternAux args[4]!
      let rhsP ← exprToPatternAux args[5]!
      match lhsP, rhsP with
      | some l, some r => return some (.mul l r)
      | _, _ => return none
    -- OfNat.ofNat para literales (3 args: tipo, valor, instancia)
    else if let some args := isAppOfWithArity? e ``OfNat.ofNat 3 then
      match args[1]! with
      | .lit (.natVal v) => return some (.const (Int.ofNat v))
      | _ => return none
    -- HPow.hPow para potencias (6 args: α, β, γ, inst, base, exp)
    else if let some args := isAppOfWithArity? e ``HPow.hPow 6 then
      let baseP ← exprToPatternAux args[4]!
      -- El exponente debe ser un literal Nat
      match args[5]! with
      | .lit (.natVal n) =>
        match baseP with
        | some base => return some (.pow base n)
        | none => return none
      | _ =>
        -- Intentar extraer exponente de OfNat.ofNat
        if let some expArgs := isAppOfWithArity? args[5]! ``OfNat.ofNat 3 then
          match expArgs[1]! with
          | .lit (.natVal n) =>
            match baseP with
            | some base => return some (.pow base n)
            | none => return none
          | _ => return none
        else
          return none
    -- Pow.pow para potencias (4 args: α, inst, base, exp)
    else if let some args := isAppOfWithArity? e ``Pow.pow 4 then
      let baseP ← exprToPatternAux args[2]!
      match args[3]! with
      | .lit (.natVal n) =>
        match baseP with
        | some base => return some (.pow base n)
        | none => return none
      | _ =>
        if let some expArgs := isAppOfWithArity? args[3]! ``OfNat.ofNat 3 then
          match expArgs[1]! with
          | .lit (.natVal n) =>
            match baseP with
            | some base => return some (.pow base n)
            | none => return none
          | _ => return none
        else
          return none
    else
      return none

  -- Constante 0
  | .const ``Nat.zero _ => return some (.const 0)

  -- Otros casos
  | _ =>
    return none

/-- Extraer LHS y RHS de una igualdad (Eq lhs rhs) -/
def extractEqualityFromExpr (e : LeanExpr) : MetaM (Option (LeanExpr × LeanExpr)) := do
  let e ← instantiateMVars e
  -- Buscar Eq.{u} α lhs rhs
  if let some (_, lhs, rhs) := e.eq? then
    return some (lhs, rhs)
  else
    return none

/-- Procesar un teorema y extraer la regla de reescritura -/
def processTheorem (name : Name) : MetaM (Option (String × Pattern × Pattern)) := do
  let info ← getConstInfo name
  let type := info.type

  -- Abrir los foralls para obtener el cuerpo
  forallTelescope type fun _args body => do
    -- Extraer la igualdad
    match ← extractEqualityFromExpr body with
    | none =>
      logWarning m!"Teorema {name} no es una igualdad"
      return none
    | some (lhs, rhs) =>
      -- Convertir LHS y RHS a Pattern
      let initState : ConvertState := { varMap := {}, nextVar := 0 }
      let (lhsPatOpt, state1) ← (exprToPatternAux lhs).run initState
      let (rhsPatOpt, _) ← (exprToPatternAux rhs).run state1

      match lhsPatOpt, rhsPatOpt with
      | some lhsPat, some rhsPat =>
        return some (name.toString, lhsPat, rhsPat)
      | _, _ =>
        logWarning m!"No se pudo convertir {name} a Pattern (expresión no soportada)"
        return none

/-! ## Parte 2: Resultado de compilación -/

/-- Resultado de compilar una regla -/
structure CompiledRule where
  name : String
  lhs : Pattern
  rhs : Pattern
  deriving Repr

/-- Compilar una lista de teoremas a reglas -/
def compileRules (names : Array Name) : MetaM (Array CompiledRule) := do
  let mut rules := #[]
  for name in names do
    match ← processTheorem name with
    | some (ruleName, lhs, rhs) =>
      rules := rules.push { name := ruleName, lhs, rhs }
    | none => pure ()
  return rules

/-! ## Parte 3: Comando #compile_rules -/

/-- Sintaxis del comando #compile_rules -/
syntax (name := compileRulesCmd) "#compile_rules" "[" ident,* "]" : command

/-- Elaboración del comando -/
@[command_elab compileRulesCmd]
def elabCompileRulesCmd : CommandElab := fun stx => do
  match stx with
  | `(#compile_rules [$ids,*]) =>
    let names : Array Name := ids.getElems.map fun id => id.getId
    -- Ejecutar en MetaM
    let rules ← liftTermElabM do
      compileRules names

    -- Mostrar las reglas compiladas
    for rule in rules do
      logInfo m!"Regla compilada: {rule.name}"
      logInfo m!"  LHS: {repr rule.lhs}"
      logInfo m!"  RHS: {repr rule.rhs}"

    -- Generar definiciones
    if rules.size > 0 then
      logInfo m!"✓ {rules.size} reglas compiladas exitosamente"
    else
      logWarning "No se compilaron reglas"

  | _ => throwUnsupportedSyntax

/-! ## Parte 4: Función para obtener reglas en runtime -/

/-- Obtener reglas compiladas como RewriteRule -/
def getCompiledRules (names : Array Name) : MetaM (Array RewriteRule) := do
  let compiled ← compileRules names
  return compiled.map fun r => RewriteRule.make r.name r.lhs r.rhs

end AmoLean.Meta
