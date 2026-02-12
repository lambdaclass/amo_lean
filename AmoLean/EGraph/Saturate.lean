/-
  AMO-Lean: E-Graph Equality Saturation

  Saturación: aplicar reglas de reescritura repetidamente hasta punto fijo
  o hasta alcanzar un límite de iteraciones/tamaño.
-/

import AmoLean.EGraph.EMatch

namespace AmoLean.EGraph

/-! ## Parte 1: Configuración de Saturación -/

/-- Configuración para el proceso de saturación -/
structure SaturationConfig where
  maxIterations : Nat := 10        -- Máximo de iteraciones (bajo para compile-time)
  maxNodes : Nat := 100            -- Máximo de nodos en el E-graph
  maxClasses : Nat := 50           -- Máximo de e-classes
  costModel : EGraphCostModel := defaultCostModel
  deriving Repr, Inhabited

/-- Configuración para uso en runtime con más capacidad -/
def SaturationConfig.large : SaturationConfig :=
  { maxIterations := 30, maxNodes := 10000, maxClasses := 5000 }

/-- Resultado de la saturación -/
structure SaturationResult where
  graph : EGraph                   -- E-graph resultante
  iterations : Nat                 -- Iteraciones realizadas
  saturated : Bool                 -- ¿Se alcanzó punto fijo?
  reason : String                  -- Razón de terminación
  deriving Inhabited

/-! ## Parte 2: Estadísticas de Iteración -/

/-- Estadísticas de una iteración de saturación -/
structure IterationStats where
  nodesBefore : Nat
  nodesAfter : Nat
  classesBefore : Nat
  classesAfter : Nat
  rulesApplied : Nat
  deriving Repr

/-- Calcular estadísticas antes/después de una iteración -/
def mkIterationStats (before after : EGraph) (rulesApplied : Nat) : IterationStats :=
  { nodesBefore := before.numNodes
  , nodesAfter := after.numNodes
  , classesBefore := before.numClasses
  , classesAfter := after.numClasses
  , rulesApplied := rulesApplied }

/-! ## Parte 3: Saturación -/

/-- Una iteración de saturación: aplicar todas las reglas una vez. -/
def saturateStep (g : EGraph) (rules : List RewriteRule) : EGraph :=
  let g1 := applyRules g rules
  let g2 := g1.rebuild
  g2

/-- Verificar si se alcanzaron los límites -/
def checkLimits (g : EGraph) (config : SaturationConfig) : Option String :=
  if g.numNodes > config.maxNodes then
    some s!"Límite de nodos alcanzado ({g.numNodes} > {config.maxNodes})"
  else if g.numClasses > config.maxClasses then
    some s!"Límite de clases alcanzado ({g.numClasses} > {config.maxClasses})"
  else
    none

/-- Verificar si se alcanzó punto fijo (sin cambios en la iteración) -/
def reachedFixpoint (before after : EGraph) : Bool :=
  before.numNodes == after.numNodes && before.numClasses == after.numClasses

/-- Saturación con límites configurables.
    Aplica reglas hasta punto fijo o límite. -/
def saturate (g : EGraph) (rules : List RewriteRule)
    (config : SaturationConfig := {}) : SaturationResult :=
  let rec loop (current : EGraph) (iter : Nat) : Nat → SaturationResult
    | 0 =>
      { graph := current
      , iterations := iter
      , saturated := false
      , reason := s!"Límite de iteraciones alcanzado ({config.maxIterations})" }
    | fuel + 1 =>
      -- Verificar límites antes de la iteración
      match checkLimits current config with
      | some reason =>
        { graph := current
        , iterations := iter
        , saturated := false
        , reason := reason }
      | none =>
        -- Aplicar una iteración
        let next := saturateStep current rules
        -- Verificar punto fijo
        if reachedFixpoint current next then
          { graph := next
          , iterations := iter + 1
          , saturated := true
          , reason := "Punto fijo alcanzado" }
        else
          loop next (iter + 1) fuel
  loop g 0 config.maxIterations

/-! ## Parte 4: Saturación con Extracción -/

/-- Saturar y extraer el mejor término desde la e-class raíz. -/
def saturateAndExtract (g : EGraph) (rootId : EClassId) (rules : List RewriteRule)
    (config : SaturationConfig := {}) : (Option (Expr Int) × SaturationResult) :=
  let result := saturate g rules config
  let gWithCosts := result.graph.computeCosts config.costModel
  let extracted := gWithCosts.extract rootId
  (extracted, { result with graph := gWithCosts })

/-- Optimizar una expresión usando E-graph y equality saturation. -/
def optimize (expr : Expr Int) (rules : List RewriteRule := RewriteRule.basicRules)
    (config : SaturationConfig := {}) : (Option (Expr Int) × SaturationResult) :=
  let (rootId, g) := EGraph.fromExpr expr
  saturateAndExtract g rootId rules config

/-! ## Parte 5: Funciones de Conveniencia -/

/-- Optimizar con reglas básicas (identidades algebraicas) -/
def optimizeBasic (expr : Expr Int) : Option (Expr Int) :=
  let (result, _) := optimize expr RewriteRule.basicRules
  result

/-- Optimizar con reglas extendidas (incluye distributividad) -/
def optimizeExtended (expr : Expr Int) : Option (Expr Int) :=
  let (result, _) := optimize expr RewriteRule.extendedRules
  result

/-- Optimizar con reglas "seguras" (sin conmutatividad ni asociatividad).
    Equivalente a extendedRules. -/
def optimizeSafe (expr : Expr Int) : Option (Expr Int) :=
  let (result, _) := optimize expr RewriteRule.safeRules
  result

/-- Optimizar con todas las reglas de semiring (incluye conmutatividad y asociatividad).
    ADVERTENCIA: Puede causar explosión del E-graph. Usar límites apropiados. -/
def optimizeSemiring (expr : Expr Int) (config : SaturationConfig := { maxIterations := 10, maxNodes := 1000 }) : Option (Expr Int) :=
  let (result, _) := optimize expr RewriteRule.semiringRules config
  result

/-- Optimizar con conmutatividad (permite encontrar formas canónicas) -/
def optimizeWithComm (expr : Expr Int) (config : SaturationConfig := { maxIterations := 10, maxNodes := 500 }) : Option (Expr Int) :=
  let rules := RewriteRule.basicRules ++ RewriteRule.commRules
  let (result, _) := optimize expr rules config
  result

/-! ## Parte 6: Tests -/

section Tests

open Expr

-- Test 1: Simplificación básica x + 0 → x
#eval do
  let expr : Expr Int := .add (.var 0) (.const 0)  -- x + 0
  IO.println "Test 1: x + 0 → x"
  match optimizeBasic expr with
  | some result => IO.println s!"  Resultado: {repr result}"
  | none => IO.println "  Error: no se pudo optimizar"

-- Test 2: Simplificación x * 1 → x
#eval do
  let expr : Expr Int := .mul (.var 0) (.const 1)  -- x * 1
  IO.println "Test 2: x * 1 → x"
  match optimizeBasic expr with
  | some result => IO.println s!"  Resultado: {repr result}"
  | none => IO.println "  Error: no se pudo optimizar"

-- Test 3: Simplificación compuesta (x + 0) * 1 → x
#eval do
  let expr : Expr Int := .mul (.add (.var 0) (.const 0)) (.const 1)
  IO.println "Test 3: (x + 0) * 1 → x"
  match optimizeBasic expr with
  | some result => IO.println s!"  Resultado: {repr result}"
  | none => IO.println "  Error: no se pudo optimizar"

-- Test 4: x * 0 → 0
#eval do
  let expr : Expr Int := .mul (.add (.var 0) (.var 1)) (.const 0)  -- (x + y) * 0
  IO.println "Test 4: (x + y) * 0 → 0"
  match optimizeBasic expr with
  | some result => IO.println s!"  Resultado: {repr result}"
  | none => IO.println "  Error: no se pudo optimizar"

-- Test 5: Resultado de saturación
#eval do
  let expr : Expr Int := .add (.mul (.var 0) (.const 1)) (.const 0)  -- x*1 + 0
  IO.println "Test 5: x*1 + 0 (detalles de saturación)"
  let (result, satResult) := optimize expr RewriteRule.basicRules
  IO.println s!"  Iteraciones: {satResult.iterations}"
  IO.println s!"  Saturado: {satResult.saturated}"
  IO.println s!"  Razón: {satResult.reason}"
  IO.println s!"  Clases finales: {satResult.graph.numClasses}"
  IO.println s!"  Nodos finales: {satResult.graph.numNodes}"
  match result with
  | some r => IO.println s!"  Resultado: {repr r}"
  | none => IO.println "  Error: no se pudo extraer"

-- Test 6: Verificar que las colecciones de reglas existen
#eval do
  IO.println "Test 6: Verificación de colecciones de reglas"
  IO.println s!"  basicRules: {RewriteRule.basicRules.length} reglas"
  IO.println s!"  extendedRules: {RewriteRule.extendedRules.length} reglas"
  IO.println s!"  safeRules: {RewriteRule.safeRules.length} reglas"
  IO.println s!"  commRules: {RewriteRule.commRules.length} reglas"
  IO.println s!"  assocRules: {RewriteRule.assocRules.length} reglas"
  IO.println s!"  semiringRules: {RewriteRule.semiringRules.length} reglas"

-- NOTA: Las reglas de conmutatividad y asociatividad están implementadas
-- pero pueden causar explosión del E-graph. Para tests en runtime:
--   #eval optimizeSafe expr                                     -- sin comm/assoc
--   #eval optimizeWithComm expr { maxIterations := 2, maxNodes := 20 }
--   #eval optimizeSemiring expr { maxIterations := 2, maxNodes := 20 }
-- Para producción, usar SaturationConfig.large

end Tests

end AmoLean.EGraph
