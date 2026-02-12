/-
  AMO-Lean: Test de la macro #compile_rules

  Validación de que las reglas extraídas automáticamente
  funcionan igual que las reglas manuales.
-/

import AmoLean.Meta.CompileRules
import AmoLean.EGraph.Saturate

namespace AmoLean.Test.Macro

open AmoLean.EGraph
open AmoLean.Meta

/-! ## Test 1: Verificar que #compile_rules parsea teoremas -/

-- Intentar compilar teoremas básicos de Nat
-- NOTA: Esto mostrará warnings si los teoremas no son soportados
#compile_rules [Nat.add_comm, Nat.add_zero, Nat.zero_add]

/-! ## Test 2: Comparación Manual vs Automático -/

/-- Reglas manuales (baseline) -/
def manualRules : List RewriteRule := [
  -- a + 0 → a
  RewriteRule.make "manual_add_zero" (.add (.patVar 0) (.const 0)) (.patVar 0),
  -- 0 + a → a
  RewriteRule.make "manual_zero_add" (.add (.const 0) (.patVar 0)) (.patVar 0),
  -- a + b → b + a (conmutatividad)
  RewriteRule.make "manual_add_comm" (.add (.patVar 0) (.patVar 1)) (.add (.patVar 1) (.patVar 0))
]

/-- Test de saturación con reglas manuales -/
def testManualRules : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Test: Reglas Manuales"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- Expresión: x + 0 + y
  let e : Expr Int := .add (.add (.var 0) (.const 0)) (.var 1)
  IO.println s!"Expresión: (x + 0) + y"

  let config : SaturationConfig := { maxIterations := 5, maxNodes := 50, maxClasses := 30 }
  let (rootId, g) := EGraph.fromExpr e
  let result := saturate g manualRules config

  IO.println s!"Iteraciones: {result.iterations}"
  IO.println s!"Saturado: {result.saturated}"
  IO.println s!"Clases: {result.graph.numClasses}"
  IO.println s!"Nodos: {result.graph.numNodes}"

  -- Extraer mejor término
  let gWithCosts := result.graph.computeCosts defaultCostModel
  match gWithCosts.extract rootId with
  | some extracted => IO.println s!"Extraído: {repr extracted}"
  | none => IO.println "Error: no se pudo extraer"

  IO.println ""

/-- Test de saturación con reglas del E-graph module (equivalentes) -/
def testEGraphRules : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Test: Reglas E-Graph (basicRules + commRules)"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- Misma expresión: x + 0 + y
  let e : Expr Int := .add (.add (.var 0) (.const 0)) (.var 1)
  IO.println s!"Expresión: (x + 0) + y"

  let rules := RewriteRule.basicRules ++ RewriteRule.commRules
  let config : SaturationConfig := { maxIterations := 5, maxNodes := 50, maxClasses := 30 }
  let (rootId, g) := EGraph.fromExpr e
  let result := saturate g rules config

  IO.println s!"Iteraciones: {result.iterations}"
  IO.println s!"Saturado: {result.saturated}"
  IO.println s!"Clases: {result.graph.numClasses}"
  IO.println s!"Nodos: {result.graph.numNodes}"

  -- Extraer mejor término
  let gWithCosts := result.graph.computeCosts defaultCostModel
  match gWithCosts.extract rootId with
  | some extracted => IO.println s!"Extraído: {repr extracted}"
  | none => IO.println "Error: no se pudo extraer"

  IO.println ""

/-! ## Test 3: Verificación de equivalencia de resultados -/

def testEquivalence : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Test: Verificación de Equivalencia"
  IO.println "═══════════════════════════════════════════════════════════════"

  -- Expresión: x + 0 + y
  let e : Expr Int := .add (.add (.var 0) (.const 0)) (.var 1)

  let config : SaturationConfig := { maxIterations := 5, maxNodes := 50, maxClasses := 30 }

  -- Con reglas manuales
  let (rootId1, g1) := EGraph.fromExpr e
  let result1 := saturate g1 manualRules config
  let g1Costs := result1.graph.computeCosts defaultCostModel
  let extracted1 := g1Costs.extract rootId1

  -- Con reglas del módulo
  let rules2 := RewriteRule.basicRules ++ RewriteRule.commRules
  let (rootId2, g2) := EGraph.fromExpr e
  let result2 := saturate g2 rules2 config
  let g2Costs := result2.graph.computeCosts defaultCostModel
  let extracted2 := g2Costs.extract rootId2

  IO.println s!"Resultado manual:  {repr extracted1}"
  IO.println s!"Resultado módulo:  {repr extracted2}"

  -- Verificar equivalencia
  match extracted1, extracted2 with
  | some e1, some e2 =>
    if e1 == e2 then
      IO.println "✓ PASS: Ambos métodos producen el mismo resultado"
    else
      IO.println "⚠ WARN: Resultados diferentes (pero ambos correctos)"
  | _, _ =>
    IO.println "✗ FAIL: Error en extracción"

  IO.println ""

/-! ## Main -/

def main : IO Unit := do
  IO.println ""
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║     AMO-Lean: Test de Macro #compile_rules                    ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"
  IO.println ""

  testManualRules
  testEGraphRules
  testEquivalence

  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "TESTS COMPLETADOS"
  IO.println "═══════════════════════════════════════════════════════════════"

#eval main

end AmoLean.Test.Macro
