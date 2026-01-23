/-
  AMO-Lean: Benchmarks de Fase 3 - Validación de Reglas Mathlib

  Este archivo valida:
  1. Correctness: Las reglas de Mathlib se activan correctamente
  2. Performance: La optimización de applyRuleAt resuelve la explosión
  3. Stress Test: Comportamiento con expresiones complejas
-/

import AmoLean.EGraph.Saturate

namespace AmoLean.Benchmarks.Phase3

open AmoLean.EGraph

/-! ## Nivel 1: Verificación de Integración (Correctness) -/

/-- Verificar que addComm genera ambas formas en la misma E-class -/
def testLevel1_CommCorrectness : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "NIVEL 1: Verificación de Integración (Correctness)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Expresión: a + b (donde a=var 0, b=var 1)
  let e : Expr Int := .add (.var 0) (.var 1)
  IO.println s!"Expresión inicial: a + b"

  -- Configuración con límites bajos para este test
  let config : SaturationConfig := { maxIterations := 3, maxNodes := 30, maxClasses := 20 }

  -- Ejecutar con reglas de conmutatividad
  let rules := RewriteRule.basicRules ++ RewriteRule.commRules
  let (rootId, g0) := EGraph.fromExpr e
  let result := saturate g0 rules config

  IO.println s!"Iteraciones: {result.iterations}"
  IO.println s!"Saturado: {result.saturated}"
  IO.println s!"Razón: {result.reason}"
  IO.println s!"Clases finales: {result.graph.numClasses}"
  IO.println s!"Nodos finales: {result.graph.numNodes}"

  -- Verificar que la clase raíz contiene nodos add
  let (canonRoot, g1) := result.graph.find rootId
  match g1.classes.get? canonRoot with
  | none => IO.println "ERROR: No se encontró la clase raíz"
  | some eclass =>
    IO.println s!"Nodos en clase raíz: {eclass.nodes.size}"
    -- Buscar si hay nodos add con hijos en ambos órdenes
    let addNodes := eclass.nodes.filter fun n =>
      match n.op with
      | .add _ _ => true
      | _ => false
    IO.println s!"Nodos 'add' en clase raíz: {addNodes.size}"
    if addNodes.size >= 2 then
      IO.println "✓ PASS: La clase contiene múltiples formas (a+b y b+a)"
    else if addNodes.size == 1 then
      IO.println "⚠ WARN: Solo 1 nodo add (puede ser correcto si se deduplicó)"
    else
      IO.println "✗ FAIL: No se encontraron nodos add"

  IO.println ""

/-! ## Nivel 2: Prueba de Fuego de Asociatividad (Performance) -/

/-- Medir tiempo de una operación IO -/
def timeIO (name : String) (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result ← action
  let finish ← IO.monoMsNow
  let elapsed := finish - start
  IO.println s!"  {name}: {elapsed} ms"
  return (result, elapsed)

/-- Comparar rendimiento de optimizeWithComm vs optimizeSafe -/
def testLevel2_AssocPerformance : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "NIVEL 2: Prueba de Fuego de Asociatividad (Performance)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Expresión profunda: a + (b + (c + d))
  let e : Expr Int := .add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3)))
  IO.println "Expresión: a + (b + (c + d))"
  IO.println ""

  -- Configuración controlada
  let configSafe : SaturationConfig := { maxIterations := 5, maxNodes := 50 }
  let configComm : SaturationConfig := { maxIterations := 3, maxNodes := 30 }

  IO.println "Midiendo tiempos..."

  -- Test con reglas seguras (sin comm/assoc)
  let (resultSafe, timeSafe) ← timeIO "optimizeSafe" do
    let (_, g) := EGraph.fromExpr e
    return saturate g RewriteRule.safeRules configSafe

  -- Test con reglas de conmutatividad
  let (resultComm, timeComm) ← timeIO "optimizeWithComm" do
    let rules := RewriteRule.basicRules ++ RewriteRule.commRules
    let (_, g) := EGraph.fromExpr e
    return saturate g rules configComm

  IO.println ""
  IO.println "Resultados:"
  IO.println s!"  Safe:     {resultSafe.iterations} iter, {resultSafe.graph.numNodes} nodos, {resultSafe.graph.numClasses} clases"
  IO.println s!"  WithComm: {resultComm.iterations} iter, {resultComm.graph.numNodes} nodos, {resultComm.graph.numClasses} clases"

  -- Calcular ratio
  let ratio := if timeSafe > 0 then (timeComm * 100) / timeSafe else 0
  IO.println ""
  IO.println s!"Ratio de tiempo (comm/safe): {ratio}%"

  if timeComm < 1000 then
    IO.println "✓ PASS: optimizeWithComm completó en < 1 segundo"
  else
    IO.println "⚠ WARN: optimizeWithComm tardó > 1 segundo"

  if ratio < 7000 then -- menos de 70x
    IO.println "✓ PASS: No hay explosión 70x como en greedy"
  else
    IO.println "✗ FAIL: Detectada explosión similar a greedy"

  IO.println ""

/-! ## Nivel 3: Benchmark de Saturación (Stress Test) -/

/-- Crear polinomio denso: x^n + x^(n-1) + ... + x + 1
    Representado como: x * (x * (... * (x * 1 + 1) + 1) ... + 1) + 1
    Usando forma de Horner simplificada -/
def mkDensePolynomial (degree : Nat) : Expr Int :=
  let x := Expr.var 0
  let one := Expr.const 1
  -- Construir: (...((1 * x + 1) * x + 1) * x + 1)...
  let rec build : Nat → Expr Int → Expr Int
    | 0, acc => acc
    | n + 1, acc => build n (.add (.mul acc x) one)
  build degree one

/-- Stress test con polinomio de grado alto -/
def testLevel3_StressTest : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "NIVEL 3: Benchmark de Saturación (Stress Test)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""

  -- Polinomio de grado 10 (20 es demasiado para compile-time)
  let degree := 10
  let e := mkDensePolynomial degree
  IO.println s!"Polinomio denso de grado {degree}"
  IO.println s!"Forma: (...((1 * x + 1) * x + 1)...)"
  IO.println ""

  -- Configuración para stress test (límites moderados)
  let config : SaturationConfig := {
    maxIterations := 5
    maxNodes := 200
    maxClasses := 100
  }

  IO.println s!"Config: maxIter={config.maxIterations}, maxNodes={config.maxNodes}, maxClasses={config.maxClasses}"
  IO.println ""

  -- Test 1: Solo reglas básicas
  IO.println "Test 3.1: Reglas básicas"
  let (result1, time1) ← timeIO "basicRules" do
    let (_, g) := EGraph.fromExpr e
    return saturate g RewriteRule.basicRules config

  IO.println s!"  Resultado: {result1.iterations} iter, {result1.graph.numNodes} nodos, {result1.graph.numClasses} clases"
  IO.println s!"  Razón: {result1.reason}"
  IO.println ""

  -- Test 2: Reglas extendidas (con distributividad)
  IO.println "Test 3.2: Reglas extendidas (+ distributividad)"
  let (result2, time2) ← timeIO "extendedRules" do
    let (_, g) := EGraph.fromExpr e
    return saturate g RewriteRule.extendedRules config

  IO.println s!"  Resultado: {result2.iterations} iter, {result2.graph.numNodes} nodos, {result2.graph.numClasses} clases"
  IO.println s!"  Razón: {result2.reason}"
  IO.println ""

  -- Test 3: Reglas seguras
  IO.println "Test 3.3: Reglas seguras"
  let (result3, time3) ← timeIO "safeRules" do
    let (_, g) := EGraph.fromExpr e
    return saturate g RewriteRule.safeRules config

  IO.println s!"  Resultado: {result3.iterations} iter, {result3.graph.numNodes} nodos, {result3.graph.numClasses} clases"
  IO.println s!"  Razón: {result3.reason}"
  IO.println ""

  -- Resumen
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "RESUMEN STRESS TEST"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Tiempos: basic={time1}ms, extended={time2}ms, safe={time3}ms"

  let allPassed := time1 < 5000 && time2 < 5000 && time3 < 5000
  if allPassed then
    IO.println "✓ PASS: Todos los tests completaron en < 5 segundos"
  else
    IO.println "⚠ WARN: Algunos tests tardaron > 5 segundos"

  -- Verificar OOM (si llegamos aquí, no hubo OOM)
  IO.println "✓ PASS: No hubo Out of Memory"
  IO.println ""

/-! ## Main: Ejecutar todos los benchmarks -/

def main : IO Unit := do
  IO.println ""
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║     AMO-Lean: Benchmarks Fase 3 - Reglas Mathlib              ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"
  IO.println ""

  testLevel1_CommCorrectness
  testLevel2_AssocPerformance
  testLevel3_StressTest

  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "BENCHMARKS COMPLETADOS"
  IO.println "═══════════════════════════════════════════════════════════════"

-- Ejecutar al compilar
#eval main

end AmoLean.Benchmarks.Phase3
