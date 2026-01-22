/-
  AMO-Lean Toy Model - Generación de Código (Fase 3 Preview)
  
  Este archivo muestra cómo generar código C desde expresiones
  optimizadas. Es un preview de la fase de code extraction.
-/

namespace AmoLean

open Expr

/-! ## Parte 1: Representación Intermedia para Código -/

/-- 
Representación de bajo nivel más cercana a C.
Similar a three-address code / SSA.
-/
inductive LowLevelExpr where
  | litInt : Int → LowLevelExpr
  | varRef : String → LowLevelExpr
  | binOp : String → LowLevelExpr → LowLevelExpr → LowLevelExpr
  deriving Repr

/-- Instrucción de asignación -/
structure Assignment where
  varName : String
  value : LowLevelExpr
  deriving Repr

/-- Programa como secuencia de asignaciones + resultado final -/
structure LowLevelProgram where
  assignments : List Assignment
  result : LowLevelExpr
  deriving Repr

/-! ## Parte 2: Lowering de Expr a LowLevelExpr -/

/-- Estado del generador de código -/
structure CodeGenState where
  nextVar : Nat := 0
  assignments : List Assignment := []

/-- Generar nombre de variable temporal fresco -/
def freshVar (s : CodeGenState) : (String × CodeGenState) :=
  (s!"t{s.nextVar}", { s with nextVar := s.nextVar + 1 })

/-- Añadir una asignación -/
def addAssignment (s : CodeGenState) (a : Assignment) : CodeGenState :=
  { s with assignments := s.assignments ++ [a] }

/-- 
Convertir Expr a LowLevelExpr con let-lifting.
Cada subexpresión no trivial se convierte en una variable temporal.
-/
partial def lowerExpr (varNames : VarId → String) : 
    Expr Int → CodeGenState → (LowLevelExpr × CodeGenState)
  | const c, s => (LowLevelExpr.litInt c, s)
  | var v, s => (LowLevelExpr.varRef (varNames v), s)
  | add e1 e2, s =>
      let (ll1, s1) := lowerExpr varNames e1 s
      let (ll2, s2) := lowerExpr varNames e2 s1
      let (tmpName, s3) := freshVar s2
      let assignment := { varName := tmpName, value := LowLevelExpr.binOp "+" ll1 ll2 }
      (LowLevelExpr.varRef tmpName, addAssignment s3 assignment)
  | mul e1 e2, s =>
      let (ll1, s1) := lowerExpr varNames e1 s
      let (ll2, s2) := lowerExpr varNames e2 s1
      let (tmpName, s3) := freshVar s2
      let assignment := { varName := tmpName, value := LowLevelExpr.binOp "*" ll1 ll2 }
      (LowLevelExpr.varRef tmpName, addAssignment s3 assignment)

/-- Convertir expresión completa a programa -/
def toLowLevel (varNames : VarId → String) (e : Expr Int) : LowLevelProgram :=
  let (result, state) := lowerExpr varNames e {}
  { assignments := state.assignments, result := result }

/-! ## Parte 3: Pretty Printing a C -/

/-- Convertir LowLevelExpr a string C -/
def lowLevelToC : LowLevelExpr → String
  | LowLevelExpr.litInt n => 
      if n < 0 then s!"({n})" else toString n
  | LowLevelExpr.varRef name => name
  | LowLevelExpr.binOp op l r => 
      s!"({lowLevelToC l} {op} {lowLevelToC r})"

/-- Convertir asignación a línea C -/
def assignmentToC (a : Assignment) (ty : String := "int64_t") : String :=
  s!"  {ty} {a.varName} = {lowLevelToC a.value};"

/-- 
Generar función C completa.
-/
def generateCFunction (name : String) (params : List String) 
    (body : LowLevelProgram) (returnType : String := "int64_t") : String :=
  let paramStr := String.intercalate ", " (params.map (s!"{returnType} " ++ ·))
  let bodyLines := body.assignments.map assignmentToC
  let bodyStr := String.intercalate "\n" bodyLines
  let returnStr := s!"  return {lowLevelToC body.result};"
  s!"{returnType} {name}({paramStr}) \{\n{bodyStr}\n{returnStr}\n}"

/-! ## Parte 4: Pipeline Completo -/

/-- 
Pipeline completo: Expr → Optimización → C
-/
def exprToC [BEq (Expr Int)] (name : String) (params : List String) 
    (e : Expr Int) : String :=
  -- 1. Optimizar la expresión
  let optimized := simplify e
  -- 2. Convertir a representación de bajo nivel
  let varNames : VarId → String := fun i => 
    if h : i < params.length then params[i] else s!"arg{i}"
  let lowLevel := toLowLevel varNames optimized
  -- 3. Generar código C
  generateCFunction name params lowLevel

/-! ## Parte 5: Ejemplos -/

section Examples

-- Ejemplo 1: x + 0 → x, debería generar código trivial
def example1 : Expr Int := add (var 0) (const 0)

#eval exprToC "add_zero_example" ["x"] example1
-- Esperado: int64_t add_zero_example(int64_t x) { return x; }
-- (después de optimización)

-- Ejemplo 2: (x + y) * z
def example2 : Expr Int := mul (add (var 0) (var 1)) (var 2)

#eval exprToC "mul_add" ["x", "y", "z"] example2

-- Ejemplo 3: x * (y + 0) * 1
def example3 : Expr Int := mul (mul (var 0) (add (var 1) (const 0))) (const 1)

#eval exprToC "complex_example" ["x", "y"] example3

-- Ejemplo 4: Expresión tipo Horner para polinomio
-- p(x) = 3 + x*(2 + x*1) = 3 + 2x + x²
def horner_poly : Expr Int := 
  add (const 3) (mul (var 0) (add (const 2) (mul (var 0) (const 1))))

#eval exprToC "horner_poly" ["x"] horner_poly

end Examples

/-! ## Parte 6: Preview de Optimizaciones Avanzadas

En el sistema completo, tendríamos:
1. Strength reduction (x * 2 → x << 1)
2. Common subexpression elimination
3. Register allocation hints
4. Vectorización automática
-/

/-- Regla de strength reduction: multiplicación por potencia de 2 -/
def rule_mul_pow2 : RewriteRule Int
  | mul e (const c) => 
      -- Verificar si c es potencia de 2
      if c > 0 && (c &&& (c - 1)) == 0 then
        -- Sería: some (shift_left e (log2 c))
        -- Por ahora solo marcamos que aplicaría
        none
      else none
  | _ => none

end AmoLean
