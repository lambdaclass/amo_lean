# Benchmark y Evaluación Pre-Fase 2

*Fecha: 23 Enero 2026*
*Contexto: Evaluación del motor de reescritura antes de implementar E-graphs*

---

## 1. Resultados del Benchmark

### Configuración del Test

Se evaluó el motor de reescritura `simplify` con polinomios de grado variable que contienen redundancias algebraicas:

```
p(x) = Σ_{i=0}^{n} ((x^i * 1) + 0)
```

Cada término tiene multiplicación por 1 y suma de 0, que deberían eliminarse.

### Resultados

| Grado | Nodos Antes | Nodos Después | Reducción | Tiempo |
|-------|-------------|---------------|-----------|--------|
| 10    | 177         | 111           | 37%       | <1ms   |
| 50    | 2,857       | 2,551         | 11%       | 5ms    |
| 100   | 10,707      | 10,101        | 6%        | 21ms   |
| 200   | 41,407      | 40,201        | 3%        | 85ms   |
| 500   | 253,507     | 250,501       | 1%        | 523ms  |

### Análisis de Escalabilidad

```
Tiempo vs Tamaño:
  177 nodos    →    0ms   (baseline)
  2,857 nodos  →    5ms   (16x nodos, 5x tiempo)
  10,707 nodos →   21ms   (60x nodos, 21x tiempo)
  41,407 nodos →   85ms   (234x nodos, 85x tiempo)
  253,507 nodos → 523ms   (1432x nodos, 523x tiempo)

Conclusión: Escalabilidad aproximadamente O(n) - lineal
```

### Observaciones Clave

1. **El motor es eficiente**: 253k nodos procesados en ~0.5 segundos
2. **La reducción porcentual disminuye**: Porque `x^n` crece (más `mul` internos que no se simplifican)
3. **Solo hace simplificaciones locales**: Elimina `*1`, `+0`, pero no reorganiza estructura
4. **No hay explosión de memoria**: El motor greedy no acumula estados intermedios

---

## 2. Críticas Recibidas y Evaluación

### Crítica 1: Explosión de Memoria en E-graphs

> "Lean 4 no tiene un GC optimizado para grafos con millones de nodos cíclicos"

**Evaluación: VÁLIDA**

El E-graph puede crecer exponencialmente durante saturación. La sugerencia de usar `Array` de `Std` en lugar de tipos inductivos recursivos es correcta.

**Mitigación planificada:**
```
EGraph = {
  classes: Array EClass      -- Array plano, índices como "punteros"
  unionFind: Array EClassId  -- Union-find con path compression
  hashcons: HashMap ENode EClassId  -- Para deduplicación
}
```

### Crítica 2: Cost Model Faltante

> "Tu reescritor aplica reglas si encajan, no si mejoran el costo"

**Evaluación: MUY VÁLIDA**

El motor actual (`simplify`) no tiene noción de "mejor" o "peor". Aplica reglas ciegamente hasta punto fijo.

Para E-graphs, el cost model es **crítico** porque:
1. La saturación genera múltiples formas equivalentes
2. La extracción necesita elegir la "mejor"
3. Sin cost model, no hay criterio de selección

**Propuesta de Cost Model:**

| Operación | Costo | Justificación |
|-----------|-------|---------------|
| `const`   | 0     | Literal, sin computación |
| `var`     | 0     | Lectura de registro |
| `add`     | 1     | 1 ciclo CPU típico |
| `mul`     | 10    | ~10 ciclos en campo finito |
| `div`     | 100   | Inversión modular costosa |
| `pow`     | n*10  | n multiplicaciones |

### Crítica 3: Benchmark Primero

> "Antes de escribir una sola línea de E-Graphs, intenta optimizar una expresión grande"

**Evaluación: EXCELENTE CONSEJO**

Resultado: El benchmark muestra que el motor actual **no es el cuello de botella**. La limitación es la **calidad de optimización**, no la velocidad.

---

## 3. Optimizaciones Viables Antes de Fase 2

Antes de implementar E-graphs (complejidad alta), hay optimizaciones de bajo costo que mejorarían el sistema actual:

### 3.1 Constant Folding (Complejidad: BAJA)

**Estado actual:** Las constantes no se evalúan.

```lean
-- Actual: mul (const 3) (const 4) → mul (const 3) (const 4)
-- Deseado: mul (const 3) (const 4) → const 12
```

**Implementación:** Agregar regla `rule_const_fold`:
```
rule_const_fold:
  | add (const a) (const b) => some (const (a + b))
  | mul (const a) (const b) => some (const (a * b))
```

**Impacto:** Reduce tamaño de expresiones con muchas constantes.

### 3.2 Reglas de Asociatividad Dirigida (Complejidad: BAJA)

**Estado actual:** No hay normalización de asociatividad.

```lean
-- (a + b) + c  y  a + (b + c)  son formas distintas
```

**Propuesta:** Normalizar a asociatividad derecha:
```
rule_assoc_right:
  | add (add a b) c => some (add a (add b c))
  | mul (mul a b) c => some (mul a (mul b c))
```

**Impacto:** Habilita más matches de otras reglas. Importante para factorización.

### 3.3 Cost Model Básico (Complejidad: BAJA)

**Estado actual:** No existe.

**Propuesta:** Definir estructura `CostModel` y función `exprCost`:
- No cambia el motor de reescritura
- Permite medir calidad de optimizaciones
- Base necesaria para extracción en E-graphs

### 3.4 Reglas de Factorización Mejoradas (Complejidad: MEDIA)

**Estado actual:** `rule_factor_right` existe pero es muy específica:
```lean
-- Solo detecta: a*c + b*c → (a + b) * c
-- No detecta: a*c + c*b (orden diferente)
```

**Propuesta:** Agregar variantes con conmutatividad:
```
rule_factor_left:   c*a + c*b → c * (a + b)
rule_factor_comm_1: a*c + c*b → (a + b) * c  (usando mul_comm)
rule_factor_comm_2: c*a + b*c → c * (a + b)  (usando mul_comm)
```

**Impacto:** Más oportunidades de factorización sin E-graphs.

### 3.5 Strength Reduction (Complejidad: MEDIA)

**Estado actual:** Comentado (`rule_mul_pow2`).

**Propuestas viables sin bitwise:**
```
rule_mul_2:  a * 2 → a + a
rule_mul_3:  a * 3 → a + a + a  (o a + (a * 2))
rule_square: a * a → pow a 2   (si añadimos pow al AST)
```

**Impacto:** Reduce multiplicaciones costosas.

### 3.6 Dead Code Elimination (Complejidad: BAJA)

**Estado actual:** Expresiones con `* 0` se simplifican, pero no se propaga.

```lean
-- Actual: add (mul x (const 0)) y → add (const 0) y → y ✓
-- Pero: let z = mul x (const 0) in add z y
--       La variable z sigue existiendo en CodeGen
```

**Propuesta:** En `CodeGen.lean`, eliminar asignaciones no usadas.

**Impacto:** Código C más limpio.

---

## 4. Priorización de Optimizaciones Pre-Fase 2

### Matriz de Decisión

| Optimización | Esfuerzo | Impacto | Riesgo | Prioridad |
|--------------|----------|---------|--------|-----------|
| Cost Model | Bajo | Alto | Bajo | **P0** |
| Constant Folding | Bajo | Medio | Bajo | **P1** |
| Asociatividad Dirigida | Bajo | Medio | Bajo | **P1** |
| Dead Code Elimination | Bajo | Bajo | Bajo | P2 |
| Factorización Mejorada | Medio | Medio | Medio | P2 |
| Strength Reduction | Medio | Bajo | Medio | P3 |

### Recomendación

**Antes de Fase 2, implementar:**

1. **Cost Model** (P0) - Necesario para E-graphs
2. **Constant Folding** (P1) - Victoria rápida
3. **Asociatividad Dirigida** (P1) - Habilita más optimizaciones

**Diferir a Fase 2 o posterior:**
- Factorización mejorada (E-graphs lo hace mejor)
- Strength reduction (requiere extensión del AST)

---

## 5. Ajustes Propuestos para Fase 2

### Fase 2 Original (del ROADMAP)

```
Fase 2: E-graph y Equality Saturation
- Estructuras: EClassId, ENode, EClass, EGraph
- Union-find + hashcons
- E-matching simple
- Saturación con las 8 reglas existentes
- Extracción con cost model
```

### Fase 2 Modificada (incorporando críticas)

```
Fase 2: E-graph y Equality Saturation

PRE-REQUISITOS (antes de E-graph):
  [x] Benchmark baseline (completado)
  [ ] Definir CostModel y exprCost
  [ ] Implementar constant folding
  [ ] Normalización de asociatividad

ESTRUCTURAS DE DATOS:
  [ ] EClassId como índice en Array (no tipo inductivo)
  [ ] ENode con hijos como Array EClassId
  [ ] EClass como Array ENode
  [ ] EGraph con:
      - classes: Array EClass
      - unionFind: Array EClassId (con path compression)
      - hashcons: HashMap ENode EClassId
  [ ] Usar Std.HashMap y Std.Array para eficiencia

ALGORITMOS:
  [ ] add(EGraph, ENode) → (EClassId, EGraph)
  [ ] merge(EGraph, EClassId, EClassId) → EGraph
  [ ] find(EGraph, EClassId) → EClassId
  [ ] rebuild(EGraph) → EGraph (deferred invariant maintenance)

E-MATCHING:
  [ ] Patrones simples (sin variables de binding)
  [ ] Match multi-patrón para reglas como a*(b+c) → a*b + a*c

SATURACIÓN:
  [ ] Scheduler básico (aplicar todas las reglas)
  [ ] Límite de iteraciones configurable
  [ ] Límite de tamaño del E-graph

EXTRACCIÓN:
  [ ] exprCost: EClassId → EGraph → Nat
  [ ] extract: EGraph → EClassId → Expr α
  [ ] Algoritmo greedy bottom-up (suficiente para empezar)

VERIFICACIÓN:
  [ ] Prueba: extract produce término equivalente al original
  [ ] Prueba: cost(extract(g, id)) ≤ cost alternativas en e-class
```

---

## 6. Métricas de Éxito para Fase 2

### Funcionales

1. E-graph puede representar expresión de 1000 nodos
2. Saturación termina en <10 segundos para grado 50
3. Extracción produce expresión de menor o igual costo

### De Calidad

1. Sin `sorry` en pruebas de corrección
2. Memoria no excede 1GB para expresiones de test
3. Código C generado es equivalente al original

### Comparativas

| Expresión | Motor Greedy | E-graph | Mejora |
|-----------|--------------|---------|--------|
| `a*b + a*c` | Sin cambio | `a*(b+c)` | 1 mul menos |
| `(x+0)*1 + y*0` | `x` | `x` | Igual |
| `a*a + 2*a*b + b*b` | Sin cambio | `(a+b)^2` | (si añadimos pow) |

---

## 7. Conclusiones

1. **El motor actual funciona bien** para su propósito (simplificaciones locales)
2. **Las críticas son válidas** y deben incorporarse al plan
3. **Hay optimizaciones de bajo costo** que agregan valor sin E-graphs
4. **La Fase 2 debe ajustarse** para incluir pre-requisitos y usar estructuras eficientes

**Siguiente paso recomendado:** Implementar Cost Model y constant folding antes de E-graphs.

---

*Documento generado como parte de la evaluación pre-Fase 2 del proyecto AMO-Lean*
