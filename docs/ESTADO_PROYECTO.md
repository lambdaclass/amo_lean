# AMO-Lean: Estado del Proyecto

*Última actualización: 23 de Enero 2026 - Fase 4 (Extensión de Potencias) Completada*

---

## 1. Estado Actual del Proyecto

### Pipeline Funcional

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Pipeline AMO-Lean                                   │
│                                                                             │
│  Expr α ──→ E-Graph Saturation ──→ Mejor Expr ──→ Código C                 │
│                                                                             │
│  (x+0)*1+y*0  ──→  equality saturation  ──→  x  ──→  int64_t f() {         │
│                    con cost model               return x;                   │
│                                                 }                           │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Capacidades Implementadas

| Componente | Estado | Archivo |
|------------|--------|---------|
| AST de expresiones (`Expr α`) con pow | ✅ Completo | `Basic.lean` |
| Semántica denotacional (`denote`) | ✅ Completo | `Basic.lean` |
| 12 reglas de reescritura greedy | ✅ Implementadas | `Basic.lean` |
| Pruebas de soundness (reglas) | ✅ 8/8 probadas | `Correctness.lean` |
| Motor bottom-up + punto fijo | ✅ Verificado | `Basic.lean` |
| Cost Model (`CostModel`, `exprCost`) | ✅ Completo | `Basic.lean` |
| Constant Folding | ✅ Completo | `Basic.lean` |
| **E-Graph con Equality Saturation** | ✅ **COMPLETO** | `EGraph/*.lean` |
| E-Matching | ✅ Completo | `EGraph/EMatch.lean` |
| Saturación con reglas | ✅ Completo | `EGraph/Saturate.lean` |
| Extracción con cost model | ✅ Completo | `EGraph/Basic.lean` |
| Generación de código C (SSA) | ✅ Funciona | `CodeGen.lean` |
| Integración Mathlib | ✅ Básica | `MathlibIntegration.lean` |
| **`sorry` en el proyecto** | ✅ **0** | Motor greedy verificado |

### Reglas de Reescritura Implementadas

**Motor Greedy:**
- `x + 0 → x`, `0 + x → x` (identidades aditivas)
- `x * 1 → x`, `1 * x → x` (identidades multiplicativas)
- `x * 0 → 0`, `0 * x → 0` (aniquiladores)
- `a * (b + c) → a*b + a*c` (distributividad izquierda)
- `(a + b) * c → a*c + b*c` (distributividad derecha)
- `const a + const b → const (a+b)` (constant folding)
- `const a * const b → const (a*b)` (constant folding)
- `a^0 → 1`, `a^1 → a` (identidades de potencia)
- `1^n → 1`, `0^n → 0` (n > 0) (casos especiales)

**E-Graph (reglas adicionales):**
- `a*b + a*c → a*(b+c)` (factorización)
- `a*a → a^2` (squareFromMul)
- `a^2 → a*a` (squareToMul)

---

## 2. Estructura del Proyecto

```
amo-lean/
├── AmoLean.lean                 # Módulo principal, API pública
├── AmoLean/
│   ├── Basic.lean               # AST, reglas, motor greedy, CostModel
│   ├── Correctness.lean         # Pruebas de soundness (0 sorry)
│   ├── MathlibIntegration.lean  # Integración con Mathlib
│   ├── CodeGen.lean             # Generación de código C
│   └── EGraph/
│       ├── Basic.lean           # Estructuras E-graph, union-find (~530 líneas)
│       ├── EMatch.lean          # Patrones, e-matching, reglas (~275 líneas)
│       └── Saturate.lean        # Saturación, extracción (~190 líneas)
├── docs/
│   ├── BENCHMARK_FASE1.md       # Análisis de rendimiento
│   ├── PROJECT_STATUS.md        # Estado (inglés)
│   └── ESTADO_PROYECTO.md       # Este archivo
├── ROADMAP.md                   # Roadmap detallado
└── lakefile.lean                # Configuración del proyecto
```

---

## 3. Fases Completadas

### Fase 1: Toy Model ✅

- [x] AST `Expr α` inductivo
- [x] Semántica denotacional
- [x] 8 reglas de reescritura
- [x] Motor bottom-up + punto fijo
- [x] Generación de código C

### Fase 1.5: Verificación Completa ✅

- [x] Redefinir `rewriteBottomUp` sin `partial` (recursión estructural)
- [x] Redefinir `rewriteToFixpoint` sin `partial` (pattern matching)
- [x] Probar `rewriteBottomUp_sound` por inducción
- [x] Probar `rewriteToFixpoint_sound` por inducción
- [x] Probar `simplify_sound`
- [x] **Resultado: 0 `sorry` en el proyecto**

### Fase 1.75: Optimizaciones Pre-E-graph ✅

- [x] Benchmark baseline (253k nodos en 0.5s, escalado O(n))
- [x] Cost Model: `CostModel` y `exprCost`
- [x] Constant Folding: `rule_const_fold_add`, `rule_const_fold_mul`
- [x] Evaluación de asociatividad (rechazada: 70x slowdown en greedy)
- [x] `simplifyWithConstFold` - función recomendada
- [x] Documentación: `docs/BENCHMARK_FASE1.md`

### Fase 2: E-Graph y Equality Saturation ✅

**Estructuras de datos:**
- [x] `EClassId`: Índice en array (Nat)
- [x] `ENodeOp`: Operaciones con IDs de hijos (no recursivo)
- [x] `ENode`: Wrapper con helpers
- [x] `EClass`: Clase de equivalencia con nodos y metadata de costo
- [x] `UnionFind`: Path compression con `Array EClassId`
- [x] `EGraph`: Estructura principal (union-find + hashcons + classes)

**Algoritmos:**
- [x] `add(EGraph, ENode) → (EClassId, EGraph)` - Añadir con deduplicación
- [x] `merge(EGraph, EClassId, EClassId) → EGraph` - Unir clases
- [x] `find(EGraph, EClassId) → EClassId` - Encontrar canónico
- [x] `rebuild(EGraph) → EGraph` - Re-canonicalización completa
- [x] `canonicalize` - Normalizar hijos de un nodo

**E-Matching:**
- [x] `Pattern` - Patrones con variables (`?a`, `?b`, etc.)
- [x] `Substitution` - Mapeo de variables a e-classes
- [x] `ematch` - Búsqueda de instancias en una e-class
- [x] `searchPattern` - Búsqueda en todo el grafo
- [x] `instantiate` - Crear nodos desde patrón + sustitución

**Saturación:**
- [x] `SaturationConfig` - Límites configurables
- [x] `saturateStep` - Una iteración (aplicar reglas + rebuild)
- [x] `saturate` - Hasta punto fijo o límite
- [x] `saturateAndExtract` - Saturar + calcular costos + extraer

**Extracción:**
- [x] `EGraphCostModel` - Modelo de costo para E-graph
- [x] `computeCosts` - Cálculo bottom-up iterativo
- [x] `extract` - Extraer mejor término desde e-class

**Tests (todos pasan):**
```
x + 0           → x          ✓
x * 1           → x          ✓
(x + 0) * 1     → x          ✓
(x + y) * 0     → 0          ✓
x*1 + 0         → x          ✓ (1 iteración)
x * (y + z)     → explorado   ✓ (2 iteraciones, 8 nodos)
```

---

## 4. Ejemplos de Uso

### Motor Greedy
```lean
import AmoLean

open AmoLean Expr

-- Expresión simple
let expr := add (mul (var 0) (const 1)) (const 0)  -- x*1 + 0
let simplified := simplify expr                      -- x
```

### Optimizador E-Graph
```lean
import AmoLean.EGraph.Saturate

open AmoLean.EGraph

-- Optimizar con reglas básicas
let expr := Expr.add (Expr.mul (Expr.var 0) (Expr.const 1)) (Expr.const 0)
match optimizeBasic expr with
| some result => -- result = Expr.var 0
| none => -- error

-- Optimizar con reglas extendidas (distributividad)
let result := optimizeExtended expr

-- Configuración personalizada
let config := { maxIterations := 50, maxNodes := 5000 }
let (result, satResult) := optimize expr RewriteRule.basicRules config
-- satResult.iterations, satResult.saturated, satResult.reason
```

### Generación de Código C
```lean
import AmoLean

let expr := Expr.mul (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.var 2)
let code := exprToC "mi_funcion" ["x", "y", "z"] expr
-- "int64_t mi_funcion(int64_t x, int64_t y, int64_t z) { ... }"
```

---

## 5. Fase en Progreso

### Fase 3: Mathlib Extendida sobre E-graph (✅ Completada - Enero 2026)

**Completado:**
- [x] Nuevas reglas desde Mathlib (conmutatividad, asociatividad):
  - `addComm`, `mulComm` (2 reglas)
  - `addAssocRight`, `addAssocLeft`, `mulAssocRight`, `mulAssocLeft` (4 reglas)
- [x] Colecciones de reglas: `commRules`, `assocRules`, `semiringRules` (15 total)
- [x] Funciones helper en namespace `MathlibToEGraph`
- [x] Optimización para evitar merges redundantes en `applyRuleAt`
- [x] **Macro `#compile_rules`** - Extracción automática de reglas desde teoremas Mathlib
  - Convierte `Lean.Expr` a `Pattern` usando metaprogramación
  - Soporta `Add.add`, `HAdd.hAdd`, `Mul.mul`, `HMul.hMul`, `OfNat.ofNat`
  - Archivo: `AmoLean/Meta/CompileRules.lean`
- [x] **Auditoría de Generalidad** - Verificado que la macro es GENÉRICA
  - Soporta teoremas con Type Classes (AddCommMagma, MulOneClass, etc.)
  - NO está limitada a tipos concretos como Nat
  - Fase 4 (ZMod/Campos Finitos) NO está bloqueada
  - Archivo: `Tests/GenericsAudit.lean`

**Pendiente (opcional):**
- [ ] E-class analysis para síntesis de instancias (mejora futura)

---

## 6. Fase 4: Campos Finitos y Potencias (✅ Completada - Enero 2026)

### Extensión de Potencias Completada

- [x] **Constructor `pow` añadido al AST**
  - `Expr.pow : Expr α → Nat → Expr α`
  - `denote` actualizado con constraint `[Pow α Nat]`
  - `CostModel.powCost` añadido (default: 50)
- [x] **ENodeOp extendido con potencias**
  - `ENodeOp.pow : EClassId → Nat → ENodeOp`
  - E-matching actualizado para potencias
  - Extracción con costo de potencias
- [x] **Pattern extendido**
  - `Pattern.pow : Pattern → Nat → Pattern`
  - Reglas: `powZero`, `powOne`, `squareFromMul`, `squareToMul`
  - `powerRules` y `fullRules` colecciones
- [x] **CompileRules con HPow**
  - Soporta `HPow.hPow` y `Pow.pow`
  - Maneja exponentes literales y `OfNat.ofNat`
- [x] **CodeGen con potencias**
  - `n=0`: genera `1`
  - `n=1`: genera la base directa
  - `n=2`: genera `(x * x)` inline
  - `n>2`: genera `pow_int(x, n)` function call
- [x] **Correctness.lean actualizado**
  - Casos `pow` añadidos a todas las pruebas

### ZMod Exploración Completada

- [x] **ZMod compilado y funcionando**
  - `Mathlib.Data.ZMod.Basic` y `Mathlib.FieldTheory.Finite.Basic` compilados
  - Variables `(a b c : ZMod 7)` definidas y operables
- [x] **Reglas genéricas funcionan en ZMod**
  - `add_comm`, `mul_comm`, `add_zero`, `mul_one`, etc.
  - Verificado que #compile_rules produce reglas aplicables a campos finitos
- [x] **Teoremas de característica verificados**
  - `ZMod.natCast_self`: `(7 : ZMod 7) = 0`
  - `(7 : ZMod 7) * a = 0` (reducción de coeficientes)
- [x] **Pequeño Teorema de Fermat verificado**
  - `ZMod.pow_card`: `a ^ p = a` para `[Fact p.Prime]`
  - `ZMod.pow_card_pow`: `a ^ (p^n) = a`
  - Archivo: `Tests/ZModDemo.lean`

### Limitaciones Restantes

La macro `#compile_rules` aún no puede extraer:
- `ZMod.natCast_self`: requiere pattern matching sobre casts
- `ZMod.pow_card`: exponente no es constante literal (es `Fintype.card`)

### Próximos Pasos (Fase 5)

- [ ] Agregar `Pattern.cast` para constantes modulares
- [ ] Soportar exponentes no literales
- [ ] Evaluación de polinomios en campos finitos
- [ ] FFT como composición de operaciones

## 7. Fases Futuras

### Fase 5: FFT/NTT

- [ ] FFT como composición de operaciones
- [ ] Descubrimiento automático de optimizaciones
- [ ] Generación de código Rust

---

## 6. Arquitectura: Toy Model ↔ Optimizador FRI

```
┌────────────────────────────────────────────────────────────────────────┐
│                         NIVELES DE ABSTRACCIÓN                         │
├────────────────────────────────────────────────────────────────────────┤
│                                                                        │
│  Nivel 4: Protocolo FRI Completo                                       │
│           ├── Compromisos Merkle                                       │
│           ├── Rondas de plegado (folding)                              │
│           └── Verificación de proximidad                               │
│                           ↑                                            │
│  Nivel 3: Operaciones sobre Polinomios                                 │
│           ├── FFT/NTT verificada                                       │
│           ├── Interpolación                                            │
│           └── Evaluación multi-punto                                   │
│                           ↑                                            │
│  Nivel 2: Aritmética de Campo Finito                                   │
│           ├── F_p (campo primo)                                        │
│           ├── Extensiones de campo                                     │
│           └── Operaciones Montgomery/Barrett                           │
│                           ↑                                            │
│  Nivel 1: Expresiones Aritméticas  ◄──── AQUÍ (E-Graph listo)         │
│           ├── AST genérico                                             │
│           ├── E-graph con saturación                                   │
│           └── Generación de código                                     │
│                                                                        │
└────────────────────────────────────────────────────────────────────────┘
```

---

## 7. Historial de Problemas y Soluciones

| Problema | Causa | Solución |
|----------|-------|----------|
| Lean 4.3.0 incompatible | Mathlib requiere versiones recientes | Actualizado a 4.16.0 |
| `leanOptions` no existe | API de Lake cambió | Nueva sintaxis de lakefile |
| `BEq` vs `Eq` en pruebas | Reglas usan `==` pero pruebas necesitan `=` | `LawfulBEq` + lemas |
| `partial` impide inducción | Lean no genera principio de inducción | **RESUELTO**: Recursión estructural + `termination_by` |
| Asociatividad lenta | 70x más lento por aplicaciones repetidas | **RESUELTO**: Validó necesidad de E-graphs |
| Memoria E-graph | Tipos recursivos causan problemas de GC | **RESUELTO**: Estructuras planas (Array + HashMap) |

---

## 8. Lecciones Aprendidas

### De la Fase 1.75 (Benchmark)
- **Greedy es rápido pero limitado**: 253k nodos en 0.5s, pero no explora alternativas
- **Asociatividad rompe greedy**: 70x slowdown porque aplica reglas indefinidamente
- **Cost model es esencial**: Sin él, no hay criterio de "mejor"

### De la Fase 2 (E-Graph)
- **Estructuras planas funcionan**: `Array` + `HashMap` evitan problemas de GC
- **Rebuild es crítico**: Sin re-canonicalización, el hashcons queda inconsistente
- **E-matching es elegante**: Patrones + sustituciones = búsqueda declarativa

---

## 9. Estimación de Complejidad

```
                        Complejidad    Estado           Dependencias
                        ───────────    ──────           ────────────
Fase 1: Toy Model       ████░░░░░░     ✅ COMPLETADA    Ninguna
Fase 1.5: Verificación  ████░░░░░░     ✅ COMPLETADA    Toy Model
Fase 1.75: Pre-E-graph  ████░░░░░░     ✅ COMPLETADA    Verificación
Fase 2: E-graph         █████░░░░░     ✅ COMPLETADA    Pre-E-graph
Fase 3: Mathlib Ext     █████░░░░░     ✅ COMPLETADA    E-graph
Fase 4: Potencias+ZMod  ██████░░░░     ✅ COMPLETADA    Mathlib Ext
Fase 5: FFT             ███████░░░     🔜 Planificada   Potencias
Fase 6: FRI             █████████░     🔜 Planificada   Todo lo anterior
Fase 7: CodeGen         ██████████     🔜 Planificada   FRI
Fase 8: Producción      ██████████     🔜 Planificada   Todo + Ingeniería
```

---

## 10. Referencias

1. Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. Sun et al. "E-Graphs as Circuits, and Optimal Extraction via Treewidth" (2024)
3. Gross et al. "Accelerating Verified-Compiler Development with a Verified Rewriting Engine" (ITP 2022)
4. Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (Fiat-Crypto)
5. Metaprogramming in Lean 4 (documentación oficial)

---

*Documento generado: Enero 2026*
*Última actualización: 23 Enero 2026 - Fase 4 (Potencias + ZMod) completada*
