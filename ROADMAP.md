# AMO-Lean: Automatic Mathematical Optimizer

## Visión General

AMO-Lean es un optimizador matemático automático verificado, diseñado para transformar código Rust (vía Hacspec) en versiones optimizadas con garantías formales de corrección.

## Arquitectura Estratificada

Basándonos en el análisis de las referencias (egg, E-graphs as Circuits, Fiat-Crypto Rewriter), adoptamos una arquitectura de dos niveles:

```
┌─────────────────────────────────────────────────────────────────┐
│                    NIVEL SEMÁNTICO (Lean)                       │
│  • Lean.Expr para representación canónica                       │
│  • MetaM para verificación de tipos e instancias                │
│  • Mathlib como fuente de verdad para reglas                    │
│  • Pruebas de corrección verificadas por el kernel              │
└─────────────────────────────────────────────────────────────────┘
                              ↕
                    [Proyección / Lifting]
                              ↕
┌─────────────────────────────────────────────────────────────────┐
│                   NIVEL SINTÁCTICO (OptExpr)                    │
│  • AST simplificado (similar a HacspecExpr)                     │
│  • E-graph con equality saturation                              │
│  • E-class analyses para tracking de información                │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│                   GENERACIÓN DE CÓDIGO                          │
│  • Lowering a three-address code                                │
│  • Pretty printing a C/Rust                                     │
└─────────────────────────────────────────────────────────────────┘
```

## Decisiones de Diseño Clave

### 1. ¿Por qué no usar Lean.Expr directamente en el E-graph?

**Problema**: `Lean.Expr` tiene binding (λ, ∀), metavariables, universos, etc. El e-matching en egg asume términos de primer orden con aridad fija.

**Solución**: Usar un AST simplificado (`OptExpr`) para el E-graph, con verificación final en `Lean.Expr`.

### 2. PHOAS vs De Bruijn

Del paper de Gross et al.:
> "de Bruijn indices suffer from linear-time lookups and tedious bookkeeping"

**Decisión**: Para el modelo de juguete usamos índices simples. Para el sistema completo, evaluaremos PHOAS en Lean 4.

### 3. Preservación de Sharing (Let-Lifting)

Del paper de Gross et al.:
> "Without sharing, P-256 compilation ran out of memory on 64GB RAM"

**Decisión**: Implementar `UnderLets` o equivalente para preservar lets durante reescritura.

### 4. Integración con Mathlib

Los teoremas de Mathlib tienen la forma:
```lean
theorem mul_comm {M : Type*} [CommMagma M] (a b : M) : a * b = b * a
```

**Desafío**: La aplicación requiere síntesis de instancias de tipo clase.

**Solución**: E-class analysis que consulta `MetaM` en puntos estratégicos, no en cada operación.

---

## Roadmap Detallado

### Fase 1: Modelo de Juguete ✓ (COMPLETADA)

**Objetivo**: Validar la arquitectura básica.

**Completado**:
- [x] `Expr α` inductivo para expresiones aritméticas
- [x] Reglas de reescritura (identidades, distributividad)
- [x] Motor de reescritura bottom-up
- [x] Generación de código C básica
- [x] Esqueleto de pruebas de corrección

---

### Fase 1.5: Verificación Completa ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Cerrar todos los `sorry` y tener pruebas completas.

**Completado**:
- [x] Redefinir `rewriteBottomUp` sin `partial` (usando recursión estructural)
- [x] Redefinir `rewriteToFixpoint` sin `partial` (usando pattern matching sobre Nat)
- [x] Redefinir `lowerExpr` sin `partial` en CodeGen
- [x] Probar `rewriteBottomUp_sound` por inducción sobre `Expr`
- [x] Probar `rewriteToFixpoint_sound` por inducción sobre `fuel`
- [x] Probar `simplify_sound` usando los lemas anteriores
- [x] Lema auxiliar `algebraicRules_sound` para las 6 reglas

**Resultado**: 0 `sorry` en el proyecto. Motor de reescritura completamente verificado.

---

### Fase 1.75: Optimizaciones Pre-E-graph ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Preparar el terreno para E-graphs con optimizaciones de bajo costo.

**Completado**:
- [x] Benchmark baseline (ver `docs/BENCHMARK_FASE1.md`)
- [x] Cost Model: `CostModel` y `exprCost` en Basic.lean
- [x] Constant Folding: `rule_const_fold_add`, `rule_const_fold_mul`
- [x] Asociatividad Dirigida: Evaluada pero descartada (causa 70x slowdown en greedy)
- [x] `simplifyWithConstFold` - función recomendada sin asociatividad
- [x] `simplifyExtended` - función con asociatividad (con advertencia)

**Hallazgos clave**:
- Motor escala O(n): 253k nodos en 0.5s
- Asociatividad no es viable en reescritura greedy
- Esto validó la necesidad de E-graphs para explorar múltiples formas

---

### Fase 2: E-graph y Equality Saturation ✓ (COMPLETADA - Enero 2026)

**Objetivo**: Reemplazar reescritura greedy con equality saturation.

**Archivos creados**:
- `AmoLean/EGraph/Basic.lean` (~530 líneas) - Estructuras y algoritmos core
- `AmoLean/EGraph/EMatch.lean` (~275 líneas) - E-matching y reglas
- `AmoLean/EGraph/Saturate.lean` (~190 líneas) - Saturación y optimización

**Estructuras de datos implementadas**:
- [x] `EClassId`: Índice en array (Nat)
- [x] `ENodeOp`: Operaciones con IDs de hijos (no recursivo)
- [x] `ENode`: Wrapper con helpers (`mkConst`, `mkAdd`, `children`, etc.)
- [x] `EClass`: Clase de equivalencia con nodos y metadata de costo
- [x] `UnionFind`: Path compression con `Array EClassId`
- [x] `EGraph`: Estructura principal (union-find + hashcons + classes)

**Algoritmos implementados**:
- [x] `add(EGraph, ENode) → (EClassId, EGraph)` - Añadir con deduplicación
- [x] `merge(EGraph, EClassId, EClassId) → EGraph` - Unir clases
- [x] `find(EGraph, EClassId) → EClassId` - Encontrar canónico
- [x] `rebuild(EGraph) → EGraph` - Re-canonicalización completa
- [x] `canonicalize` - Normalizar hijos de un nodo

**E-matching implementado**:
- [x] `Pattern` - Patrones con variables (`?a`, `?b`, etc.)
- [x] `Substitution` - Mapeo de variables a e-classes
- [x] `ematch` - Búsqueda de instancias en una e-class
- [x] `searchPattern` - Búsqueda en todo el grafo
- [x] `instantiate` - Crear nodos desde patrón + sustitución

**Reglas de reescritura**:
- [x] `basicRules`: `a+0→a`, `0+a→a`, `a*1→a`, `1*a→a`, `a*0→0`, `0*a→0`
- [x] `extendedRules`: + distributividad (`a*(b+c)→a*b+a*c`) y factorización

**Saturación implementada**:
- [x] `SaturationConfig` - Límites configurables (iteraciones, nodos, clases)
- [x] `saturateStep` - Una iteración (aplicar reglas + rebuild)
- [x] `saturate` - Hasta punto fijo o límite
- [x] `saturateAndExtract` - Saturar + calcular costos + extraer

**Extracción implementada**:
- [x] `EGraphCostModel` - Modelo de costo para E-graph
- [x] `computeCosts` - Cálculo bottom-up iterativo
- [x] `extract` - Extraer mejor término desde e-class

**Tests (todos pasan)**:
```
x + 0           → x          ✓
x * 1           → x          ✓
(x + 0) * 1     → x          ✓
(x + y) * 0     → 0          ✓
x*1 + 0         → x          ✓ (1 iteración)
x * (y + z)     → explorado   ✓ (2 iteraciones, 8 nodos)
```

**API de uso**:
```lean
import AmoLean.EGraph.Saturate

-- Optimizar con reglas básicas
let result := EGraph.optimizeBasic expr

-- Optimizar con reglas extendidas (distributividad)
let result := EGraph.optimizeExtended expr

-- Optimizar con configuración personalizada
let config := { maxIterations := 50, maxNodes := 5000 }
let (result, satResult) := EGraph.optimize expr rules config
```

---

### Fase 3: Mathlib Extendida sobre E-graph (PENDIENTE)

**Objetivo**: Usar teoremas reales de Mathlib como reglas sobre el E-graph.

**Tareas**:
- [ ] Macro `#compile_rules` para extracción automática:
  ```lean
  #compile_rules [add_comm, mul_comm, add_assoc, mul_assoc] for (ZMod p)
  ```
- [ ] Nuevas reglas desde Mathlib:
  - Conmutatividad: `add_comm`, `mul_comm`
  - Asociatividad: `add_assoc`, `mul_assoc`
  - Otras identidades de `Ring`/`Field`
- [ ] E-class analysis para síntesis de instancias de tipo clase

---

### Fase 4: Aplicación a Criptografía (FRI) (PENDIENTE)

**Objetivo**: Optimizar componentes de FRI/STARKs.

**Tareas**:
- [ ] Modelar aritmética de campos finitos (`ZMod p`, `GF(2^n)`)
- [ ] Implementar evaluación de polinomios
- [ ] Modelar FFT como composición de operaciones
- [ ] Descubrir optimizaciones automáticamente
- [ ] Generar código Rust optimizado

**Métricas de éxito**:
- Código generado ≈ rendimiento de implementaciones manuales
- Prueba formal de corrección end-to-end

---

## Estructura del Proyecto

```
amo-lean/
├── AmoLean.lean              # Módulo principal, API pública
├── AmoLean/
│   ├── Basic.lean            # AST, reglas, motor greedy, CostModel
│   ├── Correctness.lean      # Pruebas de corrección (0 sorry)
│   ├── MathlibIntegration.lean # Integración con Mathlib
│   ├── CodeGen.lean          # Generación de código C
│   └── EGraph/
│       ├── Basic.lean        # Estructuras E-graph, union-find
│       ├── EMatch.lean       # Patrones, e-matching, reglas
│       └── Saturate.lean     # Saturación, extracción
├── docs/
│   ├── BENCHMARK_FASE1.md    # Análisis de rendimiento
│   ├── PROJECT_STATUS.md     # Estado del proyecto (inglés)
│   └── ESTADO_PROYECTO.md    # Estado del proyecto (español)
├── ROADMAP.md                # Este archivo
└── lakefile.lean             # Configuración del proyecto
```

---

## Lecciones Aprendidas

### De la Fase 1.75 (Benchmark)
- **Greedy es rápido pero limitado**: 253k nodos en 0.5s, pero no explora alternativas
- **Asociatividad rompe greedy**: 70x slowdown porque aplica reglas indefinidamente
- **Cost model es esencial**: Sin él, no hay criterio de "mejor"

### De la Fase 2 (E-graph)
- **Estructuras planas funcionan**: `Array` + `HashMap` evitan problemas de GC
- **Rebuild es crítico**: Sin re-canonicalización, el hashcons queda inconsistente
- **E-matching es elegante**: Patrones + sustituciones = búsqueda declarativa

### De egg (Willsey et al.)
- **Rebuilding**: Diferir mantenimiento de invariantes mejora rendimiento 88×
- **E-class analysis**: Framework general para integrar análisis semántico
- **Separation of phases**: Read phase → Write phase → Rebuild

### De Fiat-Crypto Rewriter (Gross et al.)
- **PHOAS**: Evita bookkeeping de binders
- **Let-lifting**: Crucial para evitar explosión de memoria
- **Pattern compilation**: Seguir Maranget para eficiencia

---

## Riesgos y Mitigaciones

| Riesgo | Probabilidad | Impacto | Mitigación | Estado |
|--------|--------------|---------|------------|--------|
| Binding en E-matching | Alta | Alto | AST simplificado | ✓ Mitigado |
| Rendimiento E-graph en Lean | Media | Alto | Estructuras planas | ✓ Mitigado |
| Síntesis de instancias | Media | Medio | E-class analysis | Pendiente |
| Explosión de E-graph | Media | Alto | Límites configurables | ✓ Mitigado |

---

## Próximos Pasos

1. **Fase 3**: Implementar macro `#compile_rules` para Mathlib
2. **Pruebas de corrección E-graph**: Probar que `extract` preserva semántica
3. **Benchmark E-graph vs Greedy**: Comparar rendimiento y calidad
4. **Casos de uso criptográficos**: Evaluar con expresiones de FRI

---

## Referencias

1. Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. Sun et al. "E-Graphs as Circuits, and Optimal Extraction via Treewidth" (2024)
3. Gross et al. "Accelerating Verified-Compiler Development with a Verified Rewriting Engine" (ITP 2022)
4. Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (Fiat-Crypto)
5. Metaprogramming in Lean 4 (documentación oficial)
