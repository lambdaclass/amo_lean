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
│  • Reescritura bottom-up / E-graph (futuro)                     │
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

## Roadmap Detallado

### Fase 1: Modelo de Juguete ✓ (COMPLETADA)

**Objetivo**: Validar la arquitectura básica.

**Completado**:
- [x] `Expr α` inductivo para expresiones aritméticas
- [x] Reglas de reescritura (identidades, distributividad)
- [x] Motor de reescritura bottom-up
- [x] Generación de código C básica
- [x] Esqueleto de pruebas de corrección

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

### Fase 2: E-graph y Equality Saturation (PRÓXIMA)

**Objetivo**: Reemplazar reescritura greedy con equality saturation.

**Justificación**: La reescritura bottom-up actual es "greedy" - aplica reglas
destructivamente y puede perder oportunidades de optimización. E-graphs permiten
explorar múltiples formas equivalentes simultáneamente.

**Tareas**:
1. Implementar estructuras de datos:
   - `EClassId` (alias de Nat)
   - `ENode` (nodo con operador + IDs de hijos)
   - `EClass` (conjunto de nodos equivalentes)
   - `EGraph` (union-find + hashcons)
2. Operaciones básicas: `add`, `merge`, `find`, `rebuild`
3. E-matching simple para patrones de reglas
4. Saturación con las 8 reglas existentes de `semiring_rules`
5. Extracción con cost model básico: `const=0, var=0, add=1, mul=10`

**Archivos a crear**:
- `AmoLean/EGraph/Basic.lean` - Estructuras y union-find
- `AmoLean/EGraph/EMatch.lean` - E-matching
- `AmoLean/EGraph/Saturate.lean` - Saturación con reglas
- `AmoLean/EGraph/Extract.lean` - Extracción con cost model

**Referencia principal**: Paper de egg (Willsey et al.)

### Fase 3: Mathlib Extendida sobre E-graph

**Objetivo**: Usar teoremas reales de Mathlib como reglas sobre el E-graph.

**Tareas**:
1. Macro `#compile_rules` para extracción automática:
   ```lean
   #compile_rules [add_comm, mul_comm, add_assoc, mul_assoc] for (ZMod p)
   ```
2. Nuevas reglas desde Mathlib:
   - Conmutatividad: `add_comm`, `mul_comm`
   - Asociatividad: `add_assoc`, `mul_assoc`
   - Otras identidades de `Ring`/`Field`
3. E-class analysis para síntesis de instancias de tipo clase

### Fase 4: Aplicación a Criptografía (FRI)

**Objetivo**: Optimizar componentes de FRI/STARKs.

**Tareas**:
1. Modelar aritmética de campos finitos (`ZMod p`, `GF(2^n)`)
2. Implementar evaluación de polinomios
3. Modelar FFT como composición de operaciones
4. Descubrir optimizaciones automáticamente
5. Generar código Rust optimizado

**Métricas de éxito**:
- Código generado ≈ rendimiento de implementaciones manuales
- Prueba formal de corrección end-to-end

## Lecciones de las Referencias

### De egg (Willsey et al.)

- **Rebuilding**: Diferir mantenimiento de invariantes mejora rendimiento 88×
- **E-class analysis**: Framework general para integrar análisis semántico
- **Separation of phases**: Read phase → Write phase → Rebuild

### De E-graphs as Circuits (Sun et al.)

- **Treewidth**: E-graphs prácticos tienen treewidth bajo
- **Simplification**: Reglas de simplificación de circuitos aplican a e-graphs
- **Extraction óptima**: Algoritmo parametrizado por treewidth

### De Fiat-Crypto Rewriter (Gross et al.)

- **PHOAS**: Evita bookkeeping de binders
- **Let-lifting**: Crucial para evitar explosión de memoria
- **Pattern compilation**: Seguir Maranget para eficiencia
- **NbE + Rewriting**: Combinar normalización con reescritura

### De Term Rewriting Systems (teoría)

- **Confluencia**: Importante para determinismo
- **Terminación**: Necesaria para corrección
- **Ordenamiento de términos**: Para estrategias de simplificación

## Riesgos y Mitigaciones

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|--------------|---------|------------|
| Binding en E-matching | Alta | Alto | AST simplificado + verificación final |
| Rendimiento del E-graph en Lean | Media | Alto | Estructuras de datos eficientes (Std) |
| Síntesis de instancias de tipo clase | Media | Medio | E-class analysis + cache |
| Explosión de tamaño del E-graph | Media | Alto | Scheduling de reglas + límites |

## Próximos Pasos Inmediatos

1. **Completar pruebas de Fase 1**: Cerrar los `sorry` en `Correctness.lean`
2. **Añadir Mathlib**: Configurar dependencia y probar imports
3. **Benchmark baseline**: Medir rendimiento actual vs expresiones grandes
4. **Prototipo de E-graph**: Implementación mínima para evaluar viabilidad

## Referencias

1. Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. Sun et al. "E-Graphs as Circuits, and Optimal Extraction via Treewidth" (2024)
3. Gross et al. "Accelerating Verified-Compiler Development with a Verified Rewriting Engine" (ITP 2022)
4. Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (Fiat-Crypto)
5. Metaprogramming in Lean 4 (documentación oficial)
