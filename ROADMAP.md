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

### Fase 1: Modelo de Juguete ✓

**Objetivo**: Validar la arquitectura básica.

**Completado**:
- [x] `Expr α` inductivo para expresiones aritméticas
- [x] Reglas de reescritura (identidades, distributividad)
- [x] Motor de reescritura bottom-up
- [x] Generación de código C básica
- [x] Esqueleto de pruebas de corrección

**Pendiente**:
- [ ] Completar pruebas de corrección
- [ ] Tests más exhaustivos
- [ ] Benchmarks básicos

### Fase 2: Integración con Mathlib

**Objetivo**: Usar teoremas reales de Mathlib como reglas.

**Tareas**:
1. Añadir dependencia de Mathlib al proyecto
2. Definir morfismo `Expr α → α` para `α : Semiring`
3. Probar que `denote` preserva la estructura algebraica
4. Compilar teoremas (`add_zero`, `mul_comm`, etc.) a `VerifiedRule`
5. Tactic/macro para extracción automática de reglas

**Métrica de éxito**: Poder escribir:
```lean
#compile_rules [add_zero, mul_comm, left_distrib] for (ZMod p)
```

### Fase 3: E-graph y Equality Saturation

**Objetivo**: Reemplazar reescritura bottom-up con equality saturation.

**Tareas**:
1. Implementar E-graph sobre `OptExpr` en Lean puro
2. Operaciones: `add`, `merge`, `rebuild`
3. E-class analysis para:
   - Tipos inferidos
   - Estructura algebraica (Ring, Field, etc.)
   - Constant folding
4. E-matching para patrones de reglas
5. Función de costo y extracción

**Referencia principal**: Paper de egg (Willsey et al.)

**Consideración de rendimiento**: Del paper de E-graphs as Circuits:
> "Circuit simplification can reduce e-graph size and treewidth by 40-80%"

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
