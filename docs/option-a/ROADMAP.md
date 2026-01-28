# AMO-Lean Option A: Roadmap Oficial

**Última actualización**: 2026-01-28
**Este es el ÚNICO roadmap autoritativo para Option A.**

---

## Declaración de Propósito

**AMO-Lean Option A es un COMPILADOR OPTIMIZADOR FORMAL.**

```
Spec Matemática  →  E-Graph Saturation  →  Código C Optimizado
  (MatExpr)          (reglas verificadas)   (correcto por construcción)
```

### Lo que AMO-Lean ES:
- Un compilador que toma especificaciones matemáticas
- Aplica reglas de reescritura verificadas en Lean
- Genera código C con MENOS operaciones que una traducción ingenua
- Demuestra la optimización con benchmarks

### Lo que AMO-Lean NO ES:
- Una librería de primitivas criptográficas
- Una colección de implementaciones de algoritmos
- Un proyecto que mide éxito por "cantidad de funciones"

### Métrica de Éxito:
```
Código Naive:      N operaciones
Código Optimizado: M operaciones  donde M < N
```

---

## Timeline General

| Fase | Descripción | Estado |
|------|-------------|--------|
| **0** | Proof of Concept (FRI Fold) | ✅ COMPLETADA |
| **1** | Goldilocks Field + E-Graph Básico | ✅ COMPLETADA |
| **2** | **Reglas de Optimización** | 🔄 EN CURSO |
| **3** | CodeGen SIMD Avanzado | ⏳ Pendiente |
| **4** | API de Producción | ⏳ Pendiente |

---

## Fase 0: Proof of Concept ✅ COMPLETADA

**Objetivo**: Demostrar que el pipeline MatExpr → E-Graph → C funciona.

### Entregables Completados

| Entregable | Evidencia |
|------------|-----------|
| VecExpr DSL | `AmoLean/Vector/Basic.lean` |
| CodeGen C | `AmoLean/Vector/CodeGen.lean` |
| FRI Fold Spec | `AmoLean/FRI/FoldExpr.lean` |
| Generated C | `generated/fri_fold.h` |
| Safety Checks | 13/13 pasan |
| Oracle Testing | 6/6 pasan |
| CI/CD | GitHub Actions |

### Métricas

| Métrica | Resultado |
|---------|-----------|
| Correctness | 100% oracle tests pass |
| Safety | 13/13 DD compliance |
| Speedup vs Lean | 32.3x |

### Limitación Conocida

Phase 0 usó UInt64 nativo, no aritmética de campo real.
Esto se resolvió en Phase 1.

---

## Fase 1: Goldilocks Field + E-Graph ✅ COMPLETADA

**Objetivo**: Implementar aritmética de campo real y E-Graph básico.

### Entregables Completados

| Entregable | Evidencia |
|------------|-----------|
| Goldilocks Lean | `AmoLean/Field/Goldilocks.lean` |
| Goldilocks C | `generated/field_goldilocks.h` |
| Reducción Especializada | `goldilocks_reduce128()` |
| Tests de Borde | 37/37 pasan |
| S-Box x^7 | Implementado y verificado |
| E-Graph VecExpr | `AmoLean/EGraph/VecExpr.lean` |
| Sanitizer Tests | 37/37 pasan con ASan+UBSan |

### Métricas

| Métrica | Resultado |
|---------|-----------|
| Goldilocks correctness | 37/37 tests pass |
| E-Graph rules | 4 reglas funcionando |
| Overhead vs UInt64 | ~5x (aceptable) |
| Throughput | 568 M elem/s |

### Correcciones Críticas Aplicadas

| Error Original | Corrección |
|----------------|------------|
| `field_add` con overflow | Usar `__uint128_t` |
| Barrett Reduction | Reducción especializada Goldilocks |
| Tests solo aleatorios | Tests aleatorios + casos borde |

---

## Fase 2: Reglas de Optimización 🔄 EN CURSO

**Objetivo**: Demostrar que el E-Graph puede OPTIMIZAR código existente.

### Justificación

Las fases anteriores crearon infraestructura. Ahora debemos **demostrar valor**:
- Tomar código ingenuo
- Aplicar reglas matemáticas
- Producir código con MENOS operaciones
- Medir la reducción

### Entregables

| # | Entregable | Descripción | Impacto |
|---|------------|-------------|---------|
| 2.1 | Matrix Rewrites | `(A * B) * v → A * (B * v)` | O(N³) → O(N²) |
| 2.2 | Constant Folding | Pre-computar constantes | Elimina ops runtime |
| 2.3 | Field Simplification | `x*1=x`, `x+0=x`, `x*0=0` | Limpia código |
| 2.4 | **Optimization Benchmark** | Medir reducción | **CRÍTICO** |

### 2.1 Matrix Rewrites

La asociatividad de multiplicación matricial es la optimización más importante:

```lean
-- Regla de reescritura
theorem mat_mul_assoc_vec : (A * B) * v = A * (B * v)
```

**Impacto**:
- Naive: `(MDS * MDS) * state` → O(N³) para MDS×MDS, luego O(N²)
- Optimized: `MDS * (MDS * state)` → O(N²) + O(N²) = O(N²)

### 2.2 Constant Folding

```lean
-- Si A y B son constantes conocidas
theorem const_fold_add : const(a) + const(b) = const(a + b)
theorem const_fold_mul : const(a) * const(b) = const(a * b)
```

**Aplicación**: Round constants de Poseidon se pre-computan.

### 2.3 Field Simplification

```lean
theorem field_mul_one  : x * 1 = x
theorem field_mul_zero : x * 0 = 0
theorem field_add_zero : x + 0 = x
```

### 2.4 Optimization Benchmark (CRÍTICO)

Este es el entregable más importante. Sin él, no podemos demostrar el valor de AMO-Lean.

**Formato del benchmark**:
```
Código Naive:
  - field_mul: 847 llamadas
  - field_add: 512 llamadas

Código Optimizado:
  - field_mul: 423 llamadas (50% reducción)
  - field_add: 256 llamadas (50% reducción)
```

### Criterios de Éxito Phase 2

| Criterio | Métrica Mínima |
|----------|----------------|
| Matrix rewrite funciona | ≥1 caso donde reduce ops |
| Constant folding funciona | Round constants pre-computadas |
| Benchmark muestra mejora | ≥10% reducción en operaciones |
| Tests siguen pasando | 98/98 tests de Phase 0/1 |

---

## Fase 3: CodeGen SIMD Avanzado ⏳ PENDIENTE

**Prerequisito**: Phase 2 completada.

**Objetivo**: Generar código SIMD de alta calidad.

| Entregable | Descripción |
|------------|-------------|
| AVX2 Support | Operaciones vectoriales 256-bit |
| AVX512 Support | Operaciones vectoriales 512-bit |
| Loop Unrolling | Configurable |
| Benchmarks | vs HorizenLabs/poseidon2 |

---

## Fase 4: API de Producción ⏳ PENDIENTE

**Prerequisito**: Phase 3 completada.

**Objetivo**: API limpia para usuarios.

```lean
def compileToC (spec : MatExpr F m n) (config : CompileConfig) : IO String
```

| Entregable | Descripción |
|------------|-------------|
| `compileToC` API | Interfaz de alto nivel |
| Translation Proofs | Teoremas de equivalencia |
| Documentation | Guía de uso |

---

## Diagrama de Fases

```
Phase 0 ──────► Phase 1 ──────► Phase 2 ──────► Phase 3 ──────► Phase 4
    │              │               │               │               │
    ▼              ▼               ▼               ▼               ▼
  PoC +        Goldilocks      REGLAS DE        SIMD           API +
  CI/CD        + E-Graph      OPTIMIZACIÓN    Avanzado        Proofs
                              (Matrix,
                               Const Fold,
                               BENCHMARK)
```

---

## Política de Documentación

### Este Archivo
- Es el ÚNICO roadmap para Option A
- Cualquier cambio de estrategia se registra aquí
- El changelog al final documenta la evolución

### Otros Documentos
- `DESIGN_DECISIONS.md`: Decisiones técnicas (DD-001, DD-002, etc.)
- `PROGRESS.md`: Log de trabajo completado
- `BENCHMARKS.md`: Resultados de benchmarks

### Regla de Oro
> Si hay conflicto entre documentos, este ROADMAP tiene precedencia.

---

## Changelog

| Fecha | Cambio |
|-------|--------|
| 2026-01-28 | Documento creado, Phase 0 y 1 completadas |
| 2026-01-28 | **CORRECCIÓN**: Phase 2 redefinida como "Reglas de Optimización" |
| 2026-01-28 | Phase 2 NO es "Primitivas Plonky3" - eso era scope creep |
| 2026-01-28 | Consolidación de documentación, este archivo es ahora el único roadmap |

---

## Lección Aprendida: Evitar Drift

Este proyecto experimentó "drift" cuando existían múltiples roadmaps:
- `/docs/OPTION_A_ROADMAP.md` (original correcto)
- `/docs/option-a/ROADMAP.md` (derivó hacia "más primitivas")

**Solución**: Este archivo es ahora el ÚNICO roadmap. Los otros fueron archivados.

---

*Documento autoritativo de AMO-Lean Option A*
