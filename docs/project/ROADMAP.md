# AMO-Lean: Roadmap Oficial

**Última actualización**: 2026-01-28
**Este es el único roadmap del proyecto.**

---

## Qué es AMO-Lean

**AMO-Lean** = *Automatic Mathematical Optimizer in Lean*

Un **optimizador formal** que:
1. Toma especificaciones matemáticas (MatExpr, VecExpr)
2. Aplica reglas de reescritura verificadas via E-Graph
3. Genera código C/SIMD optimizado
4. Garantiza corrección por construcción

```
Spec Matemática  →  E-Graph Saturation  →  Código C Optimizado
  (MatExpr)          (reglas verificadas)   (correcto por construcción)
```

---

## Qué NO es AMO-Lean

- **NO es una zkVM** - Es una herramienta que zkVMs pueden usar
- **NO es una librería criptográfica** - Es un compilador/optimizador
- **NO es específico a un dominio** - Puede optimizar cualquier cómputo expresable como MatExpr

---

## Casos de Uso

| Caso de Uso | Descripción |
|-------------|-------------|
| **Primitivas criptográficas** | FRI, Poseidon2, NTT, etc. |
| **Álgebra lineal** | Multiplicación matricial, transformadas |
| **Integración en zkVMs** | Generar código optimizado para provers |
| **Standalone** | Cualquier cómputo matemático optimizable |

---

## Estado Actual

| Fase | Descripción | Estado |
|------|-------------|--------|
| **0** | Proof of Concept (FRI Fold) | ✅ COMPLETADA |
| **1** | Goldilocks Field + E-Graph Básico | ✅ COMPLETADA |
| **2** | Reglas de Optimización | 🔄 SIGUIENTE |
| **3** | CodeGen SIMD Avanzado | ⏳ Pendiente |
| **4** | API de Producción | ⏳ Pendiente |

---

## Fase 0: Proof of Concept ✅ COMPLETADA

**Objetivo**: Demostrar que el pipeline Spec → E-Graph → C funciona.

**Qué se hizo**:
- Implementar VecExpr DSL para expresar operaciones vectoriales
- Crear CodeGen que genera código C desde VecExpr
- Usar FRI Fold como caso de prueba
- Validar con oracle testing (Lean vs C)
- Medir speedup (32.3x)

**Entregables**:
| Entregable | Evidencia |
|------------|-----------|
| VecExpr DSL | `AmoLean/Vector/Basic.lean` |
| CodeGen C | `AmoLean/Vector/CodeGen.lean` |
| FRI Fold como caso de prueba | `AmoLean/FRI/FoldExpr.lean` |
| Safety Checks | 13/13 pasan |
| Oracle Testing | 6/6 pasan |
| Benchmark | **32.3x speedup** |

**Limitación**: Usó UInt64 nativo, no campo finito real.

---

## Fase 1: Goldilocks Field + E-Graph ✅ COMPLETADA

**Objetivo**: Aritmética de campo real y E-Graph funcional.

**Qué se hizo**:
- Implementar campo Goldilocks (p = 2^64 - 2^32 + 1)
- Reducción especializada (NO Barrett genérica)
- S-Box x^7 (requerido para seguridad en Goldilocks)
- Integrar VecExpr con E-Graph (4 reglas básicas)
- Tests con sanitizers (ASan + UBSan)

**Entregables**:
| Entregable | Evidencia |
|------------|-----------|
| Goldilocks Lean | `AmoLean/Field/Goldilocks.lean` |
| Goldilocks C | `generated/field_goldilocks.h` |
| E-Graph VecExpr | `AmoLean/EGraph/VecExpr.lean` |
| Tests | 37/37 Goldilocks + 37/37 Sanitizer |
| Benchmark | ~5x overhead vs UInt64 (aceptable) |

---

## Fase 2: Reglas de Optimización 🔄 SIGUIENTE

**Objetivo**: Demostrar que el E-Graph puede OPTIMIZAR código.

**Por qué es crítica**: Las fases 0 y 1 construyeron infraestructura. La fase 2 debe demostrar el VALOR del proyecto: generar código con MENOS operaciones.

**Entregables**:
| # | Entregable | Descripción | Impacto |
|---|------------|-------------|---------|
| 2.1 | Matrix Rewrites | `(A * B) * v → A * (B * v)` | O(N³) → O(N²) |
| 2.2 | Constant Folding | Pre-computar constantes | Elimina ops runtime |
| 2.3 | Field Simplification | `x*1=x`, `x+0=x`, `x*0=0` | Limpia código |
| 2.4 | **Optimization Benchmark** | Medir reducción | **CRÍTICO** |

**Criterio de éxito**: ≥10% reducción en operaciones de campo.

---

## Fase 3: CodeGen SIMD Avanzado ⏳ PENDIENTE

**Prerequisito**: Fase 2 completada.

**Objetivo**: Generar código SIMD de alta calidad.

| Entregable | Descripción |
|------------|-------------|
| AVX2 Support | Operaciones vectoriales 256-bit |
| AVX512 Support | Operaciones vectoriales 512-bit |
| Loop Unrolling | Configurable |

---

## Fase 4: API de Producción ⏳ PENDIENTE

**Prerequisito**: Fase 3 completada.

**Objetivo**: API limpia para usuarios externos.

```lean
def compileToC (spec : MatExpr F m n) (config : CompileConfig) : IO String
```

---

## Rol de FRI y Poseidon2

FRI y Poseidon2 NO son el objetivo del proyecto. Son **casos de prueba**:

| Componente | Rol |
|------------|-----|
| FRI Fold | Caso de prueba para operaciones lineales |
| Poseidon2 | Caso de prueba para operaciones no-lineales (S-Box) |
| Goldilocks | Campo real para validar aritmética |

Estos componentes sirven para:
1. **Validar** que el optimizador funciona (oracle testing)
2. **Demostrar** optimización en casos reales
3. **Benchmark** contra implementaciones de referencia

---

## Métricas del Proyecto

| Métrica | Valor |
|---------|-------|
| Tests totales | 98/98 pass |
| Speedup Lean→C | 32.3x |
| Goldilocks throughput | 568 M elem/s |
| Fases completadas | 2 de 4 |

---

## Documentación Relacionada

| Documento | Propósito |
|-----------|-----------|
| `DESIGN_DECISIONS.md` | Decisiones técnicas (DD-001 a DD-006) |
| `PROGRESS.md` | Log de trabajo completado |
| `BENCHMARKS.md` | Resultados de rendimiento |
| `TESTING_ANALYSIS.md` | Análisis de testing |

---

## Changelog

| Fecha | Cambio |
|-------|--------|
| 2026-01-28 | Phase 0 completada |
| 2026-01-28 | Phase 1 completada |
| 2026-01-28 | Documentación reorganizada |
| 2026-01-28 | Eliminado nombre "Option A" - el proyecto es AMO-Lean |
| 2026-01-28 | Clarificado: AMO-Lean es un optimizador, NO una zkVM |

---

*AMO-Lean: Automatic Mathematical Optimizer in Lean*
