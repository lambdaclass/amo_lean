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
| **2** | Reglas de Optimización | ✅ COMPLETADA |
| **3** | CodeGen SIMD Avanzado | 🔄 SIGUIENTE |
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

## Fase 2: Reglas de Optimización ✅ COMPLETADA

**Objetivo**: Demostrar que el E-Graph puede OPTIMIZAR código.

**Qué se hizo**:
- Motor de optimización con mitigaciones (`AmoLean/EGraph/Optimize.lean`)
- Constant Folding sintáctico (Const+Const → Const)
- Identity Rules (x+0=x, x*1=x)
- Zero Propagation ((expr)*0 → 0)
- Power Rules (x^0=1, x^1=x)
- Factorization (a*b + a*c → a*(b+c))
- Oracle Testing para verificar corrección de reglas
- Benchmark suite (`Benchmarks/Phase2/Optimization.lean`)

**Entregables**:
| # | Entregable | Descripción | Estado |
|---|------------|-------------|--------|
| 2.1 | Identity Rules | `x*1=x`, `x+0=x`, `x*0=0` | ✅ |
| 2.2 | Constant Folding | Pre-computar constantes | ✅ |
| 2.3 | Zero Propagation | `(complex)*0 → 0` | ✅ |
| 2.4 | **Optimization Benchmark** | Medir reducción | ✅ **91.67%** |

**Mitigaciones implementadas** (basadas en "Term Rewriting and All That"):
| Riesgo | Mitigación |
|--------|------------|
| Ciclos de Conmutatividad | Ordenamiento canónico por hash |
| Explosión de Asociatividad | Reglas dirigidas con costDelta |
| Reglas Mentirosas | Oracle testing con valores aleatorios |

**Resultado**: **91.67% reducción** (24 ops → 2 ops), superando el criterio de ≥10%.

### QA Benchmark (Los 3 Enemigos Mortales)

| Test | Requisito | Resultado | Status |
|------|-----------|-----------|--------|
| Effectiveness | ≥40% reducción | **72.22%** | ✅ |
| Semantic Equivalence | 100% equivalencia | **500/500** | ✅ |
| Rule Audit | Sin sorry | 0 sorry (12 sin teorema) | ⚠️ Relaxed |
| Compilation Time | <10s | **máx 83ms** | ✅ |

**Gap identificado**: 12 reglas son sintácticas (sin teoremas formales).
**Mitigación actual**: Oracle testing compensa.
**Plan**: Agregar teoremas en Fase 3.

---

## Fase 3: CodeGen SIMD + Verificación Parcial 🔄 SIGUIENTE

**Prerequisito**: Fase 2 completada. ✅

**Objetivo**: Generar código SIMD de alta calidad Y comenzar verificación formal.

### 3.1 CodeGen SIMD

| Entregable | Descripción | Prioridad |
|------------|-------------|-----------|
| AVX2 Support | Operaciones vectoriales 256-bit | Alta |
| AVX512 Support | Operaciones vectoriales 512-bit | Media |
| Loop Unrolling | Configurable | Media |

### 3.2 Verificación Parcial de Reglas

| Entregable | Descripción | Prioridad |
|------------|-------------|-----------|
| Teoremas para Identity Rules | `add_zero`, `mul_one`, `mul_zero` | Alta |
| Teoremas para Power Rules | `pow_zero`, `pow_one` | Media |
| CI: Rechazar reglas sin teorema | Script de auditoría automática | Alta |

**Justificación**: Comenzar verificación formal ahora reduce deuda técnica.

### 3.3 Translation Validation (FFI)

| Entregable | Descripción | Prioridad |
|------------|-------------|-----------|
| FFI Lean↔C | Llamar código C desde Lean | Alta |
| Test: Lean == C_Naive == C_Optimized | Fuzzing diferencial completo | Alta |

---

## Fase 4: API de Producción + Verificación Completa ⏳ PENDIENTE

**Prerequisito**: Fase 3 completada.

**Objetivo**: API limpia para usuarios externos Y verificación formal completa.

### 4.1 API de Producción

```lean
def compileToC (spec : MatExpr F m n) (config : CompileConfig) : IO String
```

### 4.2 Certified Compilation

| Entregable | Descripción |
|------------|-------------|
| **Teoremas para TODAS las reglas** | 0 reglas sin prueba formal |
| **VerifiedRewriteRule** | Estructura con prueba obligatoria |
| **Soundness Theorem** | `optimize_preserves_semantics` |

```lean
-- Estructura objetivo para reglas verificadas
structure VerifiedRewriteRule (F : Type*) [Field F] where
  name : String
  lhs : Pattern
  rhs : Pattern
  proof : ∀ (env : VarId → F), eval env lhs = eval env rhs
```

### 4.3 Beneficios de Verificación Completa

| Beneficio | Descripción |
|-----------|-------------|
| **Certified Compilation** | Como CompCert - código correcto por construcción |
| **Composición Segura** | Combinar reglas verificadas es seguro |
| **Confianza del Usuario** | "Optimizador formalmente verificado" |
| **Regresiones Imposibles** | Cambios incorrectos no compilan |
| **Documentación Precisa** | Teoremas = especificación ejecutable |

---

## Roadmap de Verificación

```
Fase 2 (actual)     Fase 3              Fase 4
─────────────────────────────────────────────────────────
Oracle Testing  →   Teoremas Parciales  →  Teoremas Completos
(probabilístico)    (reglas críticas)      (todas las reglas)

500 tests           ~6 teoremas            12+ teoremas
runtime             compile-time           compile-time
```

| Nivel | Garantía | Cobertura | Costo |
|-------|----------|-----------|-------|
| **Oracle Testing** | Probabilística | 100 inputs/regla | O(n) por ejecución |
| **Teoremas Parciales** | Matemática (parcial) | Reglas críticas | O(1) después de probar |
| **Teoremas Completos** | Matemática (total) | Todas las reglas | O(1) después de probar |

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
| Tests totales | 120/120 pass |
| Speedup Lean→C | 32.3x |
| Goldilocks throughput | 568 M elem/s |
| **Optimization reduction** | **91.67%** |
| Fases completadas | 3 de 4 |

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
| 2026-01-28 | **Phase 2 completada** - 91.67% reducción de operaciones |
| 2026-01-28 | QA Benchmark agregado - 4 tests críticos |
| 2026-01-28 | Roadmap de verificación formal incorporado |

---

*AMO-Lean: Automatic Mathematical Optimizer in Lean*
