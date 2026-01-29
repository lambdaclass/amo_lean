# AMO-Lean: Roadmap Oficial

**Última actualización**: 2026-01-29
**Este es el único roadmap del proyecto.**

> **IMPORTANTE:** Ver [UNIFIED_PLAN.md](UNIFIED_PLAN.md) para el plan detallado
> que incluye la arquitectura dual (Verificador + Generador).

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
| **3** | CodeGen SIMD (AVX2) | ✅ COMPLETADA |
| **4** | Empaquetado + Verificación | ✅ COMPLETADA |
| **5** | NTT Core | ✅ COMPLETADA |
| **6A** | AMO-Lean como Verificador de Plonky3 | 🔄 SIGUIENTE |
| **6B** | AMO-Lean como Generador | ⏳ FUTURO |

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

## Fase 3: CodeGen SIMD (AVX2) ✅ COMPLETADA

**Fecha**: 2026-01-28
**Objetivo**: Implementar vectorización AVX2 con verificación de correctitud.

### 3.1 CodeGen AVX2 ✅

| Entregable | Estado | Evidencia |
|------------|--------|-----------|
| AVX2 Goldilocks | ✅ | `generated/field_goldilocks_avx2.h` |
| FRI Fold vectorizado | ✅ | `generated/fri_fold_avx2.h` |
| Comparación unsigned | ✅ | `goldilocks_avx2_cmpgt_epu64()` |
| Overflow handling | ✅ | Detección y corrección de overflow |

### 3.2 Tests y QA ✅

| Test Suite | Resultado | Notas |
|------------|-----------|-------|
| AVX2 Consistency (add/sub/mul) | 300/300 ✅ | Comparación vs escalar |
| AVX2 Edge Cases | 1/1 ✅ | Valores extremos |
| AVX2 FRI Fold | 100/100 ✅ | Fold vectorizado |
| QA: Alignment Tests | ✅ | Offsets 0-24 bytes |
| QA: Tail Processing | ✅ | Tamaños 1,2,3,5,7,11,13,17,23,31,61,127,1023 |
| QA: Assembly Verification | ✅ | Sin calls a librerías en hot path |

### 3.3 Benchmarks CI (GitHub Actions)

| Métrica | Valor |
|---------|-------|
| Multiplicación Speedup | **4.00x** (teórico máximo) |
| Multiplicación Eficiencia | 100% del ideal |
| FRI Fold | Informativo (compilador auto-vectoriza escalar) |

### 3.4 Bugs Corregidos Durante CI

| Bug | Causa | Fix |
|-----|-------|-----|
| FRI fold mismatch (diff=EPSILON) | `_mm256_cmpgt_epi64` es signed | XOR con sign bit para unsigned |
| Addition overflow | `a+b >= 2^64` no manejado | Detección de overflow, agregar EPSILON |
| aligned_alloc invalid | Tamaño no múltiplo de alignment | `round_up_32()` helper |
| UBSan PRNG shift | `-fsanitize=integer` flags wraparound | Removido `,integer` de flags |

### 3.5 FFI/Translation Validation

| Entregable | Estado | Notas |
|------------|--------|-------|
| FFI Lean↔C | ⏳ Diferido | Prioridad baja vs correctitud |
| Differential Testing | ✅ | Via subprocess + oracle tests |

---

## Fase 4: Empaquetado + Verificación ✅ COMPLETADA

**Fecha**: 2026-01-29
**Objetivo**: Eliminar sorry statements y empaquetar como librería.

### 4.1 Verificación Formal Completada

| Entregable | Estado |
|------------|--------|
| **pow_one**: x^1 = x | ✅ Verificado |
| **one_pow**: 1^n = 1 | ✅ Verificado |
| **zero_pow**: 0^(n+1) = 0 | ✅ Verificado |
| Teoremas auxiliares (foldl_id, etc.) | ✅ |
| **Total reglas verificadas** | **19/20** |

### 4.2 libamolean - Librería C

| Entregable | Descripción |
|------------|-------------|
| `libamolean/` | Directorio de librería |
| `include/amolean/` | Headers públicos |
| `CMakeLists.txt` | Build con detección de CPU |
| `README.md` | Documentación y ejemplos |
| Tests | Scalar + AVX2 |

### 4.3 Release v0.1.0

```bash
git tag v0.1.0
```

| Métrica | Valor |
|---------|-------|
| Tests totales | 1456+ |
| Reglas verificadas | 19/20 (95%) |
| Speedup Lean→C | 32.3x |
| AVX2 speedup | 4.00x |
| Optimization reduction | 91.67% |

---

## Fase 5: NTT Core ✅ COMPLETADA

**Fecha**: 2026-01-29
**Objetivo**: Implementar NTT (Number Theoretic Transform) con verificación formal.

### Arquitectura de Refinamiento (Modelo Trieu)

```
┌─────────────────────────────────────────────────────────────────┐
│ CAPA 4: Código C (Skeleton + Kernel)                            │
├─────────────────────────────────────────────────────────────────┤
│ CAPA 3: Implementación con Bounds (LazyButterfly)               │
├─────────────────────────────────────────────────────────────────┤
│ CAPA 2: Algoritmo Recursivo (Cooley-Tukey DIT)                  │
├─────────────────────────────────────────────────────────────────┤
│ CAPA 1: Especificación Matemática (NTT_spec)                    │
└─────────────────────────────────────────────────────────────────┘
```

### Entregables Completados

| # | Entregable | Estado |
|---|------------|--------|
| 5.1 | `NTT/Spec.lean` - Especificación NTT | ✅ |
| 5.2 | `NTT/CooleyTukey.lean` - Algoritmo recursivo | ✅ |
| 5.3 | `NTT/Bounds.lean` - LazyGoldilocks refinados | ✅ |
| 5.4 | `NTT/LazyButterfly.lean` - Butterfly verificado | ✅ |
| 5.5 | `generated/ntt_kernel.h` - Kernel C 128-bit | ✅ |
| 5.6 | `generated/ntt_skeleton.c` - Skeleton iterativo | ✅ |

### Decisiones de Diseño

| ID | Decisión | Razón |
|----|----------|-------|
| DD-015 | NTT_spec O(N²) solo para proofs | Eficiencia viene de Cooley-Tukey |
| DD-016 | Butterfly = NTT base-2 | Verifica índices sin errores |
| DD-022 | Nat en vez de UInt64 en Lean | Evita wrapping, Nat arbitrario |
| DD-023 | Skeleton + Kernel | Loop en C + Kernel verificado |
| DD-024 | Early return para N=1 | Fix heap-buffer-overflow |

### QA Final Audit Results

| Test Suite | Resultado | Notas |
|------------|-----------|-------|
| C Kernel Tests | 16/16 ✅ | Lazy reduction + butterfly |
| Bit-Reversal Tests | 35/35 ✅ | Involution + bijection |
| Sanitizer Tests | 4/4 ✅ | ASan + UBSan (bug N=1 fixed) |
| Oracle Tests | 4/4 ✅ | Lean = C para N=4,8,16,32 |

### Performance Benchmarks

| Size | Time/NTT | Throughput |
|------|----------|------------|
| N=256 | 0.009 ms | 38.30 M elem/s |
| N=1024 | 0.045 ms | 29.90 M elem/s |
| N=4096 | 0.235 ms | 23.80 M elem/s |
| N=16384 | 1.068 ms | 20.93 M elem/s |
| N=65536 | 5.225 ms | 16.67 M elem/s |
| N=262144 | 21.39 ms | 16.40 M elem/s |

---

## Fase 6A: AMO-Lean como Verificador de Plonky3 🔄 SIGUIENTE

**Objetivo**: Usar AMO-Lean para verificar y optimizar código de Plonky3.

### Concepto

AMO-Lean actúa como **verificador formal externo** para Plonky3:

```
┌─────────────────────────────────────────────────────────────────┐
│                    PIPELINE VERIFICADOR                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Plonky3 (Rust)              AMO-Lean (Lean)                   │
│  ┌─────────────┐             ┌─────────────┐                   │
│  │ NTT impl    │ ─────────► │ Spec formal │                   │
│  │ Goldilocks  │   extract   │ Verificar   │                   │
│  │ FRI fold    │             │ Optimizar   │                   │
│  └─────────────┘             └─────────────┘                   │
│                                    │                            │
│                                    ▼                            │
│                              Código C/SIMD                      │
│                              (puede reemplazar                  │
│                               hot paths)                        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Entregables Planificados

| # | Entregable | Descripción |
|---|------------|-------------|
| 6A.1 | Análisis de Plonky3 | Identificar primitivas clave |
| 6A.2 | Mapeo Plonky3→AMO-Lean | Correspondencia de estructuras |
| 6A.3 | Verificación cruzada | Oracle testing Plonky3 vs AMO-Lean |
| 6A.4 | Hot path optimization | Generar código C para paths críticos |

### Directorios de Trabajo

```
amo-lean/
├── AmoLean/
│   ├── Plonky3/              # ← NUEVO: Verificador Plonky3
│   │   ├── Goldilocks.lean   # Mapping campo
│   │   ├── NTT.lean          # Verificación NTT
│   │   └── FRI.lean          # Verificación FRI
│   └── ...
└── verification/
    └── plonky3/              # ← NUEVO: Tests cruzados
        ├── oracle_tests.c
        └── benchmarks.c
```

---

## Fase 6B: AMO-Lean como Generador ⏳ FUTURO

**Objetivo**: Generar código optimizado para otros proyectos zkVM.

### Concepto

AMO-Lean genera código optimizado para múltiples backends:

```
Spec Matemática → E-Graph Saturation → Código Backend
                  (optimización)        ├── C/C++
                                       ├── Rust
                                       ├── CUDA
                                       └── WASM
```

### Directorios de Trabajo

```
amo-lean/
├── AmoLean/
│   ├── CodeGen/              # ← EXPANDIR
│   │   ├── C.lean            # Existente
│   │   ├── Rust.lean         # Nuevo
│   │   ├── CUDA.lean         # Nuevo
│   │   └── WASM.lean         # Nuevo
│   └── ...
└── generated/
    ├── c/                    # ← Reorganizar
    ├── rust/                 # ← Nuevo
    └── wasm/                 # ← Nuevo
```

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
| Tests totales | **1550+** pass |
| Speedup Lean→C (escalar) | 32.3x |
| **AVX2 Speedup (4-way SIMD)** | **4.00x** |
| Goldilocks throughput | 568 M elem/s |
| **NTT throughput** | **16-38 M elem/s** |
| **Optimization reduction** | **91.67%** |
| Fases completadas | **5 de 5 core** |

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
| 2026-01-28 | **Phase 3 completada** - AVX2 SIMD con 4.00x speedup |
| 2026-01-28 | CI configurado: 7 jobs, todos passing |
| 2026-01-28 | Bugs críticos corregidos: unsigned comparison, overflow handling |
| 2026-01-29 | **Phase 5 completada** - NTT Core con QA audit |
| 2026-01-29 | Bug crítico N=1 heap-buffer-overflow detectado y corregido |
| 2026-01-29 | 59 tests NTT nuevos (Lean + C) |
| 2026-01-29 | Estructura Fase 6A/6B definida |

---

*AMO-Lean: Automatic Mathematical Optimizer in Lean*
