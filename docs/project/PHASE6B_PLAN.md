# Phase 6B: AMO-Lean como Generador

**Fecha de creación**: 2026-01-29
**Estado**: EN DESARROLLO
**Prerequisito**: Phase 6A completada (v0.6.0-phase6a-plonky3-verified)
**Estrategia aprobada**: Opción C - Plan Híbrido Revisado

---

## Resumen Ejecutivo

**Objetivo**: Transformar AMO-Lean de "verificador" a "generador" de código optimizado.

**Meta de rendimiento**: NTT ≥80% velocidad de Plonky3 (actualmente ~50%)

**Entregable final**: `amolean-ntt` crate Rust publicable

---

## Decisiones de Diseño (ADR - Architecture Decision Records)

### ADR-6B-001: Estrategia de Optimización AVX2

**Estado**: APROBADA (2026-01-29)
**Decisores**: Equipo de desarrollo + QA Senior

#### Contexto

Phase 6B requiere mejorar el rendimiento de NTT de ~50% a ≥80% respecto a Plonky3.
La opción obvia era vectorizar toda la aritmética de campo usando AVX2.

#### Opciones Consideradas

| Opción | Descripción | Pros | Contras |
|--------|-------------|------|---------|
| **A** | Portar código AVX2 de Plonky3 | Probado, rápido | Dependencia externa |
| **B** | Solo twiddle caching, sin SIMD | Bajo riesgo | Solo +25-30% |
| **C** | **Híbrido: escalar mul + AVX2 add/sub** | Balanceado | Complejidad media |
| **D** | AVX2 completo (mul emulado) | Máximo SIMD | MUL 1.33x más lento |

#### Decisión

**Opción C: Estrategia Híbrida**

#### Justificación

1. **Evidencia de Plonky3**: Su código documenta que `mul64_64` emulado es "1.33x SLOWER
   than the scalar instruction". Vectorizar multiplicación es contraproducente.

2. **Análisis QA Senior**: Identificó correctamente que:
   - El "4-way split" para mul requiere 12-15 instrucciones
   - El multiplicador escalar nativo (mulx) es extremadamente rápido
   - Mejor vectorizar operaciones donde AVX2 SÍ gana: add, sub, square, data movement

3. **Datos de Plonky3**:
   - `mul` emulado: 1.33x más lento que escalar
   - `square` emulado: 1.2x más RÁPIDO que escalar (aprovecha simetría)
   - `add/sub`: Trivial de vectorizar, siempre gana

#### Consecuencias

- **Positivas**: Evitamos performance regression en multiplicación
- **Negativas**: Speedup total será menor (~75-80% vs ~85-90% teórico)
- **Riesgos mitigados**: Complejidad reducida, menos bugs potenciales

---

### ADR-6B-002: Twiddle Caching Parcial

**Estado**: APROBADA (2026-01-29)
**Decisores**: Equipo de desarrollo + QA Senior

#### Contexto

Plonky3 pre-computa todos los twiddle factors. Esto acelera NTT pero consume memoria.

#### Problema Identificado por QA

Para N = 2^18 (262,144 elementos):
- Twiddles completos = N/2 = 131,072 elementos = **1 MB**
- L3 cache típica = 8-32 MB
- **Riesgo**: Twiddles pueden evictar datos del usuario de cache

#### Decisión

**Cache parcial por capas** en lugar de cache completo.

```
Capas 0-10:  Cachear (2048 twiddles = 16 KB, cabe en L1)
Capas 11+:   Computar on-the-fly (acceso con stride grande, pocos hits)
```

#### Justificación

1. Capas tempranas de NTT acceden twiddles secuencialmente → benefician de cache
2. Capas tardías acceden con stride exponencialmente creciente → cache misses anyway
3. 16 KB cabe cómodamente en L1 (típicamente 32 KB)
4. Computar twiddle es barato: una multiplicación modular

#### Consecuencias

- **Positivas**: Sin cache thrashing, datos de usuario permanecen en L2/L3
- **Negativas**: Ligeramente menos speedup que cache completo para N pequeño
- **Trade-off aceptable**: Para N grande (donde importa), esta estrategia es superior

---

### ADR-6B-003: Manejo de Alineación de Memoria

**Estado**: APROBADA (2026-01-29)
**Decisores**: Equipo de desarrollo + QA Senior

#### Contexto

Instrucciones AVX2 como `vmovdqa` requieren alineación a 32 bytes.
Punteros estándar de C/Rust están alineados a 8 bytes (sizeof(u64)).

#### Problema

```c
// Esto causa SIGSEGV si ptr no está alineado a 32 bytes:
__m256i vec = _mm256_load_si256((__m256i*)ptr);
```

#### Opciones

| Opción | Descripción | Overhead | Seguridad |
|--------|-------------|----------|-----------|
| 1 | Requerir alineación en API | 0% | Usuario debe cumplir |
| 2 | Usar `vmovdqu` (unaligned) | ~5% | Siempre seguro |
| 3 | Copiar a buffer interno alineado | ~10% | Siempre seguro |
| 4 | Rust `#[repr(align(32))]` | 0% | Type system garantiza |

#### Decisión

- **C API**: Opción 2 (`vmovdqu`) - seguridad sobre velocidad máxima
- **Rust crate**: Opción 4 - el type system garantiza alineación

#### Justificación

1. ~5% overhead es aceptable para evitar crashes silenciosos
2. En Rust, el compilador puede verificar alineación en compile-time
3. Usuarios avanzados pueden usar la API alineada si necesitan el último 5%

---

### ADR-6B-004: Riesgos Adicionales y Mitigaciones

**Estado**: DOCUMENTADA (2026-01-29)

#### Riesgos Identificados Post-Revisión QA

| ID | Riesgo | Probabilidad | Impacto | Mitigación |
|----|--------|--------------|---------|------------|
| R6 | Cache thrashing con twiddles | Media | Alto | ADR-6B-002 |
| R7 | SIGSEGV por alineación | Alta | Crítico | ADR-6B-003 |
| R8 | CPU frequency throttling | Media | Medio | Monitorear con turbostat |
| R9 | Compiler auto-vectorization | Media | Bajo | `-fno-tree-vectorize` |
| R10 | CI/CD sin AVX2 | Alta | Bajo | Runtime feature detection |

#### Mitigaciones Detalladas

**R8 - Frequency Throttling**:
```bash
# Benchmark con monitoreo de frecuencia
sudo turbostat --show Avg_MHz,Busy%,Bzy_MHz ./benchmark
# Si frecuencia cae >20%, considerar reducir uso de AVX2
```

**R9 - Compiler Interference**:
```c
// Deshabilitar auto-vectorización donde usamos intrinsics
#pragma GCC optimize("no-tree-vectorize")
void ntt_avx2_layer(...) { ... }
```

**R10 - CI/CD**:
```c
// Runtime detection para CI sin AVX2
#include <cpuid.h>
static int has_avx2(void) {
    unsigned int eax, ebx, ecx, edx;
    if (!__get_cpuid(7, &eax, &ebx, &ecx, &edx)) return 0;
    return (ebx & bit_AVX2) != 0;
}
```

---

### ADR-6B-005: Fail-Fast Microbenchmark para AVX2

**Estado**: APROBADA (2026-01-29)
**Decisores**: Equipo de desarrollo + Revisión QA #2

#### Contexto

Antes de invertir semanas en implementar AVX2 para NTT, debemos **verificar
empíricamente** que nuestras suposiciones sobre rendimiento son correctas.

#### Problema Identificado

En la revisión del plan, se identificó que:
- Asumimos que `mul` AVX2 emulado sería lento basándonos en Plonky3
- Pero NO planeamos verificarlo con nuestro propio código
- Esto es un **error metodológico**: construir sobre supuestos no verificados

#### Decisión

**Fail-Fast Microbenchmark (Día 1 de 6B.2)**

```
ANTES de escribir código NTT AVX2:
1. Implementar goldilocks_mul_avx2() aislada (emulación 4-way)
2. Implementar goldilocks_mul_scalar() como baseline
3. Benchmark: 100M operaciones
4. Criterio GO: AVX2 ≥ 2.5x escalar (4 elem / ~1.6x overhead)
5. Criterio NO-GO: < 2x → Confirmar estrategia "Add-Sub Only"
```

#### Justificación

1. **Costo bajo**: 2-4 horas de trabajo
2. **Beneficio alto**: Confirmación empírica antes de invertir semanas
3. **Riesgo eliminado**: No construir sobre supuestos falsos
4. **Flexibilidad**: Resultado informa estrategia óptima

#### Consecuencias

- **Si pasa (≥2.5x)**: Proceder con mul AVX2 en NTT
- **Si falla (<2x)**: Confirmar estrategia "Add-Sub Only", ahorrar tiempo

---

### ADR-6B-006: Scalar Loop Unrolling Antes de SIMD

**Estado**: APROBADA (2026-01-29)
**Decisores**: Equipo de desarrollo + Revisión QA #2

#### Contexto

El plan original saltaba directamente de twiddle caching a AVX2, ignorando
optimizaciones escalares de bajo riesgo.

#### Problema Identificado (Blind Spot)

1. **ILP (Instruction Level Parallelism)** no estaba contemplado
2. Loop unrolling puede dar **10-15% de speedup** sin complejidad SIMD
3. Es más seguro y debería hacerse PRIMERO
4. CPUs modernas con ejecución Out-of-Order se benefician enormemente

#### Decisión

**Nueva subtarea 6B.1.6: Scalar Loop Unrolling**

```c
// ANTES: 1 butterfly por iteración
for (size_t j = 0; j < half_m; j++) {
    lazy_butterfly(&work[idx_a], &work[idx_b], tw);
    tw = goldilocks_mul(tw, omega_m);
}

// DESPUÉS: 4 butterflies por iteración (unroll x4)
for (size_t j = 0; j < half_m; j += 4) {
    goldilocks_t tw0 = tw;
    goldilocks_t tw1 = goldilocks_mul(tw0, omega_m);
    goldilocks_t tw2 = goldilocks_mul(tw1, omega_m);
    goldilocks_t tw3 = goldilocks_mul(tw2, omega_m);

    lazy_butterfly(&work[k+j+0], &work[k+j+0+half_m], tw0);
    lazy_butterfly(&work[k+j+1], &work[k+j+1+half_m], tw1);
    lazy_butterfly(&work[k+j+2], &work[k+j+2+half_m], tw2);
    lazy_butterfly(&work[k+j+3], &work[k+j+3+half_m], tw3);

    tw = goldilocks_mul(tw3, omega_m);
}
// + manejo de remainder si half_m % 4 != 0
```

#### Justificación

1. **Bajo riesgo**: No introduce complejidad de SIMD
2. **Alto beneficio**: +10-15% estimado
3. **ILP**: CPU puede ejecutar múltiples butterflies en paralelo
4. **Reduce overhead**: Menos branches, menos incrementos de contador
5. **Fundamento para SIMD**: El mismo patrón se aplica después a AVX2

#### Consecuencias

- **Positivas**: Speedup "gratis" antes de SIMD
- **Negativas**: Código más largo (pero más rápido)
- **Orden de ejecución**: ANTES de AVX2, DESPUÉS de twiddle caching

---

### ADR-6B-007: Metodología de Benchmark - Wall Clock Time

**Estado**: APROBADA (2026-01-29)
**Decisores**: Equipo de desarrollo + Revisión QA #2

#### Contexto

El plan original mencionaba medir con `turbostat` pero no enfatizaba medir
**wall clock time real** además de ciclos/frecuencia.

#### Problema

AVX2 intensivo puede causar **frequency throttling** en CPUs Intel. Si solo
medimos ciclos, podríamos no detectar que el throttling se come la ganancia.

#### Decisión

**Medir AMBOS: wall clock + frecuencia**

```bash
# Wall clock real (lo que importa al usuario)
time ./benchmark

# Frecuencia durante ejecución (diagnóstico)
sudo turbostat --show Avg_MHz,Busy%,Bzy_MHz ./benchmark

# Métrica de éxito: Wall clock time, NO ciclos
```

#### Consecuencias

- **Positivas**: Detectamos throttling que afecta rendimiento real
- **Negativas**: Requiere permisos root para turbostat (opcional)

---

### Resumen de Decisiones

| ADR | Decisión | Impacto en Rendimiento |
|-----|----------|------------------------|
| 001 | Híbrido: mul escalar, resto AVX2 | -5% vs full SIMD (evita regression) |
| 002 | Twiddle cache parcial (16KB) | +25% (igual que full para N grande) |
| 003 | vmovdqu para C, align(32) para Rust | -5% en C API |
| 004 | Mitigaciones para R6-R10 | Prevención de failures |
| **005** | **Fail-Fast Microbenchmark** | **Validación antes de invertir** |
| **006** | **Scalar Loop Unrolling** | **+10-15% adicional** |
| **007** | **Wall clock time** | **Detectar throttling** |

**Estimación de rendimiento REVISADA**: 78-88% de Plonky3 (meta: ≥80%)

---

## Estado Actual del CodeGen

### Lo que YA existe

| Componente | Estado | Archivos |
|------------|--------|----------|
| CodeGen C escalar | ✅ Completo | `AmoLean/CodeGen.lean` |
| NTT skeleton + kernel | ✅ Verificado | `generated/ntt_skeleton.c`, `ntt_kernel.h` |
| Lazy butterfly | ✅ Probado (~3x speedup) | `AmoLean/NTT/LazyButterfly.lean` |
| Field Goldilocks | ✅ Completo | `generated/field_goldilocks.h` |
| FRI CodeGen | ✅ Fase 7-Alpha | `AmoLean/FRI/CodeGen.lean` |
| AVX2 field headers | ⚠️ Parcial (stubs) | `generated/field_goldilocks_avx2.h` |
| Backend AVX512 | ❌ Solo placeholder | `AmoLean/Backends/C_AVX512/Basic.lean` |
| Rust bindings | ❌ No existe | - |

### Arquitectura actual

```
Spec Lean → CryptoSigma IR → ExpandedSigma → C Code
                                              └── Solo escalar
```

### Arquitectura objetivo

```
Spec Lean → CryptoSigma IR → ExpandedSigma → Backend Selection
                                              ├── C Escalar
                                              ├── C AVX2 ← NUEVO
                                              ├── C AVX512 ← FUTURO
                                              └── Rust FFI ← NUEVO
```

---

## Subfases Detalladas

### 6B.1: Twiddle Factor Caching INTELIGENTE (Crítico para rendimiento)

**Problema identificado**: AMO-Lean computa twiddles on-the-fly. Plonky3 los pre-computa.

**Impacto**: ~30-40% del gap de rendimiento.

**⚠️ ALERTA QA**: Cachear TODO puede causar cache thrashing para N grande.

**Solución**: Cache parcial + compute on-the-fly para capas grandes.

```c
// Estrategia: Cache inteligente por capas
//
// Para NTT de N elementos, hay log2(N) capas.
// Capas tempranas: Acceso secuencial, muchos elementos → CACHEAR
// Capas tardías: Acceso con stride grande, pocos accesos → COMPUTAR
//
// Ejemplo N=2^18 (262,144 elementos):
// - Capas 0-10: 2048 twiddles = 16KB → Cabe en L1 (32KB típico)
// - Capas 11-17: Computar on-the-fly (pocos accesos, stride grande)

typedef struct {
    size_t log_n;
    size_t cached_layers;       // Número de capas cacheadas
    goldilocks_t* twiddles;     // Solo twiddles para capas cacheadas
    goldilocks_t omega;         // ω primitivo para computar resto
    goldilocks_t omega_inv;     // ω^(-1) para NTT inversa
    goldilocks_t n_inv;         // 1/N para normalización
} NttContext;

// Heurística de capas a cachear:
// cached_layers = min(log_n, 10 + log2(L1_CACHE_SIZE / 8))
// Esto asegura que twiddles caben en L1

// API
NttContext* ntt_context_create(size_t log_n);
void ntt_context_destroy(NttContext* ctx);
void ntt_forward_cached(NttContext* ctx, goldilocks_t* data);
void ntt_inverse_cached(NttContext* ctx, goldilocks_t* data);
```

**Tareas**:
- [x] 6B.1.1: Diseñar estructura `NttContext` con cache parcial
- [x] 6B.1.2: Implementar heurística de selección de capas
- [ ] 6B.1.3: Generar código híbrido (cache + on-the-fly)
- [ ] 6B.1.4: Benchmark por tamaño (N=256 hasta N=2^18)
- [ ] 6B.1.5: Tests de regresión vs Plonky3
- [ ] 6B.1.7: Validar que no hay cache thrashing (perf stat)

**Obstáculos técnicos**:

| Obstáculo | Riesgo | Mitigación |
|-----------|--------|------------|
| Memory footprint | ~~Medio~~ **BAJO** | Cache parcial, max ~16KB |
| Cache thrashing | ~~N/A~~ **MITIGADO** | Heurística de capas |
| Thread safety | Bajo | Contextos inmutables post-init |
| Overhead de branch | Bajo | Branch predictor maneja bien el patrón |

**Entregable**: `generated/ntt_cached.c` + `ntt_context.h`

---

### 6B.1.6: Scalar Loop Unrolling (NUEVO - ADR-6B-006)

**Problema**: El loop interno de NTT procesa 1 butterfly por iteración,
desperdiciando ILP (Instruction Level Parallelism).

**Solución**: Unroll x4 para permitir ejecución paralela en CPUs OoO.

```c
// ANTES: 1 butterfly por iteración (baja ILP)
for (size_t j = 0; j < half_m; j++) {
    lazy_butterfly(&work[idx_a], &work[idx_b], tw);
    tw = goldilocks_mul(tw, omega_m);
}

// DESPUÉS: 4 butterflies por iteración (alta ILP)
size_t j = 0;
for (; j + 4 <= half_m; j += 4) {
    // Pre-compute 4 twiddles
    goldilocks_t tw0 = tw;
    goldilocks_t tw1 = goldilocks_mul(tw0, omega_m);
    goldilocks_t tw2 = goldilocks_mul(tw1, omega_m);
    goldilocks_t tw3 = goldilocks_mul(tw2, omega_m);

    // 4 butterflies - CPU puede ejecutar en paralelo
    lazy_butterfly(&work[k+j+0], &work[k+j+0+half_m], tw0);
    lazy_butterfly(&work[k+j+1], &work[k+j+1+half_m], tw1);
    lazy_butterfly(&work[k+j+2], &work[k+j+2+half_m], tw2);
    lazy_butterfly(&work[k+j+3], &work[k+j+3+half_m], tw3);

    tw = goldilocks_mul(tw3, omega_m);
}
// Remainder loop for half_m % 4 != 0
for (; j < half_m; j++) {
    lazy_butterfly(&work[k+j], &work[k+j+half_m], tw);
    tw = goldilocks_mul(tw, omega_m);
}
```

**Tareas**:
- [ ] 6B.1.6.1: Implementar loop unrolling x4 en ntt_cached.c
- [ ] 6B.1.6.2: Manejar remainder (half_m % 4 != 0)
- [ ] 6B.1.6.3: Benchmark vs versión sin unroll
- [ ] 6B.1.6.4: Probar unroll x2 y x8 para comparar

**Estimación**: +10-15% speedup con bajo riesgo

**Entregable**: `generated/ntt_cached.c` actualizado con loop unrolling

---

### 6B.2.0: Fail-Fast Microbenchmark (NUEVO - ADR-6B-005)

**Objetivo**: Validar empíricamente si AVX2 mul vale la pena ANTES de invertir
tiempo en implementación completa.

**Procedimiento**:

```bash
# Día 1 de 6B.2 (2-4 horas máximo)

1. Implementar goldilocks_mul_scalar() - baseline
2. Implementar goldilocks_mul_avx2()   - emulación 4-way
3. Benchmark: 100M operaciones cada una
4. Comparar throughput (ops/segundo)
```

**Criterios de decisión**:

| Resultado | Ratio AVX2/Escalar | Acción |
|-----------|-------------------|--------|
| **GO** | ≥ 2.5x | Proceder con mul AVX2 en NTT |
| **BORDERLINE** | 1.5x - 2.5x | Evaluar caso por caso |
| **NO-GO** | < 1.5x | Confirmar "Add-Sub Only", ahorrar tiempo |

**Tareas**:
- [ ] 6B.2.0.1: Implementar goldilocks_mul_avx2() aislada
- [ ] 6B.2.0.2: Crear microbenchmark (100M ops)
- [ ] 6B.2.0.3: Ejecutar y documentar resultados
- [ ] 6B.2.0.4: Decidir GO/NO-GO basado en datos

**Entregable**: `Tests/Plonky3/Bench/mul_avx2_microbench.c` + decisión documentada

---

### 6B.2: Estrategia Híbrida AVX2 (REVISADA tras análisis QA)

**⚠️ CRÍTICA INCORPORADA**: El QA Senior identificó correctamente que emular
multiplicación 64×64 en AVX2 puede ser CONTRAPRODUCENTE.

**Evidencia de Plonky3** (goldilocks/src/x86_64_avx2/packing.rs:347):
```rust
/// Full 64-bit by 64-bit multiplication. This emulated multiplication is
/// 1.33x SLOWER than the scalar instruction, but may be worth it if we
/// want our data to live in vector registers.
```

**Conclusión**: NO vectorizar multiplicación. SÍ vectorizar add/sub/square/interleave.

---

#### Estrategia Híbrida "Goldilocks-Aware"

```
┌─────────────────────────────────────────────────────────────┐
│  OPERACIÓN        │  ESTRATEGIA       │  JUSTIFICACIÓN      │
├───────────────────┼───────────────────┼─────────────────────┤
│  mul(a, b)        │  ESCALAR          │  mulx nativo rápido │
│  square(a)        │  AVX2 (opcional)  │  1.2x más rápido    │
│  add(a, b)        │  AVX2             │  Trivial vectorizar │
│  sub(a, b)        │  AVX2             │  Trivial vectorizar │
│  reduce128        │  AVX2             │  Usa ε = 2^32-1     │
│  load/store x4    │  AVX2             │  Menos instrucciones│
│  interleave       │  AVX2             │  Para butterflies   │
└─────────────────────────────────────────────────────────────┘
```

**Implementación inspirada en Plonky3**:

```c
// field_goldilocks_hybrid.h

// Constantes AVX2
static const __m256i SIGN_BIT = _mm256_set1_epi64x(0x8000000000000000ULL);
static const __m256i EPSILON  = _mm256_set1_epi64x(0xFFFFFFFF00000000ULL); // -p mod 2^64

// Add: Vectorizado (de Plonky3)
static inline __m256i avx2_goldilocks_add(__m256i x, __m256i y) {
    __m256i y_s = _mm256_xor_si256(y, SIGN_BIT);  // shift for unsigned compare
    // ... canonicalize y_s ...
    __m256i res_s = add_no_double_overflow(x, y_s);
    return _mm256_xor_si256(res_s, SIGN_BIT);
}

// Sub: Vectorizado (de Plonky3)
static inline __m256i avx2_goldilocks_sub(__m256i x, __m256i y) {
    // Similar con detección de underflow
}

// Mul: ESCALAR (mantener datos en registros pero usar mul nativo)
// Opción A: Extraer elementos, mul escalar, re-empaquetar
// Opción B: Usar Plonky3's mul64_64 si datos ya están en vector
static inline __m256i avx2_goldilocks_mul(__m256i x, __m256i y) {
    // Para NTT butterfly, los datos ya están en vectores.
    // Extraer → mul escalar → reempaquetar tiene overhead.
    // Decisión: Usar mul64_64 de Plonky3 (1.33x más lento pero
    // evita extract/insert que cuestan ~3 ciclos cada uno).
    return reduce128(mul64_64(x, y));
}

// Square: AVX2 (Plonky3 muestra 1.2x speedup)
static inline __m256i avx2_goldilocks_square(__m256i x) {
    return reduce128(square64(x)); // Solo 3 muls, no 4
}
```

**Tareas REVISADAS**:
- [ ] 6B.2.1: Portar `add/sub/neg` de Plonky3 a C
- [ ] 6B.2.2: Portar `reduce128` de Plonky3 a C
- [ ] 6B.2.3: Portar `square64` de Plonky3 a C
- [ ] 6B.2.4: Decidir si usar `mul64_64` o escalar (benchmark)
- [ ] 6B.2.5: Implementar `shift` trick para comparaciones unsigned
- [ ] 6B.2.6: Tests exhaustivos: AVX2 vs escalar para 10M valores aleatorios
- [ ] 6B.2.7: Benchmark: medir speedup real (target revisado: +20-30%)

**Obstáculos técnicos ACTUALIZADOS**:

| Obstáculo | Riesgo | Mitigación |
|-----------|--------|------------|
| ~~Carry propagation~~ | ~~ALTO~~ | Usar código de Plonky3 (probado) |
| Extract/insert overhead | Medio | Mantener datos en vectores, evitar escalar |
| Comparaciones unsigned | Medio | Shift trick (XOR con SIGN_BIT) |
| Alineación memoria | **ALTO** | Ver sección 6B.2.A abajo |
| Correctitud | Medio | Oracle testing extensivo |

---

#### 6B.2.A: Manejo de Alineación de Memoria (NUEVO)

**⚠️ CRÍTICA QA**: `vmovdqa` requiere alineación a 32 bytes. Sin esto → SIGSEGV.

**Soluciones**:

```c
// Opción 1: Requerir alineación en API (breaking change)
void ntt_forward_aligned(NttContext* ctx, goldilocks_t* data);  // data debe ser aligned

// Opción 2: Usar instrucciones unaligned (más seguro, ~5% más lento)
__m256i vec = _mm256_loadu_si256((__m256i*)ptr);  // 'u' = unaligned
_mm256_storeu_si256((__m256i*)ptr, vec);

// Opción 3: Alineación interna (recomendada)
void ntt_forward(NttContext* ctx, goldilocks_t* data) {
    // Copiar a buffer interno alineado si es necesario
    goldilocks_t* aligned_data;
    if ((uintptr_t)data % 32 != 0) {
        aligned_data = aligned_alloc(32, n * sizeof(goldilocks_t));
        memcpy(aligned_data, data, n * sizeof(goldilocks_t));
    } else {
        aligned_data = data;
    }
    // ... NTT en aligned_data ...
    if (aligned_data != data) {
        memcpy(data, aligned_data, n * sizeof(goldilocks_t));
        free(aligned_data);
    }
}

// Opción 4: Rust se encarga (preferida para amolean-ntt crate)
#[repr(C, align(32))]
pub struct AlignedBuffer([Goldilocks; N]);
```

**Decisión**: Opción 2 (unaligned) para C API, Opción 4 para Rust crate.

**Entregable**: `generated/field_goldilocks_avx2.h` (híbrido)

---

### 6B.3: AVX2 NTT Butterfly

**Prerequisito**: 6B.2 completado.

**Problema**: El butterfly actual es escalar. Necesitamos procesar 4 elementos en paralelo.

**Solución**: Butterfly vectorizado.

```c
// Procesa 4 butterflies en paralelo
static inline void avx2_butterfly_x4(
    __m256i* a,      // 4 valores "a"
    __m256i* b,      // 4 valores "b"
    __m256i twiddle  // 4 twiddles (pueden ser iguales o diferentes)
) {
    __m256i tb = avx2_goldilocks_mul(*b, twiddle);
    __m256i new_a = avx2_goldilocks_add(*a, tb);
    __m256i new_b = avx2_goldilocks_sub(*a, tb);
    *a = new_a;
    *b = new_b;
}
```

**Tareas**:
- [ ] 6B.3.1: Implementar `avx2_butterfly_x4`
- [ ] 6B.3.2: Adaptar loop structure para SIMD (stride patterns)
- [ ] 6B.3.3: Manejar casos donde N < 4 (fallback escalar)
- [ ] 6B.3.4: Verificar vs NTT escalar (oracle testing)
- [ ] 6B.3.5: Integrar con twiddle caching (6B.1)
- [ ] 6B.3.6: Benchmark (target: 2x speedup adicional)

**Obstáculos técnicos**:

| Obstáculo | Riesgo | Mitigación |
|-----------|--------|------------|
| Memory alignment | Medio | `aligned_alloc(32, ...)` obligatorio |
| Stride patterns | Medio | Diferentes estrategias por layer |
| Remainder handling | Bajo | Fallback escalar para últimos elementos |
| Twiddle layout | Medio | Pre-ordenar twiddles para acceso SIMD |

**Entregable**: `generated/ntt_avx2.c`

---

### 6B.4: Tests de Equivalencia Formal

**Problema**: El código generado debe ser IDÉNTICO en comportamiento a la spec.

**Solución**: Framework de testing multi-nivel.

```
Nivel 1: Oracle Testing (runtime)
├── Comparar C escalar vs Lean eval
├── Comparar C AVX2 vs C escalar
└── Comparar vs Plonky3 (ya hecho en 6A)

Nivel 2: Proof Anchors (compile-time)
├── Verificar precondiciones en comentarios
├── Verificar postcondiciones
└── Auditar invariantes de seguridad

Nivel 3: Equivalencia Formal (Lean)
├── Teorema: ntt_c_scalar = ntt_spec
├── Teorema: ntt_c_avx2 = ntt_c_scalar
└── Composición: ntt_c_avx2 = ntt_spec
```

**Tareas**:
- [ ] 6B.4.1: Extender oracle tests para AVX2
- [ ] 6B.4.2: Crear fuzzer para encontrar divergencias
- [ ] 6B.4.3: Documentar proof anchors en código generado
- [ ] 6B.4.4: (Stretch) Teorema parcial de equivalencia en Lean

**Obstáculos técnicos**:

| Obstáculo | Riesgo | Mitigación |
|-----------|--------|------------|
| Floating point differences | N/A | Todo es entero |
| Undefined behavior en C | Medio | `-fsanitize=undefined` en tests |
| SIMD-specific bugs | Alto | Testing exhaustivo, Valgrind |

**Entregable**: `Tests/NTT/AVX2_Oracle.c`, documentación de equivalencia

---

### 6B.5: Benchmarks vs Plonky3 (ESTIMACIONES REVISADAS)

**Meta**: ≥80% rendimiento de Plonky3.

**Estado actual**: ~50% (2x más lento).

**Roadmap de mejoras REALISTA** (post-análisis QA):

| Optimización | Speedup | Acumulado | Confianza |
|--------------|---------|-----------|-----------|
| Baseline (actual) | 1.0x | 50% | - |
| + Twiddle cache inteligente | +1.25x | 62% | ALTA |
| + AVX2 add/sub/reduce | +1.10x | 68% | ALTA |
| + AVX2 square (no mul) | +1.05x | 72% | MEDIA |
| + AVX2 data movement | +1.08x | 78% | MEDIA |
| + Loop unrolling | +1.05x | 82% | BAJA |

**Nota**: El speedup de AVX2 es MENOR que mi estimación original porque:
1. Multiplicación se mantiene escalar o usa emulación 1.33x más lenta
2. Frequency throttling puede reducir ganancias
3. Alineación de memoria agrega overhead si usamos `vmovdqu`

**Escenario pesimista**: 70% de Plonky3 (sin loop unrolling, throttling)
**Escenario optimista**: 85% de Plonky3 (todo funciona bien)
**Escenario realista**: 75-80% de Plonky3

**Tareas**:
- [ ] 6B.5.1: Establecer benchmark reproducible
- [ ] 6B.5.2: Medir después de cada optimización
- [ ] 6B.5.3: Profiling detallado (perf, VTune)
- [ ] 6B.5.4: Identificar bottlenecks restantes
- [ ] 6B.5.5: Documentar resultados finales

**Obstáculos técnicos**:

| Obstáculo | Riesgo | Mitigación |
|-----------|--------|------------|
| Plonky3 usa AVX-512 | Medio | Comparar en hardware equivalente |
| Measurement noise | Bajo | Múltiples runs, estadísticas |
| Different algorithms | Bajo | Ya verificado en 6A que son equivalentes |

**Entregable**: `docs/benchmarks/PHASE6B_PERFORMANCE.md`

---

### 6B.6: Rust Bindings (`amolean-ntt` crate)

**Objetivo**: Crate Rust publicable que usa el código C generado.

**Arquitectura**:

```
amolean-ntt/
├── Cargo.toml
├── build.rs           # Compila código C, detecta AVX2
├── src/
│   ├── lib.rs         # API pública
│   ├── ffi.rs         # Bindings C
│   ├── goldilocks.rs  # Tipo de campo
│   └── ntt.rs         # NTT wrapper
├── csrc/              # Código C generado (vendored)
│   ├── field_goldilocks.h
│   ├── ntt_cached.c
│   └── ntt_avx2.c
└── tests/
    └── integration.rs
```

**API propuesta**:

```rust
// amolean-ntt/src/lib.rs

/// Goldilocks field element (p = 2^64 - 2^32 + 1)
#[repr(transparent)]
pub struct Goldilocks(pub u64);

/// Pre-computed NTT context for a specific size
pub struct NttContext {
    inner: *mut ffi::NttContext,
}

impl NttContext {
    /// Create context for NTT of size 2^log_n
    pub fn new(log_n: usize) -> Result<Self, Error>;

    /// Forward NTT (in-place)
    pub fn forward(&self, data: &mut [Goldilocks]);

    /// Inverse NTT (in-place, includes 1/n normalization)
    pub fn inverse(&self, data: &mut [Goldilocks]);
}

// Convenience functions
pub fn ntt_forward(data: &mut [Goldilocks]);
pub fn ntt_inverse(data: &mut [Goldilocks]);
```

**Tareas**:
- [ ] 6B.6.1: Crear estructura de crate
- [ ] 6B.6.2: Escribir `build.rs` con detección de features
- [ ] 6B.6.3: Generar bindings FFI con `bindgen` o manual
- [ ] 6B.6.4: Implementar safe wrappers
- [ ] 6B.6.5: Tests de integración
- [ ] 6B.6.6: Documentación y ejemplos
- [ ] 6B.6.7: CI/CD para publicación

**Obstáculos técnicos**:

| Obstáculo | Riesgo | Mitigación |
|-----------|--------|------------|
| Memory safety | Alto | Wrappers seguros, no exponer punteros raw |
| Build complexity | Medio | `cc` crate para compilar C |
| Cross-platform | Medio | Feature flags para AVX2/fallback |
| C ABI stability | Bajo | Definir ABI explícitamente |

**Entregable**: Crate `amolean-ntt` en GitHub, listo para `cargo publish`

---

## Análisis de Riesgos (ACTUALIZADO)

### Riesgos Técnicos Originales + Nuevos

| # | Riesgo | Prob. | Impacto | Mitigación |
|---|--------|-------|---------|------------|
| R1 | ~~AVX2 mul demasiado lento~~ | ~~Media~~ | ~~Alto~~ | **CONFIRMADO**: Usar estrategia híbrida |
| R2 | Bugs sutiles en SIMD | Alta | Medio | Oracle testing exhaustivo |
| R3 | No alcanzar 80% | Media | Medio | Redefinir meta, documentar gap |
| R4 | Rust FFI memory leaks | Baja | Medio | Valgrind, miri testing |
| R5 | Incompatibilidad cross-platform | Media | Bajo | CI en Linux/macOS/Windows |
| **R6** | **Cache thrashing (twiddles)** | **Media** | **Alto** | **Cache parcial por capas** |
| **R7** | **Alineación de memoria** | **Alta** | **Crítico** | **vmovdqu o aligned_alloc** |
| **R8** | **Frequency throttling AVX** | **Media** | **Medio** | **Benchmark con turbostat** |
| **R9** | **Compiler auto-vectorize mal** | **Media** | **Bajo** | **-fno-tree-vectorize** |
| **R10** | **CI/CD sin AVX2** | **Alta** | **Bajo** | **Runtime feature detection** |

### Riesgos Adicionales Identificados

#### R8: CPU Frequency Throttling

**Problema**: Instrucciones AVX2/AVX-512 pesadas causan que la CPU baje su frecuencia
para mantener el TDP (Thermal Design Power).

**Impacto**: Un loop AVX2 puede correr a 2.5 GHz vs 3.5 GHz para código escalar.
Esto puede eliminar la ganancia de SIMD.

**Mitigación**:
```bash
# Medir frecuencia real durante benchmark
sudo turbostat --show Avg_MHz,Busy%,Bzy_MHz ./benchmark

# Si hay throttling significativo:
# - Solo usar AVX2 para N grandes (amortizar overhead de frequency transition)
# - Considerar "AVX2 light" (evitar instrucciones que causan más throttling)
```

#### R9: Compiler Auto-Vectorization Interference

**Problema**: GCC/Clang pueden auto-vectorizar código escalar de forma subóptima,
interfiriendo con nuestros intrinsics manuales.

**Mitigación**:
```bash
# Compilar con auto-vectorización deshabilitada
gcc -O3 -fno-tree-vectorize -mavx2 ntt_avx2.c

# O usar pragmas locales
#pragma GCC optimize("no-tree-vectorize")
void ntt_layer_scalar(...) { ... }
```

#### R10: CI/CD Hardware Constraints

**Problema**: GitHub Actions runners estándar pueden no tener AVX2.

**Mitigación**:
```c
// Runtime feature detection
#include <cpuid.h>

static int has_avx2(void) {
    unsigned int eax, ebx, ecx, edx;
    if (!__get_cpuid(7, &eax, &ebx, &ecx, &edx)) return 0;
    return (ebx & bit_AVX2) != 0;
}

void ntt_forward(NttContext* ctx, goldilocks_t* data) {
    if (has_avx2()) {
        ntt_forward_avx2(ctx, data);
    } else {
        ntt_forward_scalar(ctx, data);
    }
}
```

### Plan de Contingencia

**Si AVX2 mul es demasiado lento (R1)**:
1. Usar solo add/sub vectorizados (más sencillos)
2. Investigar técnicas de Montgomery vectorizado
3. Considerar AVX-512 como target principal (tiene `_mm512_mullox_epi64`)

**Si no alcanzamos 80% (R3)**:
1. Documentar optimizaciones intentadas
2. Publicar con rendimiento actual + roadmap
3. Investigar otras fuentes de overhead

---

## Dependencias Externas

| Dependencia | Propósito | Riesgo |
|-------------|-----------|--------|
| Plonky3 (referencia) | Benchmark comparativo | Bajo (ya integrado) |
| `cc` crate | Compilar C desde Rust | Bajo (estable) |
| `bindgen` (opcional) | Generar FFI bindings | Bajo |
| AVX2 hardware | Testing SIMD | Medio (no todos tienen) |

---

## Cronograma Propuesto

```
Semana 1-2: 6B.1 Twiddle Caching
├── Diseño e implementación
├── Benchmark inicial
└── CHECKPOINT: ¿+25% speedup?

Semana 3-4: 6B.2 AVX2 Field Arithmetic
├── Prototipo mul/add/sub
├── Verificación exhaustiva
└── CHECKPOINT: ¿Correctitud 100%?

Semana 5: 6B.3 AVX2 NTT Butterfly
├── Integración con twiddle cache
├── Loop restructuring
└── CHECKPOINT: ¿+50% speedup total?

Semana 6: 6B.4 Tests de Equivalencia
├── Oracle tests AVX2
├── Fuzzing
└── CHECKPOINT: ¿0 divergencias?

Semana 7: 6B.5 Benchmarks Finales
├── Comparación vs Plonky3
├── Profiling y ajustes
└── CHECKPOINT: ¿≥80% de Plonky3?

Semana 8-9: 6B.6 Rust Crate
├── Estructura y FFI
├── Safe wrappers
├── Documentación
└── CHECKPOINT: ¿Crate funcional?

Semana 10: Pulido y Release
├── CI/CD
├── README y ejemplos
└── RELEASE: v0.7.0-phase6b-generator
```

---

## Checkpoints de Decisión

| Checkpoint | Criterio GO | Criterio NO-GO |
|------------|-------------|----------------|
| CP1 (fin semana 2) | Twiddle cache: +20% speedup | <10% mejora → revisar diseño |
| CP2 (fin semana 4) | AVX2 arith: 100% correctitud | Bugs persistentes → fallback escalar |
| CP3 (fin semana 5) | NTT AVX2: +40% total | <25% → considerar solo caching |
| CP4 (fin semana 7) | ≥70% de Plonky3 | <60% → documentar, ajustar meta |
| CP5 (fin semana 9) | Crate compila y pasa tests | Blocker → delay release |

---

## Métricas de Éxito

| Métrica | Target | Mínimo Aceptable |
|---------|--------|------------------|
| Rendimiento vs Plonky3 | ≥80% | ≥70% |
| Tests de correctitud | 100% pass | 100% pass |
| Cobertura de código | ≥90% | ≥80% |
| Documentación API | Completa | Funciones públicas |
| CI/CD | Linux + macOS | Linux |

---

## Archivos a Crear/Modificar

### Nuevos

```
AmoLean/
└── CodeGen/
    └── AVX2.lean                    # Backend AVX2

generated/
├── ntt_cached.c                     # NTT con twiddle cache
├── ntt_context.h                    # API de contexto
├── ntt_avx2.c                       # NTT vectorizada
└── field_goldilocks_avx2_impl.h     # Aritmética AVX2

amolean-ntt/                         # Nuevo crate
├── Cargo.toml
├── build.rs
├── src/
│   ├── lib.rs
│   ├── ffi.rs
│   ├── goldilocks.rs
│   └── ntt.rs
├── csrc/                            # Código C vendored
└── tests/

Tests/
└── NTT/
    ├── AVX2_Oracle.c
    └── Cached_Oracle.c

docs/
└── benchmarks/
    └── PHASE6B_PERFORMANCE.md
```

### Modificados

```
AmoLean/CodeGen.lean                 # Agregar selección de backend
generated/Makefile                   # Agregar targets AVX2
docs/project/ROADMAP.md              # Actualizar estado
docs/project/PROGRESS.md             # Agregar Phase 6B
```

---

## Notas Finales

### Por qué este orden

1. **Twiddle caching primero**: Mayor impacto, menor riesgo técnico
2. **AVX2 arithmetic después**: Mayor riesgo, pero necesario para SIMD
3. **Tests intercalados**: No acumular deuda de testing
4. **Rust al final**: Depende de código C estable

### Lecciones de Phase 6A

- Oracle testing funcionó excelentemente (120/120 vectores)
- FFI overhead es despreciable (0.03%)
- `panic = "abort"` es crítico para FFI
- Documentar TODO mientras se desarrolla

### Pregunta abierta

¿Priorizar AVX-512 sobre AVX2?
- Pro: `vpmuludq` nativo para 64-bit mul
- Contra: Menos hardware disponible

**Recomendación**: Empezar con AVX2, diseñar para extensibilidad a AVX-512.

---

---

## Apéndice: Revisión QA y Cambios

### Revisión QA Senior (2026-01-29)

El plan original fue revisado por un QA Senior que identificó tres problemas críticos:

#### Crítica 1: "4-way Split" Contraproducente

**Original**: Propuse emular mul 64×64 con 4 multiplicaciones de 32-bit en AVX2.

**Crítica**: "12-15 instrucciones por operación, latencia ~20+ ciclos. El multiplicador
escalar nativo es más rápido."

**Validación**: Confirmado por código de Plonky3 que dice textualmente:
> "This emulated multiplication is 1.33x SLOWER than the scalar instruction"

**Cambio**: Estrategia híbrida - escalar para mul, AVX2 solo para add/sub/square/interleave.

#### Crítica 2: Alineación de Memoria

**Original**: No mencioné requisitos de alineación.

**Crítica**: "`vmovdqa` requiere alineación a 32 bytes. Sin esto → SIGSEGV."

**Cambio**: Agregada sección 6B.2.A con 4 opciones de mitigación. Decisión: usar
`vmovdqu` (unaligned) para C API, `#[repr(align(32))]` para Rust.

#### Crítica 3: Cache Thrashing con Twiddles

**Original**: Propuse cachear todos los twiddles.

**Crítica**: "Para N=2^18, twiddles = 1MB. Sacará datos del usuario de L2/L3."

**Cambio**: Cache parcial por capas. Solo cachear primeras capas (~16KB, cabe en L1).
Computar capas tardías on-the-fly.

### Problemas Adicionales Identificados

Tras la revisión, identifiqué 5 riesgos adicionales no contemplados originalmente:

1. **R6**: Cache thrashing (mitigado con cache parcial)
2. **R7**: Alineación de memoria (mitigado con vmovdqu)
3. **R8**: Frequency throttling AVX (monitorear con turbostat)
4. **R9**: Auto-vectorización del compilador (usar -fno-tree-vectorize)
5. **R10**: CI/CD sin AVX2 (runtime feature detection)

### Lecciones Aprendidas

1. **Verificar supuestos de performance con código real** (ej: leer Plonky3)
2. **Los primos especiales (Goldilocks, Mersenne) tienen trucos específicos** - no usar
   algoritmos genéricos
3. **SIMD no es "siempre más rápido"** - depende de la operación y el hardware
4. **La revisión de pares encuentra bugs en planes, no solo en código**

---

*Documento creado: 2026-01-29*
*Basado en: Exploración de CodeGen existente + resultados Phase 6A*
*Revisado: 2026-01-29 tras análisis QA Senior*
