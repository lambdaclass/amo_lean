# AMO-Lean Phase 3: CodeGen SIMD - Documento de Diseño

**Fecha**: 2026-01-28
**Autor**: Claude (basado en estudio de referencias)

---

## 1. Resumen del Estudio de Referencias

### 1.1 Referencias Estudiadas

| Referencia | Prioridad | Hallazgos Clave |
|------------|-----------|-----------------|
| Intel Intrinsics Guide | ALTA | VPMULUDQ: 5 ciclos latencia (Skylake), 0.5 throughput |
| uops.info | ALTA | AMD Zen 4: 3 ciclos latencia, mejor que Intel |
| Agner Fog | ALTA | Throughput = 1/ciclos por instrucción |
| Plonky2 goldilocks_field.rs | CRÍTICA | Reducción especializada, NO usa SIMD |
| Plonky3 x86_64_avx2/packing.rs | CRÍTICA | **Implementación AVX2 completa** |
| Winterfell f64/mod.rs | MEDIA | Montgomery form, constant-time, NO SIMD |
| Goldilocks Reduction (Remco) | MEDIA | Matemática de la reducción sin multiplicación |

### 1.2 Hallazgo Principal

**Plonky3** contiene la implementación AVX2 de referencia para Goldilocks. La técnica clave es:

```
64-bit × 64-bit = 128-bit  →  reducción a 64-bit
```

Usando **4 multiplicaciones de 32-bit** (`_mm256_mul_epu32`) para emular una multiplicación de 64-bit.

---

## 2. El Problema: AVX2 No Tiene mul64

AVX2 **NO** tiene una instrucción que multiplique 4×64-bit y produzca 4×128-bit.

Solo tiene:
- `_mm256_mul_epu32`: multiplica las mitades **bajas** de 32-bit de cada slot de 64-bit
- Resultado: 4×64-bit (no 128-bit)

### Solución: Descomposición "Escuela Primaria"

```
a = a_hi × 2³² + a_lo
b = b_hi × 2³² + b_lo

a × b = a_hi×b_hi × 2⁶⁴ + (a_hi×b_lo + a_lo×b_hi) × 2³² + a_lo×b_lo
```

Esto requiere **4 multiplicaciones de 32-bit** + shifts + adds.

---

## 3. Algoritmo de Plonky3 (Extraído del Código)

### 3.1 mul64_64: 64×64 → 128-bit (hi, lo)

```rust
fn mul64_64(x: __m256i, y: __m256i) -> (__m256i, __m256i) {
    // Extraer mitades altas (32-bit) usando truco de FP
    let x_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(x)));
    let y_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(y)));

    // 4 multiplicaciones de 32-bit
    let mul_ll = _mm256_mul_epu32(x, y);       // low × low
    let mul_lh = _mm256_mul_epu32(x, y_hi);    // low × high
    let mul_hl = _mm256_mul_epu32(x_hi, y);    // high × low
    let mul_hh = _mm256_mul_epu32(x_hi, y_hi); // high × high

    // Combinar resultados
    let mul_ll_hi = _mm256_srli_epi64::<32>(mul_ll);
    let t0 = _mm256_add_epi64(mul_hl, mul_ll_hi);
    let t0_lo = _mm256_and_si256(t0, EPSILON);
    let t0_hi = _mm256_srli_epi64::<32>(t0);
    let t1 = _mm256_add_epi64(mul_lh, t0_lo);
    let t2 = _mm256_add_epi64(mul_hh, t0_hi);
    let t1_hi = _mm256_srli_epi64::<32>(t1);
    let res_hi = _mm256_add_epi64(t2, t1_hi);

    // Construir resultado de 128-bit
    let t1_lo = _mm256_castps_si256(_mm256_moveldup_ps(_mm256_castsi256_ps(t1)));
    let res_lo = _mm256_blend_epi32::<0xaa>(mul_ll, t1_lo);

    (res_hi, res_lo)
}
```

### 3.2 reduce128: 128-bit → 64-bit (mod p)

```rust
fn reduce128((hi0, lo0): (__m256i, __m256i)) -> __m256i {
    // Usando la identidad: 2^64 ≡ 2^32 - 1 (mod p)
    let lo0_s = shift(lo0);
    let hi_hi0 = _mm256_srli_epi64::<32>(hi0);
    let lo1_s = sub_small_64s_64_s(lo0_s, hi_hi0);
    let t1 = _mm256_mul_epu32(hi0, EPSILON);  // hi_lo × EPSILON
    let lo2_s = add_small_64s_64_s(lo1_s, t1);
    shift(lo2_s)
}
```

---

## 4. Instrucciones AVX2 Clave

| Instrucción | Latencia (SKL) | Throughput | Uso |
|-------------|----------------|------------|-----|
| `_mm256_mul_epu32` | 5 | 0.5 | Multiplicación 32→64 |
| `_mm256_add_epi64` | 1 | 0.33 | Suma 64-bit |
| `_mm256_sub_epi64` | 1 | 0.33 | Resta 64-bit |
| `_mm256_srli_epi64` | 1 | 0.5 | Shift derecha |
| `_mm256_slli_epi64` | 1 | 0.5 | Shift izquierda |
| `_mm256_and_si256` | 1 | 0.33 | AND bit a bit |
| `_mm256_movehdup_ps` | 1 | 1.0 | Extraer hi32 |
| `_mm256_blend_epi32` | 1 | 0.33 | Mezclar elementos |

**Bottleneck**: Las 4 multiplicaciones de 32-bit dominan (5 ciclos × 4 = 20 ciclos, pero pipelining ayuda).

---

## 5. Plan de Implementación para AMO-Lean

### 5.1 Estrategia: Camino B Primero (Autovectorización)

Basado en la recomendación del texto de Phase 3:

1. **Generar C limpio** desde el E-Graph optimizado
2. **Usar `__attribute__((vector_size(32)))`** para tipos vectoriales
3. **Compilar con `clang -O3 -mavx2`**
4. **Si no es suficiente**, bajar a intrínsecos explícitos

### 5.2 Estructura de Archivos

```
generated/
├── field_goldilocks_avx2.h    # Header con vectorización
├── fri_fold_avx2.h            # FRI Fold vectorizado
└── poseidon2_avx2.h           # Poseidon2 vectorizado (futuro)

AmoLean/
├── Vector/
│   └── CodeGenAVX2.lean       # Generador de código AVX2
└── CodeGen/
    └── SIMD.lean              # Abstracciones SIMD
```

### 5.3 Tipos Vectoriales para C

```c
// Tipo vectorial de 4 elementos Goldilocks (256-bit)
typedef uint64_t v4u64 __attribute__((vector_size(32)));
typedef uint32_t v8u32 __attribute__((vector_size(32)));

// Constantes
static const uint64_t GOLDILOCKS_P = 0xFFFFFFFF00000001ULL;
static const uint64_t EPSILON = 0xFFFFFFFFULL;  // 2^32 - 1
```

### 5.4 Fases de Implementación

| Fase | Descripción | Entregable |
|------|-------------|------------|
| 3.1 | Header AVX2 básico | `field_goldilocks_avx2.h` |
| 3.2 | CodeGen Lean → C AVX2 | `CodeGenAVX2.lean` |
| 3.3 | FRI Fold vectorizado | `fri_fold_avx2.h` |
| 3.4 | Benchmark vs escalar | Resultados en `BENCHMARKS.md` |
| 3.5 | Intrínsecos (si necesario) | `field_goldilocks_intrinsics.h` |

---

## 6. Código C Objetivo (Camino B)

```c
#include <stdint.h>

typedef uint64_t v4u64 __attribute__((vector_size(32)));

static const uint64_t GOLDILOCKS_P = 0xFFFFFFFF00000001ULL;
static const uint64_t EPSILON = 0xFFFFFFFFULL;

// Reducción escalar (para referencia)
static inline uint64_t goldilocks_reduce128(unsigned __int128 x) {
    uint64_t x_lo = (uint64_t)x;
    uint64_t x_hi = (uint64_t)(x >> 64);
    uint64_t x_hi_hi = x_hi >> 32;
    uint64_t x_hi_lo = x_hi & EPSILON;

    uint64_t t0 = x_lo - x_hi_hi;
    if (x_lo < x_hi_hi) {
        t0 -= EPSILON;  // Borrow handling
    }

    uint64_t t1 = x_hi_lo * EPSILON;
    uint64_t t2 = t0 + t1;

    // Carry handling
    if (t2 < t0 || t2 >= GOLDILOCKS_P) {
        t2 -= GOLDILOCKS_P;
    }

    return t2;
}

// Multiplicación vectorizada (Clang autovectoriza)
static inline v4u64 goldilocks_mul_vec(v4u64 a, v4u64 b) {
    v4u64 result;
    for (int i = 0; i < 4; i++) {
        unsigned __int128 prod = (unsigned __int128)a[i] * b[i];
        result[i] = goldilocks_reduce128(prod);
    }
    return result;
}

// FRI Fold vectorizado
static inline v4u64 fri_fold_vec(v4u64 even, v4u64 odd, uint64_t alpha) {
    v4u64 alpha_vec = {alpha, alpha, alpha, alpha};
    v4u64 alpha_odd = goldilocks_mul_vec(alpha_vec, odd);
    // Suma vectorial (Clang genera VPADDQ)
    return even + alpha_odd;  // Modular wrap handled by subsequent reduce
}
```

---

## 7. Métricas de Éxito

| Métrica | Objetivo | Justificación |
|---------|----------|---------------|
| Speedup vs escalar | ≥2x | 4 elementos en paralelo |
| Correctness | 100% | Oracle testing contra Lean |
| Código generado | < 500 LOC | Mantenibilidad |
| Compilación | < 5s | CI/CD viable |

---

## 8. Referencias

- [Intel Intrinsics Guide](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html)
- [uops.info](https://uops.info) - VPMULUDQ latencias
- [Agner Fog's Optimization Manuals](https://www.agner.org/optimize/)
- [Plonky3 AVX2 Implementation](https://github.com/Plonky3/Plonky3/blob/main/goldilocks/src/x86_64_avx2/packing.rs)
- [Plonky2 Goldilocks Field](https://github.com/0xPolygonZero/plonky2/blob/main/field/src/goldilocks_field.rs)
- [Winterfell Field Arithmetic](https://github.com/facebook/winterfell/blob/main/math/src/field/f64/mod.rs)
- [Goldilocks Reduction](https://xn--2-umb.com/23/gold-reduce/) - Matemática de reducción

---

*AMO-Lean Phase 3 Design Document*
