# ADR-003: Estrategia SIMD para S-box y Rondas Parciales

## Estado
Aceptado

## Contexto

La S-box de Poseidon (`x^5`) debe ejecutarse eficientemente en:
1. **Full rounds**: Aplicar a todos los elementos (paralelizable)
2. **Partial rounds**: Aplicar solo al elemento 0 (aparentemente secuencial)

El desafío es generar código SIMD (AVX2/AVX-512) eficiente para ambos casos.

## Decisión

### S-box Escalar: Square Chain (3 multiplicaciones)

```c
static inline uint64_t sbox(uint64_t x) {
    uint64_t x2 = field_mul(x, x);    // x^2
    uint64_t x4 = field_mul(x2, x2);  // x^4
    return field_mul(x, x4);          // x^5
}
```

**Justificación**:
- Naive (`x*x*x*x*x`) requiere 4 multiplicaciones
- Square chain requiere 3 multiplicaciones
- Ahorro del 25% en operación más costosa

### S-box SIMD: Vectorización Paralela

```c
static inline __m256i sbox_avx2(__m256i x) {
    __m256i x2 = field_mul_avx2(x, x);
    __m256i x4 = field_mul_avx2(x2, x2);
    return field_mul_avx2(x, x4);
}
```

Procesa 4 elementos uint64 en paralelo (AVX2) o 8 elementos (AVX-512).

### Rondas Parciales: Blend en lugar de Extract

**Estrategia contraintuitiva**: Calcular S-box para TODOS los elementos, luego usar blend para mezclar solo el resultado del elemento 0.

```c
void partial_round_avx2(__m256i* state, const __m256i* rc, const Matrix* mds) {
    // 1. Sumar round constants
    *state = field_add_avx2(*state, *rc);

    // 2. Calcular S-box para TODOS (3 muls SIMD)
    __m256i sbox_all = sbox_avx2(*state);

    // 3. Blend: tomar solo posición 0 de sbox_all, resto de state
    *state = _mm256_blend_epi64(*state, sbox_all, 0b0001);

    // 4. Multiplicar por MDS
    *state = mds_multiply_avx2(mds, *state);
}
```

**Por qué esto es mejor que extraer el escalar**:

| Operación | Latencia (cycles) |
|-----------|-------------------|
| `_mm256_extract_epi64` | 3 |
| Mover a GPR | 1 |
| 3× `field_mul` escalar | 3×4 = 12 |
| Mover a YMM | 1 |
| `_mm256_insert_epi64` | 3 |
| **Total Extract/Insert** | **20 cycles** |

| Operación | Latencia (cycles) |
|-----------|-------------------|
| 3× `field_mul_avx2` | 3×4 = 12 |
| `_mm256_blend_epi64` | 1 |
| **Total Blend** | **13 cycles** |

El "desperdicio" de calcular S-box para elementos 1-3 es menor que el costo de mover datos entre registros SIMD y GPR.

## Alternativas Consideradas

### Alternativa A: Extract/Insert escalar

```c
uint64_t s0 = _mm256_extract_epi64(state, 0);
s0 = sbox(s0);
state = _mm256_insert_epi64(state, s0, 0);
```

**Rechazada**: Latencia mayor debido a movimiento entre bancos de registros.

### Alternativa B: Máscara de operación

Usar instrucciones AVX-512 con máscara nativa:

```c
state = _mm512_mask_mov_epi64(state, 0b00000001, sbox_all);
```

**Aceptada como mejora futura** para AVX-512, pero el blend de AVX2 es suficiente para la implementación inicial.

## Consecuencias

### Positivas

1. **Performance óptima**: Evita penalty de movimiento SIMD↔GPR.

2. **Código uniforme**: Full rounds y partial rounds usan la misma `sbox_avx2`, simplificando CodeGen.

3. **Escalable a AVX-512**: El patrón se traduce directamente a instrucciones con máscara.

### Negativas

1. **Trabajo "desperdiciado"**: Se calculan S-boxes que no se usan. Esto es aceptable porque el trabajo es barato comparado con el movimiento de datos.

## Optimizaciones Adicionales

### Lazy Reduction para Montgomery

En campos como Goldilocks, la reducción Montgomery después de cada multiplicación es costosa. Optimización:

```c
// En lugar de reducir después de cada mul:
// x2 = reduce(x * x)
// x4 = reduce(x2 * x2)
// x5 = reduce(x * x4)

// Usar representación redundante y reducir solo al final:
x2_unreduced = mul_no_reduce(x, x);
x4_unreduced = mul_no_reduce(x2_unreduced, x2_unreduced);
x5 = mul_and_reduce(x, x4_unreduced);
```

Esto reduce 3 reducciones a 1 por S-box.

### Unrolling de Rondas

Para Poseidon2 con parámetros fijos (RF=8, RP=56), el CodeGen puede unrollear completamente:

```c
// Generado automáticamente para BN254, t=3
void poseidon2_permutation(uint64_t state[3]) {
    // 4 full rounds (unrolled)
    FULL_ROUND(state, rc_ext_0, mds_ext);
    FULL_ROUND(state, rc_ext_1, mds_ext);
    FULL_ROUND(state, rc_ext_2, mds_ext);
    FULL_ROUND(state, rc_ext_3, mds_ext);

    // 56 partial rounds (unrolled)
    PARTIAL_ROUND(state, rc_int_0, mds_int);
    PARTIAL_ROUND(state, rc_int_1, mds_int);
    // ... 54 más ...

    // 4 full rounds finales (unrolled)
    FULL_ROUND(state, rc_ext_4, mds_ext);
    // ...
}
```

El unrolling elimina overhead de loops y permite al compilador optimizar mejor.

## Notas de Implementación

1. **Detección de patrón en CodeGen**: Reconocer `concat(elemwise(pow 5, split(x,1).0), split(x,1).1)` y emitir blend.

2. **field_mul_avx2**: Debe estar implementado en ZModSIMD (Fase 5.9). Verificar que es correcto para el campo target.

3. **Alineación**: Asegurar que los vectores de estado están alineados a 32 bytes (AVX2) o 64 bytes (AVX-512).

---

*Fecha*: Enero 2026
*Autores*: Equipo AMO-Lean
