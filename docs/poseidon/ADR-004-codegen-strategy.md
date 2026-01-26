# ADR-004: CodeGen Strategy for Poseidon S-box

## Estado
**Aceptado** (26 Enero 2026)

## Contexto

La Fase 2 de Poseidon requiere generar código C/SIMD eficiente para la S-box (x^5).
Una propuesta inicial sugería "Speculative Vectorization with Blending" para AVX2.

### Análisis del Problema

La propuesta inicial asumía que podemos vectorizar operaciones de campo dentro de un solo hash:

```
Estado Poseidon t=3: [s0, s1, s2]
Propuesta: Meter los 3 elementos en un registro YMM y operar en paralelo
```

**Problema fundamental**: El tamaño del campo vs el tamaño del registro SIMD.

| Campo | Bits/elemento | Elementos/YMM (256 bits) | Vectorización intra-hash viable |
|-------|---------------|--------------------------|--------------------------------|
| Goldilocks (2^64 - 2^32 + 1) | 64 | 4 | ✓ Sí |
| Mersenne-31 (2^31 - 1) | 31 | 8 | ✓ Sí |
| **BN254** | **254** | **1** | **✗ No** |

Para BN254 (nuestro target principal):
- Un elemento de campo ≈ 254 bits
- Se representa como 4 × 64-bit limbs = 256 bits
- Un registro AVX2 = 256 bits
- **Resultado**: UN SOLO elemento llena todo el registro

La "vectorización especulativa" propuesta NO APLICA para BN254.

### Opciones Evaluadas

#### Opción A: Ignorar el problema y vectorizar igual
**Rechazada**: Generaría código incorrecto o ineficiente para BN254.

#### Opción B: Solo soportar campos pequeños (Goldilocks)
**Rechazada**: Limita la utilidad del proyecto. BN254 es crítico para zkSNARKs.

#### Opción C: Implementación por capas (ELEGIDA)
Implementar en orden de complejidad creciente:
1. Escalar correcto primero
2. SIMD para campos pequeños después
3. Batch SIMD para campos grandes al final

## Decisión

Adoptamos una estrategia de **CodeGen por capas** con 4 sub-pasos:

```
┌─────────────────────────────────────────────────────────────────┐
│ Paso 2.1: CodeGen Escalar                          [PRIMERO]    │
│ • Corrección antes que optimización                             │
│ • Funciona para CUALQUIER campo                                 │
│ • Differential fuzzing vs Spec.lean                             │
├─────────────────────────────────────────────────────────────────┤
│ Paso 2.2: Pattern Matching en Lowering                          │
│ • Detectar concat(elemwise(split...)) → PartialSbox             │
│ • Mantener arquitectura MatExpr → SigmaExpr → C                 │
│ • No romper capas de abstracción                                │
├─────────────────────────────────────────────────────────────────┤
│ Paso 2.3: SIMD para Goldilocks                     [OPCIONAL]   │
│ • 4 elementos de 64 bits por YMM                                │
│ • Blend para partial rounds                                     │
│ • Prueba de concepto de la estrategia original                  │
├─────────────────────────────────────────────────────────────────┤
│ Paso 2.4: Batch SIMD para BN254                    [FUTURO]     │
│ • Procesar 4 hashes INDEPENDIENTES en paralelo                  │
│ • Requiere API de batch: hash4(in0, in1, in2, in3)              │
│ • La vectorización es entre hashes, no dentro de uno            │
└─────────────────────────────────────────────────────────────────┘
```

### Justificación

1. **Corrección primero**: El código escalar será la referencia para fuzzing
2. **Arquitectura preservada**: El pattern matching va en el lowering, no en CodeGen
3. **Campos pequeños como prueba**: Goldilocks valida la estrategia SIMD
4. **BN254 realista**: Batch processing es la única forma viable de SIMD

## Implementación

### Paso 2.1: CodeGen Escalar

**Objetivo**: Generar código C correcto para `elemwise (pow n) expr`.

**Archivo**: `AmoLean/Sigma/CodeGen.lean` (extender)

**Código generado para x^5**:
```c
// Square chain: x^5 = x * (x^2)^2
// 3 multiplicaciones en lugar de 4
static inline void sbox5(uint64_t *out, const uint64_t *x, const field_params *p) {
    uint64_t x2[4], x4[4];
    field_mul(x2, x, x, p);      // x2 = x * x
    field_mul(x4, x2, x2, p);    // x4 = x2 * x2
    field_mul(out, x, x4, p);    // out = x * x4 = x^5
}
```

**Para estado completo (full round)**:
```c
void sbox5_state(state_t *s, const field_params *p) {
    sbox5(&s->elem[0], &s->elem[0], p);
    sbox5(&s->elem[1], &s->elem[1], p);
    sbox5(&s->elem[2], &s->elem[2], p);
}
```

**Para partial round**:
```c
void sbox5_partial(state_t *s, const field_params *p) {
    sbox5(&s->elem[0], &s->elem[0], p);  // Solo el primer elemento
}
```

### Paso 2.2: Pattern Matching en Lowering

**Objetivo**: Detectar el patrón de partial round en MatExpr y generar código optimizado.

**Patrón a detectar**:
```lean
-- concat (elemwise op (head state)) (tail state)
-- Significa: aplicar op solo al primer elemento
```

**Transformación**:
```
MatExpr:  concat (elemwise (pow 5) (head s)) (tail s)
     ↓ pattern match en lowering
SigmaExpr: PartialSbox { op = pow 5, index = 0, state = s }
     ↓ codegen
C code:   sbox5_partial(&state, &params);
```

**Archivo**: `AmoLean/Sigma/Basic.lean` (extender lowering)

### Paso 2.3: SIMD para Goldilocks (Opcional)

**Objetivo**: Implementar la estrategia de "speculative vectorization" para campos de 64 bits.

**Precondición**: Campo con elementos de 64 bits (4 caben en YMM).

**Código generado**:
```c
// Para Goldilocks: 4 elementos por registro
void sbox5_simd_goldilocks(__m256i *state) {
    __m256i x = *state;
    __m256i x2 = field_mul_avx2(x, x);
    __m256i x4 = field_mul_avx2(x2, x2);
    __m256i x5 = field_mul_avx2(x, x4);
    *state = x5;
}

// Partial round con blend
void sbox5_partial_simd(__m256i *state) {
    __m256i x5_all = sbox5_simd_goldilocks_pure(*state);
    // Blend: solo el primer elemento de 64 bits
    *state = _mm256_blend_epi64(x5_all, *state, 0b1110);
}
```

### Paso 2.4: Batch SIMD para BN254 (Futuro)

**Objetivo**: Vectorizar procesando múltiples hashes independientes.

**API de batch**:
```c
// Procesar 4 hashes en paralelo
void poseidon2_hash_batch4(
    uint64_t out[4][4],      // 4 outputs de 256 bits cada uno
    const uint64_t in[4][4], // 4 inputs
    const poseidon_params *p
);
```

**Estructura interna**:
```
Registro YMM0: [hash0.limb0 | hash1.limb0 | hash2.limb0 | hash3.limb0]
Registro YMM1: [hash0.limb1 | hash1.limb1 | hash2.limb1 | hash3.limb1]
Registro YMM2: [hash0.limb2 | hash1.limb2 | hash2.limb2 | hash3.limb2]
Registro YMM3: [hash0.limb3 | hash1.limb3 | hash2.limb3 | hash3.limb3]
```

La aritmética Montgomery se vectoriza sobre los 4 hashes simultáneos.

## Consecuencias

### Positivas

1. **Código siempre correcto**: El escalar es la baseline verificada
2. **Arquitectura limpia**: Cada capa tiene responsabilidad clara
3. **Incremental**: Podemos entregar valor en cada paso
4. **Campos flexibles**: Soportamos tanto BN254 como Goldilocks

### Negativas

1. **Más trabajo inicial**: El escalar "no optimizado" se implementa primero
2. **Batch API compleja**: Requiere cambios en la interfaz pública para BN254 SIMD
3. **Dos caminos de código**: SIMD intra-hash (Goldilocks) vs inter-hash (BN254)

### Riesgos Mitigados

| Riesgo Original | Mitigación |
|-----------------|------------|
| Código SIMD incorrecto para BN254 | Escalar como referencia + fuzzing |
| Romper arquitectura de capas | Pattern matching en lowering, no en CodeGen |
| Optimización prematura | Corrección primero, optimización después |

## Referencias

- [ADR-001-elemwise.md](ADR-001-elemwise.md) - Extensión del IR
- [ADR-003-codegen-simd.md](ADR-003-codegen-simd.md) - Estrategia SIMD original (superseded)
- SPIRAL papers sobre vectorización de DSP
- Montgomery multiplication para campos grandes

---

*Fecha*: 26 Enero 2026
*Autores*: Equipo AMO-Lean
*Supersedes*: ADR-003-codegen-simd.md (parcialmente)
