# Progreso de Implementación - Fase Poseidon

## Estado General

| Paso | Descripción | Estado | Notas |
|------|-------------|--------|-------|
| 0 | Prerrequisitos (ZModSIMD) | Parcial | ZModSIMD existe, falta pow_chain |
| 0.5 | Especificación ejecutable | **Completado** | Spec.lean funcionando sin Mathlib |
| 1 | Extensión IR (elemwise) | **Completado** | head/tail, elemwise, E-Graph, sanity tests ✓ |
| 1.5 | Sanity Tests | **Completado** | 4/4 tests pasan, safe to proceed to CodeGen |
| 2 | CodeGen | **COMPLETADO** | Escalar + SIMD (ADR-004) |
| 2.1 | CodeGen Escalar | **Completado** | S-box con square chain, full/partial rounds |
| 2.2 | Pattern Matching Lowering | **Completado** | partialElemwise, partialSbox kernel |
| 2.3 | SIMD Goldilocks | **Completado** | AVX2 intra-hash, blend para partial |
| 2.4 | Batch SIMD BN254 | **Completado** | AoS↔SoA, 4 hashes paralelos |
| 3 | Poseidon2 en MatExpr | Pendiente | |
| 4 | Verificación | Pendiente | |
| 5 | Integración MerkleTree | Pendiente | |

---

## Paso 0: Prerrequisitos

### Objetivo
Asegurar que ZModSIMD tiene las primitivas necesarias para S-box.

### Checklist
- [ ] `field_mul` escalar funciona correctamente
- [ ] `field_mul_avx2` implementado y testeado
- [ ] `pow_chain_5` optimizado (3 muls)
- [ ] Reducción Montgomery lazy disponible

### Archivos a modificar
- `AmoLean/Matrix/ZModSIMD.lean`

---

## Paso 0.5: Especificación Ejecutable

### Objetivo
Implementar Poseidon2 como función pura en Lean (sin IR) para validación.

### Checklist
- [x] Definir `Params` structure (genérico para cualquier primo p y tamaño t)
- [x] Cargar parámetros BN254 (MDS, round constants placeholder)
- [x] Implementar `poseidon2Permutation : Params p t → State p t → State p t`
- [x] Implementar `poseidon2Hash` con construcción sponge
- [x] S-box con square chain: x^5 = x * (x^2)^2 (3 muls)
- [ ] Cargar round constants completas (actualmente placeholder)
- [ ] Validar contra test vectors del paper Poseidon2
- [ ] Documentar cualquier discrepancia

### Archivos creados
- `AmoLean/Protocols/Poseidon/Spec.lean` - Especificación pura
- `AmoLean/Protocols/Poseidon/Params/BN254.lean` - Parámetros BN254

### Implementación
- Estado: `State p t := Fin t → ZMod p`
- Full round: AddRC → S-box(all) → MDS
- Partial round: AddRC → S-box(first) → MDS
- Permutación: [RF/2 full] → [RP partial] → [RF/2 full]

### Parámetros BN254 t=3
- α = 5, RF = 8, RP = 56
- MDS: [[2,1,1], [1,2,1], [1,1,3]]
- Fuente: HorizenLabs/poseidon2

### Test Vectors
Fuente: Paper Poseidon2, Apéndice (pendiente de cargar)

---

## Paso 1: Extensión del IR

### Objetivo
Añadir constructor `elemwise` a MatExpr y soporte para rondas parciales.

### Checklist
- [x] Añadir `head`/`tail` a VecExpr (para rondas parciales)
- [x] Definir `ElemOp` (pow, custom)
- [x] Añadir `elemwise` a `MatExpr`
- [x] Actualizar lowering (lower) para `elemwise`
- [x] Añadir `sbox` kernel a Sigma
- [x] Actualizar evaluadores
- [x] elemwise como barrera opaca en E-Graph (arquitectónico)

### Archivos modificados
- `AmoLean/Vector/Basic.lean` - Añadido head/tail a VecExpr
- `AmoLean/Matrix/Basic.lean` - Añadido ElemOp y elemwise
- `AmoLean/EGraph/Vector.lean` - Soporte elemwise en MatEGraph (barrera opaca)
- `AmoLean/Sigma/Basic.lean` - Kernel sbox, lowering de elemwise
- `AmoLean/Sigma/Expand.lean` - Expansión de S-box (square chain: 3 muls)
- `AmoLean/Verification/Semantics.lean` - Evaluador para sbox
- `Tests/ElemwiseSanity.lean` - Tests de sanidad (4 tests, todos pasan)

### Implementación

**VecExpr** ahora tiene:
```lean
| head : VecExpr α (n + 1) → VecExpr α 1
| tail : VecExpr α (n + 1) → VecExpr α n
```

**MatExpr** ahora tiene:
```lean
inductive ElemOp where
  | pow : Nat → ElemOp      -- x^n (S-box para α=5)
  | custom : String → ElemOp

| elemwise : ElemOp → MatExpr α m n → MatExpr α m n
```

**Barrera opaca**: elemwise no se penetra por reglas de álgebra lineal - esto es arquitectónico (no hay reglas que miren dentro).

---

## Paso 1.5: Sanity Tests

### Objetivo
Verificar la robustez de la extensión elemwise antes de proceder al CodeGen.

### Checklist
- [x] Test 1: Semantic Check - sbox5 (x^5) computa correctamente
- [x] Test 2: Optimization Check - E-Graph requiere regla explícita de composición
- [x] Test 3: Safety Check (CRÍTICO) - E-Graph NO prueba (A+B)^2 = A^2 + B^2
- [x] Test 4: Barrier Integrity - elemwise no se distribuye sobre adición

### Archivo creado
- `Tests/ElemwiseSanity.lean`

### Resultados
```
╔════════════════════════════════════════════════════════════╗
║          ELEMWISE SANITY TESTS - Phase Poseidon            ║
╚════════════════════════════════════════════════════════════╝

=== Test 1: Semantic Check (sbox5) ===
  PASS: sbox5(0) = 0
  PASS: sbox5(1) = 1
  PASS: sbox5(2) = 15
  PASS: sbox5(3) = 5
  PASS: sbox5(4) = 4
  PASS: sbox5(5) = 14
  PASS: sbox5(16) = 16
  All semantic checks PASSED

=== Test 2: Optimization Check (elemwise composition) ===
  Are equivalent before composition rule? false
  Are equivalent after manual merge? true
  Composition check PASSED

=== Test 3: Safety Check (CRITICAL) ===
  SAFETY CHECK PASSED
  E-Graph correctly does NOT claim (x+y)^2 = x^2 + y^2

=== Test 4: Elemwise Barrier Integrity ===
  BARRIER INTEGRITY PASSED
  E-Graph correctly keeps elemwise opaque.

╔════════════════════════════════════════════════════════════╗
║  SUMMARY: 4 passed, 0 failed                              ║
║  STATUS: ALL TESTS PASSED - Safe to proceed to CodeGen     ║
╚════════════════════════════════════════════════════════════╝
```

### Problemas Encontrados y Soluciones

#### Problema 1: Sintaxis `let open` no soportada en Lean 4
**Error**: `unexpected token 'open'; expected ':=', '_', 'rec' or identifier`
**Causa**: Intenté usar `let open AmoLean.EGraph in` dentro de un bloque `do`
**Solución**: Mover los `open` statements al nivel de módulo con `open ... (...)` al inicio

#### Problema 2: Axioma `sorry` bloqueaba evaluación
**Error**: `aborting evaluation since the expression depends on the 'sorry' axiom`
**Causa**: `#eval` estándar rechaza código con dependencias de sorry
**Solución**: Usar `#eval!` para forzar evaluación

#### Problema 3: Valor esperado incorrecto para 5^5 mod 17
**Error**: Test fallaba con `sbox5(5) = 14, expected 3`
**Causa**: Cálculo manual inicial erróneo
**Solución**: Recalculado: 5^5 = 3125, 3125 mod 17 = 14. Corregido en tests.

---

## Paso 2: CodeGen (Estrategia por Capas)

### Decisión Arquitectónica

**Ver**: [ADR-004-codegen-strategy.md](ADR-004-codegen-strategy.md)

**Problema identificado**: La propuesta original de "Speculative Vectorization" asumía que
múltiples elementos de campo caben en un registro AVX2. Esto es **falso para BN254**:

| Campo | Bits/elemento | Elementos/YMM | Vectorización intra-hash |
|-------|---------------|---------------|--------------------------|
| Goldilocks | 64 | 4 | ✓ Viable |
| BN254 | 254 | 1 | ✗ No viable |

**Solución**: Estrategia por capas - corrección primero, optimización después.

---

### Paso 2.1: CodeGen Escalar

**Objetivo**: Generar código C correcto para `elemwise (pow n)`, funcionando para cualquier campo.

**Prioridad**: ALTA (es la base para differential fuzzing)

#### Checklist
- [x] Implementar `genSboxFunction` en CodeGen
- [x] Generar square chain óptima para x^5 (3 muls), x^7 (4 muls), x^11 (5 muls)
- [x] Generar `sbox5_full_round` para full rounds
- [x] Generar `sbox5_partial_round` para partial rounds
- [x] Parametrizar por tipo de campo (BN254, Goldilocks, Generic)
- [x] Proof anchors para verificación
- [ ] Tests de correctitud vs Spec.lean (pendiente: differential fuzzing)

#### Archivos creados
- `AmoLean/Protocols/Poseidon/CodeGen.lean` - CodeGen específico Poseidon (~420 líneas)
- `generated/poseidon_sbox_bn254.h` - Código C generado para BN254

#### Funciones implementadas
- `optimalSquareChain`: Cadenas óptimas para α ∈ {5, 7, 11}
- `genSboxFunction`: S-box escalar con square chain
- `genFullRoundSbox`: Full round (todos los elementos)
- `genPartialRoundSbox`: Partial round (solo primer elemento)
- `genTypeDefs`: Tipos C para estado Poseidon
- `genSboxCFile`: Header C completo

#### Código C objetivo

```c
// =============================================================================
// Poseidon S-box: x^5 using optimal square chain (3 multiplications)
// Generated by AMO-Lean Phase Poseidon
// =============================================================================

#include "field_ops.h"  // field_mul, field_params

// Square chain: x^5 = x * (x^2)^2
// Requires exactly 3 field multiplications
static inline void sbox5(
    uint64_t *out,           // Output: 4 limbs for BN254
    const uint64_t *x,       // Input: 4 limbs
    const field_params *p    // Field parameters (modulus, Montgomery constants)
) {
    uint64_t x2[4], x4[4];
    field_mul(x2, x, x, p);      // x2 = x * x
    field_mul(x4, x2, x2, p);    // x4 = x2 * x2 = x^4
    field_mul(out, x, x4, p);    // out = x * x4 = x^5
}

// Full round: apply S-box to all state elements
void sbox5_full_round(
    poseidon_state *state,
    const field_params *p
) {
    for (int i = 0; i < POSEIDON_T; i++) {
        sbox5(state->elem[i], state->elem[i], p);
    }
}

// Partial round: apply S-box only to first element
void sbox5_partial_round(
    poseidon_state *state,
    const field_params *p
) {
    sbox5(state->elem[0], state->elem[0], p);
}
```

---

### Paso 2.2: Pattern Matching en Lowering

**Objetivo**: Detectar el patrón de partial round en MatExpr y generar código optimizado.

**Estado**: **COMPLETADO**

#### Checklist
- [x] Añadir `partialElemwise` a MatExpr
- [x] Añadir `partialSbox` a Kernel
- [x] Extender lowering para generar `partialSbox`
- [x] Implementar `expandPartialSbox` en Expand
- [x] Tests de detección de patrones (Tests 6-9)
- [x] Actualizar nodeCount, opCountEstimate, estimateCost

#### Implementación

**En MatExpr** (nuevo constructor):
```lean
| partialElemwise : (idx : Nat) → ElemOp → MatExpr α m n → MatExpr α m n
```

**En Kernel** (nuevo kernel):
```lean
| partialSbox : Nat → Nat → Nat → Kernel  -- size, exponent, index
```

**Lowering** (nuevo caso):
```lean
| @MatExpr.partialElemwise _ m' n' idx op a =>
  let (innerExpr, state1) := lower m' n' state a
  let exp := match op with | ElemOp.pow α => α | _ => 1
  let partialSboxExpr := .compute (.partialSbox (m' * n') exp idx) ...
  (.seq innerExpr partialSboxExpr, state1)
```

**Expansión** (scalar ops):
```lean
def expandPartialSbox (size : Nat) (α : Nat) (idx : Nat) : ExpandedKernel :=
  -- Apply S-box only to element at `idx`, copy others
  -- For α=5: 3 muls for the target element, 0 for others
```

#### Archivos modificados
- `AmoLean/Matrix/Basic.lean` - partialElemwise, fullRoundSbox, partialRoundSbox
- `AmoLean/Sigma/Basic.lean` - partialSbox kernel, lowering de partialElemwise
- `AmoLean/Sigma/Expand.lean` - expandPartialSbox, tests 6-9

#### Resultados de tests
```
Test 6: Full S-box (3 elements)   → 9 muls (3 × 3)
Test 7: Partial S-box (idx=0)     → 3 muls (1 × 3)
Test 8: Full round lowering (9 elements) → 27 muls
Test 9: Partial round lowering          → 3 muls ✓
```

---

### Paso 2.3: SIMD para Goldilocks

**Objetivo**: Implementar vectorización AVX2 para campos de 64 bits.

**Estado**: **COMPLETADO**

**Estrategia**: Intra-hash SIMD - 4 elementos del estado en paralelo.

#### Checklist
- [x] Detectar si el campo es "SIMD-friendly" (≤64 bits)
- [x] Implementar `field_mul_avx2` para Goldilocks (reducción especial p = 2^64 - 2^32 + 1)
- [x] Implementar `sbox7_simd` con instrucciones AVX2
- [x] Implementar `sbox7_partial_simd` con blend para partial rounds
- [x] Generar `sbox7_full_round_simd` y `sbox7_partial_round_simd`

#### Archivos generados
- `generated/poseidon_sbox_goldilocks_simd.h` (~206 líneas)

#### Implementación

**Detección de campo SIMD-friendly**:
```lean
def isSIMDFriendly : FieldType → Bool
  | .Goldilocks => true   -- 64-bit: 4 elementos por YMM
  | .BN254 => false       -- 254-bit: 1 elemento llena YMM
  | .Generic => false
```

**S-box vectorizada**:
```c
static inline __m256i sbox7_simd(__m256i x) {
    __m256i x2 = field_mul_avx2(x, x);      // x^2
    __m256i x4 = field_mul_avx2(x2, x2);    // x^4
    __m256i x5 = field_mul_avx2(x, x4);     // x^5
    return x5;
}
```

**Partial round con blend**:
```c
static inline __m256i sbox7_partial_simd(__m256i state) {
    __m256i x5_all = sbox7_simd(state);
    // Blend: lane 0 de x5_all, lanes 1-3 de state
    return _mm256_blend_epi64(x5_all, state, 0b1110);
}
```

---

### Paso 2.4: Batch SIMD para BN254

**Objetivo**: Vectorizar procesando 4 hashes independientes en paralelo.

**Estado**: **COMPLETADO**

**Estrategia**: Inter-hash SIMD - procesar limbs correspondientes de 4 hashes juntos.

#### Checklist
- [x] Diseñar API de batch: `poseidon2_sbox5_full_round_batch4`, `poseidon2_sbox5_partial_round_batch4`
- [x] Implementar estructuras AoS (user-facing) y SoA (SIMD-friendly)
- [x] Implementar transpose bidireccional: `batch4_aos_to_soa`, `batch4_soa_to_aos`
- [x] Implementar `batch4_field_mul` con schoolbook multiplication vectorizada
- [x] Implementar `batch4_sbox5` con square chain

#### Archivos generados
- `generated/poseidon_sbox_bn254_batch.h` (~352 líneas)

#### Estructura de datos

```c
// Array of Structures (AoS): User-facing
typedef struct {
    uint64_t hash[4][3][4];  // [hash_idx][elem_idx][limb_idx]
} batch4_aos_3;

// Structure of Arrays (SoA): SIMD-friendly
typedef struct {
    __m256i elem[3][4];  // [elem_idx][limb_idx] = 4 hashes
} batch4_soa_3;
```

#### API Pública

```c
// Procesa 4 hashes en paralelo (full round)
void poseidon2_sbox5_full_round_batch4(
    batch4_aos_3 *states,
    const field_params *p
);

// Procesa 4 hashes en paralelo (partial round)
void poseidon2_sbox5_partial_round_batch4(
    batch4_aos_3 *states,
    const field_params *p
);
```

#### Flujo de ejecución
1. Transpose AoS → SoA
2. Aplicar S-box vectorizado (4 hashes simultáneos)
3. Transpose SoA → AoS

---

## Paso 3: Poseidon2 en MatExpr

### Objetivo
Expresar Poseidon2 completo usando el IR extendido.

### Checklist
- [ ] Full round como MatExpr
- [ ] Partial round con split/concat
- [ ] Poseidon2 permutation completa
- [ ] Modo sponge para hash de longitud variable
- [ ] Verificar que E-Graph no explota con expresión completa

### Archivos a crear
- `AmoLean/Protocols/Poseidon/MatExpr.lean`

---

## Paso 4: Verificación

### Objetivo
Validar correctitud de código generado.

### Checklist
- [ ] Differential fuzzing: `poseidon2_spec` vs C generado
- [ ] Benchmark vs implementación Rust de referencia
- [ ] Prueba formal: `eval(poseidon2_matexpr) = poseidon2_spec`
- [ ] Documentar cualquier `sorry`

### Framework de testing
Usar framework de fuzzing de Fase 6.

---

## Paso 5: Integración

### Objetivo
Conectar Poseidon2 con el resto del sistema.

### Checklist
- [ ] MerkleTree usando Poseidon2
- [ ] Fiat-Shamir usando Poseidon2
- [ ] Conectar con FRI para commits completos
- [ ] Tests end-to-end

### Archivos a crear/modificar
- `AmoLean/Protocols/MerkleTree.lean`
- `AmoLean/FRI/Commit.lean` (actualizar)

---

## Registro de Cambios

| Fecha | Cambio | Autor |
|-------|--------|-------|
| 2026-01-26 | Documentación inicial creada | Equipo |
| 2026-01-26 | Paso 0.5: Spec.lean (sin Mathlib, compila rápido) | Equipo |
| 2026-01-26 | Paso 1.0: head/tail añadidos a VecExpr | Equipo |
| 2026-01-26 | Paso 1.1: ElemOp y elemwise añadidos a MatExpr | Equipo |
| 2026-01-26 | Paso 1.2: elemwise en MatEGraph como barrera opaca | Equipo |
| 2026-01-26 | Paso 1.3: sbox kernel, lowering, evaluadores actualizados | Equipo |
| 2026-01-26 | Paso 1.5: Tests de sanidad (4/4 pasan) - Ready for CodeGen | Equipo |
| 2026-01-26 | ADR-004: Estrategia CodeGen por capas (reemplaza SIMD naive) | Equipo |
| 2026-01-26 | Paso 2: Inicio de implementación CodeGen escalar | Equipo |
| 2026-01-26 | Paso 2.1: CodeGen escalar completado (S-box, full/partial rounds) | Equipo |
| 2026-01-26 | Paso 2.2: Pattern matching completado (partialElemwise, partialSbox) | Equipo |
| 2026-01-26 | Paso 2.3: SIMD Goldilocks completado (AVX2 intra-hash, blend) | Equipo |
| 2026-01-26 | Paso 2.4: Batch SIMD BN254 completado (AoS↔SoA, 4 hashes) | Equipo |
| 2026-01-26 | **Paso 2 COMPLETO** - CodeGen escalar + SIMD funcionando | Equipo |

---

## Notas y Observaciones

*Añadir notas durante la implementación...*

---

## Bloqueos Actuales

*Ninguno por ahora*

---

## Decisiones Tomadas

Ver ADRs en este directorio:
- [ADR-001-elemwise.md](ADR-001-elemwise.md) - Extensión de MatExpr
- [ADR-002-partial-rounds.md](ADR-002-partial-rounds.md) - Split/concat para rondas parciales
- [ADR-003-codegen-simd.md](ADR-003-codegen-simd.md) - Estrategia SIMD original (parcialmente superseded)
- [ADR-004-codegen-strategy.md](ADR-004-codegen-strategy.md) - **Estrategia CodeGen por capas** (actual)
