# Phase 1: Plan de Acción Detallado

**Estado**: EN PROGRESO
**Fecha de inicio**: 2026-01-28
**Última actualización**: 2026-01-28

---

## Resumen Ejecutivo

Phase 1 implementa aritmética de campo Goldilocks real, corrigiendo los errores críticos identificados en la revisión técnica de la propuesta original.

### Correcciones Críticas Aplicadas

| Problema Original | Corrección |
|-------------------|------------|
| `field_add` con overflow silencioso | Usar `__uint128_t` para suma intermedia |
| Barrett Reduction genérica | Reducción especializada Goldilocks (shifts + sumas) |
| Tests solo aleatorios | Tests aleatorios + casos borde obligatorios |
| UBSan básico | UBSan + `-fsanitize=integer` |

---

## 1. Especificación Matemática: Campo Goldilocks

### 1.1 Definición del Campo

```
Campo Goldilocks: F_p

p = 2^64 - 2^32 + 1
p = 18446744069414584321 (decimal)
p = 0xFFFFFFFF00000001 (hexadecimal)

Tipo: Primo de Solinas (Generalized Mersenne Prime)
```

### 1.2 Propiedad Clave para Reducción Eficiente

```
2^64 ≡ 2^32 - 1 (mod p)

Demostración:
  2^64 - (2^32 - 1) = 2^64 - 2^32 + 1 = p ≡ 0 (mod p)
  ∴ 2^64 ≡ 2^32 - 1 (mod p)
```

Esta propiedad permite reducir un producto de 128 bits usando solo shifts y sumas, sin división.

### 1.3 Algoritmo de Reducción

Para un valor de 128 bits `x = x_hi · 2^64 + x_lo`:

```
x ≡ x_lo + x_hi · (2^64 mod p) (mod p)
x ≡ x_lo + x_hi · (2^32 - 1) (mod p)
x ≡ x_lo + (x_hi << 32) - x_hi (mod p)
```

El resultado puede exceder p, requiriendo iteración o reducción final.

### 1.4 Operaciones Requeridas

| Operación | Fórmula | Complejidad |
|-----------|---------|-------------|
| add(a,b) | (a + b) mod p | O(1) con `__uint128_t` |
| sub(a,b) | (a - b + p) mod p | O(1) |
| mul(a,b) | (a · b) mod p | O(1) con reducción especializada |
| neg(a) | (p - a) mod p | O(1) |
| inv(a) | a^(p-2) mod p | O(log p) via exp. binaria |

---

## 2. Bug Crítico Corregido: Overflow en Suma

### 2.1 Código Original (INCORRECTO)

```c
// ❌ PELIGROSO - NO USAR
static inline field_t field_add(field_t a, field_t b) {
    field_t sum = a + b;  // OVERFLOW SILENCIOSO AQUÍ
    return sum - (GOLDILOCKS_P & -(sum >= GOLDILOCKS_P));
}
```

### 2.2 Por Qué Falla

```
Caso: a = p-1, b = p-1
  a + b = 2p - 2 ≈ 2^65 - 2^33

En uint64_t (64 bits):
  sum = (2p - 2) mod 2^64
  sum ≈ p - 2^32 - 1  (valor wrapped)

Como sum < p:
  La condición (sum >= p) es FALSE
  Retornamos sum (INCORRECTO)

Valor correcto: (2p - 2) mod p = p - 2
Valor retornado: p - 2^32 - 1
```

### 2.3 Código Corregido (SEGURO)

```c
// ✅ CORRECTO - Usar __uint128_t para evitar overflow
static inline field_t field_add(field_t a, field_t b) {
    __uint128_t sum = (__uint128_t)a + b;
    if (sum >= GOLDILOCKS_P) {
        return (field_t)(sum - GOLDILOCKS_P);
    }
    return (field_t)sum;
}
```

---

## 3. Reducción Especializada vs Barrett

### 3.1 Barrett Reduction (NO USAR)

Barrett es un algoritmo genérico para `x mod p`:
- Requiere precomputar `μ = floor(2^k / p)`
- Usa multiplicaciones de 128+ bits
- Es lento para primos con estructura especial

### 3.2 Reducción Goldilocks (USAR)

Aprovecha la estructura `p = 2^64 - 2^32 + 1`:

```c
// Reducción especializada de Goldilocks
// Input: x de 128 bits
// Output: x mod p (64 bits)

static inline field_t field_reduce128(__uint128_t x) {
    // Separar en partes alta y baja
    uint64_t x_lo = (uint64_t)x;
    uint64_t x_hi = (uint64_t)(x >> 64);

    // Si no hay parte alta, posible reducción directa
    if (x_hi == 0) {
        return (x_lo >= GOLDILOCKS_P) ? x_lo - GOLDILOCKS_P : x_lo;
    }

    // Aplicar: 2^64 ≡ 2^32 - 1 (mod p)
    // x ≡ x_lo + x_hi * (2^32 - 1) (mod p)
    // x ≡ x_lo + (x_hi << 32) - x_hi (mod p)

    __uint128_t t = (__uint128_t)x_lo +
                    (((__uint128_t)x_hi) << 32) - x_hi;

    // Puede haber carry, repetir si necesario
    uint64_t t_lo = (uint64_t)t;
    uint64_t t_hi = (uint64_t)(t >> 64);

    if (t_hi > 0) {
        // Segunda iteración (raro pero posible)
        t = (__uint128_t)t_lo + (((uint64_t)t_hi) << 32) - t_hi;
        t_lo = (uint64_t)t;
    }

    // Reducción final condicional
    return (t_lo >= GOLDILOCKS_P) ? t_lo - GOLDILOCKS_P : t_lo;
}
```

### 3.3 Comparación de Performance

| Método | Operaciones | Uso en Phase 1 |
|--------|-------------|----------------|
| Barrett | 2-3 mul128, 1 sub | ❌ NO |
| Goldilocks especializado | 1-2 shift, 2-4 add/sub | ✅ SÍ |

---

## 4. Tests de Borde Obligatorios

### 4.1 Casos Críticos para `field_add`

| Test | a | b | Esperado | Razón |
|------|---|---|----------|-------|
| zero_zero | 0 | 0 | 0 | Identidad |
| zero_one | 0 | 1 | 1 | Identidad |
| one_pMinus1 | 1 | p-1 | 0 | Wrap exacto |
| pMinus1_pMinus1 | p-1 | p-1 | p-2 | **Máximo overflow** |
| half_half | p/2 | p/2 | p-1 (aprox) | Medio rango |

### 4.2 Casos Críticos para `field_mul`

| Test | a | b | Razón |
|------|---|---|-------|
| zero_any | 0 | random | Aniquilador |
| one_any | 1 | random | Identidad |
| pMinus1_pMinus1 | p-1 | p-1 | Máximo producto |
| near_sqrt_p | 2^32 | 2^32 | Cerca del punto especial |
| overflow_boundary | 2^32-1 | 2^32+1 | Cerca de ε |

### 4.3 Casos Críticos para `field_reduce128`

| Test | x_hi | x_lo | Razón |
|------|------|------|-------|
| pure_low | 0 | p-1 | Sin reducción |
| pure_low_over | 0 | p | Reducción simple |
| hi_one | 1 | 0 | 2^64 mod p = 2^32 - 1 |
| max_product | p-1 | p-1 | (p-1)^2 mod p |

---

## 5. Restricción Crítica: Exponente S-Box

### 5.1 El Problema

Para que la S-Box $x^d$ sea una **biyección** (invertible) en un campo $\mathbb{F}_p$, se requiere:

$$\gcd(d, p-1) = 1$$

### 5.2 Análisis para Goldilocks

```
p = 2^64 - 2^32 + 1
p - 1 = 2^32 × (2^32 - 1)
p - 1 = 2^32 × 3 × 5 × 17 × 257 × 65537
```

| Exponente | gcd(d, p-1) | ¿Biyección? | Uso |
|-----------|-------------|-------------|-----|
| d = 3 | 3 | ❌ NO | No usar |
| d = 5 | 5 | ❌ NO | **BN254 sí, Goldilocks NO** |
| d = 7 | 1 | ✅ SÍ | **Usar para Goldilocks** |
| d = 11 | 1 | ✅ SÍ | Alternativa válida |

### 5.3 Implicación

⚠️ **CRÍTICO para Phase 2 (Poseidon2)**:
- BN254 usa S-Box $x^5$
- **Goldilocks DEBE usar S-Box $x^7$**
- Usar $x^5$ en Goldilocks resulta en hash criptográficamente inseguro

### 5.4 Implementación

```c
// Para Goldilocks: S-Box es x^7, NO x^5
#define GOLDILOCKS_SBOX_EXPONENT 7

static inline field_t sbox(field_t x) {
    // x^7 = x^4 * x^2 * x (3 multiplicaciones)
    field_t x2 = field_mul(x, x);
    field_t x4 = field_mul(x2, x2);
    field_t x6 = field_mul(x4, x2);
    return field_mul(x6, x);
}
```

---

## 6. Referencias Técnicas

### 5.1 Implementación de Referencia: Plonky2

**Archivo**: `plonky2/field/src/goldilocks_field.rs`
**URL**: https://github.com/0xPolygonZero/plonky2/blob/main/field/src/goldilocks_field.rs

Puntos clave a estudiar:
1. Estructura `GoldilocksField`
2. Implementación de `reduce128`
3. Traits de campo (`Field`, `PrimeField`)
4. Tests incluidos

### 5.2 Bibliografía

1. **"Hacker's Delight"** (Henry S. Warren)
   - Capítulo 10: Integer Division by Constants
   - Técnicas de reducción modular sin división

2. **"Handbook of Applied Cryptography"** (Menezes et al.)
   - Sección 14.3: Modular Arithmetic
   - Barrett y Montgomery reduction

3. **Intel Intrinsics Guide**
   - `_addcarry_u64` para suma con acarreo
   - `_mulx_u64` para multiplicación 64x64→128

---

## 6. Plan de Implementación

### 6.1 Fase A: Goldilocks C (Crítico)

| Tarea | Archivo | Prioridad |
|-------|---------|-----------|
| field_add corregido | `generated/field_goldilocks.h` | P0 |
| field_sub | `generated/field_goldilocks.h` | P0 |
| field_mul con reduce128 | `generated/field_goldilocks.h` | P0 |
| field_neg | `generated/field_goldilocks.h` | P1 |
| Tests de borde C | `generated/test_goldilocks.c` | P0 |

### 6.2 Fase B: Goldilocks Lean

| Tarea | Archivo | Prioridad |
|-------|---------|-----------|
| Tipo GoldilocksField | `AmoLean/Field/Goldilocks.lean` | P0 |
| Instancia de campo | `AmoLean/Field/Goldilocks.lean` | P1 |
| Teoremas básicos | `AmoLean/Field/Goldilocks.lean` | P1 |

### 6.3 Fase C: Testing

| Tarea | Archivo | Prioridad |
|-------|---------|-----------|
| Oracle tests Goldilocks | `Tests/Oracle/GoldilocksOracle.lean` | P0 |
| Tests de borde | `Tests/Oracle/GoldilocksOracle.lean` | P0 |
| Actualizar CI/CD | `.github/workflows/ci.yml` | P1 |

### 6.4 Fase D: E-Graph Integration ✅ COMPLETADA

| Tarea | Archivo | Estado |
|-------|---------|--------|
| VecExpr en E-Graph | `AmoLean/EGraph/VecExpr.lean` | ✅ |
| Reglas de optimización | `AmoLean/EGraph/VecExpr.lean` | ✅ |

**Reglas implementadas:**
- `splitLo(concat(a,b)) = a` ✅
- `splitHi(concat(a,b)) = b` ✅
- `v + zero = v` ✅
- `concat(splitLo(v), splitHi(v)) = v` ✅

**Tests de E-Graph:**
- Test 1: Vector addition (v1 + v2) ✅
- Test 2: Split-concat optimization ✅
- Test 3: Add-zero identity ✅
- Test 4: FRI fold pattern ✅
- Test 5: Full saturation ✅

### 6.5 Fase E: Benchmark

| Tarea | Archivo | Prioridad |
|-------|---------|-----------|
| Re-benchmark con Goldilocks | `Benchmarks/Phase1/` | P1 |
| Comparación UInt64 vs Goldilocks | `docs/option-a/` | P1 |

---

## 7. Criterios de Éxito

| Criterio | Métrica | Verificación |
|----------|---------|--------------|
| Correctness | 100% oracle tests | Automatizado |
| Edge Cases | Todos los tests de borde pasan | Automatizado |
| Sanitizers | Sin errores con `-fsanitize=integer` | CI/CD |
| Field Laws | Pruebas Lean de leyes básicas | Compilación |
| Performance | Speedup > 10x vs Lean | Benchmark |

---

## 8. Riesgos y Mitigaciones

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|--------------|---------|------------|
| Overflow no detectado | Media | Alto | Tests de borde + UBSan |
| Reducción incorrecta | Media | Alto | Comparar con Plonky2 |
| Performance < 10x | Baja | Medio | Aceptable, optimizar en P2 |
| E-Graph integration blocker | Media | Medio | Bypass como en P0 |

---

## 9. Checklist de Inicio

Antes de comenzar implementación:

- [ ] Estudiar `goldilocks_field.rs` de Plonky2
- [ ] Verificar entendimiento de reducción especializada
- [ ] Confirmar tests de borde cubriendo todos los casos
- [ ] Actualizar CI/CD con nuevos sanitizers

---

*Documento creado: 2026-01-28*
*Este plan incorpora las correcciones críticas de la revisión técnica.*
