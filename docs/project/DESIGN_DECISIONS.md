# Option A: Decisiones de Diseño

Este documento registra todas las decisiones de diseño tomadas durante Option A.

---

## DD-001: Arquitectura General de Option A

**Fecha**: 2026-01-28
**Estado**: Aprobada

### Contexto

AMO-Lean tenía dos caminos posibles:
- **Option A**: Conectar specs (FRI, Poseidon2) al pipeline de optimización E-Graph → CodeGen
- **Option B**: Usar las implementaciones de referencia directamente (sin optimización formal)

### Decisión

**Elegimos Option A**: Expresar FRI y Poseidon2 como `MatExpr`/`VecExpr`, pasarlos por el E-Graph con reglas verificadas, y generar código C optimizado.

### Rationale

1. Era la visión original de AMO-Lean
2. Proporciona garantías formales de corrección
3. El trabajo de referencia (FRI+Poseidon2) no se pierde - sirve para validación
4. Mayor valor a largo plazo para integración con zkVMs

### Consecuencias

- Las implementaciones de referencia (`FRI/Prover.lean`, etc.) se mantienen para testing
- Necesitamos expresar operaciones como `MatExpr`/`VecExpr`
- El código generado debe validarse contra las referencias

---

## DD-002: Aritmética de Campo en Código Generado

**Fecha**: 2026-01-28
**Estado**: Aprobada

### Contexto

El código C generado necesita realizar aritmética de campo finito. Hay tres opciones:

1. **Operadores nativos** (`+`, `*`): Incorrecto para campos finitos ≠ 2^64
2. **Aritmética inline**: `(a + b) % P` - Correcto pero acoplado al campo
3. **Funciones abstractas**: `field_add(a, b)` - Correcto y desacoplado

### Problema Identificado

Si generamos:
```c
out[i] = even[i] + alpha * odd[i];  // Aritmética mod 2^64
```

Esto es **matemáticamente incorrecto** para campos como BN254 (mod P donde P es primo de 254 bits) o Goldilocks (mod 2^64 - 2^32 + 1).

### Decisión

**Generar llamadas a funciones de campo abstractas**:

```c
out[i] = field_add(even[i], field_mul(alpha, odd[i]));
```

Con un header configurable:

```c
// field_ops.h - Versión testing (UInt64 nativo)
#define field_add(a, b) ((a) + (b))
#define field_mul(a, b) ((a) * (b))

// field_ops.h - Versión producción (campo específico)
static inline uint64_t field_add(uint64_t a, uint64_t b) {
    return add_mod(a, b, FIELD_MODULUS);
}
```

### Rationale

1. El código generado es **siempre correcto** semánticamente
2. La elección de campo es una decisión de linking, no de generación
3. Permite testing rápido con aritmética nativa
4. Facilita transición a campos reales sin regenerar código

### Referencias

- Fiat-Crypto usa un approach similar con "synthesis of field arithmetic"

---

## DD-003: Manejo de Memoria en Código Generado

**Fecha**: 2026-01-28
**Estado**: Aprobada

### Contexto

Lean usa tipos inmutables. C usa punteros mutables. El código generado necesita:
1. Recibir buffers de entrada
2. Escribir en buffer de salida
3. Manejar correctamente aliasing

### Problemas Identificados

1. **Buffer overflow**: Si `n` en Lean ≠ tamaño real del buffer en C
2. **Aliasing**: Si `out == even` (operación in-place), el compilador puede optimizar incorrectamente
3. **Null pointers**: Caller podría pasar punteros nulos

### Decisión

1. **Usar `restrict`** en punteros de salida para indicar no-aliasing
2. **Generar assertions** en modo debug
3. **Documentar contrato** en comentarios del código generado

```c
/**
 * FRI fold operation: out[i] = even[i] + alpha * odd[i]
 *
 * REQUIRES:
 *   - even, odd, out are non-null
 *   - even, odd, out point to arrays of at least n elements
 *   - out does not alias even or odd
 */
void fri_fold(const uint64_t* restrict even,
              const uint64_t* restrict odd,
              uint64_t alpha,
              uint64_t* restrict out,
              size_t n) {
#ifdef DEBUG
    assert(even != NULL && "even is null");
    assert(odd != NULL && "odd is null");
    assert(out != NULL && "out is null");
    assert(out != even && out != odd && "output aliases input");
#endif
    for (size_t i = 0; i < n; i++) {
        out[i] = field_add(even[i], field_mul(alpha, odd[i]));
    }
}
```

### Rationale

1. `restrict` permite optimizaciones de compilador (vectorización)
2. Assertions en debug detectan errores de integración temprano
3. Documentación clara previene mal uso
4. En release, assertions se eliminan (zero overhead)

---

## DD-004: Operaciones Vectoriales Opacas en E-Graph

**Fecha**: 2026-01-28
**Estado**: Aprobada

### Contexto

Al insertar un vector de tamaño N en el E-Graph, hay dos opciones:

1. **Expandir**: Crear N nodos, uno por elemento
2. **Opaco**: Crear 1 nodo que representa la operación vectorial completa

### Problema Identificado

Si expandimos un vector de 1024 elementos:
- E-Graph tendría 1024+ nodos por operación
- Saturación podría agotar memoria
- No ganaríamos optimizaciones útiles (las optimizaciones son a nivel de operación, no de elemento)

### Decisión

**Mantener operaciones vectoriales como nodos opacos**:

```
E-Graph ve:            NO ve:

  VecAdd               add(v[0], w[0])
   / \                 add(v[1], w[1])
  v   w                ... (N nodos)
```

La expansión a elementos individuales ocurre **solo en CodeGen**, al generar el loop.

### Rationale

1. E-Graph se mantiene pequeño (O(operaciones), no O(elementos))
2. Optimizaciones vectoriales (fusión de loops, etc.) son a nivel de operación
3. CodeGen genera loops eficientes sin explotar el E-Graph
4. Coincide con el diseño actual de `MatEGraph`

### Verificación

Confirmar que `EGraph/Vector.lean` trata `VecExpr` como nodos únicos, no expandidos.

---

## DD-005: Estrategia de Validación (Translation Validation)

**Fecha**: 2026-01-28
**Estado**: Aprobada

### Contexto

¿Cómo verificamos que el código C generado es correcto?

Opciones:
1. **Confiar en las transformaciones**: Si las reglas están probadas, el código es correcto
2. **Testing manual**: Escribir tests en C que comparen con valores esperados
3. **Translation validation via FFI**: Llamar al C compilado desde Lean y comparar

### Decisión

**Usar Translation Validation via FFI**:

```
1. Ejecutar spec en Lean           → resultado_lean
2. Generar código C desde spec     → fri_fold.c
3. Compilar con clang              → fri_fold.so
4. Llamar desde Lean via FFI       → resultado_c
5. Comparar resultado_lean == resultado_c
```

### Rationale

1. **Más fuerte que confiar**: Incluso si las transformaciones son correctas, puede haber bugs en CodeGen
2. **Automatizable**: Los tests se ejecutan en CI
3. **Detecta errores de integración**: Problemas de memoria, aliasing, etc.
4. **Usa la referencia que ya tenemos**: `FRI/Prover.lean` es el oráculo

### Herramientas

- Compilar con `clang -fsanitize=address,undefined` para detectar errores de memoria
- Usar `-O0 -g` para debug, `-O3` para verificar que optimizaciones no rompen nada

---

## DD-006: Compilación con Sanitizers

**Fecha**: 2026-01-28
**Estado**: Aprobada

### Contexto

El código C generado puede tener bugs sutiles:
- Buffer overflows
- Undefined behavior (signed overflow, null deref)
- Use after free

### Decisión

**Compilar siempre con sanitizers en desarrollo**:

```makefile
# Debug build
debug: fri_fold.c
    clang -fsanitize=address,undefined -g -O0 -o $@ $<

# Release build
release: fri_fold.c
    clang -O3 -march=native -o $@ $<

# Test build (sanitizers + optimizaciones para detectar bugs de optimización)
test: fri_fold.c
    clang -fsanitize=address,undefined -O2 -o $@ $<
```

### Rationale

1. AddressSanitizer detecta buffer overflows, use-after-free
2. UndefinedBehaviorSanitizer detecta signed overflow, null deref, etc.
3. Overhead es ~2x en tiempo, aceptable para desarrollo
4. Encontrar bugs temprano es más barato que debuggear producción

---

---

## DD-011 a DD-020: Decisiones de Fase 5 (NTT Core)

Ver [PHASE5_NTT_PLAN.md](PHASE5_NTT_PLAN.md) para las decisiones DD-011 a DD-020 relacionadas con la implementación de NTT.

---

## DD-021: Axiomas Diferidos para NTT (Deuda Técnica Controlada)

**Fecha**: 2026-01-29
**Estado**: Aprobada

### Contexto

La implementación de NTT tiene 9 teoremas pendientes (sorry) que son matemáticamente correctos pero requieren esfuerzo significativo de "proof engineering" en Lean.

### Decisión

**Marcar los 9 teoremas como axiomas temporales** para desbloquear la Fase de Optimización (Semanas 4-6).

### Teoremas Diferidos

| # | Teorema | Archivo | Justificación Matemática |
|---|---------|---------|--------------------------|
| 1 | `intt_ntt_identity_finset` | Properties.lean | Ortogonalidad de raíces de unidad |
| 2 | `parseval` | Properties.lean | Teorema de Plancherel |
| 3 | `cooley_tukey_upper_half` | Correctness.lean | Fórmula DFT splitting (CT 1965) |
| 4 | `cooley_tukey_lower_half` | Correctness.lean | Usa ω^(n/2) = -1 |
| 5 | `ct_recursive_eq_spec` | Correctness.lean | Inducción fuerte |
| 6 | `ntt_intt_recursive_roundtrip` | Correctness.lean | Composición de (5) + spec |
| 7 | `ntt_coeff_add` | Spec.lean | Linealidad de sumatorias |
| 8 | `ntt_coeff_scale` | Spec.lean | Linealidad de sumatorias |
| 9 | `ntt_intt_identity` | Spec.lean | Equivalente a (1) para listas |

### Rationale

1. **Validación empírica**: Oracle tests pasan para N=4,8,16,32
2. **Matemática estándar**: Todos son teoremas conocidos de Fourier/NTT
3. **Riesgo cero matemático**: Solo hay riesgo de "no saber escribirlo en Lean"
4. **ROI negativo**: Semanas de proof engineering vs. avanzar a CodeGen
5. **Completación diferida**: Se probarán en Fase 6 (Hardening)

### Documentación

Ver `AmoLean/NTT/Axioms.lean` para registro detallado de cada axioma.

---

## DD-022: Modelo LazyGoldilocks con Nat (No UInt64)

**Fecha**: 2026-01-29
**Estado**: Aprobada

### Contexto

Para implementar "Lazy Reduction" (optimización Harvey), los valores intermedios pueden exceder el rango de `UInt64` (hasta 4p donde p ≈ 2^64).

### Problema Identificado

```lean
-- ❌ INCORRECTO: UInt64 tiene semántica de wrapping
structure LazyGoldilocks where
  val : UInt64  -- Si val > 2^64, Lean trunca silenciosamente
  bound : val.toNat < 4 * P  -- Prueba sobre valor truncado!
```

**Escenario de fallo:**
- `a = 2^63, b = 2^63` (ambos válidos < p)
- `a + b = 2^64` en matemáticas
- `a + b = 0` en UInt64 (wrap around)
- Lean prueba "0 < 4p" ✓ (correcto para valor truncado)
- C calcula `2^64` en `__uint128_t` (valor real)
- **La prueba formal es incorrecta para el código C real**

### Decisión

**Usar `Nat` (precisión infinita) en Lean para modelar valores lazy:**

```lean
-- ✅ CORRECTO: Nat no tiene overflow
structure LazyGoldilocks where
  val : Nat
  h_bound : val < 4 * GOLDILOCKS_PRIME
```

### Implementación

| Capa | Tipo | Semántica |
|------|------|-----------|
| Lean Spec | `Nat` | Precisión infinita, proofs correctas |
| Lean Impl Model | `BitVec 128` | Matches C exactamente |
| C Implementation | `__uint128_t` | Registros rdx:rax en x86-64 |

### Teorema de Refinamiento

```lean
theorem lazy_simulates_spec (a b : LazyGoldilocks) :
    (lazy_add a b).reduce = (a.reduce + b.reduce) := by
  -- Aritmética modular sobre Nat
  sorry  -- Pendiente
```

### Consecuencias

1. Proofs de bounds son matemáticamente correctas
2. CodeGen puede usar `__uint128_t` con garantía de equivalencia
3. No hay riesgo de proofs "correctas" sobre valores truncados

---

## DD-023: Estrategia CodeGen Skeleton + Kernel

**Fecha**: 2026-01-29
**Estado**: Aprobada

### Contexto

Generar NTT iterativo completo desde Lean recursivo usando E-Graph es muy complejo (deducir loops for es difícil).

### Decisión

**Separar Skeleton (manual) de Kernel (generado):**

```
┌─────────────────────────────────────────────────────────────┐
│  Skeleton (C manual)                                        │
│  - Estructura de loops: for layer, for group, for pair      │
│  - Bit-reversal permutation                                 │
│  - Gestión de memoria                                       │
├─────────────────────────────────────────────────────────────┤
│  Kernel (Generado desde Lean)                               │
│  - lazy_butterfly() optimizado                              │
│  - Reducción Montgomery/Harvey                              │
│  - Operaciones de campo                                     │
└─────────────────────────────────────────────────────────────┘
```

### Rationale

1. **E-Graph para lo que es bueno**: Optimización algebraica del kernel
2. **Humano para lo que es difícil**: Estructura de loops iterativos
3. **Menor riesgo**: No dependemos de E-Graph para deducir loops
4. **Verificación clara**: Oracle testing Lean recursivo vs C iterativo

---

## Índice de Decisiones

| ID | Título | Fecha |
|----|--------|-------|
| DD-001 | Arquitectura General de Option A | 2026-01-28 |
| DD-002 | Aritmética de Campo en Código Generado | 2026-01-28 |
| DD-003 | Manejo de Memoria en Código Generado | 2026-01-28 |
| DD-004 | Operaciones Vectoriales Opacas en E-Graph | 2026-01-28 |
| DD-005 | Estrategia de Validación (Translation Validation) | 2026-01-28 |
| DD-006 | Compilación con Sanitizers | 2026-01-28 |
| DD-011 | Especificación CRT-based (no evaluation-based) | 2026-01-29 |
| DD-012 | No escribir versión iterativa en Lean | 2026-01-29 |
| DD-013 | Enfoque híbrido para type classes | 2026-01-29 |
| DD-014 | Lazy reduction con tipos refinados | 2026-01-29 |
| DD-015 | Spec O(N²) solo para razonamiento | 2026-01-29 |
| DD-016 | Funciones auxiliares evens/odds | 2026-01-29 |
| DD-017 | N⁻¹ explícito en INTT | 2026-01-29 |
| DD-018 | Bridge Lemmas en lugar de CommRing Global | 2026-01-29 |
| DD-019 | Gap de Tipos Fin.univ ↔ Finset.range | 2026-01-29 |
| DD-020 | Criterio de Éxito para CT=Spec | 2026-01-29 |
| DD-021 | Axiomas Diferidos para NTT | 2026-01-29 |
| DD-022 | Modelo LazyGoldilocks con Nat (No UInt64) | 2026-01-29 |
| DD-023 | Estrategia CodeGen Skeleton + Kernel | 2026-01-29 |
| DD-024 | Early Return para N=1 en NTT | 2026-01-29 |

---

## DD-024: Early Return para N=1 en NTT

**Fecha**: 2026-01-29
**Estado**: Aprobada (Bug Fix)

### Contexto

Durante la auditoría final con AddressSanitizer, se detectó un heap-buffer-overflow en `ntt_forward()` cuando N=1.

### Problema Identificado

```c
// En precompute_twiddles():
size_t half = n / 2;  // Para N=1, half = 0
goldilocks_t* twiddles = malloc(half * sizeof(goldilocks_t));  // malloc(0)
twiddles[0] = 1;  // OVERFLOW: escribiendo a buffer de 0 bytes
```

### Decisión

**Agregar early return para N=1** en `ntt_forward()`:

```c
int ntt_forward(goldilocks_t* data, size_t n, goldilocks_t omega) {
    if (n == 0 || (n & (n - 1)) != 0) {
        return -1;
    }

    // N=1: Identity transform, nothing to do
    if (n == 1) {
        return 0;
    }

    // ... rest of function
}
```

### Rationale

1. **Matemáticamente correcto**: NTT de un solo elemento es la identidad
2. **Evita edge case**: No hay butterflies para N=1 (log2(1) = 0 capas)
3. **Detectado por ASan**: Validación del enfoque de sanitizers

### Archivos Modificados

- `generated/ntt_skeleton.c` - Agregado early return
- `generated/precompute_twiddles()` - Agregado check para half == 0

---

*Última actualización: 2026-01-29*
