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

## Índice de Decisiones

| ID | Título | Fecha |
|----|--------|-------|
| DD-001 | Arquitectura General de Option A | 2026-01-28 |
| DD-002 | Aritmética de Campo en Código Generado | 2026-01-28 |
| DD-003 | Manejo de Memoria en Código Generado | 2026-01-28 |
| DD-004 | Operaciones Vectoriales Opacas en E-Graph | 2026-01-28 |
| DD-005 | Estrategia de Validación (Translation Validation) | 2026-01-28 |
| DD-006 | Compilación con Sanitizers | 2026-01-28 |

---

*Última actualización: 2026-01-28*
