# Fase 5: Issues y Problemas Encontrados

**Fecha de creación**: 2026-01-29
**Estado**: ACTIVO

Este documento registra problemas encontrados durante la implementación de la Fase 5.

---

## Formato de Issues

```
### ISSUE-5.XXX: Título breve
**Fecha**: YYYY-MM-DD
**Severidad**: CRÍTICA | ALTA | MEDIA | BAJA
**Estado**: ABIERTO | EN PROGRESO | RESUELTO | WONTFIX
**Módulo**: archivo.lean afectado

**Descripción**:
[Descripción del problema]

**Causa raíz**:
[Análisis de por qué ocurre]

**Solución aplicada**:
[Cómo se resolvió, o plan para resolver]

**Lecciones aprendidas**:
[Qué aprendimos para evitar problemas similares]
```

---

## Issues Activos

(Ninguno actualmente)

---

## Issues Resueltos

### ISSUE-5.002: Heap-Buffer-Overflow en NTT N=1
**Fecha**: 2026-01-29
**Severidad**: CRÍTICA
**Estado**: RESUELTO
**Módulo**: ntt_skeleton.c

**Descripción**:
AddressSanitizer detectó heap-buffer-overflow al ejecutar NTT con N=1.
El programa crasheaba con `WRITE of size 8` en `precompute_twiddles`.

**Causa raíz**:
Para N=1, `half = n/2 = 0`, lo que causaba:
1. `malloc(0)` retornaba puntero válido (comportamiento definido por implementación)
2. `twiddles[0] = 1` escribía fuera de bounds (heap-buffer-overflow)

**Solución aplicada**:
1. Añadir early return en `ntt_forward()` para N=1:
   ```c
   if (n == 1) {
       return 0;  // Identity transform
   }
   ```
2. Añadir check en `precompute_twiddles()`:
   ```c
   if (half == 0) {
       return NULL;
   }
   ```

**Lecciones aprendidas**:
- Siempre testear edge cases (N=1, N=2) con sanitizers
- `malloc(0)` es válido pero peligroso - verificar tamaño antes
- AddressSanitizer es indispensable para código de bajo nivel

**Decisión de diseño**: DD-024

---

### ISSUE-5.001: Mathlib IsPrimitiveRoot trae dependencias pesadas
**Fecha**: 2026-01-29
**Severidad**: ALTA
**Estado**: RESUELTO
**Módulo**: RootsOfUnity.lean

**Descripción**:
Al intentar usar `IsPrimitiveRoot` de `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`,
el tiempo de compilación aumentó drásticamente y aparecieron conflictos de nombres.

**Causa raíz**:
Mathlib's IsPrimitiveRoot arrastra toda la jerarquía algebraica de campos,
incluyendo módulos que no necesitamos para NTT.

**Solución aplicada**:
Definimos nuestra propia `structure IsPrimitiveRoot` ligera que solo requiere:
1. `ω^n = 1`
2. `ω^k ≠ 1` para `0 < k < n`

Solo importamos módulos mínimos de Mathlib:
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Mathlib.Algebra.Ring.Basic`
- `Mathlib.Tactic.Ring`

**Lecciones aprendidas**:
- Validar tu análisis de obstáculos previo fue correcto
- Copiar definiciones esenciales es mejor que arrastrar dependencias pesadas
- El tiempo de compilación es un indicador crítico de salud del proyecto

---

## Problemas Evitados Proactivamente

Esta sección documenta problemas que fueron identificados mediante análisis previo
y mitigados ANTES de que ocurrieran.

### AVOIDED-5.001: Explosión O(N²) en NTT_spec
**Fecha análisis**: 2026-01-29
**Severidad potencial**: ALTA
**Decisión de diseño**: DD-015

**Descripción del riesgo**:
La especificación naive de NTT como suma directa `Σ aᵢ·ωⁱʲ` tiene complejidad O(N²).
Para N=1024, esto son ~1 millón de operaciones que colgarían el compilador de Lean.

**Análisis realizado**:
- Consultamos Trieu et al.: "The specification is for reasoning, not for execution"
- La eficiencia viene de Cooley-Tukey (Capa 2), no de la spec

**Mitigación aplicada**:
- NTT_spec se usa SOLO para proofs, nunca para N grande
- Tests limitados a N ≤ 64 donde O(N²) es aceptable
- Roundtrip tests con `native_decide` en compile-time

---

### AVOIDED-5.002: Índices fuera de rango en Cooley-Tukey
**Fecha análisis**: 2026-01-29
**Severidad potencial**: ALTA
**Decisión de diseño**: DD-016

**Descripción del riesgo**:
En la implementación recursiva de Cooley-Tukey, es muy fácil equivocarse
con los índices (stride, offset, twiddle factor index). Un error aquí
significa que estás sumando basura.

**Análisis realizado**:
- Los errores de índices son difíciles de detectar sin tests exhaustivos
- Lean ofrece tipos dependientes pero requieren manejo cuidadoso

**Mitigación aplicada**:
- Definir `List.evens`, `List.odds`, `List.interleave` como funciones auxiliares
- Probar teoremas de preservación:
  - `evens_odds_length`: longitud se preserva
  - `evens_odds_reconstruct`: roundtrip funciona
- Tests de equivalencia: `NTT_recursive = NTT_naive` para N pequeño

---

### AVOIDED-5.003: Olvidar N⁻¹ en INTT
**Fecha análisis**: 2026-01-29
**Severidad potencial**: ALTA
**Decisión de diseño**: DD-017

**Descripción del riesgo**:
La inversa de NTT requiere multiplicar por N⁻¹ al final. Sin esto,
`INTT(NTT(x)) = x * N` en lugar de `x`. Este error es sutil y puede
pasar desapercibido en tests casuales.

**Análisis realizado**:
- Es un error común documentado en la literatura
- La normalización debe ser explícita, no implícita

**Mitigación aplicada**:
- INTT incluye `n_inv` en su firma de forma explícita
- Roundtrip property test obligatorio: `INTT(NTT(x)) = x`
- Teorema formal `ntt_intt_identity` usando `sum_of_powers_zero`

---

## Estadísticas

| Severidad | Abiertos | Resueltos | Evitados | Total |
|-----------|----------|-----------|----------|-------|
| CRÍTICA | 0 | 1 | 0 | 1 |
| ALTA | 0 | 1 | 3 | 4 |
| MEDIA | 0 | 0 | 0 | 0 |
| BAJA | 0 | 0 | 0 | 0 |

**Nota**: "Evitados" son problemas identificados proactivamente y mitigados
antes de que causaran impacto en el desarrollo.

---

*Última actualización: 2026-01-29*
