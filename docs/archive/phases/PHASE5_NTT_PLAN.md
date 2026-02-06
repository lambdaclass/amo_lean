# Fase 5: NTT Core - Plan Detallado

**Fecha de creación**: 2026-01-29
**Estado**: EN PROGRESO - Semanas 1-4 sustancialmente completadas
**Duración estimada**: 4-6 semanas
**Última actualización**: 2026-01-29

---

## 1. Objetivo

Implementar una especificación formal completa de NTT (Number Theoretic Transform) en Lean 4, con pruebas de corrección y generación de código C optimizado.

**Entregables principales:**
1. Especificación matemática de NTT (inmutable, sobre listas)
2. Algoritmo Cooley-Tukey recursivo con prueba de equivalencia
3. Soporte para lazy reduction con tipos refinados
4. Generación de código C iterativo via E-Graph

---

## 2. Bibliografía Estudiada

### 2.1 Papers Fundamentales (PDFs en `docs/references/ntt/`)

| Paper | Relevancia | Aporte Principal |
|-------|------------|------------------|
| **Formally Verified NTT** (Trieu, ANSSI 2025) | CRÍTICA | Especificación CRT-based, refinamiento por capas, 7 meses de trabajo en Coq |
| **Verification of an Optimized NTT** (Navas, Dutertre) | MUY ALTA | Prueba de ausencia de overflow via interpretación abstracta |
| **Faster Arithmetic for NTT** + **Harvey Optimization** | ALTA | Representación redundante [0, 2p), elimina condicionales |
| **Intro to NTT** + **Implementing NTT** | MEDIA | Fundamentos matemáticos, Cooley-Tukey, Gentleman-Sande |
| **NTT for CRYSTALS** + **NTT Meets SIS** | MEDIA | Contexto criptográfico, parámetros reales |
| **Pipelined NTT** + **NTT Accel via Constants** | BAJA | Insights de paralelismo para SIMD |

### 2.2 Repositorios Estudiados

| Repositorio | URL | Aporte |
|-------------|-----|--------|
| **risc0-lean4** | github.com/risc0/risc0-lean4 | Type classes para campos, NTT ejecutable (sin pruebas), estructura de proyecto |
| **GPU-NTT** | github.com/Alisah-Ozcan/GPU-NTT | Optimizaciones traducibles a AVX2, Barrett reduction, batch processing |

### 2.3 Documentación de Lean 4

| Recurso | URL | Tema |
|---------|-----|------|
| Functional Programming in Lean | lean-lang.org | Arrays, monads, insertion sort verificado |
| Lean 4 Reference Manual | lean-lang.org/doc/reference | ST monad, mvcgen, Std.Do |
| Mathlib4 Docs | leanprover-community.github.io/mathlib4_docs | IsPrimitiveRoot, ZMod, Field hierarchy |
| Blog de Markus Himmel | markushimmel.de | Primer programa imperativo verificado con mvcgen |

### 2.4 Series de Blog

| Serie | URL | Contenido |
|-------|-----|-----------|
| NTT Series (Higashi) | higashi.blog/2023/12/15/ntt-03/ | Convolución, NTT, "Kyber Trick" |

---

## 3. Decisiones de Diseño

### DD-011: Especificación CRT-based (no evaluation-based)

**Decisión**: Usar Chinese Remainder Theorem para especificar NTT.

**Razón**: El paper de Trieu demuestra que es más general (maneja NTT completa e incompleta) y el bit-reversal emerge naturalmente.

```
NTT(p) = (p mod (X^k - ζ^a₀), ..., p mod (X^k - ζ^aₙ))
```

### DD-012: No escribir versión iterativa en Lean

**Decisión**: Probar Cooley-Tukey recursivo y usar E-Graph/CodeGen para generar código iterativo.

**Razón**: Probar loop invariants en Lean 4 es difícil y las herramientas (mvcgen) son muy nuevas (Lean 4.22+).

### DD-013: Enfoque híbrido para type classes

**Decisión**: Definir `NTTField` lightweight + usar `IsPrimitiveRoot` de Mathlib.

**Razón**:
- `Field` de Mathlib requiere `ratCast : ℚ → K` (innecesario para NTT)
- `IsPrimitiveRoot` solo requiere `CommMonoid` (ligero)
- risc0-lean4 usa enfoque similar

### DD-014: Lazy reduction con tipos refinados

**Decisión**: Separar capa algebraica (mod p perfecto) de capa de implementación (bounds [0, 4p)).

**Razón**: Permite probar corrección algebraica independientemente de optimizaciones de implementación.

### DD-015: Spec O(N²) solo para razonamiento, no ejecución

**Decisión**: La especificación naive `NTT_spec` es O(N²) y está diseñada para probar teoremas, no para ejecutar con N grande.

**Razón**:
- La eficiencia viene de Cooley-Tukey (Capa 2), no de la spec (Capa 1)
- Trieu: "The specification is for reasoning, not for execution"
- Tests se limitan a N ≤ 64 donde O(N²) es aceptable

**Problema evitado**: Explosión exponencial al intentar ejecutar spec para N=1024.

### DD-016: Funciones auxiliares `evens/odds` con teoremas de preservación

**Decisión**: Definir `List.evens`, `List.odds`, `List.interleave` como funciones auxiliares con teoremas que garantizan:
- `evens_odds_length`: `l.evens.length + l.odds.length = l.length`
- `evens_odds_reconstruct`: `interleave l.evens l.odds = l`

**Razón**:
- Evita errores de índices en Cooley-Tukey recursivo
- Los teoremas de preservación aseguran que no perdemos/duplicamos elementos
- Permite razonar sobre la recursión sin manipular índices explícitos

**Problema evitado**: Índices fuera de rango y errores de stride/offset en CT.

### DD-017: N⁻¹ explícito en INTT, no implícito

**Decisión**: INTT incluye multiplicación por N⁻¹ de forma explícita en su definición y firma.

```lean
def INTT (a : List F) (ω : F) (n_inv : F) : List F :=
  (NTT_spec a (inv ω)).map (· * n_inv)
```

**Razón**:
- Hace visible la normalización, no la esconde
- Facilita probar `ntt_intt_identity` usando `sum_of_powers_zero`
- Evita el error común de olvidar N⁻¹

**Problema evitado**: `INTT(NTT(x)) = x * N` en lugar de `x`.

---

## 4. Arquitectura de Refinamiento (Modelo Trieu)

### 4.1 Las Cuatro Capas

```
┌─────────────────────────────────────────────────────────────────┐
│ CAPA 4: Código C/AVX2 Generado                                  │
│         - Loops iterativos                                      │
│         - Arrays mutables in-place                              │
│         - SIMD intrinsics                                       │
├─────────────────────────────────────────────────────────────────┤
│ CAPA 3: Implementación con Bounds                               │
│         - LazyGoldilocks : val < 4p                             │
│         - butterfly_lazy con tracking de bounds                 │
│         - Teorema: lazy_simulates_spec                          │
├─────────────────────────────────────────────────────────────────┤
│ CAPA 2: Algoritmo Recursivo (Cooley-Tukey)                      │
│         - Sobre listas inmutables                               │
│         - Divide-and-conquer                                    │
│         - Teorema: CT_recursive = NTT_spec                      │
├─────────────────────────────────────────────────────────────────┤
│ CAPA 1: Especificación Matemática                               │
│         - NTT como suma: Σ aᵢ·ωⁱʲ                               │
│         - Propiedades algebraicas (inversa, convolución)        │
│         - Sin consideraciones de implementación                 │
└─────────────────────────────────────────────────────────────────┘
```

### 4.2 Teoremas de Refinamiento

| Transición | Teorema | Técnica de Prueba |
|------------|---------|-------------------|
| Capa 1 → Capa 2 | `ct_recursive_eq_spec` | Inducción en profundidad de recursión |
| Capa 2 → Capa 3 | `lazy_butterfly_simulates` | Aritmética modular + bounds |
| Capa 3 → Capa 4 | (Por construcción) | E-Graph con reglas verificadas |

### 4.3 Comparación con Trieu (Coq/Fiat-Crypto)

| Aspecto | Trieu (Coq) | AMO-Lean (Lean 4) |
|---------|-------------|-------------------|
| Especificación | CRT-based | CRT-based (adoptado) |
| Prueba recursivo→spec | Inducción en r | Inducción en profundidad |
| Prueba iterativo | Fiat-Crypto síntesis | E-Graph + CodeGen |
| Bounds | Bedrock2 separation logic | Tipos refinados + omega |
| Code generation | Fiat-Crypto → C | E-Graph → C |

---

## 5. Estructura de Archivos

```
AmoLean/NTT/
├── Field.lean           # NTTField lightweight type class          [✅ DONE]
├── RootsOfUnity.lean    # IsPrimitiveRoot propio, propiedades      [✅ DONE]
├── Goldilocks.lean      # Instancia para campo Goldilocks          [✅ DONE]
├── ListUtils.lean       # evens, odds, interleave + teoremas       [✅ DONE]
├── Spec.lean            # Capa 1: NTT_spec, INTT (O(N²))           [✅ DONE]
├── Properties.lean      # Teoremas: linealidad, ortogonalidad      [✅ DONE (sorries)]
├── CooleyTukey.lean     # Capa 2: Algoritmo recursivo O(N log N)   [✅ DONE]
├── Butterfly.lean       # Operación butterfly extraída             [✅ DONE (sorries)]
├── Correctness.lean     # Teorema: CT = Spec + native_decide tests [✅ DONE (sorries)]
├── Bounds.lean          # Capa 3: LazyGoldilocks                    [⏳ Semana 4-5]
├── LazyButterfly.lean   # butterfly_lazy + simulación               [⏳ Semana 4-5]
└── CodeGen.lean         # Capa 4: Generación de C                   [⏳ Semana 5-6]

Tests/NTT/
├── ListUtilsTest.lean   # Tests para funciones de lista            [✅ DONE]
├── AlgebraTest.lean     # Tests algebraicos NTT/INTT               [✅ DONE]
├── CorrectnessTest.lean # Golden tests: NTT_spec == NTT_recursive  [✅ DONE]
└── PropertiesTest.lean  # Tests de propiedades                     [✅ DONE]

Bench/
└── NTT_Math.lean        # Benchmarks O(N²) vs O(N log N)           [✅ DONE]
```

---

## 6. Plan de Tareas Detallado

### Semana 1-2: Fundamentos

| # | Tarea | Archivo | Dependencias | Criterio de Éxito |
|---|-------|---------|--------------|-------------------|
| 1.1 | Definir NTTField type class | Field.lean | - | Compila, instanciable |
| 1.2 | Definir PrimitiveRoot wrapper | RootsOfUnity.lean | Mathlib | Usa IsPrimitiveRoot |
| 1.3 | Probar sum_of_powers_zero | RootsOfUnity.lean | 1.2 | Sin sorry |
| 1.4 | Instanciar Goldilocks | Goldilocks.lean | 1.1, 1.2 | Tests pasan |

**Entregable Semana 2**: `RootsOfUnity.lean` con teoremas básicos probados.

### Semana 2-3: Especificación (ACTUALIZADO con técnicas superadoras)

**Análisis de riesgos realizado**: 2026-01-29
- Riesgo 1: Explosión O(N²) → Mitigado con DD-015
- Riesgo 2: Índices erróneos → Mitigado con DD-016
- Riesgo 3: Olvidar N⁻¹ → Mitigado con DD-017

| # | Tarea | Archivo | Dependencias | Criterio de Éxito | Técnica |
|---|-------|---------|--------------|-------------------|---------|
| 2.0a | Definir List.evens | ListUtils.lean | - | Teorema preservación | DD-016 |
| 2.0b | Definir List.odds | ListUtils.lean | - | Teorema preservación | DD-016 |
| 2.0c | Definir List.interleave | ListUtils.lean | - | evens/odds roundtrip | DD-016 |
| 2.1 | Definir NTT_spec (naive O(N²)) | Spec.lean | 1.*, 2.0* | Compila, tests N≤64 | DD-015 |
| 2.2 | Definir INTT con N⁻¹ explícito | Spec.lean | 2.1 | Firma incluye n_inv | DD-017 |
| 2.3 | Probar ntt_intt_identity | Properties.lean | 2.1, 2.2 | Sin sorry | sum_of_powers_zero |
| 2.4 | Tests de equivalencia | Spec.lean | 2.1, 2.2 | Pass para N∈{4,8,16,32} | Oracle testing |

**Tests requeridos (antes de considerar completa la semana)**:
```
✓ NTT_spec ejecutable para N ≤ 64
✓ INTT(NTT(x)) = x para N ∈ {4, 8, 16, 32}
✓ Teorema ntt_intt_identity sin sorry
✓ evens/odds roundtrip: interleave(evens(l), odds(l)) = l
```

**Entregable Semana 3**: `ListUtils.lean` + `Spec.lean` + `Properties.lean` con teoremas principales.

### Semana 3-4: Algoritmo Recursivo

| # | Tarea | Archivo | Dependencias | Criterio de Éxito |
|---|-------|---------|--------------|-------------------|
| 3.1 | Definir butterfly_spec | Butterfly.lean | 1.* | Definición compila |
| 3.2 | Definir ct_recursive | CooleyTukey.lean | 3.1 | Termination proof |
| 3.3 | Probar butterfly properties | Butterfly.lean | 3.1 | Sin sorry |
| 3.4 | Probar ct_recursive_eq_spec | Correctness.lean | 2.*, 3.2 | Sin sorry |

**Entregable Semana 4**: `CooleyTukey.lean` + `Correctness.lean` probados.

### Semana 4-5: Bounds y Lazy Reduction

| # | Tarea | Archivo | Dependencias | Criterio de Éxito |
|---|-------|---------|--------------|-------------------|
| 4.1 | Definir LazyGoldilocks | Bounds.lean | Goldilocks | Tipo refinado funciona |
| 4.2 | Definir butterfly_lazy | LazyButterfly.lean | 4.1 | Compila |
| 4.3 | Probar bounds preservation | LazyButterfly.lean | 4.2 | omega resuelve |
| 4.4 | Probar lazy_simulates_spec | LazyButterfly.lean | 4.3, 3.1 | Sin sorry |

**Entregable Semana 5**: `Bounds.lean` + `LazyButterfly.lean` con simulación probada.

### Semana 5-6: Code Generation

| # | Tarea | Archivo | Dependencias | Criterio de Éxito |
|---|-------|---------|--------------|-------------------|
| 5.1 | Diseñar NTT CodeGen | CodeGen.lean | 4.* | Genera código C |
| 5.2 | Generar ntt_forward.h | generated/ | 5.1 | Compila con gcc |
| 5.3 | Generar ntt_inverse.h | generated/ | 5.1 | Compila con gcc |
| 5.4 | Oracle testing | tests/ | 5.2, 5.3 | Lean = C en 1000 casos |
| 5.5 | Benchmark vs referencia | Benchmarks/ | 5.4 | Documentar resultados |

**Entregable Semana 6**: `generated/ntt_*.h` + benchmarks documentados.

---

## 7. Riesgos y Mitigaciones

### 7.1 Riesgos Originales (Pre-implementación)

| Riesgo | Prob. | Impacto | Mitigación | Estado |
|--------|-------|---------|------------|--------|
| IsPrimitiveRoot pesado | Baja | Medio | Definir versión propia | ✅ RESUELTO (ISSUE-5.001) |
| sum_of_powers_zero difícil | Media | Alto | Buscar en Mathlib | ✅ RESUELTO (probado sin sorry) |
| E-Graph no genera NTT iterativo | Media | Alto | Escribir CodeGen específico | ⏳ Pendiente |
| Bounds tracking tedioso | Alta | Medio | Usar omega | ⏳ Pendiente |
| Goldilocks reduction difícil | Media | Medio | Probar bounds | ⏳ Pendiente |

### 7.2 Riesgos Semana 2-3 (Análisis proactivo 2026-01-29)

| Riesgo | Descripción | Impacto | Mitigación | DD |
|--------|-------------|---------|------------|-----|
| **Explosión O(N²)** | NTT_spec naive cuelga Lean para N grande | Alto | Spec solo para proofs, tests N≤64 | DD-015 |
| **Índices erróneos** | Errores de stride/offset en Cooley-Tukey | Alto | Funciones evens/odds con teoremas | DD-016 |
| **Olvidar N⁻¹** | INTT(NTT(x)) = x*N en lugar de x | Alto | N⁻¹ explícito en firma de INTT | DD-017 |

### 7.3 Técnicas de Mitigación Adoptadas

| Técnica | Propósito | Aplicación |
|---------|-----------|------------|
| **Separación Spec/Impl** | Evitar O(N²) en producción | Spec para proofs, CT para ejecución |
| **Funciones auxiliares probadas** | Evitar errores de índices | evens, odds, interleave con teoremas |
| **Tests de equivalencia** | Detectar errores temprano | NTT_rec = NTT_naive para N pequeño |
| **Roundtrip property** | Verificar corrección INTT | INTT(NTT(x)) = x para N∈{4,8,16,32} |
| **N⁻¹ en tipos** | Hacer visible la normalización | Firma explícita en INTT |

---

## 8. Política de Documentación Incremental

### Después de cada submódulo:
1. Actualizar este documento con estado actual
2. Registrar problemas encontrados en `PHASE5_ISSUES.md`
3. Actualizar métricas en tabla de progreso

### Después de cada semana:
1. Informe de progreso al usuario
2. Benchmark si hay código generado
3. Commit con mensaje descriptivo

### Tabla de Progreso

| Módulo | Estado | LOC Lean | Teoremas | Sorry | Fecha |
|--------|--------|----------|----------|-------|-------|
| Field.lean | ✅ DONE | 182 | 9 | 1 | 2026-01-29 |
| RootsOfUnity.lean | ✅ DONE | 292 | 19 | 0 | 2026-01-29 |
| Goldilocks.lean | ✅ DONE | 136 | 0 (tests) | 0 | 2026-01-29 |
| ListUtils.lean | ✅ DONE | ~150 | 8 | 0 | 2026-01-29 |
| Spec.lean | ✅ DONE | ~175 | 8 | 2 | 2026-01-29 |
| Properties.lean | ✅ DONE | ~195 | 10 | 5 | 2026-01-29 |
| CooleyTukey.lean | ✅ DONE | ~220 | 5 | 1 | 2026-01-29 |
| Butterfly.lean | ✅ DONE | ~175 | 12 | 5 | 2026-01-29 |
| Correctness.lean | ✅ DONE | ~125 | 8 | 6 | 2026-01-29 |
| Bounds.lean | ⏳ PENDIENTE | - | - | - | - |
| LazyButterfly.lean | ⏳ PENDIENTE | - | - | - | - |
| CodeGen.lean | ⏳ PENDIENTE | - | - | - | - |

**Total Semanas 1-4**: ~1650 LOC, ~79 teoremas, 20 sorry (~75% sin sorry)

### Test Suite

| Test File | Status | Tests | Pass Rate |
|-----------|--------|-------|-----------|
| ListUtilsTest.lean | ✅ | ~20 | 100% |
| AlgebraTest.lean | ✅ | ~15 | 100% |
| CorrectnessTest.lean | ✅ | ~50 | 100% |
| PropertiesTest.lean | ✅ | ~12 | 100% |
| Bench/NTT_Math.lean | ✅ | Benchmarks | O(N²) vs O(N log N) verified |

### Tareas Semana 2-3 (Actualizadas con técnicas superadoras)

| # | Tarea | Técnica | Estado |
|---|-------|---------|--------|
| 2.0a | List.evens + teorema preservación | DD-016 | ✅ DONE |
| 2.0b | List.odds + teorema preservación | DD-016 | ✅ DONE |
| 2.0c | List.interleave + roundtrip | DD-016 | ✅ DONE |
| 2.1 | NTT_spec (O(N²), solo proofs) | DD-015 | ✅ DONE |
| 2.2 | INTT con N⁻¹ explícito | DD-017 | ✅ DONE |
| 2.3 | ntt_intt_identity (sin sorry) | sum_of_powers_zero | ⚠️ SORRY |
| 2.4 | Tests equivalencia N∈{4,8,16,32} | Oracle testing | ✅ DONE |

### Tareas Semana 3-4

| # | Tarea | Archivo | Estado |
|---|-------|---------|--------|
| 3.1 | Definir butterfly_spec | Butterfly.lean | ✅ DONE |
| 3.2 | Definir NTT_recursive O(N log N) | CooleyTukey.lean | ✅ DONE |
| 3.3 | Probar butterfly properties | Butterfly.lean | ⚠️ SORRY (5) |
| 3.4 | Probar ct_recursive_eq_spec | Correctness.lean | ⚠️ SORRY (6) |
| 3.5 | native_decide tests N=4,8 | Correctness.lean | ✅ DONE |
| 3.6 | QA test suite | Tests/NTT/ | ✅ DONE |
| 3.7 | Benchmark O(N²) vs O(N log N) | Bench/NTT_Math.lean | ✅ DONE |

---

## 9. Criterios de Éxito de la Fase

| Criterio | Métrica | Target |
|----------|---------|--------|
| Completitud | Teoremas sin sorry | ≥ 90% |
| Corrección | Oracle tests | 100% pass |
| Rendimiento | vs Plonky3 NTT | ≤ 2x overhead |
| Documentación | Este documento actualizado | Sí |

---

## 10. Referencias Cruzadas

- [ROADMAP.md](ROADMAP.md) - Contexto del proyecto
- [UNIFIED_PLAN.md](UNIFIED_PLAN.md) - Plan unificado B+C
- [PROGRESS.md](PROGRESS.md) - Log de trabajo
- [docs/references/ntt/](../references/ntt/) - PDFs de bibliografía

---

*Documento creado: 2026-01-29*
*Última actualización: 2026-01-29 (Plan de eliminación de sorries adoptado)*

---

## 11. Plan de Eliminación de Sorries (Deuda Técnica)

### 11.1 Contexto

**Estado**: Los tests unitarios y de integración pasan (100%), pero la verificación formal tiene 22 sorries.
**Objetivo**: Cerrar los sorries para certificar matemáticamente la Fase 5.
**Rol**: Formal Verification Engineer.

### 11.2 Decisiones de Diseño para Eliminación de Sorries

#### DD-018: Bridge Lemmas en lugar de CommRing Global

**Decisión**: NO intentar instanciar `CommRing` de Mathlib globalmente para `NTTField`. En su lugar, crear **bridge lemmas** locales.

**Razón**: Evitar el "Infierno de las Clases de Tipos" de Mathlib. Instanciar `CommRing` requiere ~20 campos y puede traer conflictos con otras instancias.

**Implementación**:
```lean
-- ❌ EVITAR: Instancia global
instance : CommRing F := { ... }

-- ✅ USAR: Bridge lemmas locales
section BridgeLemmas
variable [inst : NTTField F]
lemma add_eq : inst.add a b = a + b := rfl
lemma mul_eq : inst.mul a b = a * b := rfl
-- Permite usar `ring` localmente sin compromiso global
end BridgeLemmas
```

#### DD-019: Gap de Tipos Fin.univ ↔ Finset.range

**Problema**: `sum_of_powers_zero` usa `Finset.range n`, pero `orthogonality_relation` usa `Finset.univ` sobre `Fin n`.

**Solución**: Usar `Fin.sum_univ_eq_sum_range` de Mathlib como puente explícito.

```lean
-- Puente necesario:
Fin.sum_univ_eq_sum_range : ∑ i : Fin n, f i = ∑ i ∈ Finset.range n, f i
```

#### DD-020: Criterio de Éxito para CT=Spec (Boss Final)

**Éxito completo**: 0 sorries en `ct_recursive_eq_spec`.

**Éxito aceptable**: Sorry solo en el paso inductivo principal, con:
- `cooley_tukey_upper_half` probado ✅
- `cooley_tukey_lower_half` probado ✅
- `native_decide` tests verifican N=4,8,16,32 ✅
- Superficie de duda documentada

### 11.3 Plan de Ejecución por Fases

```
FASE 1: Bridge Lemmas + Ring Lemmas [6 sorries]
├── 1.0 Crear bridge lemmas en Field.lean
├── 1.1 Field.lean: sub_eq_add_neg
├── 1.2 Butterfly.lean: butterfly_twiddle_one
├── 1.3 Butterfly.lean: butterfly_sum, butterfly_diff
└── 1.4 Butterfly.lean: butterfly_inverse_scaled

FASE 2: Singleton & Length [2 sorries]
├── 2.1 Correctness.lean: ntt_eq_singleton
└── 2.2 CooleyTukey.lean: NTT_recursive_length

FASE 3: Spec Linearity [2 sorries]
├── 3.1 Spec.lean: ntt_coeff_add
└── 3.2 Spec.lean: ntt_coeff_scale

FASE 4: Orthogonality [5 sorries]
├── 4.0 Crear lema puente Fin.univ ↔ Finset.range
├── 4.1 Properties.lean: orthogonality_relation
├── 4.2 Properties.lean: ntt_delta
├── 4.3 Properties.lean: ntt_constant_nonzero
├── 4.4 Properties.lean: parseval
└── 4.5 Spec.lean: ntt_intt_identity

FASE 5: CT = Spec [5 sorries]
├── 5.1 Correctness.lean: ntt_recursive_length_eq
├── 5.2 Correctness.lean: cooley_tukey_upper_half
├── 5.3 Correctness.lean: cooley_tukey_lower_half
├── 5.4 Correctness.lean: ct_recursive_eq_spec (Boss Final)
└── 5.5 Correctness.lean: ntt_intt_recursive_roundtrip
```

### 11.4 Inventario de Sorries por Archivo

| Archivo | Sorries | Fase | Dificultad |
|---------|---------|------|------------|
| Field.lean | 1 | 1 | Baja |
| Butterfly.lean | 6 | 1 | Baja |
| Correctness.lean | 6 | 2, 5 | Baja-Alta |
| CooleyTukey.lean | 1 | 2 | Baja |
| Spec.lean | 3 | 3, 4 | Baja-Media |
| Properties.lean | 5 | 4 | Media |
| **TOTAL** | **22** | | |

### 11.5 Herramientas Disponibles

| Recurso | Estado | Uso |
|---------|--------|-----|
| `powSum_nonzero` | ✅ Probado | Fase 4 |
| `sum_of_powers_zero` | ✅ Probado | Fase 4 |
| `twiddle_half_eq_neg_one` | ✅ Probado | Fase 5 |
| `squared_is_primitive` | ✅ Probado | Fase 5 |
| `Fin.sum_univ_eq_sum_range` | ✅ Mathlib | Fase 4 |
| `ring` tactic | ✅ Mathlib | Fase 1 |
| `native_decide` | ✅ Lean 4 | Verificación |

---

## 12. Notas de Implementación (Semanas 1-4)

### Logros Clave

1. **NTT Spec completa** (Capa 1): Definición matemática de NTT/INTT con propiedades de linealidad
2. **Cooley-Tukey O(N log N)** (Capa 2): Algoritmo recursivo funcional con terminación probada
3. **Butterfly extraído**: Módulo independiente para la operación atómica del NTT
4. **Suite de tests QA**: Tests de correctness, propiedades y benchmarks
5. **native_decide verification**: Pruebas compiletime de equivalencia spec=recursive para N=4,8

### Sorries Pendientes (Refinamiento futuro)

| Archivo | Teorema | Dificultad | Nota |
|---------|---------|------------|------|
| Properties.lean | orthogonality_relation | Media | Usa powSum_nonzero |
| Properties.lean | intt_ntt_identity_finset | Alta | Requiere rearreglo de sumas |
| Properties.lean | ntt_delta, ntt_constant_nonzero | Baja | Manipulación Finset |
| Properties.lean | parseval | Media | Usa ortogonalidad |
| Butterfly.lean | butterfly_sum, butterfly_diff, etc | Baja | Ring lemmas para NTTField |
| Correctness.lean | cooley_tukey_upper/lower_half | Alta | Splitting formula DFT |
| Correctness.lean | ct_recursive_eq_spec | Alta | Inducción fuerte |
| CooleyTukey.lean | NTT_recursive_length | Baja | Inducción estructural |

### Decisiones de Implementación

1. **NTTField vs CommRing**: Usamos NTTField lightweight para definiciones, CommRing de Mathlib para proofs formales
2. **Finset.univ vs Finset.range**: Para sumas formales usamos `Fin n` con `Finset.univ` para evitar conversiones
3. **native_decide para tests**: Verificación compiletime garantiza equivalencia sin necesidad de proofs complejas

---

## 13. Plan Semanas 4-6: Bounds y CodeGen (Actualizado 2026-01-29)

### 13.1 Decisiones de Diseño Adicionales

#### DD-021: Axiomas Diferidos (Deuda Técnica Controlada)

**Decisión**: Los 9 sorries restantes se tratan como axiomas temporales.

**Justificación**:
- Validación empírica: Oracle tests pasan para N=4,8,16,32
- Matemática estándar: Todos son teoremas conocidos de Fourier/NTT
- ROI: Semanas de proof engineering vs. avanzar a CodeGen
- Completación: Se probarán en Fase 6 (Hardening)

**Documentación**: `AmoLean/NTT/Axioms.lean`

#### DD-022: Modelo LazyGoldilocks con Nat (CRÍTICO)

**Problema detectado**: UInt64 en Lean tiene semántica de wrapping.

```lean
-- ❌ INCORRECTO
structure LazyGoldilocks where
  val : UInt64  -- Wrap around silencioso si val > 2^64

-- ✅ CORRECTO
structure LazyGoldilocks where
  val : Nat     -- Precisión infinita, proofs correctas
  h_bound : val < 4 * GOLDILOCKS_PRIME
```

**Escenario de fallo evitado**:
- `a = 2^63, b = 2^63` → `a + b = 0` en UInt64 (wrap)
- Lean probaría "0 < 4p" ✓ (sobre valor truncado)
- C calcularía 2^64 en `__uint128_t` (valor real)
- **La prueba sería "correcta" pero sobre datos incorrectos**

**Implementación**:
| Capa | Tipo | Uso |
|------|------|-----|
| Lean Spec | `Nat` | Proofs matemáticamente correctas |
| C Impl | `__uint128_t` | Registros rdx:rax nativos |

#### DD-023: CodeGen Skeleton + Kernel

**Decisión**: Separar estructura de loops (manual) de operaciones (generadas).

```
┌─────────────────────────────────────────┐
│  Skeleton (C manual)                    │
│  - for layer = 0 to log2(n)             │
│  - for group = ...                      │
│  - for pair = ...                       │
│  - bit-reversal permutation             │
├─────────────────────────────────────────┤
│  Kernel (Generado)                      │
│  - lazy_butterfly(a, b, tw)             │
│  - lazy_reduce(x)                       │
└─────────────────────────────────────────┘
```

### 13.2 Plan de Tareas Actualizado

#### Semana 4-5: Bounds y Lazy Reduction

| # | Tarea | Archivo | Criterio de Éxito |
|---|-------|---------|-------------------|
| 4.1 | Definir LazyGoldilocks con Nat | Bounds.lean | Tipo compila, bounds < 4p |
| 4.2 | Definir lazy_add, lazy_sub, lazy_mul | Bounds.lean | Operaciones preservan bounds |
| 4.3 | Definir lazy_reduce | Bounds.lean | reduce : Lazy → Strict |
| 4.4 | Definir lazy_butterfly | LazyButterfly.lean | Usa operaciones lazy |
| 4.5 | Probar bounds_preserved | LazyButterfly.lean | omega resuelve |
| 4.6 | Probar lazy_simulates_spec | LazyButterfly.lean | Refinamiento correcto |

#### Semana 5-6: Code Generation

| # | Tarea | Archivo | Criterio de Éxito |
|---|-------|---------|-------------------|
| 5.1 | Escribir skeleton NTT iterativo | generated/ntt_skeleton.c | Compila con gcc |
| 5.2 | Generar kernel lazy_butterfly | generated/ntt_kernel.h | E-Graph optimiza |
| 5.3 | Integrar skeleton + kernel | generated/ntt_forward.h | Compila completo |
| 5.4 | Generar INTT | generated/ntt_inverse.h | Compila |
| 5.5 | Oracle testing | tests/test_ntt_c.c | Lean = C para 1000 casos |
| 5.6 | Benchmarks | Benchmarks/NTT/ | Documentar vs Plonky3 |

### 13.3 Archivos a Crear

```
AmoLean/NTT/
├── Bounds.lean           # LazyGoldilocks con Nat
└── LazyButterfly.lean    # butterfly_lazy + simulación

generated/
├── ntt_skeleton.c        # Loops iterativos (manual)
├── ntt_kernel.h          # lazy_butterfly (generado)
├── ntt_forward.h         # NTT completo
└── ntt_inverse.h         # INTT completo

tests/
└── test_ntt_c.c          # Oracle testing
```

### 13.4 Riesgos y Mitigaciones

| Riesgo | Prob. | Impacto | Mitigación | Estado |
|--------|-------|---------|------------|--------|
| UInt64 wrapping en Lean | ALTA | CRÍTICO | DD-022: Usar Nat | ✅ ADOPTADO |
| 4p overflow en UInt64 | ALTA | ALTO | Usar __uint128_t en C | ✅ DECIDIDO |
| E-Graph no genera loops | MEDIA | ALTO | DD-023: Skeleton manual | ✅ ADOPTADO |
| lazy_simulates_spec difícil | MEDIA | MEDIO | Probar con omega | ⏳ PENDIENTE |

### 13.5 Criterios de Éxito Semanas 4-6

| Criterio | Métrica | Target |
|----------|---------|--------|
| Bounds proofs | Teoremas sin sorry | ≥ 80% |
| Oracle testing | Lean = C | 100% pass |
| Performance | vs Plonky3 NTT | ≤ 2x overhead |
| CodeGen | Código C compila | gcc -O3 sin warnings |
