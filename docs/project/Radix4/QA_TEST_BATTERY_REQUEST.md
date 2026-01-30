# Solicitud de Batería de Tests - QA Review Phase

**Fecha**: 2026-01-30
**Proyecto**: NTT Radix-4 para amo-lean (Lean 4)
**Fase actual**: Transición IMPLEMENTACIÓN → BENCHMARKS
**Destinatario**: QA Senior de Ingeniería de Software

---

## Contexto

Eres un **QA Senior de Ingeniería de Software** especializado en verificación formal y sistemas criptográficos. Tu rol es diseñar una batería de tests exhaustiva para evaluar la implementación del algoritmo NTT Radix-4 en Lean 4.

### Workflow del Proyecto

```
1. PLANIFICACIÓN        ✅ Completado
2. REVISIÓN QA          ✅ Completado (tu feedback anterior incorporado)
3. BIBLIOGRAFÍA         ✅ Completado (14 papers + libro A=B)
4. REFINAMIENTO         ✅ Completado
5. QA FINAL             ✅ Completado
   ════════════════════════════════════════════════════════
   ⏸️ CHECKPOINT HUMANO  ✅ Aprobado
   ════════════════════════════════════════════════════════
6. IMPLEMENTACIÓN       ✅ COMPLETADO ← ACABAMOS DE TERMINAR
7. BENCHMARKS           🟡 ← ESTAMOS AQUÍ (necesitamos tu batería de tests)
8. RESUMEN              ⏳
```

---

## Lo que se Implementó

### Estructura de Archivos

```
AmoLean/NTT/Radix4/
├── Butterfly4.lean   -- Operación butterfly de 4 puntos
├── Stride4.lean      -- Funciones stride-4 split/interleave
├── Algorithm.lean    -- Especificación del algoritmo Radix-4
└── Equivalence.lean  -- Pruebas de equivalencia
```

### Teoremas Probados (sin sorry)

| Archivo | Teorema | Descripción |
|---------|---------|-------------|
| Stride4.lean | `stride4_0_length` ... `stride4_3_length` | Longitud de cada stride |
| Stride4.lean | `stride4_lengths` | Cuando 4\|N, cada stride tiene N/4 elementos |
| Stride4.lean | `stride4_total_length` | Las 4 partes suman N |
| Stride4.lean | `interleave4_length` | Longitud del interleave |
| Stride4.lean | `interleave4_stride4` | Roundtrip: interleave4(stride4_*) = original |
| Stride4.lean | `stride4_evens_relation`, `stride4_odds_relation` | Relación con evens/odds |
| Butterfly4.lean | `butterfly4_fst` | Primer elemento es suma total |
| Butterfly4.lean | `butterfly4_as_butterfly2_composition` | Radix-4 = 2 capas de Radix-2 |
| Butterfly4.lean | `butterfly4_with_psi_squared_neg_one` | Simplificación cuando ψ²=-1 |
| Equivalence.lean | `radix4_eq_spec` | NTT_radix4 = NTT_spec |
| Equivalence.lean | `radix2_eq_spec` | NTT_recursive = NTT_spec |
| Equivalence.lean | `radix4_eq_radix2` | NTT_radix4 = NTT_recursive |
| Equivalence.lean | `ntt_algorithm_choice` | Libertad de elección de algoritmo |

### Sorries Restantes (7 de 13 originales)

| Archivo | Teorema | Descripción | Criticidad |
|---------|---------|-------------|------------|
| Butterfly4.lean:177 | `butterfly4_ibutterfly4_identity` | Roundtrip del butterfly | Media |
| Algorithm.lean:60 | `NTT_radix4_singleton` | Caso base N=1 | Baja |
| Algorithm.lean:67 | `NTT_radix4_nil` | Caso base N=0 | Baja |
| Algorithm.lean:171 | `combineRadix4_uses_butterfly4` | Relación combine-butterfly | Media |
| Equivalence.lean:138 | `intt_radix4_eq_spec` | INTT equivalencia | Media |
| Equivalence.lean:153 | `roundtrip_any_algorithm` (1) | INTT(NTT(x))=x via spec | Alta |
| Equivalence.lean:156 | `roundtrip_any_algorithm` (2) | Propiedad del inverso | Media |

### Tests Existentes (10+ pasando)

**Butterfly4.lean**:
```
Test 1: butterfly4(1,0,0,0,ω₄) = [1,1,1,1]     ✅ DFT de delta
Test 2: butterfly4(1,1,1,1,ω₄) = [4,0,0,0]     ✅ DFT de constante
Test 3: butterfly4(1,2,3,4,ω₄) → X₀=10         ✅ Suma correcta
Test 4: ω₄² = -1                                ✅ Propiedad raíz
Test 5: ω₁₆⁴ = ω₄, ω₁₆¹⁶ = 1                   ✅ Relación raíces
```

**Algorithm.lean**:
```
Test 1: stride4 roundtrip N=16                  ✅ split+interleave=original
Test 2: combineRadix4 E=[1,1,1,1] → [4,0,0,0]  ✅ DFT constante
Test 3: combineRadix4 E0=[1], rest=0 → [1,1,1,1] ✅ DFT delta
Test 4: stride4 lengths N=64                    ✅ Cada stride=16
Test 5: combineRadix4 N=16 → |result|=16        ✅ Longitud correcta
```

**Stride4.lean**:
```
Tests de roundtrip y longitudes para N=16       ✅
```

### Decisiones de Diseño Clave

1. **Axiomatización**: `NTT_radix4` y `INTT_radix4` son axiomas (no implementación recursiva) para evitar problemas de terminación
2. **Pattern Matching**: stride4 usa pattern matching en lugar de filterMap para inducción estructural
3. **NTTField explícito**: Operaciones como `inst.add`, `inst.mul` en lugar de notación estándar
4. **Integración**: Submódulo dentro de amo-lean, reutiliza lemas de RootsOfUnity

---

## Tu Tarea

Diseña una **batería de tests exhaustiva** para evaluar esta implementación. Considera:

### 1. Corrección Funcional
- ¿Los tests actuales cubren suficientes casos?
- ¿Faltan casos edge (N=0, N=1, N no divisible por 4)?
- ¿Se verifican todas las propiedades matemáticas críticas?

### 2. Cobertura de Pruebas Formales
- ¿Los 7 sorries restantes son aceptables para un MVP?
- ¿Cuáles son críticos y cuáles pueden diferirse?
- ¿Hay teoremas importantes sin probar?

### 3. Calidad del Código
- ¿La estructura de archivos es adecuada?
- ¿Los nombres de funciones/teoremas son claros?
- ¿La documentación es suficiente?

### 4. Consistencia con el Plan
- ¿Se siguieron las decisiones de diseño aprobadas?
- ¿Se incorporó todo el feedback QA anterior?

### 5. Propiedades Matemáticas a Verificar
Para NTT Radix-4, las propiedades críticas son:
- Linealidad: NTT(a + b) = NTT(a) + NTT(b)
- Roundtrip: INTT(NTT(x)) = x
- Equivalencia: Radix4 = Radix2 = Spec
- Butterfly: T₄ · T₄⁻¹ = I

---

## Entregables Esperados

1. **Lista de tests adicionales** necesarios (con prioridad)
2. **Evaluación de sorries**: cuáles cerrar ahora vs diferir
3. **Checklist de aceptación** para pasar a fase de benchmarks
4. **Riesgos identificados** y mitigaciones
5. **Recomendaciones** para mejorar la calidad

---

## Información Adicional

- **Campo usado**: GoldilocksField (p = 2⁶⁴ - 2³² + 1)
- **Raíces de unidad**: `primitiveRoot n` genera ω con ωⁿ = 1
- **Mathlib**: Se usan lemas de `IsPrimitiveRoot`, `geom_sum`
- **Build**: `lake build` pasa sin errores

---

Por favor, proporciona tu análisis estructurado como QA Senior. Tu feedback será incorporado antes de pasar a la fase de benchmarks formales.
