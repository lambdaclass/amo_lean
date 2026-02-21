# Insights: AMO-Lean v2.2.0 QA Follow-ups — Forward Roundtrip + Injectivity

**Fecha**: 2026-02-21
**Dominio**: lean4
**Estado del objeto**: upgrade (CONDITIONAL PASS → FULL PASS)

## 1. Análisis del Objeto de Estudio

AMO-Lean v2.2.0 está en fase de cierre con 6 findings de QA pendientes en el módulo Bridge (AmoLean/Bridge/TrustLean.lean, 342 LOC). El núcleo del trabajo es completar forward roundtrips para tipos que solo tienen backward roundtrips probados, derivar injectivity, y agregar stress testing.

### Estado actual de roundtrips

| Tipo | Backward (TL→AMO→TL) | Forward (AMO→TL→AMO) |
|------|----------------------|----------------------|
| ScalarVar | probado | probado |
| IdxExpr | probado | probado |
| Gather/Scatter | probado | probado |
| ScalarExpr | probado | **FALTA** |
| ScalarAssign | probado | **FALTA** |
| ScalarVarList | probado | **FALTA** |
| ScalarAssignList | probado | **FALTA** |
| ExpandedKernel | probado | **FALTA** |
| ExpandedSigma | probado | **FALTA** |

### Cadena de dependencias (DAG)

```
ScalarExpr forward (F6.a)
    ↓
ScalarAssign forward (F6.b) + ScalarVarList forward
    ↓
ScalarAssignList forward
    ↓
ExpandedKernel forward (F6.c)
    ↓
ExpandedSigma forward (F1) ← CRÍTICO
    ↓
convert_injective (F2) ← CRÍTICO

Paralelos (sin bloqueos):
- Stress test (F5)
- Path dependency docs (F4)
```

### Keywords

forward-roundtrip, Option.bind_eq_some, injectivity, partial-function, structural-induction, do-notation, IsPartialInv, Encodable, convert_injective, ExpandedSigma, ScalarExpr, simp-only

## 2. Lecciones Aplicables

### Lecciones reutilizables

| ID | Título | Aplicación |
|---|---|---|
| **L-359** | Injectivity requires forward roundtrip as lemma | F2 depende de F1 |
| **L-358** | Forward roundtrip harder than backward | Planificar esfuerzo correctamente |
| **L-360** | Custom recursive list conversions avoid List.mapM mismatch | Ya aplicado, mantener patrón |
| **L-243** | Generalise the induction hypothesis early | IH con estado completo para ScalarExpr/ExpandedSigma |
| **L-181** | Option.some.injEq at h | `simp only [Option.some.injEq] at h` para Option injection |
| **L-275** | Negative simp lemmas essential for Option evaluators | Forward proofs necesitan negative lemmas |
| **L-142** | Equation lemmas para unfold selectivo | `f.eq_N` para rama específica |
| **L-170** | simp only [...] at ih ⊢ — sincronizar IH | Evitar IH desincronizada con goal |
| **L-337** | Compositional correctness via helper lemmas | Factor por constructor |
| **L-340** | Zero Sorry Discipline | GATE antes de cerrar |
| **L-317** | FUNDACIONAL nodes should front-load injectivity | Injectivity PRIMERO |

### Anti-patrones a evitar

- Usar solo backward roundtrip para derivar injectivity (L-358, L-359)
- Usar List.mapM con Option en inducción — accumulator mismatch (L-360)
- `simp [*]` en proofs críticas — frágil entre versiones (L-305)
- Diferir propiedades fundacionales como debt (L-138)
- Omitir negative simp lemmas para type-mismatch (L-275)

## 3. Bibliografía Existente Relevante

### Documentos clave

- **CompCert** (Leroy et al.): Semantic preservation via simulation diagrams
- **Lean4Lean** (Carneiro 2024): Relación inductiva de traducción + Hoare monádica ligera
- **'do' Unchained** (Ullrich & de Moura, ICFP 2022): Correctitud formal del desugaring do-notation
- **Rossel et al. 2026**: Equality saturation tactic en Lean
- **Accelerating Verified-Compiler Development** (Gross et al.): NbE + PHOAS para type isomorphism

### Gaps identificados

1. Option.bind_eq_some proof patterns — parcialmente cubierto por online research
2. Partial function injectivity via roundtrip — cubierto por Mathlib `Function.IsPartialInv`
3. Type isomorphism proof automation — cubierto por `PartialEquiv` en Mathlib

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

1. **split tactic para funciones match-heavy**: `unfold f; split <;> intro v' h; ...` cierra en paralelo (Trust-Lean v1.1.0)
2. **Custom mapOption con 4 lemmas**: nil, cons, length, get — mejor que List.mapM (VR1CS v1.3)
3. **do-notation para composición Option**: más legible que Option.bind explícito (amo-lean v2.2.0)
4. **Backward como def, forward como theorem**: backward es especificación, forward es garantía (amo-lean v2.2.0)

### Benchmarks de referencia

| Proyecto | Métrica | Valor |
|----------|---------|-------|
| Trust-Lean v1.2.0 | Theorems | 179 |
| amo-lean v2.2.0 Bridge | LOC | 342 |
| amo-lean v2.2.0 Bridge | Theorems | 17 |
| VR1CS v1.3 PBT | Trials | ~2,850 |

## 5. Nueva Bibliografía Encontrada (Online)

### Hallazgos críticos

#### `Option.bind_eq_some` — Cambio en Lean 4.9
**Desde Lean 4.9, `Option.bind_eq_some` ya NO es un simp lemma.** Debe usarse explícitamente:
```lean
simp only [Option.bind_eq_some]
-- O descomponer manualmente:
obtain ⟨a, ha, hfa⟩ := h  -- si h : x.bind f = some b
```

#### `Function.IsPartialInv` — Injectivity gratis
Mathlib define `Function.IsPartialInv f g := ∀ x y, g y = some x ↔ f x = y`:
- `isPartialInv_left`: roundtrip forward (`g (f x) = some x`)
- `injective_of_isPartialInv`: injectivity gratis del roundtrip

**Alternativa**: Probar injectivity directamente sin Mathlib usando forward roundtrip como lemma.

#### `Encodable` — Modelo canónico de roundtrip
- `encodek : decode (encode a) = some a`
- `ofLeftInjection f finv linv`: construye encodabilidad desde inyección con inversa parcial
- `decode` usa `Option.bind` internamente — mismos patrones de prueba

#### `PartialEquiv` — Para bridges de tipo
Equivalencias parciales con source/target subsets + roundtrip en ambas direcciones.

### Recursos clave

- Mathlib.Logic.Function.Basic: `injective_of_isPartialInv`
- Mathlib.Data.Option.Basic: `Option.bind_eq_some`, `Option.some_injective`
- Init.Data.Option.Basic: `Option.bind_some`, `Option.bind_none` (@[simp])
- Lean 4 TPIL: Induction and Recursion chapter

## 6. Insights de Nueva Bibliografía

Sección omitida (sin descargas nuevas — solo web research).

## 7. Síntesis de Insights

### Hallazgos clave

1. **`Option.bind_eq_some` must be explicit**: No es simp lemma desde Lean 4.9. Usar `simp only [Option.bind_eq_some]` o `obtain ⟨a, ha, hfa⟩ := h`.

2. **Forward roundtrip pattern**: Para cada tipo con conversión parcial:
   ```lean
   theorem roundtrip_T_forward (x : AmoT) (x' : TLT) (h : convertT x = some x') :
       convertBackT x' = x := by
     -- (1) destruct x, (2) unfold convertT, (3) simp [Option.bind_eq_some] at h,
     -- (4) obtain components, (5) use IH on sub-terms, (6) rfl
   ```

3. **Injectivity derivation** (dos opciones):
   - **Opción A** (directa): Forward roundtrip → apply convertBack to both sides → QED
   - **Opción B** (Mathlib): Instanciar `Function.IsPartialInv` → `injective_of_isPartialInv`

4. **Dependency chain es lineal**: ScalarExpr → ScalarAssign → lists → ExpandedKernel → ExpandedSigma → Injectivity. Cada forward proof depende del anterior.

5. **Stress test con >100 expresiones**: Usar `List.replicate` o generación recursiva en `#eval`. No requiere proofs, solo `#eval`/`example`.

6. **~100-150 LOC adicionales** estimados para F1+F2+F5+F6.

### Riesgos identificados

1. **ScalarExpr recursión**: `add`, `sub`, `mul` tienen dos sub-expresiones parciales → need two `obtain` + two IH calls per case
2. **ExpandedSigma 6 constructores**: Each with different sub-conversions → proof could be ~50-60 lines
3. **do-notation opacity**: May need `show` or `change` to expose bind structure for simp

### Recomendaciones para planificación

1. Probar ScalarExpr forward FIRST como de-risk (es el tipo recursivo más simple)
2. F4 (docs) y F5 (stress test) son parallelizables con F6+F1+F2
3. No usar `Function.IsPartialInv` de Mathlib — overhead de import; derivar injectivity directamente del forward roundtrip (~5 LOC)
4. Mantener custom recursive list functions (ya definidas en Bridge)
5. Usar `simp only [Option.bind_eq_some]` explícitamente (Lean 4.26 compatible)

### Recursos prioritarios

1. **L-359**: Injectivity via forward roundtrip (proof strategy)
2. **L-181**: `Option.some.injEq at h` (tactic pattern)
3. **L-243**: Generalise IH early (induction strategy)
4. **Mathlib Option.bind_eq_some**: Explicit simp lemma for do-notation
5. **AmoLean/Bridge/TrustLean.lean lines 53-67**: Existing `roundtrip_scalarVar_forward` as template
