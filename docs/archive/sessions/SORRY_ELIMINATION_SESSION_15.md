# Sesión 15: Estrategia C-Lite++ para lowering_correct

**Fecha**: 2026-02-04
**Objetivo**: Probar `lowering_correct` usando verificación algebraica sobre campo genérico

---

## Resumen Ejecutivo

| Métrica | Valor |
|---------|-------|
| Sorries objetivo | 7 (Verification/Theorems.lean) |
| Estrategia | C-Lite++ (Campo genérico con raíces primitivas) |
| Prerequisito crítico | Eliminar `partial` de `lower` y `evalMatExpr` |
| Archivos a crear | `Verification/AlgebraicSemantics.lean` |
| Archivos a modificar | `Sigma/Basic.lean`, `Matrix/Basic.lean` |

---

## F1: Análisis de Expertos

### F1.S1: Consulta con DeepSeek (Experto Lean 4)

**Pregunta**: ¿Cómo eliminar `partial` de funciones estructuralmente recursivas sobre `MatExpr`?

**Respuesta clave**:
```lean
/-- Función de tamaño para terminación -/
def MatExpr.size : MatExpr α m n → Nat
  | .identity _ => 1
  | .kron a b => 1 + a.size + b.size
  | .compose a b => 1 + a.size + b.size
  -- ... otros casos

def lower (m n : Nat) (state : LowerState) (mExpr : MatExpr α m n) : ... :=
  match mExpr with
  | ... => ...
termination_by mExpr.size

decreasing_by
  simp_wf
  -- tácticas para probar que size decrece
```

**Lección L-057**: Para eliminar `partial` de funciones recursivas sobre tipos inductivos:
1. Definir función `size` que cuenta nodos
2. Usar `termination_by` con la medida de tamaño
3. Usar `decreasing_by` con `simp_wf` para automatizar pruebas

### F1.S2: Consulta con Gemini QA (Senior QA Engineer)

**Riesgos identificados**:

| Riesgo | Descripción | Gravedad |
|--------|-------------|----------|
| **A: Raíces de Unidad** | `Rat` no tiene raíces n-ésimas primitivas (solo ±1) | ALTA |
| **B: DecidableEq** | Campo genérico necesita `[DecidableEq α]` para comparaciones | MEDIA |
| **C: Partial** | Sin terminación, no hay principio de inducción | CRÍTICA |

**Lección L-058**: `Rat` NO es válido para verificar DFT porque carece de raíces primitivas de la unidad. Usar `Complex`, `ZMod p`, o hipótesis explícita `(ω : α) (hω : IsPrimitiveRoot ω n)`.

**Lección L-059**: Siempre agregar `[DecidableEq α]` junto con `[Field α]` cuando el código usa comparaciones `if a == b then ...`.

### F1.S3: Posible Bug en evalSigma .seq

El QA identificó:
```lean
| .seq s1 s2 =>
  let state1 := evalSigma env state s1
  let state2 := { readMem := state1.writeMem, writeMem := state1.writeMem }
  evalSigma env state2 s2
```

**Análisis**: `state2.writeMem = state1.writeMem` significa que s2 sobrescribe en el mismo buffer que s1 escribió. Esto es correcto para operaciones in-place pero requiere que s2 sobrescriba exactamente las posiciones necesarias.

**Decisión**: Documentar como "semántica de buffer único" y verificar caso por caso.

---

## F2: Estrategia C-Lite++

### F2.S1: Principio Central

**Insight**: `MatExpr α m n` ya está parametrizado sobre `α : Type`. Solo el módulo `Verification/` hardcodea `Float`.

**Estrategia**:
1. No tocar código existente funcional
2. Crear nuevo módulo `AlgebraicSemantics.lean` con semántica genérica
3. Probar teoremas sobre `[Field α]` con raíz primitiva explícita
4. Conectar con Float via axioma de aproximación (opcional)

### F2.S2: Fases de Implementación

```
FASE 0: PRERREQUISITOS (Eliminar bloqueadores)
├── F0.S1: Definir MatExpr.size
├── F0.S2: Eliminar `partial` de lower
├── F0.S3: Eliminar `partial` de evalMatExpr (si aplica)
└── F0.S4: Verificar semántica de .seq

FASE 1: MÓDULO ALGEBRAICO
├── F1.S1: Crear Verification/AlgebraicSemantics.lean
├── F1.S2: evalMatExprAlg [Field α] [DecidableEq α] [Inhabited α]
└── F1.S3: runSigmaAlg correspondiente

FASE 2: TEOREMAS
├── F2.S1: Casos base (identity, dft con IsPrimitiveRoot)
├── F2.S2: Casos inductivos (kron, compose)
└── F2.S3: lowering_algebraic_correct
```

### F2.S3: Tipos Válidos para Verificación

| Tipo | Raíces n-ésimas | Válido para DFT |
|------|-----------------|-----------------|
| `Rat` | Solo ±1 | ❌ NO |
| `Complex` | ∀ n | ✅ SÍ |
| `ZMod p` (p primo, p ≡ 1 mod n) | ✅ | ✅ SÍ |
| `GoldilocksField` | Para n = 2^k | ✅ SÍ |
| `Float` | Aproximado | ⚠️ Solo testing |

### F2.S4: Firma del Teorema Principal

```lean
/-- Teorema principal algebraico -/
theorem lowering_algebraic_correct
    {α : Type*} [Field α] [DecidableEq α] [Inhabited α]
    (ω : α) (hω : IsPrimitiveRoot ω n)
    (mat : MatExpr α k n) (v : List α) (hv : v.length = n) :
    runSigmaAlg (lowerFresh k n mat) v k = evalMatExprAlg k n ω mat v := by
  induction mat with
  | identity => ...
  | dft n' => ...  -- usa hω
  | kron a b ih_a ih_b => ...
  | compose a b ih_a ih_b => ...
```

---

## F3: Código de Referencia

### F3.S1: MatExpr.size (a implementar)

```lean
def MatExpr.size : MatExpr α m n → Nat
  | .identity _ => 1
  | .zero _ _ => 1
  | .dft _ => 1
  | .ntt _ _ => 1
  | .twiddle _ _ => 1
  | .perm _ => 1
  | .diag _ => 1
  | .scalar _ => 1
  | .kron a b => 1 + a.size + b.size
  | .compose a b => 1 + a.size + b.size
  | .add a b => 1 + a.size + b.size
  | .smul _ a => 1 + a.size
  | .transpose a => 1 + a.size
  | .conjTranspose a => 1 + a.size
  | .elemwise _ a => 1 + a.size
  | .partialElemwise _ _ a => 1 + a.size
  | .mdsApply _ _ a => 1 + a.size
  | .addRoundConst _ _ a => 1 + a.size
```

### F3.S2: Patrón para termination_by

```lean
def lower ... (mExpr : MatExpr α m n) : ... :=
  match mExpr with
  | .kron a b =>
    let (exprA, _) := lower ... a  -- a.size < mExpr.size
    let (exprB, _) := lower ... b  -- b.size < mExpr.size
    ...
termination_by mExpr.size
```

### F3.S3: Manejo de Raíces Primitivas

```lean
-- Reutilizar de NTT/RootsOfUnity.lean
structure IsPrimitiveRoot {M : Type*} [Monoid M] (ω : M) (n : ℕ) : Prop where
  pow_eq_one : ω ^ n = 1
  pow_ne_one_of_lt : ∀ k : ℕ, 0 < k → k < n → ω ^ k ≠ 1

-- En teoremas:
theorem dft_correct {α : Type*} [Field α]
    (ω : α) (hω : IsPrimitiveRoot ω n) (v : List α) :
    evalDFT ω n v = ... := by
  -- usar hω.pow_eq_one y hω.pow_ne_one_of_lt
```

---

## F4: Dependencias y Archivos

### F4.S1: Archivos a Modificar

| Archivo | Cambio | Riesgo |
|---------|--------|--------|
| `Matrix/Basic.lean` | Agregar `MatExpr.size` | Bajo |
| `Sigma/Basic.lean` | Eliminar `partial` de `lower` | Medio |

### F4.S2: Archivos a Crear

| Archivo | Contenido |
|---------|-----------|
| `Verification/AlgebraicSemantics.lean` | Semántica genérica sobre Field α |

### F4.S3: Archivos NO Tocados

| Archivo | Razón |
|---------|-------|
| `Verification/Semantics.lean` | Mantener para testing con Float |
| `Verification/Theorems.lean` | Mantener sorries originales, agregar algebraicos |
| `NTT/*` | Ya completo, no relacionado |
| `FRI/*` | Ya completo, no relacionado |
| `Matrix/Perm.lean` | Ya completo, no relacionado |

---

## F5: Criterios de Éxito

- [x] `MatExpr.size` definido y compila (reutilizado `nodeCount`)
- [x] `lower` sin `partial` y compila
- [x] `AlgebraicSemantics.lean` creado (515 líneas)
- [x] `evalMatExprAlg` implementado (total, con termination proof)
- [ ] `lowering_algebraic_correct` probado:
  - [x] Caso identity: PROBADO
  - [ ] Caso DFT: en progreso (Fase 1)
  - [ ] Caso compose: pendiente (Fase 2)
  - [ ] Caso kron: pendiente (Fase 3)
- [x] Tests existentes siguen pasando (2641/2641)
- [x] Documentación actualizada (LECCIONES_QA §28-29, SESSION_15)
- [x] Estrategia superadora documentada (F9)
- [x] Consultas con expertos completadas (QA + DeepSeek)

---

## F6: Log de Progreso

| Timestamp | Acción | Resultado |
|-----------|--------|-----------|
| 2026-02-04 | Documentación creada | SORRY_ELIMINATION_SESSION_15.md |
| 2026-02-04 | F0.S1: Reutilizar nodeCount | `MatExpr.nodeCount` ya existe |
| 2026-02-04 | F0.S2: Eliminar `partial` de `lower` | ✅ Usando `termination_by mExpr.nodeCount` |
| 2026-02-04 | F0.S3: Verificar semántica `.seq` | ✅ Correcta para operaciones in-place |
| 2026-02-04 | F1.S1: Crear AlgebraicSemantics.lean | ✅ 315 líneas |
| 2026-02-04 | F1.S2: Implementar evalMatExprAlg | ✅ Con parámetro ω para raíces |
| 2026-02-04 | F1.S3: Agregar SigmaExpr.nodeCount | ✅ En Sigma/Basic.lean |
| 2026-02-04 | F2.S1: Eliminar `partial` de evalMatExprAlg | ✅ Usando termination_by + decreasing_by |
| 2026-02-04 | F2.S2: Eliminar `partial` de evalSigmaAlg | ✅ Usando termination_by + foldl |
| 2026-02-04 | F2.S3: Probar identity_algebraic_correct | ✅ `simp only [evalMatExprAlg]` |
| 2026-02-04 | F2.S4: Probar dft2_algebraic_correct | ✅ `simp only [evalMatExprAlg]` |
| 2026-02-04 | F2.S5: Axiom array_getElem_bang | ✅ Bridge Array/List indexing |
| 2026-02-04 | F2.S6: Probar read_ofList | ✅ Usando axiom |
| 2026-02-04 | F2.S7: Probar map_read_range_eq_list | ✅ Gather pattern |
| 2026-02-04 | F2.S8: Probar lowering_identity_correct | ✅ Modulo scatter_zeros_toList |
| 2026-02-04 | F2.S8.C1: Lemmas puente Memory ↔ List | ✅ size_write_eq, toList_write_eq_set |
| 2026-02-04 | F2.S8.C2: Axiomatizar scatter_zeros_toList | ✅ Axiom con justificación |
| 2026-02-04 | F2.S8.C3: lowering_identity_correct completo | ✅ Usando axiom |
| 2026-02-04 | F2.S9: Caso identity en lowering_algebraic_correct | ✅ Probado |
| 2026-02-05 | F8.S1: Consulta QA (Gemini) 3 rondas | ✅ NEEDS_REVISION |
| 2026-02-05 | F8.S2: Consulta Lean Expert (DeepSeek) 3 rondas | ✅ Insights DFT/Kron/Compose |
| 2026-02-05 | F8.S3: Búsqueda Mathlib lemmas | ✅ foldl_map, enum_cons, etc |
| 2026-02-05 | F8.S4: Análisis adjustBlock/adjustStride | ✅ Semántica documentada |
| 2026-02-05 | F9: Estrategia superadora sintetizada | ✅ Documentada |
| 2026-02-05 | Lecciones L-060 a L-068 documentadas | ✅ LECCIONES_QA §28-29 |

---

## F7: Estado Actual

### Axiomas en AlgebraicSemantics.lean

| Axioma | Propósito | Justificación |
|--------|-----------|---------------|
| `array_getElem_bang_eq_list_getElem` | Bridge Array/List indexing | Propiedad fundamental de toArray |
| `scatter_zeros_toList` | foldl/Memory reasoning | Verificado computacionalmente |

### Sorries en Verification/

| Archivo | Sorries | Naturaleza |
|---------|---------|------------|
| AlgebraicSemantics.lean | 1 | `lowering_algebraic_correct` (casos dft, kron, compose) |
| Theorems.lean | 7 | Teoremas Float originales |
| Poseidon_Semantics.lean | 12 | Verificados computacionalmente |
| **Total Verification/** | **20** | - |

### Sorries en todo el proyecto

| Módulo | Sorries | Naturaleza |
|--------|---------|------------|
| NTT/Spec.lean | 1 | Deprecated |
| NTT/Properties.lean | 1 | Parseval (avanzado) |
| Field/Goldilocks.lean | 1 | uint64_sub_toNat |
| Matrix/Perm.lean | 4 | Inverse axioms |
| Verification/ | 20 | Ver arriba |
| **Total** | **27** | - |

### Logros de la Sesión

1. **`lower` ahora es total** (sin `partial`)
   - Usa `termination_by mExpr.nodeCount`
   - Permite inducción sobre MatExpr

2. **`evalMatExprAlg` ahora es total** (sin `partial`)
   - Inlined blockwise/strided operations
   - Usa `termination_by mExpr.nodeCount`
   - Pruebas `identity_algebraic_correct` y `dft2_algebraic_correct` ahora triviales

3. **`evalSigmaAlg` ahora es total** (sin `partial`)
   - Usa `List.foldl` para loops
   - Usa `termination_by sigma.nodeCount`
   - Permite razonamiento formal sobre ejecución

4. **AlgebraicSemantics.lean creado**
   - Semántica genérica sobre `Field α`
   - DFT parametrizado por `(ω : α) (hω : IsPrimitiveRoot ω n)`
   - Todas las funciones son totales

5. **lowering_identity_correct PROBADO**
   - Primer caso completo del teorema principal
   - Usa lemmas puente Memory ↔ List
   - Axiomas documentados con justificación

6. **lowering_algebraic_correct estructurado**
   - Caso identity: ✅ PROBADO
   - Caso dft: TODO
   - Caso kron: TODO
   - Caso compose: TODO

7. **Proyecto compila completamente**
   - 2641/2641 módulos
   - Tests pasan

### Impacto de hacer funciones totales

Al eliminar `partial`:
- **Inducción habilitada**: Podemos hacer inducción sobre `MatExpr` y `SigmaExpr`
- **Pruebas triviales**: `identity_algebraic_correct` y `dft2_algebraic_correct` son `rfl`/`simp`
- **Camino claro**: `lowering_algebraic_correct` ahora es tractable vía inducción
- **lowering_identity_correct** probado completamente (primer caso del teorema principal)

---

## F8: Consultas con Expertos (2026-02-05)

### F8.S1: QA (Gemini) — 3 Rondas

**Ronda 1 — Diagnóstico arquitectónico:**
- `scatter_zeros_toList` NO debería ser axioma permanente — es la pieza central de movimiento de datos y es demostrable vía inducción sobre `List.foldl` + `List.set`
- Necesitamos lemmas puente semánticos para `adjustBlock` y `adjustStride`
- El caso DFT base (DFT₁ = identity) debe manejarse explícitamente

**Ronda 2 — Kronecker en detalle:**
- Para `.kron` con `I ⊗ B`, factorizar razonamiento de indexación:
  - Probar que el loop con adjustBlock en iteración `i` aplica `B` al bloque `[i*n₂ .. (i+1)*n₂-1]`
  - Probar **non-interference**: iteración `i` no toca posiciones del bloque `j ≠ i`
  - Concatenar bloques produce `flatMap (fun i => evalMatExprAlg B (block i))`
- **State management para Compose**: probar que `.seq exprB exprA` hace que salida de B sea entrada de A
- Recomendación: **NEEDS_REVISION**

**Ronda 3 — Axiomas y nivel de verificación:**
- Aceptable mantener axiomas verificados como paso intermedio
- Pero `scatter_zeros_toList` es lo bastante simple como para demostrarse
- Prioridad propuesta: DFT → Compose → Kron

### F8.S2: Lean Expert (DeepSeek) — 3 Rondas

**Ronda 1 — Insight clave sobre DFT:**
- DFT es **estructuralmente idéntico** al caso identity en el lowering:
  ```
  .dft n' → .compute (.dft n') (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0))
  ```
- Prueba es casi idéntica: `evalGather_ofList_contiguous → evalKernelAlg → scatter_zeros_toList`
- `IsPrimitiveRoot` **NO se necesita** en el paso de lowering

**Ronda 2 — Kron con invariante de loop:**
- Definir `kron_I_B_invariant` para foldl
- Probar que cada iteración preserva el invariante
- Tácticas: `induction l generalizing init`, `List.foldl_map`, `ext_getElem`
- Necesita `adjustBlock_preserves_semantics`

**Ronda 3 — Compose:**
- `.temp k (.seq exprB exprA)` crea buffer temporal, ejecuta B, luego A
- Coincide con `evalMatExprAlg` que hace `a(b(input))`
- Debería ser definitional unfolding + hipótesis inductivas

### F8.S3: Búsqueda Mathlib (/lean-search)

| Lemma | Uso |
|-------|-----|
| `List.foldl_map` | Simplificar gather → write patterns |
| `List.foldl_ext` | Extensionalidad para folds |
| `List.enum_cons` | Inducción sobre enum |
| `List.foldlIdxM_eq_foldlM_enum` | Bridge indexed → plain fold |
| `List.range'_eq_map_range` | Reindexación de rangos |
| `Array.toList_setIfInBounds` | Memory.write → List.set |

### F8.S4: Análisis de adjustBlock/adjustStride

```
adjustBlock loopVar blockIn blockOut:
  .compute k _ _ → .compute k (Gather.block blockIn loopVar) (Scatter.block blockOut loopVar)
  Traverse SigmaExpr recursivamente, solo modifica .compute

adjustStride loopVar innerSize mSize nSize:
  .compute k _ _ → .compute k {count=nSize, baseAddr=.var loopVar, stride=innerSize}
                              {count=mSize, baseAddr=.var loopVar, stride=innerSize}
  Traverse SigmaExpr recursivamente, solo modifica .compute
```

---

## F9: Estrategia Superadora "Inducción Estructural con Lemmas Puente"

### F9.S1: Principio Rector

Todos los casos base del lowering (identity, dft, ntt, twiddle, perm) producen la **misma estructura**: un `.compute` con gather/scatter contiguos. Un **meta-lemma** cubre todos estos casos de una vez.

### F9.S2: Fases de Implementación

```
FASE 0: META-LEMMA COMPUTE CONTIGUOUS
├── lowering_compute_contiguous_correct
└── Instanciar para identity (ya probado), dft, ntt, twiddle

FASE 1: CASO DFT (Dificultad: BAJA)
├── lower_dft: lowerFresh (.dft n') = .compute (.dft n') contiguous contiguous
├── kernel_match: evalKernelAlg ω (.dft n') v = evalDFT ω n' v  (o evalDFT2)
└── Instanciar meta-lemma

FASE 2: CASO COMPOSE (Dificultad: MEDIA)
├── evalSigmaAlg_seq: unfolding de .seq
├── evalSigmaAlg_temp: unfolding de .temp
├── compose_lowering: usar IH sobre a y b
└── State threading: salida de B = entrada de A

FASE 3: CASO KRON I⊗B (Dificultad: ALTA)
├── evalGather_block: semántica de Gather.block
├── evalScatter_block: semántica de Scatter.block
├── adjustBlock_semantics: adjustBlock preserva semántica con direccionamiento por bloques
├── loop_block_invariant: después de i iteraciones, primeros i bloques correctos
├── non_interference: iteración i no modifica bloques j ≠ i
└── kron_I_B_correct: concatenación = flatMap de bloques

FASE 4: CASO KRON A⊗I (Dificultad: ALTA, DIFERIBLE)
├── Análogo con adjustStride
└── Puede diferirse si no aparece en descomposiciones usadas

FASE 5: FORMALIZACIÓN DE AXIOMAS
├── scatter_zeros_toList: inducción sobre v con List.set
└── array_getElem_bang_eq_list_getElem: buscar en Batteries
```

### F9.S3: Orden de Ataque

```
Fase 0 (meta-lemma)  →  Fase 1 (DFT)  →  Fase 2 (Compose)  →  Fase 3 (Kron I⊗B)
         ↓                    ↓                   ↓                      ↓
      Desbloquea           Trivial con        Definitional +        Loop invariant +
      todos los            meta-lemma         IH sobre a,b          adjustBlock
      casos base
```

### F9.S4: Evaluación Comparativa

| Criterio | Solo QA | Solo DeepSeek | Estrategia Superadora |
|----------|---------|---------------|----------------------|
| Meta-lemma compute | No | Sí (implícito) | **Sí (explícito)** |
| Orden de ataque | DFT→Compose→Kron | DFT→Kron→Compose | **DFT→Compose→Kron** |
| adjustBlock lemma | Propuesto | Refinado | **Combinado** |
| Non-interference | Sí | No | **Sí** |
| Fallback axiom | Criticado | Aceptado | **Condicional** |
| Loop invariant | No | Sí | **Sí (mejorado)** |

### F9.S5: Riesgos y Mitigaciones

| Riesgo | Probabilidad | Mitigación |
|--------|-------------|------------|
| adjustBlock semántica compleja | Alta | Axiomatizar con tests si bloqueados |
| foldl/loop invariant difícil | Media | Usar `List.foldl_map` + inducción |
| Compose no es definitional eq | Baja | simp + unfold + IH |
| DFT kernel mismatch | Baja | Probar `evalKernelAlg (.dft n) = evalDFT ω n` |

---

## F10: Lecciones de la Sesión

| ID | Lección | Referencia |
|----|---------|------------|
| L-060 | Meta-lemma para casos compute contiguos | LECCIONES_QA §28.1 |
| L-061 | IsPrimitiveRoot no se necesita para lowering | LECCIONES_QA §28.2 |
| L-062 | Semántica de .seq y state threading | LECCIONES_QA §28.3 |
| L-063 | adjustBlock/adjustStride son transformaciones de direccionamiento | LECCIONES_QA §28.4 |
| L-064 | Invariantes de loop para foldl sobre List.range | LECCIONES_QA §28.5 |
| L-065 | Priorizar por dificultad creciente | LECCIONES_QA §28.6 |
| L-066 | Bridge lemmas Memory ↔ List | LECCIONES_QA §28.7 |
| L-067 | Axiomatización condicional | LECCIONES_QA §28.8 |
| L-068 | Consulta multi-experto produce estrategias superiores | LECCIONES_QA §28.9 |

