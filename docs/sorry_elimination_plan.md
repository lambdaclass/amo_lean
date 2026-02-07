# Sorry Elimination Plan: AlgebraicSemantics.lean

**Proyecto**: amo-lean
**Archivo**: `AmoLean/Verification/AlgebraicSemantics.lean`
**Fecha de creacion**: 2026-02-07
**Ultima actualizacion**: 2026-02-07
**Estado**: Fase 2 Correccion 3 - Teoremas _fresh implementados

---

## Resumen Ejecutivo

| Metrica | Valor |
|---------|-------|
| Sorries en declaraciones | 13 |
| Teoremas _fresh completados | 2 (adjustBlock_alpha_fresh, adjustStride_alpha_fresh) |
| Sorries path kron | 1 (evalSigmaAlg_lower_state_irrelevant.kron - pendiente lower_loopVars_bounded) |
| Sorries otros paths | 12 (transpose, compose, length analysis, writeMem irrelevance) |
| Build status | Compila sin errores |
| @[simp] lemmas en Basic.lean | 4 (lower_identity, lower_zero, lower_dft, lower_ntt) |

---

## Trabajo Completado: Fase 2 Correccion 2

### Subfase 1: Infraestructura adjustStride ✓

Implementados teoremas analogos a adjustBlock para patrones stride (A ⊗ I):

```lean
-- Linea 276
theorem adjustStride_fv_subset (v : LoopVar) (innerSize mSize nSize : Nat) (expr : SigmaExpr) :
    SigmaExpr.fv (adjustStride v innerSize mSize nSize expr) ⊆ {v}

-- Linea 299
theorem adjustStride_fresh (v w : LoopVar) (innerSize mSize nSize : Nat) (expr : SigmaExpr)
    (hw : w ≠ v) : w ∉ SigmaExpr.fv (adjustStride v innerSize mSize nSize expr)

-- Linea 336
theorem adjustStride_loopVarsOf (v : LoopVar) (innerSize mSize nSize : Nat) (expr : SigmaExpr) :
    SigmaExpr.loopVarsOf (adjustStride v innerSize mSize nSize expr) = SigmaExpr.loopVarsOf expr
```

### Subfase 2: adjustBlock_alpha_fresh - COMPLETADO ✓

Implementado teorema con precondicion de freshness explicita:

```lean
-- Linea 698 (AlgebraicSemantics.lean)
theorem adjustBlock_alpha_fresh (ω : α) (v1 v2 : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr)
    (env : LoopEnv) (st : EvalState α) (i : Nat)
    (hfresh : ∀ w ∈ SigmaExpr.loopVarsOf expr, w ≠ v1 ∧ w ≠ v2) :
    evalSigmaAlg ω (env.bind v1 i) st (adjustBlock v1 n_in n_out expr) =
    evalSigmaAlg ω (env.bind v2 i) st (adjustBlock v2 n_in n_out expr)
-- CERRADO: Todos los casos incluyendo loop
```

Caso loop cerrado usando:
1. `Finset.mem_union_left` para mostrar `loopVar ∈ loopVarsOf (.loop n loopVar body)`
2. `LoopEnv.bind_comm` para reordenar bindings una vez que tenemos `loopVar ≠ v1/v2`
3. IH aplicado con freshness derivada del body

### Subfase 2b: adjustStride_alpha_fresh - COMPLETADO ✓

```lean
-- Linea 864 (AlgebraicSemantics.lean)
theorem adjustStride_alpha_fresh (ω : α) (v1 v2 : LoopVar) (innerSize mSize nSize : Nat)
    (expr : SigmaExpr) (env : LoopEnv) (st : EvalState α) (i : Nat)
    (hfresh : ∀ w ∈ SigmaExpr.loopVarsOf expr, w ≠ v1 ∧ w ≠ v2) :
    evalSigmaAlg ω (env.bind v1 i) st (adjustStride v1 innerSize mSize nSize expr) =
    evalSigmaAlg ω (env.bind v2 i) st (adjustStride v2 innerSize mSize nSize expr)
-- CERRADO: Misma estructura que adjustBlock_alpha_fresh
```

**Insight clave**: Los teoremas _fresh estan completamente probados. Para usarlos en el caso kron, se necesita `lower_loopVars_bounded` que demuestra que todos los loopVars generados por lower son >= nextLoopVar.

### Subfase 3: adjustBlock_preserves_eval ✓

Documentado que requiere `SameStructure` para prueba completa:

```lean
theorem adjustBlock_preserves_eval (ω : α) (v : LoopVar) (n_in n_out : Nat)
    (expr1 expr2 : SigmaExpr) (env : LoopEnv) (st : EvalState α)
    (h : ∀ env' st', evalSigmaAlg ω env' st' expr1 = evalSigmaAlg ω env' st' expr2) :
    evalSigmaAlg ω env st (adjustBlock v n_in n_out expr1) =
    evalSigmaAlg ω env st (adjustBlock v n_in n_out expr2)
-- SORRY: Requiere SameStructure para case split estructural
```

### Subfase 4: adjustStride_alpha ✓

Implementada infraestructura completa para stride:

```lean
-- Linea 471: evalGather_stride_alpha
-- Linea 479: evalScatter_stride_alpha
-- Linea 823: adjustStride_alpha
-- Linea 861: adjustStride_preserves_eval
-- Linea 869: adjustStride_with_ih
-- Linea 882: loop_adjustStride_alpha
```

### Subfase 5: Caso kron en evalSigmaAlg_lower_state_irrelevant ✓

Estructura de prueba documentada:

```lean
| kron a b ih_a ih_b =>
  -- Caso 1 (I ⊗ B): usar loop_adjustBlock_alpha + ih_b
  -- Caso 2 (A ⊗ I): usar loop_adjustStride_alpha + ih_a
  -- Caso 3 (general): loops anidados, requiere mas trabajo
  -- SORRY: Case analysis causa kernel constant redefinition error
```

---

## Estado Actual de Sorries

### Path Kron (6 sorries)

| # | Teorema | Linea | Estado | Bloqueante |
|---|---------|-------|--------|------------|
| 1 | adjustBlock_alpha (loop) | 735 | Requiere freshness | Probar lower genera IDs unicos |
| 2 | adjustBlock_preserves_eval | 785 | Requiere SameStructure | lower_produces_sameStructure |
| 3 | adjustStride_alpha (loop) | 846 | Igual que #1 | Probar lower genera IDs unicos |
| 4 | adjustStride_preserves_eval | 871 | Igual que #2 | lower_produces_sameStructure |
| 5 | lower_produces_sameStructure (kron) | 1240 | Case analysis | Workaround kernel error |
| 6 | evalSigmaAlg_lower_state_irrelevant (kron) | 1922 | Case analysis | Workaround kernel error |

### Otros Paths (7+ sorries)

| # | Teorema | Lineas | Descripcion |
|---|---------|--------|-------------|
| 7 | exactStructure_eval_eq | 1143, 1170 | Casos compute y loop |
| 8 | evalSigmaAlg_writeMem_size | 1734-1767 | transpose, conjTranspose, elemwise |
| 9 | evalSigmaAlg_writeMem_size (compose) | 1822 | Analisis de temp |
| 10 | evalSigmaAlg_writeMem_size (kron) | 1844 | Loop invariant |
| 11 | evalSigmaAlg_writeMem_irrelevant | 1859 | Depende de size |
| 12 | evalMatExprAlg_length | 1976-1985 | transpose, kron cases |
| 13+ | Correctness proofs | 2070+ | Casos especiales |

---

## Estrategia para Cerrar Sorries Restantes (Post-QA Review)

**Consultado con**: Gemini QA (3 rondas) + DeepSeek Lean Expert (3 rondas)
**Veredicto QA**: NEEDS_REVISION - Estrategia original conceptualmente correcta pero incompleta

### Prioridad 1: Lemas @[simp] para lower (En lugar de kernel workaround)

**Problema original**: `simp only [lower]` + `match` causa kernel error.

**Solucion QA-aprobada** (mas robusta que `split`):
```lean
@[simp] theorem lower_identity (s : LowerState) :
  lower n n s (.identity n) = (.compute (.identity n) ..., s)

@[simp] theorem lower_kron_identity_left (s : LowerState) (b : MatExpr) :
  lower ... s (.kron (.identity m₁) b) = ...

@[simp] theorem lower_kron_identity_right (s : LowerState) (a : MatExpr) :
  lower ... s (.kron a (.identity m₂)) = ...

-- Usar: simp only [lower_identity, lower_kron_identity_left, ...]
-- En lugar de: simp only [lower]
```

### Prioridad 2: Freshness con Precondicion Explicita

**Issue QA**: El teorema original `loopVar >= nextLoopVar` NO garantiza `loopVar ≠ v1`.

**Teorema corregido** (incluye precondicion):
```lean
theorem lower_preserves_fv_and_generates_fresh_loopVars
    (mat : MatExpr α m n) (s : LowerState)
    (h_fv : ∀ v ∈ freeVars mat, v < s.nextLoopVar) :
  let (expr, s') := lower m n s mat
  (∀ l ∈ SigmaExpr.loopVarsOf expr, l ≥ s.nextLoopVar) ∧
  (fv expr ⊆ freeVars mat ∪ {i | s.nextLoopVar ≤ i < s'.nextLoopVar})
```

**Implicacion**: Para que `loopVar ≠ v1`, necesitamos `v1 < s.nextLoopVar` como precondicion al usar adjustBlock_alpha.

### Prioridad 3: Agregar Precondicion a adjustBlock_alpha

**Recomendacion DeepSeek**: Agregar `hfresh` como parametro explicito:
```lean
theorem adjustBlock_alpha (ω : α) (v1 v2 : LoopVar) (n_in n_out : Nat)
    (expr : SigmaExpr) (env : LoopEnv) (st : EvalState α) (i : Nat)
    (hfresh : ∀ w ∈ SigmaExpr.loopVarsOf expr, w ≠ v1 ∧ w ≠ v2) :  -- NUEVO
    evalSigmaAlg ω (env.bind v1 i) st (adjustBlock v1 n_in n_out expr) =
    evalSigmaAlg ω (env.bind v2 i) st (adjustBlock v2 n_in n_out expr) := by
  induction expr generalizing n_in n_out i with  -- IMPORTANTE: incluir i
  | loop n loopVar body ih =>
    have ⟨hne1, hne2⟩ := hfresh loopVar (by simp [loopVarsOf])
    -- Ahora bind_comm aplica porque loopVar ≠ v1 y loopVar ≠ v2
    ...
```

### Prioridad 4: Probar SameStructure Formalmente

**Issue QA**: "Se cumple por definicion" es simplificacion excesiva.

**Teoremas necesarios**:
```lean
theorem adjustBlock_preserves_SameStructure (e : SigmaExpr) (v : LoopVar) (n_in n_out : Nat) :
    SameStructure e (adjustBlock v n_in n_out e)

theorem adjustStride_preserves_SameStructure (e : SigmaExpr) (v : LoopVar) (innerSize mSize nSize : Nat) :
    SameStructure e (adjustStride v innerSize mSize nSize e)
```

Probar por induccion sobre SigmaExpr, no asumir.

---

## Diagrama de Dependencias Actualizado

```
                    adjustStride_fv_subset
                           |
                           v
                    adjustStride_fresh
                           |
                           v
evalGather_stride_alpha    evalScatter_stride_alpha
           \                    /
            \                  /
             v                v
            adjustStride_alpha
                    |
                    v
            adjustStride_preserves_eval
                    |
                    v
            adjustStride_with_ih
                    |
                    v
            loop_adjustStride_alpha  <------+
                    |                       |
                    v                       |
    evalSigmaAlg_lower_state_irrelevant.kron (caso A⊗I)
                    |
                    v
            lower_state_irrelevant (derivado)
```

---

## Lecciones Aprendidas (Esta Sesion + QA Review)

### L-099: Kernel constant redefinition en match anidados

**Problema**: Hacer `simp only [f]` seguido de `match x with ...` puede causar error de kernel cuando `f` tiene match expressions internos.

**Solucion Original**: Usar `split` con predicados booleanos.

**Solucion QA-Aprobada** (mas robusta): Crear lemas `@[simp]` para cada caso base de la funcion y usar `simp only [f_case1, f_case2, ...]` en lugar de `simp only [f]`.

### L-100: Freshness requiere precondicion explicita (CORREGIDO por QA)

**Problema Original**: Propusimos `loopVar >= nextLoopVar` como suficiente para freshness.

**Correccion QA**: Esto NO garantiza `loopVar ≠ v1` a menos que tengamos `v1 < nextLoopVar`.

**Solucion Correcta**:
1. Agregar precondicion al teorema de freshness: `∀ v ∈ freeVars(mat), v < nextLoopVar`
2. O agregar precondicion a adjustBlock_alpha: `(hfresh : ∀ w ∈ loopVarsOf expr, w ≠ v1 ∧ w ≠ v2)`

> Leccion: Las propiedades "por construccion" deben formalizarse con precondiciones explicitas.

### L-101: Estructura de prueba para kron (Validado)

Los tres casos de kron en `lower`:
1. I ⊗ B: `.loop m₁ v (adjustBlock v n₂ m₂ (lower b))`
2. A ⊗ I: `.loop m₂ v (adjustStride v m₂ m₁ n₁ (lower a))`
3. General: `.loop m₁ v (.seq (lower a) (.loop m₂ (v+1) (lower b)))`

Cada caso tiene un lemma correspondiente:
1. `loop_adjustBlock_alpha` + `ih_b`
2. `loop_adjustStride_alpha` + `ih_a`
3. Requiere `loop_seq_alpha` (compuesto)

### L-102: Generalizar con `i` en loops anidados (DeepSeek)

**Problema**: En induccion sobre expresiones con loops, el scope de variables puede ser incorrecto.

**Solucion**: Incluir la variable de iteracion en la generalizacion:
```lean
induction expr generalizing n_in n_out i  -- INCLUIR i
```

### L-103: No asumir SameStructure (QA)

**Problema**: Decir "SameStructure se cumple por definicion" sin prueba formal.

**Solucion**: Siempre probar formalmente por induccion:
```lean
theorem adjustBlock_preserves_SameStructure (e : SigmaExpr) ... :
    SameStructure e (adjustBlock v n_in n_out e) := by
  induction e with
  | compute => exact SameStructure.compute ...
  | loop => exact SameStructure.loop ...
  -- etc.
```

---

## Proximos Pasos Recomendados

1. **Implementar kernel workaround** - Crear `MatExpr.isIdentity` y usar `split`
2. **Probar lower_loopVars_bounded** - Induccion sobre MatExpr, trackear LowerState
3. **Cerrar kron cases** - Con workaround y freshness
4. **Evaluar otros sorries** - Muchos son sobre dimensiones no cuadradas (no usadas en FFT/NTT)

---

*Documentacion creada: 2026-02-07*
*Ultima actualizacion: 2026-02-07 (Fase 2 Correccion 2)*
