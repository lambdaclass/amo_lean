# Sorry Elimination Plan: AlgebraicSemantics.lean

**Proyecto**: amo-lean
**Archivo**: `AmoLean/Verification/AlgebraicSemantics.lean`
**Fecha de creacion**: 2026-02-07
**Ultima actualizacion**: 2026-02-07
**Estado**: Fase 2 Correccion 3 - Infraestructura de freshness completada

---

## Resumen Ejecutivo

| Metrica | Valor |
|---------|-------|
| Sorries en declaraciones | 17 |
| Teoremas _fresh completados | 2 (adjustBlock_alpha_fresh, adjustStride_alpha_fresh) |
| Teoremas boundedness | 2 (lower_loopVars_bounded_and_state_monotonic, freshness_from_bounded) |
| Sorries path kron | 3 (lower_loopVars_bounded kron, evalSigmaAlg_lower_state_irrelevant kron, nested loop) |
| Sorries otros paths | 14 (transpose, compose, length analysis, writeMem, correctness) |
| Build status | Compila sin errores |
| @[simp] lemmas en Basic.lean | 4 (lower_identity, lower_zero, lower_dft, lower_ntt) |

---

## Trabajo Completado: Fase 2 Correccion 3

### Subfase 1: lower_loopVars_bounded_and_state_monotonic - IMPLEMENTADO

Teorema que prueba que todos los loopVars generados por `lower` son >= state.nextLoopVar:

```lean
-- Linea 362 (AlgebraicSemantics.lean)
theorem lower_loopVars_bounded_and_state_monotonic {α : Type} {m n : Nat}
    (mat : MatExpr α m n) (s : LowerState) :
    (∀ l ∈ SigmaExpr.loopVarsOf (lower m n s mat).1, l ≥ s.nextLoopVar) ∧
    (lower m n s mat).2.nextLoopVar ≥ s.nextLoopVar
-- COMPLETADO: Todos los casos excepto kron (kernel constant error)
```

**Casos probados**:
- identity, zero, dft, ntt, twiddle, perm, diag, scalar: triviales (loopVarsOf = ∅)
- transpose, conjTranspose: delegado al IH
- smul, elemwise, partialElemwise, mdsApply, addRoundConst: IH + union membership
- add: cadena de estados, union de loopVars
- compose: cadena de estados, union de loopVars

**Caso kron**: SORRY debido a kernel constant redefinition error al hacer case analysis.

### Subfase 2: freshness_from_bounded - IMPLEMENTADO

Corolario que conecta boundedness con los teoremas _alpha_fresh:

```lean
-- Linea 477 (AlgebraicSemantics.lean)
theorem freshness_from_bounded {α : Type} {m n : Nat} (mat : MatExpr α m n) (s : LowerState)
    (v1 v2 : LoopVar) (hv1 : v1 < s.nextLoopVar) (hv2 : v2 < s.nextLoopVar) :
    ∀ w ∈ SigmaExpr.loopVarsOf (lower m n s mat).1, w ≠ v1 ∧ w ≠ v2
-- COMPLETADO: Derivado directamente de lower_loopVars_bounded_and_state_monotonic
```

### Infraestructura Existente (De Fase 2 Correccion 2)

- `adjustBlock_alpha_fresh`: COMPLETADO (loop case cerrado)
- `adjustStride_alpha_fresh`: COMPLETADO (loop case cerrado)
- `loop_adjustBlock_alpha`: COMPLETADO
- `loop_adjustStride_alpha`: COMPLETADO
- `@[simp]` lemmas: `lower_identity`, `lower_zero`, `lower_dft`, `lower_ntt`

---

## Bloqueante Principal: Kernel Constant Redefinition

### Descripcion del Problema

Cuando intentamos hacer case analysis despues de unfold/simp de `lower` para kron:

```lean
| kron a b ih_a ih_b =>
  simp only [lower]  -- o unfold lower
  split  -- o split_ifs, o cases a with
  -- ERROR: (kernel) constant has already been declared 'AmoLean.Sigma.lower.match_3.eq_1'
```

### Causa Raiz

La funcion `lower` tiene match expressions anidados para determinar si `a` o `b` es identity:

```lean
| @MatExpr.kron _ m₁ n₁ m₂ n₂ a b =>
  let aIsIdentity := match a with | .identity _ => true | _ => false
  let bIsIdentity := match b with | .identity _ => true | _ => false
  if aIsIdentity then ...
  else if bIsIdentity then ...
  else ...
```

Cuando Lean simplifica esto y luego intenta generar equation lemmas para el case split, los mismos equation lemmas ya fueron generados, causando el conflicto.

### Soluciones Intentadas

1. **`simp only [lower]` + `split`**: Kernel error
2. **`unfold lower` + `split`**: Kernel error
3. **`simp only [lower]` + `split_ifs`**: Kernel error
4. **`cases a with` + `simp only [lower]`**: Kernel error en branches anidados

### Solucion Propuesta (Pendiente)

Refactorizar `lower` para que kron use funciones auxiliares decidibles:

```lean
def MatExpr.isIdentity : MatExpr α m n → Bool
  | .identity _ => true
  | _ => false

-- En lower.kron:
if a.isIdentity then ...
else if b.isIdentity then ...
else ...
```

Con `isIdentity` como funcion separada, las equation lemmas se generan una sola vez y el case analysis funciona.

---

## Estado Actual de Sorries por Categoria

### Teoremas de Freshness/Boundedness (1 sorry)

| Teorema | Linea | Estado |
|---------|-------|--------|
| lower_loopVars_bounded_and_state_monotonic (kron) | ~475 | Kernel error |

### Teoremas de Alpha-Equivalencia (3 sorries)

| Teorema | Linea | Estado |
|---------|-------|--------|
| adjustBlock_alpha (loop) | ~902 | Requiere freshness |
| adjustStride_alpha (loop) | ~938 | Requiere freshness |
| evalSigmaAlg_lower_state_irrelevant (kron) | ~2145 | Kernel error |

### Teoremas de Estructura (2 sorries)

| Teorema | Linea | Estado |
|---------|-------|--------|
| adjustBlock_preserves_eval | ~1060 | Requiere SameStructure |
| adjustStride_preserves_eval | ~1092 | Requiere SameStructure |

### Teoremas de Tamano/Longitud (8+ sorries)

| Teorema | Linea | Descripcion |
|---------|-------|-------------|
| evalSigmaAlg_writeMem_size_preserved | ~1908, ~2079 | Varios casos |
| evalMatExprAlg_length | ~2173, ~2272 | transpose, kron |
| Otros | Varias | writeMem irrelevance, correctness |

---

## Dependencias de Teoremas

```
lower_loopVars_bounded_and_state_monotonic
                    |
                    v
            freshness_from_bounded
                    |
                    v
    adjustBlock_alpha_fresh  +  adjustStride_alpha_fresh
                    |                     |
                    v                     v
         loop_adjustBlock_alpha    loop_adjustStride_alpha
                    \                    /
                     \                  /
                      v                v
      evalSigmaAlg_lower_state_irrelevant (kron)
                           |
                           v
                lower_state_irrelevant
```

---

## Lecciones Aprendidas (Fase 2 Correccion 3)

### L-106: Kernel constant error es bloqueante duro

**Problema**: El error de kernel constant no tiene workaround simple dentro del proof term.

**Solucion**: Requiere cambio de codigo en la definicion de la funcion (separar predicados en funciones auxiliares).

### L-107: La infraestructura de freshness esta completa

Los teoremas `_alpha_fresh` funcionan perfectamente cuando se les proporciona la precondicion de freshness. El problema esta en obtener esa precondicion para expresiones generadas por `lower`.

### L-108: Los casos I⊗B y A⊗I son closeable en principio

Una vez resuelto el kernel error:
- I⊗B: `apply loop_adjustBlock_alpha; intro env' st'; exact ih_b ...`
- A⊗I: `apply loop_adjustStride_alpha; intro env' st'; exact ih_a ...`

El caso general A⊗B requiere trabajo adicional para loops anidados.

---

## Proximos Pasos Recomendados

1. **Refactorizar `lower.kron`** - Extraer `MatExpr.isIdentity` como funcion separada
2. **Cerrar `lower_loopVars_bounded` kron** - Con el predicado separado, el case analysis funcionara
3. **Cerrar `evalSigmaAlg_lower_state_irrelevant` kron** - Usando la misma tecnica
4. **Evaluar caso general A⊗B** - Puede requerir `loop_seq_alpha` para loops anidados
5. **Documentar sorries restantes** - Muchos son sobre casos edge (no-cuadrados, correctness parcial)

---

## Metricas de Progreso

| Fase | Sorries Inicio | Sorries Fin | Cambio |
|------|----------------|-------------|--------|
| Inicio (Fase 2) | ~20 | - | - |
| Correccion 2 | ~18 | 13 | -5 |
| Correccion 3 | 13 | 17 | +4 (nuevos teoremas con sorry en kron) |

**Nota**: El aumento de sorries es porque agregamos teoremas nuevos (lower_loopVars_bounded, etc.) que tienen sorry en el caso kron debido al kernel error. La infraestructura esta mas completa y lista para cerrar una vez resuelto el bloqueante.

---

*Documentacion creada: 2026-02-07*
*Ultima actualizacion: 2026-02-07 (Fase 2 Correccion 3)*
