# Sorry Elimination Plan: AlgebraicSemantics.lean

**Proyecto**: amo-lean
**Archivo**: `AmoLean/Verification/AlgebraicSemantics.lean`
**Fecha de creacion**: 2026-02-07
**Ultima actualizacion**: 2026-02-07
**Estado**: Fase 2 Correccion 3 - KERNEL ERROR RESUELTO

---

## Resumen Ejecutivo

| Metrica | Valor |
|---------|-------|
| Sorries en declaraciones | 13 (bajamos de 17) |
| Teoremas _fresh completados | 2 (adjustBlock_alpha_fresh, adjustStride_alpha_fresh) |
| Teoremas boundedness | 2 (lower_loopVars_bounded_and_state_monotonic, freshness_from_bounded) |
| Casos kron cerrados | I⊗B y A⊗I en lower_loopVars_bounded y evalSigmaAlg_lower_state_irrelevant |
| Sorry restante kron | 1 (caso general A⊗B en evalSigmaAlg_lower_state_irrelevant) |
| Build status | Compila sin errores |
| @[simp] lemmas MatExpr.isIdentity | 16 (uno por constructor) |

---

## RESOLUCION: Kernel Constant Redefinition Error

### Solucion Implementada

El kernel error fue resuelto refactorizando `lower.kron` para usar `MatExpr.isIdentity`:

```lean
-- En AmoLean/Matrix/Basic.lean
@[simp]
def MatExpr.isIdentity : MatExpr α m n → Bool
  | .identity _ => true
  | _ => false

-- @[simp] lemmas para cada constructor
@[simp] theorem isIdentity_identity : isIdentity (identity n) = true := rfl
@[simp] theorem isIdentity_kron : isIdentity (kron a b) = false := rfl
-- ... etc para los 16 constructores

-- En AmoLean/Sigma/Basic.lean, lower.kron ahora usa:
| @MatExpr.kron _ m₁ n₁ m₂ n₂ a b =>
  if a.isIdentity then ...
  else if b.isIdentity then ...
  else ...
```

### Por que funciona

Con `isIdentity` como funcion separada:
- Las equation lemmas se generan una sola vez (para isIdentity)
- `simp only [lower]` no regenera equation lemmas conflictivas
- `split_ifs` funciona correctamente para case analysis

---

## Trabajo Completado: Fase 2 Correccion 3

### Subfase 1: lower_loopVars_bounded_and_state_monotonic - COMPLETADO

```lean
theorem lower_loopVars_bounded_and_state_monotonic {α : Type} {m n : Nat}
    (mat : MatExpr α m n) (s : LowerState) :
    (∀ l ∈ SigmaExpr.loopVarsOf (lower m n s mat).1, l ≥ s.nextLoopVar) ∧
    (lower m n s mat).2.nextLoopVar ≥ s.nextLoopVar
```

**Todos los casos probados incluyendo kron**:
- Caso I⊗B: loopVar = s.nextLoopVar, inner >= s.nextLoopVar + 1
- Caso A⊗I: loopVar = s.nextLoopVar, inner >= s.nextLoopVar + 1
- Caso A⊗B: outer = s.nextLoopVar, inner = s.nextLoopVar + 1, nested >= state chained

### Subfase 2: freshness_from_bounded - COMPLETADO

```lean
theorem freshness_from_bounded {α : Type} {m n : Nat} (mat : MatExpr α m n) (s : LowerState)
    (v1 v2 : LoopVar) (hv1 : v1 < s.nextLoopVar) (hv2 : v2 < s.nextLoopVar) :
    ∀ w ∈ SigmaExpr.loopVarsOf (lower m n s mat).1, w ≠ v1 ∧ w ≠ v2
```

### Subfase 3: evalSigmaAlg_lower_state_irrelevant kron - PARCIALMENTE COMPLETADO

```lean
| kron a b ih_a ih_b =>
  simp only [lower]
  split_ifs with ha hb
  -- Case 1: I⊗B - CERRADO con loop_adjustBlock_alpha
  · apply loop_adjustBlock_alpha; intro env' st'; exact ih_b _ _ env' st'
  -- Case 2: A⊗I - CERRADO con loop_adjustStride_alpha
  · apply loop_adjustStride_alpha; intro env' st'; exact ih_a _ _ env' st'
  -- Case 3: A⊗B - SORRY (requiere nested_loop_alpha)
  · sorry
```

---

## Estado Actual de Sorries (13 total)

### Sorries del Path Kron (1)

| Teorema | Linea | Estado |
|---------|-------|--------|
| evalSigmaAlg_lower_state_irrelevant (caso A⊗B) | ~2192 | Requiere nested_loop_alpha |

### Sorries de Alpha-Equivalencia (4)

| Teorema | Linea | Estado |
|---------|-------|--------|
| adjustBlock_alpha (loop) | ~935 | Requiere freshness |
| adjustStride_alpha (loop) | ~971 | Requiere freshness |
| adjustBlock_preserves_eval | ~1093 | Requiere SameStructure |
| adjustStride_preserves_eval | ~1125 | Requiere SameStructure |

### Sorries de Estructura (2)

| Teorema | Linea | Estado |
|---------|-------|--------|
| ExactStructure.adjustBlock_same | ~1395 | Requiere freshness |
| ExactStructure.adjustStride_same | ~1451 | Requiere freshness |

### Sorries de Tamano/Longitud (6)

| Teorema | Linea | Descripcion |
|---------|-------|-------------|
| evalSigmaAlg_writeMem_size_preserved | ~1941, ~2112 | Varios casos |
| evalMatExprAlg_length | ~2219, ~2318 | transpose, kron |
| Otros | ~2440, ~2480 | writeMem irrelevance, correctness |

---

## Lecciones Aprendidas (Fase 2 Correccion 3)

### L-106: Kernel constant error se resuelve con refactorizacion

**Problema**: Inline match expressions en funciones recursivas causan kernel constant redefinition.

**Solucion**: Extraer el predicado a una funcion separada con @[simp].

```lean
-- MAL: inline match
let aIsIdentity := match a with | .identity _ => true | _ => false

-- BIEN: funcion separada
if a.isIdentity then ...
```

### L-107: split_ifs funciona despues de refactorizar

Una vez que el predicado es una funcion separada, `simp only [lower]` + `split_ifs` funciona sin kernel error.

### L-108: Los casos I⊗B y A⊗I son directos

Con la infraestructura de `loop_adjustBlock_alpha` y `loop_adjustStride_alpha`:
- I⊗B: `apply loop_adjustBlock_alpha; intro env' st'; exact ih_b _ _ env' st'`
- A⊗I: `apply loop_adjustStride_alpha; intro env' st'; exact ih_a _ _ env' st'`

### L-109: El caso A⊗B requiere nested_loop_alpha

El caso general tiene loops anidados con dos variables:
- Outer: state.nextLoopVar
- Inner: state.nextLoopVar + 1

Esto requiere un teorema especializado para equivalencia de loops anidados con diferentes variables.

---

## Metricas de Progreso

| Fase | Sorries Inicio | Sorries Fin | Cambio |
|------|----------------|-------------|--------|
| Inicio (Fase 2) | ~20 | - | - |
| Correccion 2 | ~18 | 17 | -1 |
| Correccion 3 (inicio) | 17 | - | - |
| Correccion 3 (fin) | - | 13 | **-4** |

**Reduccion neta**: 4 sorries eliminados en esta sesion.

---

## Proximos Pasos Recomendados

1. **Implementar `nested_loop_alpha`** - Teorema para equivalencia de loops anidados
2. **Cerrar caso A⊗B** - Usando nested_loop_alpha
3. **Cerrar sorries de SameStructure** - adjustBlock_preserves_eval, adjustStride_preserves_eval
4. **Documentar sorries restantes** - Categorizar por prioridad

---

*Documentacion creada: 2026-02-07*
*Ultima actualizacion: 2026-02-07 (Fase 2 Correccion 3 - Kernel Error Resuelto)*
