# Sesión 12: Eliminación de Axiomas en Matrix/Perm.lean

**Fecha**: 2026-02-04
**Duración**: ~2 horas
**Objetivo**: Eliminar axiomas introducidos en Sesión 11, probar teoremas con `rfl`

---

## Resumen Ejecutivo

| Métrica | Antes | Después |
|---------|-------|---------|
| **Axiomas en Perm.lean** | 5 | **0** |
| **Teoremas con `rfl`** | 0 | **5** |
| **Sorries activos** | 0 | **1** |
| **Build status** | ✅ | ✅ |

### Resultado Principal

**DESCUBRIMIENTO CLAVE**: Pattern matching en la **firma de la función** (con parámetro implícito `{k : Nat}`) permite a Lean generar equation lemmas correctamente, donde `match p with` fallaba con "cannot generate splitter".

---

## F1: Contexto del Problema

### F1.S1: Limitación Técnica de Lean

En Sesión 11, se introdujeron 5 axiomas porque:

```lean
-- El match tradicional FALLA para indexed inductives:
def applyIndex (p : Perm n) (i : Fin n) : Fin n :=
  match p with
  | identity => i  -- Error: cannot generate equation splitter
  | ...
```

**Causa raíz**: Los constructores de `Perm` tienen índices que pueden solaparse:
- `identity : Perm n` (cualquier n)
- `swap : Perm 2` (solo n=2)
- `stride m n : Perm (m * n)` (cuando m*n = 2, solapa con swap)
- `bitRev k : Perm (2^k)` (cuando k=1, 2^1 = 2, solapa)

Lean no puede generar un "splitter" porque no sabe qué caso aplicar sin inspeccionar el constructor.

### F1.S2: Axiomas Anteriores (Sesión 11)

```lean
axiom Perm.apply_identity {n : Nat} (i : Fin n) : applyIndex identity i = i
axiom Perm.apply_compose {n : Nat} (p q : Perm n) (i : Fin n) : ...
axiom Perm.applyIndex_bitRev (k : Nat) (i : Fin (2^k)) : ...
axiom apply_inverse_identity {n : Nat} (i : Fin n) : ...
axiom tensor_compose_pointwise {m n : Nat} (p1 p2 : Perm m) (q1 q2 : Perm n) (i : Fin (m * n)) : ...
```

---

## F2: Descubrimiento - Pattern Matching en Firma

### F2.S1: La Solución

El QA y el experto Lean sugirieron usar pattern matching en la **firma** de la función:

```lean
-- ANTES (falla):
def applyIndex (p : Perm n) (i : Fin n) : Fin n :=
  match p with ...

-- DESPUÉS (funciona):
def applyIndex : {k : Nat} → Perm k → Fin k → Fin k
  | _, identity, i => i
  | _, swap, ⟨0, _⟩ => ⟨1, by omega⟩
  | _, swap, ⟨1, _⟩ => ⟨0, by omega⟩
  | _, compose p q, i => applyIndex p (applyIndex q i)
  | _, @tensor m n p q, i => ...
  | ...
```

### F2.S2: Por Qué Funciona

1. El parámetro implícito `{k : Nat}` está **antes** del pattern matching
2. Cada caso de pattern match especifica `_` para el índice (Lean lo infiere)
3. El equation compiler puede generar lemmas porque:
   - `| _, identity, i => i` genera `applyIndex identity i = i`
   - El `_` permite que el mismo pattern aplique para cualquier `k`

### F2.S3: Validación con Prototipo

Prototipo en `/tmp/perm_proto4.lean`:

```lean
inductive Perm : Nat → Type where
  | identity : Perm n
  | swap : Perm 2
  | compose : Perm n → Perm n → Perm n

def applyIndex : {k : Nat} → Perm k → Fin k → Fin k
  | _, identity, i => i
  | _, swap, ⟨0, _⟩ => ⟨1, by omega⟩
  | _, swap, ⟨1, _⟩ => ⟨0, by omega⟩
  | _, swap, ⟨i + 2, h⟩ => ⟨i + 2, h⟩
  | _, compose p q, i => applyIndex p (applyIndex q i)

-- ¡FUNCIONA CON RFL!
theorem apply_identity {n : Nat} (i : Fin n) : applyIndex identity i = i := rfl
theorem apply_compose {n : Nat} (p q : Perm n) (i : Fin n) :
    applyIndex (compose p q) i = applyIndex p (applyIndex q i) := rfl
```

---

## F3: Implementación

### F3.S1: Axiomas Eliminados

| Axioma | Resolución | Técnica |
|--------|------------|---------|
| `apply_identity` | `theorem ... := rfl` | Pattern en firma |
| `apply_compose` | `theorem ... := rfl` | Pattern en firma |
| `apply_inverse_identity` | `theorem ... := rfl` | Pattern en firma |
| `applyIndex_bitRev` | `theorem ... := rfl` | Pattern en firma |
| `tensor_compose_pointwise` | `theorem ... := by sorry` | Prueba parcial documentada |

### F3.S2: Teorema Desbloqueado

`swap_self_inverse_pointwise` ahora se puede probar:

```lean
theorem Perm.swap_self_inverse_pointwise (i : Fin 2) :
    Perm.applyIndex Perm.swap (Perm.applyIndex Perm.swap i) = i := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
```

### F3.S3: Sorry Restante

`tensor_compose_pointwise` requiere razonamiento aritmético sobre div/mod:

```lean
-- Proof sketch documentado en el código:
-- LHS: r = (p2 outer)*n + (q2 inner), luego (p1 (r/n))*n + (q1 (r%n))
-- RHS: (p1 (p2 outer))*n + (q1 (q2 inner))
-- Key: (a*n + b) / n = a y (a*n + b) % n = b cuando b < n
theorem tensor_compose_pointwise ... := by
  simp only [Perm.apply_compose]
  sorry  -- Expansión de tensor en term-mode es compleja
```

---

## F4: Lecciones Aprendidas

### F4.S1: L-043 - Pattern Matching en Firma para Indexed Inductives

**Problema**: `match p with` falla para indexed inductives cuando los índices pueden solaparse.

**Solución**: Usar pattern matching directamente en la **firma** de la función:

```lean
-- En lugar de:
def f (p : T n) : R := match p with | constructor => ...

-- Usar:
def f : {k : Nat} → T k → R
  | _, constructor, ... => ...
```

**Beneficio**: Lean genera equation lemmas correctamente, permitiendo `rfl` proofs.

### F4.S2: L-044 - Sintaxis @constructor para Patrones con Índices Explícitos

Cuando un constructor tiene parámetros que determinan el índice, usar `@`:

```lean
-- tensor : Perm m → Perm n → Perm (m * n)
-- Para pattern match necesitamos m y n:
| _, @tensor m_size n_size p q, i => ...
```

### F4.S3: L-045 - Prototipado Rápido para Validar Estrategias

Antes de modificar código complejo, validar la estrategia con un prototipo mínimo:

```lean
-- /tmp/perm_proto4.lean
-- Versión simplificada que solo tiene identity, swap, compose
-- Si funciona aquí, funcionará en el código completo
```

### F4.S4: L-046 - Proofs por Cases sobre Fin n

Para `Fin n` con n pequeño y conocido, usar pattern matching explícito:

```lean
-- Para Fin 2:
match i with
| ⟨0, _⟩ => rfl
| ⟨1, _⟩ => rfl

-- Más limpio que fin_cases + native_decide
```

---

## F5: Consultas a QA y Experto

### F5.S1: Consulta Inicial sobre Axiomas

**Pregunta del usuario**: ¿Los axiomas son legítimos o son escapes porque no se pueden probar?

**Investigación**: Los axiomas eran computacionalmente verdaderos pero Lean no podía probarlos formalmente debido a la limitación de match elaboration.

### F5.S2: Debate con QA (3 rondas)

**Tema**: Estrategia A (Redesign Perm) vs Estrategia B (Recursores explícitos)

**Conclusiones del QA**:
1. El diseño de `PermCore.size` propuesto tenía fallos matemáticos
2. Un predicado `isValid` ayudaría pero añade complejidad
3. La solución real estaba en **cómo** se define `applyIndex`, no en cambiar `Perm`

### F5.S3: Consulta a Experto Lean

**Sugerencia clave**: Usar `@[elab_as_elim]` para custom eliminators.

**Resultado**: La estrategia de pattern matching en firma funcionó mejor que custom eliminators.

---

## F6: Archivos Modificados

| Archivo | Cambios |
|---------|---------|
| `AmoLean/Matrix/Perm.lean` | Reescritura de `applyIndex`, eliminación de 5 axiomas |

### F6.S1: Diff Principal

```diff
- def applyIndex (p : Perm n) (i : Fin n) : Fin n :=
-   match p with ...

+ def applyIndex : {k : Nat} → Perm k → Fin k → Fin k
+   | _, identity, i => i
+   | _, swap, ⟨0, _⟩ => ⟨1, by omega⟩
+   ...
```

```diff
- axiom Perm.apply_identity {n : Nat} (i : Fin n) :
-     Perm.applyIndex Perm.identity i = i

+ @[simp]
+ theorem Perm.apply_identity {n : Nat} (i : Fin n) :
+     Perm.applyIndex Perm.identity i = i := rfl
```

---

## F7: Estado Final

### F7.S1: Verificación

```bash
$ lake build AmoLean.Matrix.Perm
⚠ [5/5] Built AmoLean.Matrix.Perm
warning: ././././AmoLean/Matrix/Perm.lean:607:8: declaration uses 'sorry'
Build completed successfully.
```

### F7.S2: Tests Computacionales

```lean
#eval Perm.toIndexList (Perm.stride 2 3)    -- [0, 3, 1, 4, 2, 5] ✓
#eval Perm.toIndexList (Perm.stride 3 2)    -- [0, 2, 4, 1, 3, 5] ✓
#eval Perm.toIndexList (Perm.bitRev 3)      -- [0, 4, 2, 6, 1, 5, 3, 7] ✓
#eval Perm.toIndexList (Perm.tensor Perm.swap Perm.identity)  -- ✓
```

---

## F8: Próximos Pasos

1. **tensor_compose_pointwise**: Completar prueba (requiere lemmas auxiliares sobre div/mod)
2. **Posibles mejoras**: Agregar más casos a `inverse` para soportar `inverse (compose p q)`
3. **Documentación**: Actualizar roadmap del proyecto

---

## Referencias

- **Sesión 11**: Introducción de axiomas y análisis del problema
- **Prototipo**: `/tmp/perm_proto4.lean` (validación de la estrategia)
- **Lean 4 Doc**: Equation compiler para indexed inductives
