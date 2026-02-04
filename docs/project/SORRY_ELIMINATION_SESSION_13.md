# Sesion 13: Intento de Cerrar tensor_compose_pointwise

**Fecha**: 2026-02-04
**Duracion**: ~2 horas
**Objetivo**: Probar formalmente tensor_compose_pointwise en Perm.lean

---

## Resumen Ejecutivo

| Metrica | Antes | Despues |
|---------|-------|---------|
| **Sorries en Perm.lean** | 1 | **1** |
| **Lemmas auxiliares** | 0 | **2** |
| **Documentacion** | Basica | **Detallada** |
| **Build status** | OK | OK |

### Resultado Principal

**CONCLUSION**: La prueba de `tensor_compose_pointwise` esta BLOQUEADA por una limitacion tecnica de Lean 4 (splitter generation para indexed inductives). Los lemmas auxiliares fueron implementados exitosamente, pero el paso final requiere desplegar `applyIndex` para el constructor `tensor`, lo cual dispara el error "cannot generate splitter".

---

## F1: Investigacion y Consultas

### F1.S1: Consulta a QA (Gemini 2.5 Pro) - 3 rondas

**Veredicto**: APPROVE con refinamientos

**Puntos clave**:
1. La estrategia propuesta subestimaba la complejidad de `dite`
2. Se requiere manejo simetrico de casos `m=0` Y `n=0`
3. Recomendacion de crear lemma auxiliar general para div/mod
4. Sugerencia de crear `@[simp]` lemma de alto nivel

### F1.S2: Consulta a Experto Lean (DeepSeek) - 3 rondas

**Tacticas sugeridas**:
- `by_cases` para condiciones de `dite`
- `Fin.ext` para trabajar a nivel Nat
- `calc` para claridad en cadenas de igualdad

**Lemmas Mathlib identificados**:
- `Nat.add_mul_div_right`
- `Nat.mul_mod_left`
- `Nat.mod_eq_of_lt`
- `Nat.div_eq_of_lt_le`

---

## F2: Implementacion

### F2.S1: Lemmas Auxiliares Exitosos

```lean
private theorem nat_mul_add_div_eq (a b n : Nat) (hn : n > 0) (hb : b < n) :
    (a * n + b) / n = a := by
  have key : a * n + b < (a + 1) * n := by
    simp only [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left hb _
  rw [Nat.div_eq_of_lt_le (Nat.le_add_right (a * n) b) key]

private theorem nat_mul_add_mod_eq (a b n : Nat) (hn : n > 0) (hb : b < n) :
    (a * n + b) % n = b := by
  rw [Nat.add_mod]
  have h1 : a * n % n = 0 := Nat.mul_mod_left a n
  have h2 : b % n = b := Nat.mod_eq_of_lt hb
  have h3 : b % n % n = b % n := Nat.mod_eq_of_lt (Nat.mod_lt b hn)
  rw [h1, Nat.zero_add, h3, h2]
```

**Estado**: Compilan correctamente.

### F2.S2: Prueba Principal - BLOQUEADA

```lean
theorem tensor_compose_pointwise ... := by
  simp only [Perm.apply_compose]
  by_cases hn : n = 0
  · subst hn; simp only [Nat.mul_zero] at i; exact Fin.elim0 i
  by_cases hm : m = 0
  · subst hm; simp only [Nat.zero_mul] at i; exact Fin.elim0 i
  -- BLOQUEADO AQUI: No podemos desplegar applyIndex para tensor
  sorry
```

**Error al intentar `simp only [applyIndex]`**:
```
failed to generate splitter for match auxiliary declaration
'AmoLean.Matrix.Perm.applyIndex.match_1'
```

---

## F3: Analisis del Bloqueo

### F3.S1: Causa Raiz

El tipo `Perm : Nat -> Type` es un **indexed inductive** cuyos constructores tienen indices que pueden solaparse:
- `identity : Perm n` (cualquier n)
- `swap : Perm 2` (solo n=2)
- `tensor : Perm m -> Perm n -> Perm (m * n)` (cuando m*n = 2, solapa con swap)

Lean no puede generar un "splitter" porque no puede determinar estaticamente que caso aplicar sin inspeccionar el constructor.

### F3.S2: Por Que Funciona para Otros Teoremas

Los teoremas `apply_identity`, `apply_compose` funcionan con `rfl` porque:
1. El pattern matching esta en la **firma** de `applyIndex`
2. Lean genera equation lemmas para cada caso de pattern match
3. Pero estos lemmas solo aplican cuando el constructor es **conocido** en el goal

Para `tensor_compose_pointwise`, el constructor `tensor` esta presente pero necesitamos:
1. Desplegar `applyIndex (tensor _ _) _` para obtener la estructura div/mod
2. Aplicar los lemmas auxiliares
3. Verificar la igualdad

El paso 1 es donde `simp` intenta generar un splitter y falla.

### F3.S3: Soluciones Posibles (Trabajo Futuro)

| Solucion | Complejidad | Impacto |
|----------|-------------|---------|
| Custom eliminator con `@[elab_as_elim]` | Alta | Solo este teorema |
| Restructurar `Perm` como inductivo simple + predicado `isValid` | Muy Alta | Todo el modulo |
| Usar `native_decide` con instancias concretas | Media | Solo para n pequeno |
| Dejar sorry documentado | Baja | Ya hecho |

---

## F4: Lecciones Aprendidas

### L-047: Limitacion Fundamental de Splitters

**Problema**: Los indexed inductives con indices solapados no pueden tener splitters generados automaticamente.

**Sintoma**: Error "cannot generate splitter for match auxiliary declaration" al usar `simp`, `unfold`, o `rw` con funciones definidas por pattern match.

**Workaround actual**: Usar pattern matching en la firma de la funcion permite generar equation lemmas, pero no splitters para `simp`.

### L-048: Progreso Parcial es Valioso

Los lemmas auxiliares `nat_mul_add_div_eq` y `nat_mul_add_mod_eq` son:
- Reutilizables para otros teoremas de tensor
- Prueban la aritmetica subyacente correcta
- Documentan la estrategia de prueba

### L-049: Dificultades con simp y Nat Lemmas

Durante la implementacion, encontramos:
- `simp only [Nat.add_mod, Nat.mul_mod_right]` causa **maximum recursion depth**
- `ring` no esta disponible sin Mathlib Ring tactic
- `conv_lhs` no esta disponible en core Lean 4
- Solucion: Usar `rw` explicito con secuencia de lemmas

### L-050: Documentacion del Bloqueo

Cuando un teorema esta bloqueado por limitaciones tecnicas:
1. Documentar claramente en el docstring
2. Explicar la causa raiz
3. Listar posibles soluciones futuras
4. Mantener el sorry con conciencia

---

## F5: Estado del Proyecto

### F5.S1: Sorries Restantes en Perm.lean

| Sorry | Causa | Prioridad |
|-------|-------|-----------|
| `tensor_compose_pointwise` | Splitter limitation | Baja (computacionalmente verificado) |

### F5.S2: Funcionalidad Verificada

- `applyIndex` para todos los constructores: identity, swap, compose, stride, bitRev, tensor, inverse
- Tests computacionales via `#eval`
- 5 axiomas convertidos a teoremas con `rfl`

---

## F6: Archivos Modificados

| Archivo | Cambios |
|---------|---------|
| `AmoLean/Matrix/Perm.lean` | +2 lemmas auxiliares, documentacion actualizada |

---

## F7: Proximos Pasos

1. **Cerrar GoldilocksField sorries**: 22 sorries pendientes, estrategia via isomorfismo a ZMod
2. **NTT verification**: Depende de Perm y GoldilocksField
3. **Custom eliminator**: Investigar `@[elab_as_elim]` para Perm (trabajo futuro)

---

## Referencias

- **Session 12**: Descubrimiento del pattern matching en firma
- **QA Consultation**: 3 rondas con Gemini 2.5 Pro
- **Lean Expert**: DeepSeek via OpenRouter
- **Mathlib docs**: Nat lemmas para division y modulo
