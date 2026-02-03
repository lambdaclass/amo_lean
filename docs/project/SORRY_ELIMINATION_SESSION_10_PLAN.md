# Session 10: FRI Sorry Elimination - COMPLETADA

**Fecha**: 2026-02-03
**Objetivo**: Eliminar 5 sorries relacionados con FRI Protocol
**Estado**: COMPLETADA - 5/5 sorries eliminados

---

## Resumen Ejecutivo

| Métrica | Plan | Resultado |
|---------|------|-----------|
| Sorries a eliminar | 5 | 5 ✓ |
| Archivos afectados | 2 | 2 ✓ |
| Estrategia principal | Master Lemma | `go_sizes` helper |
| Consultas realizadas | Lean Expert + QA (3 rondas) | Completadas |

---

## F1: Resultados por Sorry

| # | Sorry | Archivo | Línea | Estado | Técnica Usada |
|---|-------|---------|-------|--------|---------------|
| 1 | `absorb_order_matters` | Transcript.lean | 439 | ✓ | `List.append_cancel_left` |
| 2 | `friFold_spec` | FRI_Properties.lean | 91 | ✓ | `Array.getElem_ofFn` + `getElem!_pos` |
| 3 | `commitments_count` | FRI_Properties.lean | 275 | ✓ | `go_sizes` helper lemma |
| 4 | `challenges_count` | FRI_Properties.lean | 282 | ✓ | `go_sizes` helper lemma |
| 5 | `challenges_derived_in_order` | FRI_Properties.lean | 291 | ✓ | Corolario de `challenges_count` |

---

## F2: Pruebas Implementadas

### F2.S1: absorb_order_matters (Transcript.lean)

```lean
theorem absorb_order_matters {F : Type} (s1 s2 : TranscriptState F) (a b : F) (h : a ≠ b) :
    absorb (absorb s1 a) b ≠ absorb (absorb s1 b) a := by
  simp only [absorb]
  intro heq
  -- Si los estados son iguales, sus campos absorbed son iguales
  have h_absorbed : s1.absorbed ++ [a] ++ [b] = s1.absorbed ++ [b] ++ [a] := by
    have := congrArg TranscriptState.absorbed heq
    simp only [List.append_assoc] at this ⊢
    exact this
  simp only [List.append_assoc, List.singleton_append] at h_absorbed
  -- Cancelar prefijo común
  have h_suffix : [a, b] = [b, a] := List.append_cancel_left h_absorbed
  -- Extraer a = b de [a, b] = [b, a]
  have h_eq : a = b := (List.cons.inj h_suffix).1
  -- Contradicción
  exact h h_eq
```

**Insight clave**: `List.append_cancel_left` (no `append_left_cancel`) permite cancelar prefijos iguales.

### F2.S2: friFold_spec (FRI_Properties.lean)

```lean
theorem friFold_spec (input : Array UInt64) (alpha : UInt64)
    (i : Nat) (hi : i < input.size / 2) :
    (friFold input alpha).get! i = input.get! (2 * i) + alpha * input.get! (2 * i + 1) := by
  unfold friFold
  have h_bound : i < (Array.ofFn fun j : Fin (input.size / 2) =>
      input.get! (2 * j.val) + alpha * input.get! (2 * j.val + 1)).size := by
    simp only [Array.size_ofFn]; exact hi
  rw [Array.get!_eq_getElem!]
  rw [getElem!_pos ... h_bound]
  rw [Array.getElem_ofFn]
```

**Insight clave**: Cadena de conversiones `get!` → `getElem!` → `getElem` → `Array.getElem_ofFn`.

### F2.S3: go_sizes Helper Lemma (FRI_Properties.lean)

```lean
private theorem go_sizes (numRounds : Nat) (computeCommitment : Array UInt64 → UInt64)
    (poly : Array UInt64) (ts : TranscriptState)
    (commits challenges : Array UInt64) (round : Nat)
    (h_bound : round ≤ numRounds) :
    let (finalCommits, finalChallenges, _) :=
      executeRounds.go numRounds computeCommitment poly ts commits challenges round
    finalCommits.size = commits.size + (numRounds - round) ∧
    finalChallenges.size = challenges.size + (numRounds - round) := by
  -- Inducción fuerte con generalize
  generalize h_term : numRounds - round = n
  induction n using Nat.strongRecOn generalizing poly ts commits challenges round h_bound with
  | ind n ih =>
    unfold executeRounds.go
    simp only
    split
    · -- Caso base: n = 0
      have h_n_zero : n = 0 := by rw [← h_term]; exact Nat.sub_eq_zero_of_le ...
      subst h_n_zero; simp only [Nat.add_zero]; trivial
    · -- Caso inductivo
      have h_lt_n : n - 1 < n := by omega
      have h_rec := ih (n - 1) h_lt_n ...
      simp only [Array.size_push] at h_rec
      constructor <;> omega
```

**Insight clave**:
1. Lean genera `executeRounds.go` accesible para probar propiedades
2. Usar `generalize` + `Nat.strongRecOn` para inducción sobre la métrica de terminación
3. `trivial` resuelve metas que son `True` después de simplificación

### F2.S4: Corolarios (FRI_Properties.lean)

```lean
theorem commitments_count ... := by
  simp only [executeRounds]
  have h := go_sizes numRounds computeCommitment initialPoly TranscriptState.init #[] #[] 0 ...
  simp only [Array.size_empty, Nat.zero_add, Nat.sub_zero] at h
  exact h.1

theorem challenges_count ... := by
  -- Análogo a commitments_count
  exact h.2

theorem challenges_derived_in_order ... := by
  intro _
  have h2 := challenges_count initialPoly numRounds computeCommitment
  simp only [executeRounds] at h2 ⊢
  omega
```

---

## F3: Lecciones Aprendidas

### F3.S1: Del Experto Lean (DeepSeek)

| Recomendación | Aplicada | Resultado |
|---------------|----------|-----------|
| `List.append_right_cancel` | Parcial | El nombre correcto es `List.append_cancel_left` |
| `Array.ofFn_get` | Sí | Funciona via `Array.getElem_ofFn` |
| `generalizing` en inducción | Sí | Crítico para `go_sizes` |
| Tácticas `omega`, `linarith` | Sí | `omega` resolvió toda la aritmética |

### F3.S2: Del QA (Gemini 2.5 Pro)

| Insight | Validez | Comentario |
|---------|---------|------------|
| Riesgo de acoplamiento entre teoremas | ✓ Válido | Motivó helper lemma unificado |
| Propuesta de Master Lemma | Parcial | Usamos `go_sizes` que captura ambas propiedades |
| Usar principio de inducción generado | ✓ Crítico | `executeRounds.go` es accesible en Lean 4 |
| `Nat.strongInductionOn` puede fallar | ✓ Válido | Usamos `Nat.strongRecOn` con `generalize` |

### F3.S3: Descubrimientos Técnicos

1. **`let rec` genera funciones accesibles**: En Lean 4, `executeRounds.go` es un identificador válido que puede usarse en teoremas externos.

2. **Naming de lemmas en Mathlib/Lean 4**:
   - `List.append_left_cancel` NO existe
   - `List.append_cancel_left` SÍ existe
   - Siempre verificar nombres exactos con `#check`

3. **Cadena de conversión para Array access**:
   ```
   Array.get! → getElem! → getElem (con bound) → Array.getElem_ofFn
   ```

4. **`trivial` vs `rfl`**: Después de simplificación, la meta puede ser `True` (usar `trivial`) no una igualdad (usar `rfl`).

5. **`simp only [executeRounds]` propaga a `go`**: Cuando la meta tiene `executeRounds`, simp la expande y `omega` puede conectar con hipótesis sobre `go`.

---

## F4: Desviaciones del Plan Original

| Plan | Realidad | Razón |
|------|----------|-------|
| Master Lemma `executeRounds_spec` con 4 propiedades | Helper `go_sizes` con 2 propiedades | Más simple, suficiente para los teoremas |
| Corolarios como proyecciones triviales | Corolarios requieren `simp` + `omega` | Conexión entre `executeRounds` y `go` |
| `List.append_right_cancel` | `List.append_cancel_left` | Nombre incorrecto en Lean 4 |
| Inducción simple con `induction` | `Nat.strongRecOn` + `generalize` | Necesario para matching de terminación |

---

## F5: Métricas de Éxito - VERIFICADAS

- [x] 0 sorries en `AmoLean/FRI/Transcript.lean`
- [x] 0 sorries en `AmoLean/Verification/FRI_Properties.lean`
- [x] `lake build` compila sin warnings de sorry para FRI
- [x] Build completo exitoso

---

## F6: Recursos Consultados

### Experto Lean (DeepSeek via OpenRouter)
- Proporcionó estrategias iniciales
- Nombres de lemmas parcialmente incorrectos (naming de Lean 4 vs Mathlib)

### QA (Gemini 2.5 Pro) - 3 Rondas
- **R1**: Identificó acoplamiento entre teoremas
- **R2**: Propuso Master Lemma unificado
- **R3**: Enfatizó usar inducción nativa de Lean

### Bibliografía
- Paper: "On the Concrete Security of Non-interactive FRI" (Block et al.) - contexto teórico
- ZkLinalg: No usado directamente pero validó estructura general

---

## F7: Recomendaciones para Futuras Sesiones

1. **Siempre verificar nombres de lemmas** con `#check` antes de usarlos
2. **Para funciones con `let rec`**, verificar si Lean genera `.go` accesible
3. **Preferir `Nat.strongRecOn` + `generalize`** sobre `Nat.strongInductionOn` para funciones con `termination_by`
4. **Documentar cadenas de conversión** (ej: `get!` → `getElem!` → `getElem`)
5. **Probar invariante general** (como `go_sizes`) en lugar de propiedades individuales

---

*Session 10 completada exitosamente el 2026-02-03.*
