# Session 11: Matrix/Perm Sorry Elimination

**Fecha**: 2026-02-03
**Objetivo**: Eliminar 20 sorries de Matrix/Perm.lean
**Estado**: PLAN EN REVISIÓN

---

## Resumen Ejecutivo

| Métrica | Valor |
|---------|-------|
| Sorries a eliminar | 20 |
| Archivos afectados | 1 (AmoLean/Matrix/Perm.lean) |
| Estrategia principal | Bottom-up: Aritmética → Perm → Álgebra |
| Consultores | QA (Gemini 3 rondas) + Lean Expert (DeepSeek 2 rondas) |

---

## F1: Análisis del Módulo

### F1.S1: Contexto

El módulo `Matrix/Perm.lean` implementa **permutaciones simbólicas para FFT** según el enfoque SPIRAL (Franchetti et al.). Las permutaciones clave son:

1. **Stride permutation** `L^{mn}_n`: Reordena matriz row-major a column-major
2. **Bit-reversal**: Reordena índices por bits invertidos (FFT radix-2)
3. **Tensor product**: Operaciones paralelas en subestructuras

### F1.S2: Definiciones Clave

```lean
-- Bit reversal con acumulador
def bitReverse (numBits : Nat) (x : Nat) : Nat :=
  go numBits x 0
where
  go : Nat → Nat → Nat → Nat
    | 0,     _,  acc => acc
    | b + 1, x', acc => go b (x' / 2) (acc * 2 + x' % 2)

-- Stride permutation
def strideIndex (m n : Nat) (i : Nat) : Nat := (i % m) * n + (i / m)
def strideIndexInv (m n : Nat) (i : Nat) : Nat := (i % n) * m + (i / n)

-- Permutation type
inductive Perm : Nat → Type where
  | identity : Perm n
  | stride : (m n : Nat) → Perm (m * n)
  | bitRev : (k : Nat) → Perm (2^k)
  | swap : Perm 2
  | compose : Perm n → Perm n → Perm n
  | inverse : Perm n → Perm n
  | tensor : Perm m → Perm n → Perm (m * n)
```

### F1.S3: Insight Crítico del QA

**NO USAR AXIOMAS**. El QA enfatizó:
> "An `axiom` introduces a new, unproven assumption. If this assumption is subtly false, it can be used to prove `False`, rendering the entire library logically inconsistent."

Los tests computacionales (`#eval`) dan confianza pero **no son pruebas formales**.

---

## F2: Estrategia de Prueba (Bottom-Up)

### F2.S1: Fase 1 - Aritmética Fundacional (4 sorries)

**Meta**: Probar propiedades de las funciones auxiliares `bitReverse` y `strideIndex`.

| # | Sorry | Línea | Estrategia |
|---|-------|-------|------------|
| 1 | `bitReverse_lt` | 46 | Inducción sobre k, análisis de `go` |
| 2 | `bitReverse_involution` | 41 | Helper lemma + inducción |
| 3 | `strideIndex_lt` | 69 | Propiedades de mod/div |
| 4 | `stride_inverse_eq` | 64 | Lemmas Nat.div_add_mod |

#### F2.S1.C1: `bitReverse_lt`

```lean
theorem bitReverse_lt (k : Nat) (x : Nat) (h : x < 2^k) :
    bitReverse k x < 2^k := by
  -- Estrategia: Inducción sobre k
  -- Caso base: k = 0 → x = 0, bitReverse 0 x = 0 < 1
  -- Caso inductivo: usar que go preserva el rango
  sorry
```

**Lemma auxiliar necesario**:
```lean
lemma go_lt (b x acc : Nat) (hacc : acc < 2^(k-b)) (hx : x < 2^b) :
    bitReverse.go b x acc < 2^k := by
  sorry
```

#### F2.S1.C2: `bitReverse_involution`

```lean
theorem bitReverse_involution (k : Nat) (x : Nat) (h : x < 2^k) :
    bitReverse k (bitReverse k x) = x := by
  -- Estrategia del Lean Expert:
  revert x
  induction k with
  | zero => simp [bitReverse]; intro x h; have : x = 0 := by omega; simp [*]
  | succ k ih =>
    intro x hx
    unfold bitReverse
    -- Usar helper lemma: go b x acc = acc * 2^b + bitReverse b x
    sorry
```

**Helper lemma crítico** (recomendado por QA):
```lean
lemma go_spec (b x acc : Nat) :
    bitReverse.go b x acc = acc * 2^b + bitReverse b x := by
  induction b generalizing x acc with
  | zero => simp [bitReverse, bitReverse.go]
  | succ b ih =>
    simp [bitReverse, bitReverse.go]
    sorry
```

#### F2.S1.C3: `stride_inverse_eq`

```lean
theorem stride_inverse_eq (m n : Nat) (i : Nat) (h : i < m * n) :
    strideIndex n m (strideIndex m n i) = i := by
  -- Estrategia del Lean Expert:
  unfold strideIndex
  -- Lemmas clave de Mathlib:
  -- - Nat.div_add_mod
  -- - Nat.mod_add_div
  -- - Nat.add_mul_mod_self_left
  rw [Nat.add_comm (i % m * n)]
  -- ... continuar con reescrituras
  sorry
```

### F2.S2: Fase 2 - Propiedades Atómicas de Perm (6 sorries)

**Meta**: Usar lemmas de Fase 1 para probar propiedades de constructores `Perm`.

| # | Sorry | Línea | Estrategia |
|---|-------|-------|------------|
| 5 | `apply_identity` | 159 | `rfl` o `simp [applyIndex]` |
| 6 | `apply_compose` | 165 | `rfl` o `simp [applyIndex]` |
| 7 | `swap_self_inverse` | 170 | `fin_cases` sobre Fin 2 |
| 8 | `stride_transpose_inverse_pointwise` | 176 | Usar `stride_inverse_eq` |
| 9 | `bitRev_self_inverse` | 181 | Usar `bitReverse_involution` |
| 10 | `toIndexList` bound | 152 | `omega` |

#### F2.S2.C1: Teoremas triviales

```lean
theorem apply_identity (i : Fin n) : Perm.applyIndex Perm.identity i = i := by
  rfl  -- Definicional

theorem apply_compose (p q : Perm n) (i : Fin n) :
    Perm.applyIndex (Perm.compose p q) i = Perm.applyIndex p (Perm.applyIndex q i) := by
  rfl  -- Definicional
```

#### F2.S2.C2: swap_self_inverse

```lean
theorem swap_self_inverse : Perm.compose Perm.swap Perm.swap = (Perm.identity : Perm 2) := by
  -- Estrategia: Extensionality sobre Fin 2
  -- Problema: Perm no tiene ext theorem nativo
  -- Solución: Probar equality via comportamiento en applyIndex
  sorry
```

**Insight del QA**: Necesitamos definir una forma de extensionality para `Perm`.

### F2.S3: Fase 3 - Álgebra de Permutaciones (10 sorries)

**Meta**: Probar propiedades de grupo usando extensionality pointwise.

| # | Sorry | Línea | Estrategia |
|---|-------|-------|------------|
| 11 | `compose_identity_left` | 205 | Extensionality |
| 12 | `compose_identity_right` | 210 | Extensionality |
| 13 | `compose_assoc` | 215 | Extensionality |
| 14 | `inverse_identity` | 219 | `rfl` o cases |
| 15 | `inverse_inverse` | 223 | Case analysis |
| 16 | `inverse_compose` | 228 | Extensionality + cases |
| 17 | `tensor_identity_left_one` | 242 | Aritmética i/n, i%n |
| 18 | `tensor_identity_right_one` | 250 | Aritmética i/n, i%n |
| 19 | `tensor_compose` | 256 | Extensionality + aritmética |
| 20 | `stride_factor_pointwise` | 196 | **El más complejo** |

#### F2.S3.C1: Problema de Extensionality

El tipo `Perm` es inductivo pero la igualdad es **estructural**, no semántica.
Dos `Perm` que producen el mismo mapeo pueden ser estructuralmente diferentes.

**Solución del Lean Expert**: Probar igualdad **pointwise** via `applyIndex`.

```lean
-- Lo que queremos probar:
theorem compose_identity_left (p : Perm n) : compose identity p = p

-- Pero esto requiere que compose identity p y p sean estructuralmente iguales
-- Sin embargo, compose identity p = Perm.compose Perm.identity p (constructor)
-- mientras que p puede ser cualquier constructor

-- Solución: Cambiar el statement a pointwise
theorem compose_identity_left_pointwise (p : Perm n) (i : Fin n) :
    applyIndex (compose identity p) i = applyIndex p i := by
  simp [applyIndex]
```

**Decisión arquitectónica**: Los teoremas algebraicos deben ser **pointwise** porque
`Perm` es un tipo inductivo sin extensionality nativa.

#### F2.S3.C2: stride_factor_pointwise (El "Final Boss")

```lean
theorem stride_factor_pointwise (k m n : Nat) (i : Nat) (h : i < k * (m * n)) :
    strideIndex k (m * n) i =
    strideIndex k n (strideIndex m n (i % (m * n))) +
    (i / (m * n)) * (k * n) := by
  -- Esta es la fórmula de factorización de stride del paper SPIRAL
  -- Requiere manipulación extensiva de div/mod
  -- Atacar al final cuando tengamos todos los lemmas aritméticos
  sorry
```

---

## F3: Grafo de Dependencias

```
                    ┌─────────────────────────┐
                    │    FASE 1: ARITMÉTICA   │
                    └─────────────────────────┘
                              │
        ┌─────────────────────┼─────────────────────┐
        ▼                     ▼                     ▼
┌───────────────┐    ┌───────────────┐    ┌───────────────┐
│ bitReverse_lt │    │ strideIndex_lt│    │stride_inverse_│
│               │    │               │    │    eq         │
└───────┬───────┘    └───────────────┘    └───────┬───────┘
        │                                         │
        ▼                                         ▼
┌───────────────┐                        ┌───────────────┐
│bitReverse_    │                        │stride_transp_ │
│ involution    │                        │inverse_point  │
└───────┬───────┘                        └───────────────┘
        │
        ▼
┌───────────────┐
│bitRev_self_   │
│  inverse      │
└───────────────┘

                    ┌─────────────────────────┐
                    │   FASE 2: ATÓMICAS      │
                    └─────────────────────────┘
                              │
    ┌─────────┬───────┬───────┴───────┬───────┬─────────┐
    ▼         ▼       ▼               ▼       ▼         ▼
apply_    apply_   swap_self_   toIndexList  ^^^      ^^^
identity  compose  inverse      bound       (ver arriba)

                    ┌─────────────────────────┐
                    │   FASE 3: ÁLGEBRA       │
                    └─────────────────────────┘
                              │
    ┌─────────┬───────┬───────┴───────┬───────┬─────────┐
    ▼         ▼       ▼               ▼       ▼         ▼
compose_* inverse_* tensor_*   stride_factor_pointwise
(6 sorries) (3 sorries) (3 sorries)    (1 sorry - FINAL)
```

---

## F4: Orden de Ataque

### F4.S1: Sesión 11A - Aritmética Bit Reversal

| Paso | Tarea | Dependencias |
|------|-------|--------------|
| 1 | Probar `go_lt` helper | - |
| 2 | Probar `bitReverse_lt` | go_lt |
| 3 | Probar `go_spec` helper | - |
| 4 | Probar `bitReverse_involution` | go_spec, bitReverse_lt |

### F4.S2: Sesión 11B - Aritmética Stride

| Paso | Tarea | Dependencias |
|------|-------|--------------|
| 5 | Probar `strideIndex_lt` | - |
| 6 | Probar `stride_inverse_eq` | Lemmas Nat.div/mod |

### F4.S3: Sesión 11C - Propiedades Atómicas

| Paso | Tarea | Dependencias |
|------|-------|--------------|
| 7 | Probar `apply_identity` | - |
| 8 | Probar `apply_compose` | - |
| 9 | Probar `toIndexList` bound | omega |
| 10 | Probar `swap_self_inverse` | Fin 2 cases |
| 11 | Probar `stride_transpose_inverse_pointwise` | stride_inverse_eq |
| 12 | Probar `bitRev_self_inverse` | bitReverse_involution |

### F4.S4: Sesión 11D - Álgebra

| Paso | Tarea | Dependencias |
|------|-------|--------------|
| 13-15 | `compose_identity_left/right`, `compose_assoc` | apply_* |
| 16-18 | `inverse_identity`, `inverse_inverse`, `inverse_compose` | Fase 2 |
| 19-20 | `tensor_identity_left/right_one` | Aritmética div/mod |
| 21 | `tensor_compose` | tensor_identity_* |
| 22 | `stride_factor_pointwise` | Todos |

---

## F5: Tácticas Recomendadas

### F5.S1: Para aritmética (Fase 1)

```lean
-- Lemmas de Mathlib a importar
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits

-- Tácticas principales
- omega  -- Para desigualdades lineales
- simp [Nat.div_add_mod, Nat.mod_add_div]  -- Para div/mod
- rw [Nat.add_mul_mod_self_left]  -- Para (a + b*n) % n
- rw [Nat.mul_div_cancel]  -- Para (a*n) / n
```

### F5.S2: Para permutaciones (Fases 2-3)

```lean
-- Para Fin n
- fin_cases i  -- Cuando n es pequeño (ej: Fin 2)
- exact ⟨val, proof⟩  -- Para construir Fin

-- Para extensionality (workaround)
- funext i  -- En teoremas pointwise
- simp [Perm.applyIndex]  -- Unfold aplicación

-- Para casos
- cases p with | identity => ... | compose => ...
```

### F5.S3: Imports necesarios

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits  -- Para Nat.testBit si necesario
import Mathlib.Data.Fin.Basic
```

---

## F6: Riesgos y Mitigaciones

| Riesgo | Probabilidad | Mitigación |
|--------|--------------|------------|
| `bitReverse` helper complejo | Alta | Probar `go_spec` primero |
| Extensionality de Perm | Alta | Usar statements pointwise |
| `stride_factor_pointwise` intratable | Media | Dejar para el final, construir lemmas |
| Imports de Mathlib lentos | Baja | Imports selectivos |

---

## F7: Métricas de Éxito

- [ ] 0 sorries en funciones auxiliares (bitReverse, strideIndex)
- [ ] 0 sorries en propiedades atómicas de Perm
- [ ] 0 sorries en álgebra de Perm
- [ ] `lake build` compila sin warnings
- [ ] Documentación de técnicas usadas

---

## F8: Recursos del Experto Lean

### Código sugerido para `bitReverse_involution`:

```lean
theorem bitReverse_involution (k : Nat) (x : Nat) (h : x < 2^k) :
    bitReverse k (bitReverse k x) = x := by
  revert x
  induction k with
  | zero => simp [bitReverse]; intro x h; have : x = 0 := by omega; simp [*]
  | succ k ih =>
    intro x hx
    unfold bitReverse
    simp [go]
    have : x / 2 < 2^k := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      omega
    rw [ih (x / 2) this]
    rw [Nat.mod_two_of_bodd x]
    rw [Nat.div_add_mod x 2]
```

### Código sugerido para `stride_inverse_eq`:

```lean
theorem stride_inverse_eq (m n : Nat) (i : Nat) (h : i < m * n) :
    strideIndex n m (strideIndex m n i) = i := by
  unfold strideIndex
  rw [Nat.add_comm (i % m * n)]
  rw [Nat.div_add_mod (i % m * n + i / m) m]
  rw [Nat.add_mul_mod_self_left]
  rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul h)]
  rw [Nat.mod_add_div]
```

---

## F9: Decisiones Arquitectónicas

### DD-030: Teoremas algebraicos como pointwise

**Problema**: `Perm` es inductivo → igualdad estructural ≠ igualdad semántica.

**Decisión**: Cambiar statements a forma pointwise:
```lean
-- En lugar de:
theorem compose_identity_left (p : Perm n) : compose identity p = p

-- Usar:
theorem compose_identity_left_pointwise (p : Perm n) (i : Fin n) :
    applyIndex (compose identity p) i = applyIndex p i
```

**Justificación**: Los teoremas originales son **falsos** estructuralmente.
`Perm.compose Perm.identity p` y `p` son términos diferentes.

**Consecuencia**: Todos los teoremas de Fase 3 serán pointwise.

---

*Plan preparado con consultas a Gemini QA (3 rondas) y DeepSeek Lean Expert (2 rondas).*
