# Sesión 2: Eliminación de Sorries - Phase 3 Cooley-Tukey

**Fecha**: 2026-01-31
**Objetivo**: Avanzar en sorries S8-S10 (Cooley-Tukey correctness)
**Referencia**: `PHASE3_COOLEY_TUKEY_STRATEGY.md`

---

## Resumen Ejecutivo

Esta sesión se enfocó en construir los **bridge lemmas** necesarios para la fórmula de splitting DFT. Se probaron exitosamente los lemas que conectan `ntt_term` con las sublistas `evens`/`odds`, y se documentó la estructura de prueba para el teorema principal.

### Progreso

| Lema/Teorema | Estado | Archivo |
|--------------|--------|---------|
| `foldl_split_parity` | ✅ PROBADO | Phase3Proof.lean |
| `foldl_even_reindex` | ✅ PROBADO | Phase3Proof.lean |
| `foldl_odd_reindex` | ✅ PROBADO | Phase3Proof.lean |
| `twiddle_even_factor_ntt` | ✅ PROBADO | Phase3Proof.lean |
| `twiddle_odd_factor_ntt` | ✅ PROBADO | Phase3Proof.lean |
| `ntt_term_even_index` | ✅ PROBADO | Phase3Proof.lean |
| `ntt_term_odd_index` | ✅ PROBADO | Phase3Proof.lean |
| `ntt_coeff_upper_half_split` | ⏳ SORRY (estructura documentada) | Phase3Proof.lean:825 |
| `ntt_coeff_lower_half_split` | ⏳ SORRY | Phase3Proof.lean:843 |

---

## Decisiones de Diseño Tomadas

### DD-035: Usar NTTFieldLawful en lugar de NTTField para CooleyTukeySplitting

**Problema**: La sección original usaba `[inst : NTTField F] [CommRing F] [IsDomain F]`, pero los lemas `twiddle_*_factor_ntt` requieren `NTTFieldLawful` para acceder a `pow_mul` y `pow_add`.

**Decisión**: Cambiar la variable de sección a:
```lean
variable {F : Type*} [inst : NTTFieldLawful F] [CommRing F] [IsDomain F]
```

**Justificación**:
- `NTTFieldLawful` extiende `NTTField`, proporcionando las leyes algebraicas necesarias
- Permite usar directamente `NTTFieldLawful.pow_mul`, `pow_add`, `mul_comm`, `mul_assoc`
- No afecta la aplicabilidad ya que GoldilocksField tiene `NTTFieldLawful`

**Impacto**:
- `NTT_spec_upper_half_eq` también requiere `NTTFieldLawful` ahora
- Consistencia con los lemas de twiddle factors

---

### DD-036: Helper Lemmas para Bridge entre inst.mul y *

**Problema**: Los lemas de `NTTFieldLawful` (como `mul_comm`, `mul_assoc`) usan la notación `*`, pero las definiciones como `ntt_term` usan `inst.mul` explícitamente. Lean no unifica automáticamente `inst.mul a b` con `a * b`.

**Decisión**: Crear helper lemmas simp:
```lean
@[simp] theorem inst_mul_eq_mul (a b : F) : inst.mul a b = a * b := rfl
@[simp] theorem inst_zero_eq_zero : inst.zero = (0 : F) := rfl
@[simp] theorem inst_add_eq_add (a b : F) : inst.add a b = a + b := rfl

theorem mul_zero_ntt (x : F) : x * (0 : F) = 0 := by
  rw [NTTFieldLawful.mul_comm, NTTFieldLawful.zero_mul]
```

**Justificación**:
- Permite usar `simp only [inst_mul_eq_mul]` para convertir entre representaciones
- Los lemas son `rfl` porque `inst.mul` y `*` son definitionally equal
- `mul_zero_ntt` derivado porque `NTTFieldLawful` solo tiene `zero_mul`, no `mul_zero`

**Ubicación**: Phase3Proof.lean, sección CooleyTukeySplitting (líneas 601-617)

---

### DD-037: Definición de ntt_term como Helper

**Problema**: `ntt_coeff` usa foldl con match sobre Option, lo cual dificulta razonar sobre términos individuales de la suma.

**Decisión**: Definir función auxiliar `ntt_term`:
```lean
def ntt_term (ω : F) (a : List F) (k : ℕ) (i : ℕ) : F :=
  match a[i]? with
  | some aᵢ => inst.mul aᵢ (inst.pow ω (i * k))
  | none => inst.zero
```

**Justificación**:
- Extrae el cálculo de un término individual de `ntt_coeff`
- Permite probar propiedades término a término (bridge lemmas)
- Facilita la conexión con `evens`/`odds` vía `evens_get`/`odds_get`

**Relación con ntt_coeff**:
```
ntt_coeff ω a k ≈ Σᵢ<a.length ntt_term ω a k i
```
(La equivalencia exacta requiere un lema adicional de lifting)

---

## Lemas Probados en Detalle

### 1. foldl_split_parity (Capa 2)

```lean
theorem foldl_split_parity (n : ℕ) (f : ℕ → F) :
    (List.range n).foldl (fun acc i => acc + f i) (0 : F) =
    (evenIndices n).foldl (fun acc i => acc + f i) (0 : F) +
    (oddIndices n).foldl (fun acc i => acc + f i) (0 : F)
```

**Estrategia**: Inducción sobre `n` con case split por `Nat.even_or_odd n`
- Caso `n` par: `n` va a `evenIndices`, usar `evenIndices_succ_of_even`
- Caso `n` impar: `n` va a `oddIndices`, usar `oddIndices_succ_of_odd`
- Táctica `abel` para rearreglar sumas

**Lemas auxiliares requeridos**:
- `evenIndices_succ_of_even`, `evenIndices_succ_of_odd`
- `oddIndices_succ_of_even`, `oddIndices_succ_of_odd`

**Nota técnica**: La definición de `Even n` en Lean es `n = k + k` (no `n = 2 * k`), lo cual afecta los patterns en las pruebas.

---

### 2. Twiddle Factor Lemmas para NTTFieldLawful (Capa 1b)

```lean
theorem twiddle_even_factor_ntt (ω : F) (m k : ℕ) :
    inst.pow ω (2 * m * k) = inst.pow (inst.pow ω 2) (m * k)

theorem twiddle_odd_factor_ntt (ω : F) (m k : ℕ) :
    inst.pow ω ((2 * m + 1) * k) =
    inst.mul (inst.pow ω k) (inst.pow (inst.pow ω 2) (m * k))
```

**Estrategia**:
- Usar `NTTFieldLawful.pow_mul` y `NTTFieldLawful.pow_add`
- Aritmética de exponentes: `2*m*k = 2*(m*k)` y `(2m+1)*k = k + 2*(m*k)`

**Dependencias**: Solo requiere `[inst : NTTFieldLawful F]`

---

### 3. ntt_term_even_index (Bridge Lemma - Capa 2)

```lean
theorem ntt_term_even_index (ω : F) (a : List F) (k m : ℕ)
    (hm : m < (evens a).length) :
    ntt_term ω a k (2 * m) = ntt_term (inst.mul ω ω) (evens a) k m
```

**Estrategia**:
1. Unfold `ntt_term` con `simp only [ntt_term]`
2. Usar `evens_get` para reescribir `(evens a)[m]? = a[2*m]?`
3. Case split sobre `a[2*m]?`:
   - `none`: Ambos lados son `inst.zero` → `rfl`
   - `some aᵢ`: Usar `twiddle_even_factor_ntt` y `pow_2_eq_mul_ntt`

**Insight clave**: El case split sobre Option es esencial porque el match en `ntt_term` produce diferentes resultados.

---

### 4. ntt_term_odd_index (Bridge Lemma - Capa 2)

```lean
theorem ntt_term_odd_index (ω : F) (a : List F) (k m : ℕ)
    (hm : m < (odds a).length) :
    ntt_term ω a k (2 * m + 1) =
    inst.mul (inst.pow ω k) (ntt_term (inst.mul ω ω) (odds a) k m)
```

**Estrategia**:
1. Similar a `ntt_term_even_index` pero más complejo
2. Caso `none`: Usar `mul_zero_ntt` con `.symm` (el goal está invertido)
3. Caso `some`:
   - Usar `twiddle_odd_factor_ntt` y `pow_2_eq_mul_ntt`
   - Manipulación algebraica: `aᵢ * (ωᵏ * p) = ωᵏ * (aᵢ * p)`
   - Usar calc block con `NTTFieldLawful.mul_assoc` y `mul_comm`

**Dificultad encontrada**: Los rewrites con `NTTFieldLawful.mul_comm` fallaban porque el goal usaba `*` (de Mul instance) pero el lemma requiere matching explícito. Solución: Usar calc block con `have` para definir los lemmas intermedios.

---

## Estructura de Prueba para ntt_coeff_upper_half_split

```lean
theorem ntt_coeff_upper_half_split (ω : F) (input : List F)
    (heven : 2 ∣ input.length) (k : ℕ) (hk : k < input.length / 2) :
    ntt_coeff ω input k =
    inst.add
      (ntt_coeff (inst.mul ω ω) (evens input) k)
      (inst.mul (inst.pow ω k) (ntt_coeff (inst.mul ω ω) (odds input) k))
```

**Estructura documentada en el código** (8 pasos):

1. **Step 1**: Expresar `ntt_coeff` como suma de `ntt_term`
2. **Step 2**: Split por paridad usando `foldl_split_parity`
3. **Step 3**: Reindexar suma par (i = 2m) usando `foldl_even_reindex`
4. **Step 4**: Aplicar `ntt_term_even_index`
5. **Step 5**: Reindexar suma impar (i = 2m+1) usando `foldl_odd_reindex`
6. **Step 6**: Aplicar `ntt_term_odd_index`
7. **Step 7**: Factorizar `ω^k` fuera de la suma impar
8. **Step 8**: Reconocer como `ntt_coeff` sobre evens y odds

**Gap técnico pendiente**: El Step 7 (factorizar constante fuera de foldl) requiere un lema adicional del tipo:
```lean
theorem foldl_factor_const (c : F) (f : ℕ → F) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + c * f i) 0 =
    c * (List.range n).foldl (fun acc i => acc + f i) 0
```

---

## Problemas Encontrados y Soluciones

### P1: Instance Diamond (NTTField + CommRing)

**Problema**: Cuando se tiene `[NTTField F] [CommRing F]`, hay dos instancias de `Mul F` que podrían no coincidir.

**Síntoma**: `rw [NTTFieldLawful.mul_comm]` fallaba con "pattern not found"

**Solución**:
- Usar `NTTFieldLawful` que proporciona una sola fuente de verdad
- Crear helper lemmas `inst_mul_eq_mul` para bridge explícito
- Usar calc blocks con `have` para lemmas intermedios

---

### P2: Even n expande a k + k, no 2 * k

**Problema**: `Even n` en Lean se define como `∃ k, n = k + k`, no `∃ k, n = 2 * k`

**Síntoma**: Patterns como `2 * k + 1 + 1` no matcheaban con `k + k + 1 + 1`

**Solución**: Ajustar los patterns en los lemmas `evenIndices_succ_*` y `oddIndices_succ_*`:
```lean
obtain ⟨k, rfl⟩ := he  -- Ahora n = k + k
have h1 : (k + k + 1 + 1) / 2 = k + 1 := by omega
```

---

### P3: API de Aristotle no funcionando

**Problema**: El agente QA Aristotle (Harmonic) tenía problemas de configuración:
- Modo formal: "validate_lean_project must be True when auto_add_imports is True"
- Modo informal: Timeout

**Estado**: No resuelto. Se procedió sin consulta QA externa.

**Recomendación**: Revisar configuración en `/Users/manuelpuebla/lean4-agent-orchestra/src/agents/aristotle_agent.py` líneas 77-78.

---

## Arquitectura de Capas Actualizada

```
CAPA 1: FUNDAMENTOS                    ✅ COMPLETA
├── primitive_root_two_eq_neg_one      ✅
├── twiddle_even_factor                ✅ (CommRing)
├── twiddle_odd_factor                 ✅ (CommRing)
├── twiddle_even_factor_ntt            ✅ (NTTFieldLawful) [NUEVA]
├── twiddle_odd_factor_ntt             ✅ (NTTFieldLawful) [NUEVA]
├── pow_2_eq_mul_ntt                   ✅ [NUEVA]
├── E_getElem_some, O_getElem_some     ✅
└── Helper lemmas (inst_*_eq_*)        ✅ [NUEVAS]

CAPA 2: DFT SPLITTING                  ✅ COMPLETA
├── foldl_split_parity                 ✅
├── foldl_even_reindex                 ✅
├── foldl_odd_reindex                  ✅
├── ntt_term (definición)              ✅ [NUEVA]
├── ntt_term_even_index                ✅ [NUEVA]
└── ntt_term_odd_index                 ✅ [NUEVA]

CAPA 3: COOLEY-TUKEY SPLITTING         ⏳ PARCIAL
├── ntt_coeff_upper_half_split         ⏳ SORRY (estructura documentada)
└── ntt_coeff_lower_half_split         ⏳ SORRY

CAPA 4: TEOREMA PRINCIPAL              ⏳ PENDIENTE
└── ct_recursive_eq_spec               ⏳ (depende de Capa 3)
```

---

## Próximos Pasos

### Inmediatos (para completar Capa 3):

1. **Probar lema de factorización**:
   ```lean
   theorem foldl_mul_factor (c : F) (f : ℕ → F) (n : ℕ) :
       (List.range n).foldl (fun acc i => acc + c * f i) 0 =
       c * (List.range n).foldl (fun acc i => acc + f i) 0
   ```

2. **Probar equivalencia ntt_coeff ↔ sum of ntt_term**:
   ```lean
   theorem ntt_coeff_eq_foldl_ntt_term (ω : F) (a : List F) (k : ℕ) :
       ntt_coeff ω a k =
       (List.range a.length).foldl (fun acc i => acc + ntt_term ω a k i) 0
   ```

3. **Completar `ntt_coeff_upper_half_split`** usando los lemas anteriores

4. **Completar `ntt_coeff_lower_half_split`** usando:
   - `ntt_coeff_upper_half_split`
   - `twiddle_half_eq_neg_one` (ya probado en RootsOfUnity.lean)

### Posteriores:

5. Probar `ct_recursive_eq_spec` (S10) por inducción fuerte
6. Probar `ntt_intt_recursive_roundtrip` (S11)

---

## Archivos Modificados

| Archivo | Cambios |
|---------|---------|
| `AmoLean/NTT/Phase3Proof.lean` | +200 líneas aprox. Nuevos lemas, helpers, bridge lemmas |

---

## Métricas

- **Sorries cerrados en sesión**: 0 (pero 7 lemas auxiliares nuevos probados)
- **Sorries restantes en Phase3Proof.lean**: 2
- **Tiempo de sesión**: ~4 horas
- **Bloqueos por tooling**: API Aristotle no funcionó

---

## Lecciones Aprendidas

1. **Type class diamonds son reales**: Cuando hay múltiples instancias de la misma clase, los rewrites pueden fallar silenciosamente.

2. **calc blocks son útiles**: Para manipulaciones algebraicas complejas, es mejor usar calc con pasos explícitos que cadenas de `rw`.

3. **Las definiciones de Mathlib importan**: `Even n` se define como `k + k`, no `2 * k`. Esto afecta pattern matching.

4. **Bridge lemmas son esenciales**: Antes de intentar el teorema principal, construir los lemmas que conectan las diferentes representaciones.

5. **La documentación en el código ayuda**: El comment block con la estructura de 8 pasos para `ntt_coeff_upper_half_split` facilita retomar el trabajo.
