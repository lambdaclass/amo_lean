# Fase 3: Estrategia de Prueba Cooley-Tukey

**Fecha**: 2026-01-31
**Objetivo**: Eliminar sorries S8, S9, S10 (Cooley-Tukey correctness)
**Tiempo estimado**: 20-25 horas

---

## 1. Sorries a Eliminar

### S8: `cooley_tukey_upper_half` (Correctness.lean:80)

```lean
theorem cooley_tukey_upper_half {n : ℕ} (hn : n > 0) (hn_even : 2 ∣ n)
    (ω : F) (hω : IsPrimitiveRoot ω n)
    (input : List F) (h_len : input.length = n)
    (E O : List F) (hE : E = NTT_spec (ω^2) (evens input))
    (hO : O = NTT_spec (ω^2) (odds input))
    (k : ℕ) (hk : k < n / 2) :
    (NTT_spec ω input)[k]? = some (E[k]?.getD 0 + ω^k * O[k]?.getD 0)
```

**Significado matemático**: X_k = E_k + ω^k · O_k para k < n/2

### S9: `cooley_tukey_lower_half` (Correctness.lean:95)

```lean
theorem cooley_tukey_lower_half {n : ℕ} (hn : n > 2) (hn_even : 2 ∣ n)
    (ω : F) (hω : IsPrimitiveRoot ω n)
    (input : List F) (h_len : input.length = n)
    (E O : List F) (hE : E = NTT_spec (ω^2) (evens input))
    (hO : O = NTT_spec (ω^2) (odds input))
    (k : ℕ) (hk : k < n / 2) :
    (NTT_spec ω input)[k + n/2]? = some (E[k]?.getD 0 - ω^k * O[k]?.getD 0)
```

**Significado matemático**: X_{k+n/2} = E_k - ω^k · O_k (usa ω^{n/2} = -1)

### S10: `ct_recursive_eq_spec` (Correctness.lean:120)

```lean
theorem ct_recursive_eq_spec (ω : F) (input : List F)
    (h_pow2 : ∃ k : ℕ, input.length = 2^k) :
    NTT_recursive ω input = NTT_spec ω input
```

**Significado**: El algoritmo recursivo Cooley-Tukey es correcto respecto a la especificación.

---

## 2. Recursos Disponibles (Probados)

### RootsOfUnity.lean

| Lema | Línea | Descripción |
|------|-------|-------------|
| `twiddle_half_eq_neg_one` | 226 | ω^(n/2) = -1 para n > 2 par |
| `twiddle_shift` | 249 | ω^(k+n/2) = -ω^k |
| `squared_is_primitive` | 268 | ω² es raíz primitiva de orden n/2 |
| `sum_of_powers_zero` | 140 | Σᵢ ω^i = 0 para raíz primitiva |
| `powSum_nonzero` | 184 | Σₖ ω^(d·k) = 0 para 0 < d < n |
| `IsPrimitiveRoot.pow_eq_pow_mod` | 65 | ω^k depende solo de k mod n |

### Properties.lean

| Lema | Línea | Descripción |
|------|-------|-------------|
| `orthogonality_sum_lt` | 51 | Σₖ ω^(d·k) = n si d=0, sino 0 |
| `ntt_additive` | 111 | NTT(a+b) = NTT(a) + NTT(b) |
| `ntt_scale` | 121 | NTT(c·a) = c·NTT(a) |
| `ntt_linear` | 131 | Combinación de additive + scale |

### ListUtils.lean

| Lema | Descripción |
|------|-------------|
| `evens`, `odds` | Funciones de extracción |
| `evens_length`, `odds_length` | Preservación de longitud |
| `evens_get`, `odds_get` | Acceso a elementos |

### CooleyTukey.lean

| Definición/Lema | Descripción |
|-----------------|-------------|
| `NTT_recursive` | Algoritmo con prueba de terminación |
| `NTT_recursive_length` | Preservación de longitud |

---

## 3. Decisiones de Diseño

### DD-030: Enfoque por Capas (Staged Approach)

**Decisión**: Probar primero para `ntt_coeff_finset` (Finset-based), diferir bridge a List.

**Justificación**:
- `ntt_coeff_finset` usa `Finset.sum` que tiene mejor soporte en Mathlib
- Las propiedades algebraicas (sum_filter, sum_comm) son más limpias
- El bridge lemma puede venir después sin bloquear el progreso

**Impacto**: Menor acoplamiento, pruebas más limpias.

### DD-031: Inducción sobre Exponente

**Decisión**: Usar inducción sobre `k` donde `n = 2^k`, no strong induction sobre `n`.

**Justificación**:
- La estructura recursiva de Cooley-Tukey divide n → n/2
- Con `n = 2^k`, la división es `2^k → 2^(k-1)`
- Evita probar que "n/2 preserva ser potencia de 2"

**Patrón de prueba**:
```lean
obtain ⟨k, hk⟩ := h_pow2
induction k generalizing a with
| zero => -- n = 1, caso base (singleton)
| succ k' ih => -- n = 2^(k'+1), usar ih para subproblemas
```

### DD-032: Manejo del Caso n = 2

**Decisión**: No tratar n = 2 como caso especial. Probar lema general `primitive_root_two_eq_neg_one`.

**Justificación**:
- Para n = 2, ω es raíz primitiva de orden 2, entonces ω² = 1 y ω ≠ 1
- Esto implica ω = -1 (única solución en un dominio)
- La fórmula Cooley-Tukey funciona uniformemente

**Lema a probar**:
```lean
theorem primitive_root_two_eq_neg_one {ω : F} (hω : IsPrimitiveRoot ω 2) : ω = -1
```

### DD-033: Descomposición de Sumas con sum_filter

**Decisión**: Usar `Finset.sum_filter` con predicado de paridad, no construir Finsets explícitos.

**Justificación**:
- `Finset.sum_filter_add_sum_filter_not` ya existe en Mathlib
- Evita definir `evenIndices`, `oddIndices` como Finsets separados
- Predicado `fun i => i.val % 2 = 0` es suficiente

**Patrón**:
```lean
have h := Finset.sum_filter_add_sum_filter_not Finset.univ
  (fun i : Fin n => i.val % 2 = 0) f
```

### DD-034: Well-Definedness Explícita

**Decisión**: Probar lemas de well-definedness antes de las pruebas principales.

**Justificación**:
- `E[k]?.getD 0` puede ocultar errores si k está fuera de rango
- Necesitamos saber que `E[k]? = some _` para índices válidos
- Hace las pruebas más robustas y claras

**Lemas requeridos**:
```lean
theorem E_getElem_some (E : List F) (hE : E = NTT_spec (ω^2) (evens input))
    (k : ℕ) (hk : k < n/2) : ∃ e, E[k]? = some e

theorem O_getElem_some (O : List F) (hO : O = NTT_spec (ω^2) (odds input))
    (k : ℕ) (hk : k < n/2) : ∃ o, O[k]? = some o
```

---

## 4. Arquitectura de Lemas Auxiliares

```
┌─────────────────────────────────────────────────────────────────────┐
│                    CAPA 4: TEOREMA PRINCIPAL                        │
│                                                                     │
│  ct_recursive_eq_spec : NTT_recursive = NTT_spec                   │
│  (Inducción sobre exponente k donde n = 2^k)                       │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    CAPA 3: COOLEY-TUKEY                             │
│                                                                     │
│  cooley_tukey_upper_half : X_k = E_k + ω^k·O_k                     │
│  cooley_tukey_lower_half : X_{k+n/2} = E_k - ω^k·O_k               │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    CAPA 2: DFT SPLITTING                            │
│                                                                     │
│  ntt_coeff_split : Σⱼ aⱼ·ω^{jk} = Σₘ a_{2m}·ω^{2mk} + Σₘ a_{2m+1}·ω^{(2m+1)k} │
│  even_sum_reindex : Σ over evens → Σ over Fin(n/2)                 │
│  odd_sum_reindex : Σ over odds → Σ over Fin(n/2)                   │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    CAPA 1: FUNDAMENTOS                              │
│                                                                     │
│  primitive_root_two_eq_neg_one : IsPrimitiveRoot ω 2 → ω = -1      │
│  twiddle_even_factor : ω^{2mk} = (ω²)^{mk}                         │
│  twiddle_odd_factor : ω^{(2m+1)k} = ω^k · (ω²)^{mk}                │
│  E_getElem_some, O_getElem_some : Well-definedness                 │
│  ntt_spec_length : (NTT_spec ω a).length = a.length                │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 5. Plan de Ejecución

### Fase 3.1: Lemas Fundamentales (Capa 1)

| Orden | Lema | Archivo | Horas Est. |
|-------|------|---------|------------|
| 3.1.1 | `primitive_root_two_eq_neg_one` | Phase3Proof.lean | 1h |
| 3.1.2 | `twiddle_even_factor` | Phase3Proof.lean | 0.5h |
| 3.1.3 | `twiddle_odd_factor` | Phase3Proof.lean | 0.5h |
| 3.1.4 | `ntt_spec_length` | Phase3Proof.lean | 1h |
| 3.1.5 | `E_getElem_some`, `O_getElem_some` | Phase3Proof.lean | 1h |
| **Subtotal** | | | **4h** |

### Fase 3.2: DFT Splitting (Capa 2)

| Orden | Lema | Archivo | Horas Est. |
|-------|------|---------|------------|
| 3.2.1 | `sum_filter_even_odd` | Phase3Proof.lean | 2h |
| 3.2.2 | `even_sum_reindex` | Phase3Proof.lean | 2h |
| 3.2.3 | `odd_sum_reindex` | Phase3Proof.lean | 2h |
| 3.2.4 | `ntt_coeff_split` | Phase3Proof.lean | 2h |
| **Subtotal** | | | **8h** |

### Fase 3.3: Cooley-Tukey (Capa 3)

| Orden | Sorry | Archivo | Horas Est. |
|-------|-------|---------|------------|
| 3.3.1 | S8 `cooley_tukey_upper_half` | Correctness.lean | 3h |
| 3.3.2 | S9 `cooley_tukey_lower_half` | Correctness.lean | 2h |
| **Subtotal** | | | **5h** |

### Fase 3.4: Teorema Principal (Capa 4)

| Orden | Sorry | Archivo | Horas Est. |
|-------|-------|---------|------------|
| 3.4.1 | S10 `ct_recursive_eq_spec` | Correctness.lean | 8h |
| **Subtotal** | | | **8h** |

**Total estimado**: ~25 horas

---

## 6. Riesgos y Mitigaciones

### R1: Aritmética de índices compleja (ALTO)

**Problema**: Muchas pruebas requieren `k < n/2 → 2k < n`, `evens a [k] = a[2k]`, etc.

**Mitigación**:
- Usar `omega` agresivamente
- Crear lemas @[simp] para patrones comunes
- Documentar invariantes de índices

### R2: Coerciones ℕ → F (MEDIO)

**Problema**: Mezclar `n : ℕ` con `(n : F)` en expresiones.

**Mitigación**:
- Ser explícito: siempre escribir `(n : F)` cuando se refiere al elemento de campo
- Verificar que n < char F (siempre verdadero para Goldilocks)

### R3: Bridge lemma lento (MEDIO)

**Problema**: Convertir entre `List.foldl` y `Finset.sum` es no trivial.

**Mitigación**:
- DD-030: Diferir el bridge, trabajar con Finset primero
- Si es necesario, usar stepping stones:
  1. `foldl_add_eq_finset_sum`
  2. `range_sum_eq_fin_sum`

### R4: Caso n = 2 (BAJO después de DD-032)

**Problema**: `twiddle_half_eq_neg_one` requiere n > 2.

**Mitigación**: `primitive_root_two_eq_neg_one` maneja el caso uniformemente.

---

## 7. Verificación

### Tests de Sanidad (native_decide)

Ya existen en Correctness.lean (líneas 148-154):
```lean
example : NTT_recursive_test 4 = true := by native_decide
example : NTT_recursive_test 8 = true := by native_decide
```

### Criterios de Éxito

1. [ ] `lake build AmoLean.NTT.Correctness` sin warnings de sorry
2. [ ] Tests native_decide siguen pasando
3. [ ] No se introducen nuevos axiomas
4. [ ] Código documentado con comentarios explicativos

---

## 8. Bibliografía Consultada

1. **Cooley & Tukey (1965)** - "An Algorithm for the Machine Calculation of Complex Fourier Series"
2. **CLRS Cap. 30** - "Introduction to Algorithms" - FFT/NTT
3. **Mathlib Documentation** - `Finset.sum_filter`, `IsPrimitiveRoot`
4. **Trieu (2025)** - "Formally Verified NTT" (ANSSI) - Estrategia de refinamiento por capas

---

## 9. Notas de Implementación

### Archivo Principal: `AmoLean/NTT/Phase3Proof.lean`

Contendrá todos los lemas auxiliares de Capas 1-2.

### Integración

Los lemas probados en Phase3Proof.lean se usarán para cerrar los sorries en:
- `Correctness.lean` (S8, S9, S10)

### Convenciones

- Usar `abbrev P := GOLDILOCKS_PRIME` consistente con Phase2Proof.lean
- Mantener namespace `AmoLean.NTT.Phase3Proof`
- Importar `AmoLean.NTT.RootsOfUnity` y `AmoLean.NTT.Properties`
