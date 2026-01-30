# Plan de Trabajo - Verificación NTT Radix-4

## Estado Inicial

| Archivo | Sorries | Descripción |
|---------|---------|-------------|
| Correctness.lean | 4 | cooley_tukey_upper_half, lower_half, ct_recursive_eq_spec, roundtrip |
| Radix4.lean | 2 | NTT_radix4 implementation, auxiliary lemmas |
| Equivalence.lean | 3 | radix4_eq_spec, radix2_eq_radix4, ntt_algorithm_choice |
| Butterfly4.lean | 3 | butterfly4 matrix properties |
| **Total** | **13** | - |

---

## Fase 0: Investigación Mathlib

### Objetivo
Identificar lemas existentes que podemos reutilizar.

### Tareas
- [ ] Buscar `IsPrimitiveRoot` y lemas asociados
- [ ] Buscar `geom_sum` para series geométricas
- [ ] Buscar `Finset.sum_bij` para reindexación
- [ ] Buscar `ZMod` y propiedades de campos finitos
- [ ] Documentar hallazgos en `MATHLIB_LEMMAS.md`

### Entregable
Documento con inventario de lemas disponibles.

---

## Fase 1: Lemas Fundamentales

### Objetivo
Establecer lemas que todas las fases posteriores usarán.

### Lemas a Probar

#### 1.1 omega_pow_ne_one
```lean
lemma omega_pow_ne_one (hω : IsPrimitiveRoot ω N) {n : ℕ} (hn : 0 < n) (hnN : n < N) :
    ω ^ n ≠ 1
```
**Estrategia**: Usar `hω.pow_eq_one_iff_dvd`

#### 1.2 omega_pow_sub_one_ne_zero
```lean
lemma omega_pow_sub_one_ne_zero (hω : IsPrimitiveRoot ω N) {n : ℕ} (hn : ¬ N ∣ n) :
    ω ^ n - 1 ≠ 0
```
**Estrategia**: Usar 1.1

#### 1.3 roots_of_unity_sum
```lean
lemma roots_of_unity_sum (hω : IsPrimitiveRoot ω N) (n : ℕ) :
    (∑ k : Fin N, ω ^ (n * k.val)) = if N ∣ n then (N : F) else 0
```
**Estrategia**: Split cases, usar `geom_sum_eq` para caso n ≢ 0

#### 1.4 sum_split_even_odd
```lean
lemma sum_split_even_odd (f : Fin (2*n) → F) :
    (∑ k, f k) = (∑ j, f ⟨2*j, _⟩) + (∑ j, f ⟨2*j+1, _⟩)
```
**Estrategia**: Usar `Finset.sum_disj_union`

#### 1.5 psi_sq_eq_neg_one
```lean
lemma psi_sq_eq_neg_one (hω : IsPrimitiveRoot ω N) (hN4 : 4 ∣ N) :
    (ω ^ (N/4))^2 = -1
```
**Estrategia**: `ω^(N/2) = -1` de `IsPrimitiveRoot`

### Verificación
```bash
lake build Radix4NTT.Fundamentals
```

---

## Fase 2: Correctness.lean - Cooley-Tukey

### Objetivo
Probar la descomposición recursiva.

### Lemas a Probar

#### 2.1 pow_even_index
```lean
lemma pow_even_index (ω : F) (k j : ℕ) :
    ω ^ (k * (2 * j)) = (ω^2) ^ (k * j)
```

#### 2.2 pow_odd_index
```lean
lemma pow_odd_index (ω : F) (k j : ℕ) :
    ω ^ (k * (2 * j + 1)) = ω^k * (ω^2) ^ (k * j)
```

#### 2.3 cooley_tukey_upper_half
```lean
theorem cooley_tukey_upper_half (x : Fin (2*n) → F) (ω : F)
    (hω : IsPrimitiveRoot ω (2*n)) (k : Fin n) :
    NTT_spec ω x ⟨k.val, _⟩ =
      NTT_spec (ω^2) (x ∘ (·*2)) k + ω^k.val * NTT_spec (ω^2) (x ∘ (·*2+1)) k
```

#### 2.4 cooley_tukey_lower_half
```lean
theorem cooley_tukey_lower_half (x : Fin (2*n) → F) (ω : F)
    (hω : IsPrimitiveRoot ω (2*n)) (k : Fin n) :
    NTT_spec ω x ⟨k.val + n, _⟩ =
      NTT_spec (ω^2) (x ∘ (·*2)) k - ω^k.val * NTT_spec (ω^2) (x ∘ (·*2+1)) k
```

#### 2.5 NTT_spec_one
```lean
lemma NTT_spec_one (x : Fin 1 → F) (ω : F) : NTT_spec ω x = x
```

#### 2.6 ct_recursive_eq_spec
```lean
theorem ct_recursive_eq_spec (x : Fin N → F) (ω : F) (hω : IsPrimitiveRoot ω N) :
    NTT_recursive ω x = NTT_spec ω x
```

### Verificación
```bash
lake build Radix4NTT.Correctness
# Esperado: 0 sorry
```

---

## Fase 3: Butterfly4.lean

### Objetivo
Probar propiedades de la operación butterfly de 4 puntos.

### Definiciones
```lean
def T4_matrix (ψ : F) : Matrix (Fin 4) (Fin 4) F := ...
def T4_inv_matrix (ψ : F) : Matrix (Fin 4) (Fin 4) F := ...
```

### Lemas a Probar

#### 3.1 butterfly4_eq_T4_mul
```lean
lemma butterfly4_eq_T4_mul (x : Fin 4 → F) (ψ : F) :
    butterfly4 ψ x = T4_matrix ψ *ᵥ x
```

#### 3.2 T4_invertible
```lean
lemma T4_invertible (ψ : F) (hψ : ψ^2 = -1) (h4 : IsUnit (4 : F)) :
    T4_matrix ψ * T4_inv_matrix ψ = 1
```

### Verificación
```bash
lake build Radix4NTT.Butterfly4
# Esperado: 0 sorry
```

---

## Fase 4: Radix4.lean

### Objetivo
Reemplazar el axioma con implementación real.

### Tareas
- [ ] Definir `split4` y `combine4`
- [ ] Implementar `NTT_radix4` con recursión terminante
- [ ] Probar `radix4_eq_spec`

### Lemas a Probar

#### 4.1 split4_combine4_id
```lean
lemma split4_combine4_id (ψ : F) (x : Fin (4*n) → F) :
    combine4 ψ (split4 x) = ... -- permutación de NTT aplicada
```

#### 4.2 radix4_eq_spec
```lean
theorem radix4_eq_spec (x : Fin N → F) (ω : F) (hω : IsPrimitiveRoot ω N) :
    NTT_radix4 ω N x = NTT_spec ω x
```

### Verificación
```bash
lake build Radix4NTT.Radix4
# Esperado: 0 sorry
```

---

## Fase 5: Equivalence.lean

### Objetivo
Probar equivalencia entre implementaciones.

### Lemas a Probar

#### 5.1 radix2_eq_radix4
```lean
theorem radix2_eq_radix4 (x : Fin N → F) (ω : F) (hω : IsPrimitiveRoot ω N) :
    NTT_radix2 ω x = NTT_radix4 ω N x
```
**Estrategia**: Transitividad via NTT_spec

#### 5.2 ntt_algorithm_choice
```lean
theorem ntt_algorithm_choice (x : Fin N → F) (ω : F) (hω : IsPrimitiveRoot ω N) :
    NTT ω x = NTT_spec ω x
```

### Verificación
```bash
lake build Radix4NTT.Equivalence
# Esperado: 0 sorry
```

---

## Fase 6: Roundtrip

### Objetivo
Probar inversibilidad de la transformada.

### Lema Principal
```lean
theorem ntt_intt_roundtrip (x : Fin N → F) (ω : F)
    (hω : IsPrimitiveRoot ω N) (hN : IsUnit (N : F)) :
    INTT_spec ω (NTT_spec ω x) = x
```

### Estrategia
1. Expandir definiciones
2. Intercambiar orden de sumas con `Finset.sum_comm`
3. Aplicar `roots_of_unity_sum`
4. Usar `Finset.sum_ite_eq'` para extraer término diagonal

### Verificación
```bash
lake build Radix4NTT
# Esperado: 0 sorry total
```

---

## Fase 7: Tests Unitarios

### Objetivo
Verificar corrección con valores concretos.

### Tests
```lean
-- Test 1: NTT de delta
example : NTT_spec (2 : ZMod 5) ![1, 0, 0, 0] = ![1, 1, 1, 1] := by native_decide

-- Test 2: Roundtrip
example : INTT_spec (2 : ZMod 5) (NTT_spec (2 : ZMod 5) ![1, 2, 3, 4]) =
          ![1, 2, 3, 4] := by native_decide

-- Test 3: Equivalencia
example : NTT_radix2 (2 : ZMod 5) ![1, 2, 3, 4] =
          NTT_radix4 (2 : ZMod 5) 4 ![1, 2, 3, 4] := by native_decide
```

### Verificación
```bash
lake build
# Todos los tests deben pasar
```

---

## Cronograma de Verificación

| Fase | Comando | Criterio de Éxito |
|------|---------|-------------------|
| 0 | `grep` | Documento completo |
| 1 | `lake build Fundamentals` | 0 sorry |
| 2 | `lake build Correctness` | 0 sorry |
| 3 | `lake build Butterfly4` | 0 sorry |
| 4 | `lake build Radix4` | 0 sorry |
| 5 | `lake build Equivalence` | 0 sorry |
| 6 | `lake build` (todo) | 0 sorry total |
| 7 | `lake build` + tests | Todos pasan |

---

## Métricas de Progreso

### Antes de Implementación
- Sorries totales: 13
- Archivos con sorry: 4

### Objetivo Final
- Sorries totales: 0
- Archivos con sorry: 0
- Tests unitarios: ≥ 3 pasando
