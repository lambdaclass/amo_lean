# Plan de Eliminacion de Sorries - amo-lean NTT

**Fecha**: 2026-01-30
**Objetivo**: Cerrar TODOS los sorries del modulo NTT (17 sorries + 7 axiomas)

---

## Inventario Completo de Sorries y Axiomas

### Resumen

| Categoria | Cantidad | Ubicacion |
|-----------|----------|-----------|
| Sorries NTT Core | 14 | Spec, Properties, Correctness, Bounds, LazyButterfly |
| Sorries Radix4 | 3 | Algorithm |
| Axiomas Radix4 | 7 | Algorithm, Butterfly4, Equivalence |
| **TOTAL** | **24** | |

---

## Jerarquia de Dependencias

```
                    ┌─────────────────────────────────────┐
                    │     NIVEL 0: FUNDAMENTOS            │
                    │     (Sin dependencias internas)     │
                    └─────────────────────────────────────┘
                                    │
    ┌───────────────────────────────┼───────────────────────────────┐
    │                               │                               │
    ▼                               ▼                               ▼
┌─────────────┐            ┌─────────────────┐            ┌─────────────────┐
│ ntt_coeff_  │            │ lazy_sub_       │            │ ofStrict_bound  │
│ add/scale   │            │ simulates       │            │ (Bounds.lean)   │
│ (Spec.lean) │            │ (Bounds.lean)   │            │                 │
└─────────────┘            └─────────────────┘            └─────────────────┘
      │                           │                               │
      └───────────┬───────────────┴───────────────────────────────┘
                  │
                  ▼
         ┌────────────────────────────────────────┐
         │      NIVEL 1: SIMULACION LAZY         │
         │   lazy_butterfly_*_simulates          │
         │   lazy_butterfly_sum                  │
         │   (LazyButterfly.lean)                │
         └────────────────────────────────────────┘
                          │
                          ▼
         ┌────────────────────────────────────────┐
         │      NIVEL 2: COOLEY-TUKEY            │
         │   cooley_tukey_upper/lower_half       │
         │   (Correctness.lean)                  │
         └────────────────────────────────────────┘
                          │
                          ▼
         ┌────────────────────────────────────────┐
         │      NIVEL 3: CORRECCION ALGORITMO    │
         │   ct_recursive_eq_spec                │
         │   ntt_intt_recursive_roundtrip        │
         │   (Correctness.lean)                  │
         └────────────────────────────────────────┘
                          │
                          ▼
         ┌────────────────────────────────────────┐
         │      NIVEL 4: IDENTIDAD CENTRAL       │
         │   intt_ntt_identity_finset            │
         │   ntt_intt_identity                   │
         │   (Properties.lean, Spec.lean)        │
         └────────────────────────────────────────┘
                          │
                          ▼
         ┌────────────────────────────────────────┐
         │      NIVEL 5: PROPIEDADES AVANZADAS   │
         │   parseval                            │
         │   (Properties.lean)                   │
         └────────────────────────────────────────┘
                          │
                          ▼
         ┌────────────────────────────────────────┐
         │      NIVEL 6: RADIX-4                 │
         │   NTT_radix4_singleton/nil            │
         │   combineRadix4_uses_butterfly4       │
         │   + 7 axiomas                         │
         │   (Radix4/*)                          │
         └────────────────────────────────────────┘
```

---

## Analisis Detallado por Sorry/Axioma

### NIVEL 0: Fundamentos (Aritmetica Modular)

#### S1. `ntt_coeff_add` (Spec.lean:92)
```lean
theorem ntt_coeff_add (ω : F) (a b : List F) (k : Nat)
    (heq : a.length = b.length) :
    ntt_coeff ω (List.zipWith inst.add a b) k =
    inst.add (ntt_coeff ω a k) (ntt_coeff ω b k)
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟢 BAJA |
| **Dependencias** | Ninguna |
| **Tecnica** | Inductcion sobre listas + distributividad de foldl |
| **Bibliografia** | Mathlib: `List.foldl_map`, `List.zipWith_*` |
| **Estimacion** | 1-2 horas |

**Estrategia de prueba**:
1. Induccion sobre `a.length`
2. Caso base: listas vacias trivial
3. Caso inductivo: usar `List.foldl_cons` y propiedades de campo

---

#### S2. `ntt_coeff_scale` (Spec.lean:98)
```lean
theorem ntt_coeff_scale (ω : F) (a : List F) (c : F) (k : Nat) :
    ntt_coeff ω (a.map (inst.mul c)) k =
    inst.mul c (ntt_coeff ω a k)
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟢 BAJA |
| **Dependencias** | Ninguna |
| **Tecnica** | Induccion + conmutatividad/distributividad |
| **Bibliografia** | Mathlib: `Finset.mul_sum` (ya usado en Properties.lean:125) |
| **Estimacion** | 1 hora |

**Nota**: Ya tenemos `ntt_scale` probado para Finset en Properties.lean:121-128. Solo necesitamos trasladar a la version con listas.

---

#### S3. `lazy_sub_simulates` (Bounds.lean:200)
```lean
theorem lazy_sub_simulates (a b : LazyGoldilocks)
    (ha : a.val < BOUND_2P) (hb : b.val < BOUND_2P) :
    (sub a b ha hb).reduceNat = strictSubNat a.reduceNat b.reduceNat
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟢 BAJA |
| **Dependencias** | Ninguna |
| **Tecnica** | Aritmetica modular: `(a + 2p - b) % p = (a - b) % p` |
| **Bibliografia** | Mathlib: `Nat.add_mod`, `Nat.sub_mod` |
| **Estimacion** | 1-2 horas |

**Estrategia**:
```
(a + 2p - b) % p
= ((a % p) + (2p % p) - (b % p)) % p    [Nat.add_mod, Nat.sub_mod]
= ((a % p) + 0 - (b % p)) % p           [2p % p = 0]
= (a % p - b % p) % p                   [simplificacion]
```

---

#### S4. `ofStrict_bound` (Bounds.lean:216)
```lean
theorem ofStrict_bound (x : GoldilocksField) :
    (ofStrict x).val < GOLDILOCKS_PRIME
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟢 BAJA |
| **Dependencias** | Invariante de GoldilocksField |
| **Tecnica** | Extraer invariante del constructor |
| **Bibliografia** | Definicion de GoldilocksField en Field/Goldilocks.lean |
| **Estimacion** | 30 min |

**Prerequisito**: Verificar que GoldilocksField tiene invariante `value < ORDER`.

---

### NIVEL 1: Simulacion Lazy Butterfly

#### S5. `lazy_butterfly_fst_simulates` (LazyButterfly.lean:147)
```lean
theorem lazy_butterfly_fst_simulates (a b : LazyGoldilocks)
    (twiddle : Nat) (...) :
    (lazy_butterfly_fst a b twiddle ha hb htw).reduceNat =
    (strict_butterfly_nat a.reduceNat b.reduceNat twiddle).1
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟡 MEDIA |
| **Dependencias** | S3 (lazy_sub_simulates) |
| **Tecnica** | Desplegar definiciones + usar S3 |
| **Bibliografia** | Mathlib: `Nat.add_mod`, `Nat.mul_mod` |
| **Estimacion** | 2-3 horas |

---

#### S6. `lazy_butterfly_snd_simulates` (LazyButterfly.lean:160)

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟡 MEDIA |
| **Dependencias** | S3 (lazy_sub_simulates) |
| **Tecnica** | Analogo a S5 |
| **Estimacion** | 1-2 horas (reutilizando S5) |

---

#### S7. `lazy_butterfly_sum` (LazyButterfly.lean:181)
```lean
theorem lazy_butterfly_sum (...) :
    ((lazy_butterfly ...).1.reduceNat +
     (lazy_butterfly ...).2.reduceNat) % GOLDILOCKS_PRIME =
    (2 * a.reduceNat) % GOLDILOCKS_PRIME
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟡 MEDIA |
| **Dependencias** | S5, S6 |
| **Tecnica** | `(a+t) + (a+2p-t) = 2a + 2p ≡ 2a (mod p)` |
| **Bibliografia** | Aritmetica modular basica |
| **Estimacion** | 1-2 horas |

---

### NIVEL 2: Cooley-Tukey Recurrence

#### S8. `cooley_tukey_upper_half` (Correctness.lean:80)
```lean
theorem cooley_tukey_upper_half {n : ℕ} (hn : n > 0) (hn_even : 2 ∣ n)
    (ω : F) (hω : IsPrimitiveRoot ω n)
    (input : List F) (h_len : input.length = n)
    (E O : List F)
    (k : ℕ) (hk : k < n / 2) :
    (NTT_spec ω input)[k]? =
    some (inst.add (E[k]?.getD inst.zero)
                   (inst.mul (inst.pow ω k) (O[k]?.getD inst.zero)))
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟠 MEDIA-ALTA |
| **Dependencias** | RootsOfUnity (pow_mul, etc.) |
| **Tecnica** | Descomponer suma DFT en pares/impares |
| **Bibliografia** | **Cooley & Tukey 1965**, CLRS Cap. 30 |
| **Estimacion** | 4-6 horas |

**Sketch de prueba**:
```
X_k = Σ_{j=0}^{n-1} a_j · ω^{jk}
    = Σ_{j even} a_j · ω^{jk} + Σ_{j odd} a_j · ω^{jk}
    = Σ_{m=0}^{n/2-1} a_{2m} · ω^{2mk} + Σ_{m=0}^{n/2-1} a_{2m+1} · ω^{(2m+1)k}
    = Σ_m a_{2m} · (ω^2)^{mk} + ω^k · Σ_m a_{2m+1} · (ω^2)^{mk}
    = E_k + ω^k · O_k
```

**Lemas de Mathlib necesarios**:
- `Finset.sum_filter` para dividir en pares/impares
- `pow_mul`, `pow_add` para manipular exponentes

---

#### S9. `cooley_tukey_lower_half` (Correctness.lean:95)

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟠 MEDIA-ALTA |
| **Dependencias** | S8, `twiddle_half_eq_neg_one` (ya probado) |
| **Tecnica** | Igual que S8 + usar ω^{n/2} = -1 |
| **Bibliografia** | Cooley & Tukey 1965 |
| **Estimacion** | 2-3 horas (reutilizando S8) |

**Insight clave**: Ya tenemos `twiddle_half_eq_neg_one` probado en RootsOfUnity.lean:226-246.

---

### NIVEL 3: Correccion del Algoritmo

#### S10. `ct_recursive_eq_spec` (Correctness.lean:120)
```lean
theorem ct_recursive_eq_spec (ω : F) (input : List F)
    (h_pow2 : ∃ k : ℕ, input.length = 2^k) :
    NTT_recursive ω input = NTT_spec ω input
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🔴 ALTA |
| **Dependencias** | S8, S9 |
| **Tecnica** | Induccion fuerte sobre input.length |
| **Bibliografia** | CLRS Cap. 30, "Introduction to Algorithms" |
| **Estimacion** | 8-12 horas |

**Este es el teorema central del proyecto NTT.**

**Estrategia**:
1. Induccion fuerte sobre `input.length`
2. Caso base (n=1): Ya probado como `ntt_eq_singleton`
3. Caso inductivo:
   - Dividir en evens/odds
   - Aplicar hipotesis inductiva a cada mitad
   - Usar S8 y S9 para combinar

**Lemas auxiliares necesarios**:
- `evens_length`, `odds_length` (preservacion de longitud)
- `squared_is_primitive` (ya probado)
- Propiedades de `List.zip`

---

#### S11. `ntt_intt_recursive_roundtrip` (Correctness.lean:137)

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟡 MEDIA |
| **Dependencias** | S10, S12 (ntt_intt_identity) |
| **Tecnica** | Componer ct_recursive_eq_spec con roundtrip de spec |
| **Estimacion** | 2-3 horas |

---

### NIVEL 4: Identidad Central

#### S12. `intt_ntt_identity_finset` (Properties.lean:100)
```lean
theorem intt_ntt_identity_finset {n : ℕ} (hn : n > 1) {ω n_inv : F}
    (hω : IsPrimitiveRoot ω n)
    (h_inv : n_inv * (n : F) = 1)
    (a : Fin n → F) (i : Fin n) :
    intt_coeff_finset ω n_inv (fun k => ntt_coeff_finset ω a k) i = a i
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🔴 ALTA |
| **Dependencias** | `orthogonality_sum_lt` (ya probado) |
| **Tecnica** | Doble suma + ortogonalidad |
| **Bibliografia** | **Terras "Fourier Analysis on Finite Groups"**, Mathlib BigOperators |
| **Estimacion** | 6-10 horas |

**Sketch de prueba**:
```
INTT(NTT(a))_i = n_inv · Σ_k (Σ_j a_j ω^{jk}) · ω^{-ik}
              = n_inv · Σ_j a_j · Σ_k ω^{(j-i)k}      [intercambiar sumas]
              = n_inv · Σ_j a_j · [n si j=i, 0 si no] [ortogonalidad]
              = n_inv · n · a_i
              = a_i
```

**Lemas de Mathlib necesarios**:
- `Finset.sum_comm` para intercambiar sumas
- Ya tenemos `orthogonality_sum_lt` probado

---

#### S13. `ntt_intt_identity` (Spec.lean:166)

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟡 MEDIA |
| **Dependencias** | S12 |
| **Tecnica** | Reducir version List a version Finset |
| **Estimacion** | 3-4 horas |

---

### NIVEL 5: Propiedades Avanzadas

#### S14. `parseval` (Properties.lean:228)
```lean
theorem parseval {n : ℕ} (hn : n > 1) (ω : F) (hω : IsPrimitiveRoot ω n)
    (a : Fin n → F) :
    (n : F) * (Finset.univ.sum fun i => a i * a i) =
    Finset.univ.sum fun k => ntt_coeff_finset ω a k * ntt_coeff_finset ω a k
```

| Aspecto | Detalle |
|---------|---------|
| **Dificultad** | 🟠 MEDIA-ALTA |
| **Dependencias** | S12 o independiente usando ortogonalidad |
| **Tecnica** | Expandir NTT, usar ortogonalidad |
| **Bibliografia** | Plancherel theorem, cualquier libro de Fourier |
| **Estimacion** | 4-6 horas |

**No es critico para performance. Prioridad BAJA.**

---

### NIVEL 6: Radix-4

#### S15-S17. Sorries en Radix4/Algorithm.lean

| Sorry | Linea | Dificultad | Notas |
|-------|-------|------------|-------|
| `NTT_radix4_singleton` | 60 | 🟢 BAJA | Simplificar NTT_spec [x] |
| `NTT_radix4_nil` | 67 | 🟢 BAJA | Caso degenerado |
| `combineRadix4_uses_butterfly4` | 171 | 🟡 MEDIA | Relacion estructural |

---

#### A1-A7. Axiomas en Radix4

| Axioma | Archivo | Dificultad | Estrategia |
|--------|---------|------------|------------|
| `NTT_radix4` | Algorithm:38 | 🔴 ALTA | Definir recursivamente con termination_by |
| `NTT_radix4_eq_spec` | Algorithm:41 | 🔴 ALTA | Depende de A1 + analog a S10 |
| `INTT_radix4` | Algorithm:72 | 🔴 ALTA | Similar a A1 |
| `INTT_radix4_NTT_radix4_identity` | Algorithm:75 | 🟠 MEDIA | Depende de A2, S12 |
| `butterfly4_orthogonality` | Butterfly4:173 | 🟠 MEDIA | Algebra matricial |
| `ntt_spec_roundtrip` | Equivalence:141 | 🟡 MEDIA | Depende de S12 |
| `intt_radix4_eq_spec_axiom` | Equivalence:151 | 🟠 MEDIA | Depende de A3 |

---

## Evaluacion de Bibliografia

### Ya Disponible en el Proyecto

| Recurso | Ubicacion | Cubre |
|---------|-----------|-------|
| Mathlib `IsPrimitiveRoot` | Importado | Ortogonalidad basica |
| `sum_of_powers_zero` | RootsOfUnity.lean:140 | Suma geometrica |
| `powSum_nonzero` | RootsOfUnity.lean:184 | Σ ω^{ik} = 0 |
| `twiddle_half_eq_neg_one` | RootsOfUnity.lean:226 | ω^{n/2} = -1 |
| `squared_is_primitive` | RootsOfUnity.lean:268 | ω² primitivo |
| `ntt_additive`, `ntt_scale` | Properties.lean:111-128 | Linealidad (Finset) |

### Necesaria pero No Disponible

| Recurso | Necesario Para | Donde Obtener |
|---------|----------------|---------------|
| `Finset.sum_comm` | S12 (doble suma) | Mathlib `Algebra.BigOperators.Order` |
| `Finset.sum_filter_add_sum_filter_not` | S8 (pares/impares) | Mathlib `Algebra.BigOperators.Basic` |
| Teoria de matrices 4x4 | A5 (butterfly4) | Manual o Mathlib.LinearAlgebra |

### Bibliografia Externa Recomendada

| Libro/Paper | Para | Prioridad |
|-------------|------|-----------|
| CLRS "Introduction to Algorithms" Cap. 30 | S8, S9, S10 | ALTA |
| Terras "Fourier Analysis on Finite Groups" | S12 | MEDIA |
| Cooley & Tukey 1965 | S8, S9 | REFERENCIA |
| Mathlib documentation | Todos | ALTA |

---

## Plan de Ejecucion Propuesto

### Fase 1: Fundamentos (Dias 1-2)
**Objetivo**: Cerrar sorries de aritmetica modular basica

| Orden | Sorry | Horas Est. | Dependencias |
|-------|-------|------------|--------------|
| 1.1 | S4 `ofStrict_bound` | 0.5 | - |
| 1.2 | S3 `lazy_sub_simulates` | 1.5 | - |
| 1.3 | S1 `ntt_coeff_add` | 2 | - |
| 1.4 | S2 `ntt_coeff_scale` | 1 | - |
| **Total** | **4 sorries** | **~5 horas** | |

### Fase 2: Lazy Butterfly (Dias 3-4)
**Objetivo**: Completar simulacion de lazy butterfly

| Orden | Sorry | Horas Est. | Dependencias |
|-------|-------|------------|--------------|
| 2.1 | S5 `lazy_butterfly_fst_simulates` | 3 | S3 |
| 2.2 | S6 `lazy_butterfly_snd_simulates` | 2 | S3 |
| 2.3 | S7 `lazy_butterfly_sum` | 2 | S5, S6 |
| **Total** | **3 sorries** | **~7 horas** | |

### Fase 3: Cooley-Tukey (Dias 5-8)
**Objetivo**: Probar recurrencia CT y teorema central

| Orden | Sorry | Horas Est. | Dependencias |
|-------|-------|------------|--------------|
| 3.1 | S8 `cooley_tukey_upper_half` | 5 | - |
| 3.2 | S9 `cooley_tukey_lower_half` | 3 | S8 |
| 3.3 | S10 `ct_recursive_eq_spec` | 10 | S8, S9 |
| **Total** | **3 sorries** | **~18 horas** | |

### Fase 4: Identidad Central (Dias 9-11)
**Objetivo**: Probar INTT(NTT(x)) = x

| Orden | Sorry | Horas Est. | Dependencias |
|-------|-------|------------|--------------|
| 4.1 | S12 `intt_ntt_identity_finset` | 8 | orthogonality |
| 4.2 | S13 `ntt_intt_identity` | 4 | S12 |
| 4.3 | S11 `ntt_intt_recursive_roundtrip` | 3 | S10, S13 |
| **Total** | **3 sorries** | **~15 horas** | |

### Fase 5: Radix-4 Sorries (Dias 12-13)
**Objetivo**: Cerrar sorries triviales de Radix4

| Orden | Sorry | Horas Est. | Dependencias |
|-------|-------|------------|--------------|
| 5.1 | S15 `NTT_radix4_singleton` | 1 | - |
| 5.2 | S16 `NTT_radix4_nil` | 0.5 | - |
| 5.3 | S17 `combineRadix4_uses_butterfly4` | 2 | - |
| **Total** | **3 sorries** | **~3.5 horas** | |

### Fase 6: Axiomas Radix-4 (Dias 14-21)
**Objetivo**: Convertir axiomas en definiciones + teoremas

| Orden | Axioma | Horas Est. | Estrategia |
|-------|--------|------------|------------|
| 6.1 | A1 `NTT_radix4` | 6 | Definir con termination_by |
| 6.2 | A2 `NTT_radix4_eq_spec` | 10 | Induccion similar a S10 |
| 6.3 | A3 `INTT_radix4` | 4 | Similar a A1 |
| 6.4 | A4 `INTT_radix4_NTT_radix4_identity` | 4 | Usar S12 |
| 6.5 | A5 `butterfly4_orthogonality` | 6 | Algebra matricial |
| 6.6 | A6 `ntt_spec_roundtrip` | 3 | Usar S12 |
| 6.7 | A7 `intt_radix4_eq_spec_axiom` | 4 | Usar A3 |
| **Total** | **7 axiomas** | **~37 horas** | |

### Fase 7: Opcional - Parseval (Dia 22)
**Objetivo**: Probar conservacion de energia (no critico)

| Orden | Sorry | Horas Est. | Dependencias |
|-------|-------|------------|--------------|
| 7.1 | S14 `parseval` | 5 | S12 |

---

## Resumen de Recursos

### Tiempo Total Estimado

| Fase | Horas | Dias (~6h/dia) |
|------|-------|----------------|
| Fase 1: Fundamentos | 5 | 1 |
| Fase 2: Lazy Butterfly | 7 | 1-2 |
| Fase 3: Cooley-Tukey | 18 | 3 |
| Fase 4: Identidad | 15 | 2-3 |
| Fase 5: Radix4 Sorries | 3.5 | 1 |
| Fase 6: Radix4 Axiomas | 37 | 6 |
| Fase 7: Parseval (opt) | 5 | 1 |
| **TOTAL** | **~90 horas** | **~15 dias** |

### Riesgos Identificados

| Riesgo | Impacto | Mitigacion |
|--------|---------|------------|
| Terminacion de NTT_radix4 | Alto | Usar `termination_by` con medida explicita |
| Finset.sum_comm no disponible | Medio | Importar desde Mathlib |
| Algebra matricial para butterfly4 | Medio | Prueba directa por calculo |
| Tiempo subestimado | Medio | Comenzar por sorries mas simples |

---

## Metricas de Exito

1. **0 sorries** en AmoLean/NTT/
2. **0 axiomas** en AmoLean/NTT/Radix4/
3. **lake build** sin warnings de sorry
4. **Todos los tests** existentes pasan
5. **Benchmark vs Plonky3** mantiene o mejora performance

---

## Proximos Pasos Inmediatos

1. [ ] Verificar que `Finset.sum_comm` esta disponible en imports actuales
2. [ ] Comenzar con S4 `ofStrict_bound` (mas simple)
3. [ ] Documentar invariante de GoldilocksField si no existe
4. [ ] Crear rama `feature/sorry-elimination`
