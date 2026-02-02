# Sesión 4: Eliminación de Sorries - Teoremas S12 y S13 Completados

**Fecha**: 2026-02-02
**Objetivo**: Completar los teoremas de ortogonalidad (S12) e identidad INTT (S13)
**Resultado**: ÉXITO - S12 y S13 probados sin sorries

---

## Resumen Ejecutivo

Esta sesión completó exitosamente los teoremas **S12** (`ntt_orthogonality_sum`) y **S13** (`intt_ntt_identity_finset`), que establecen la ortogonalidad de raíces de unidad y la identidad fundamental INTT(NTT(x)) = x.

### Progreso Final

| Teorema | Estado | Archivo |
|---------|--------|---------|
| `ntt_orthogonality_sum` (S12) | PROBADO | OrthogonalityProof.lean |
| `intt_ntt_identity_finset` (S13) | PROBADO | Properties.lean |
| `term_self_eq_one` | PROBADO | OrthogonalityProof.lean |
| `sum_self_eq_n` | PROBADO | OrthogonalityProof.lean |
| `sum_diff_eq_zero` | PROBADO | OrthogonalityProof.lean |
| `term_eq_pow_diff` | PROBADO | OrthogonalityProof.lean |
| `exp_mod_eq` | PROBADO | OrthogonalityProof.lean |

---

## Consulta al QA: Estrategia Clave

### Problema Planteado

El teorema `pow_transform'` (ahora `term_eq_pow_diff`) requería probar:
```
ω^(jk) * ω^(n - (ik mod n)) = ω^(((j+n-i) mod n) * k)
```

Los intentos iniciales fallaron debido a:
1. `omega` no maneja expresiones con `%` (módulo)
2. `rw` no encuentra patrones dentro de sumas complejas
3. Aritmética de naturales con restas truncadas causa problemas
4. `Nat.div_add_mod` devuelve `n * (m/n)` pero necesitábamos `(m/n) * n`

### Respuesta del QA

**Insight crítico**: El problema es algebraico, no aritmético.

> "El problema es que estás luchando contra la aritmética de Nat cuando el problema real es algebraico. ω^n = 1, así que ω^(n-x) es el inverso multiplicativo de ω^x. No luches con la aritmética de Nat - usa propiedades algebraicas."

**Estrategia recomendada**:
1. Para j = i: Cada término es ω^m * ω^(n - m%n) = 1 (porque los exponentes suman un múltiplo de n)
2. Para j ≠ i: Transformar la suma a Σ_k ω^(d*k) donde d = (j+n-i) % n > 0, luego usar `powSum_nonzero`
3. Usar `Finset.sum_congr` para transformar término a término
4. Reutilizar `orthogonality_sum_lt` que ya estaba probado

---

## Decisiones de Diseño Tomadas

### DD-042: Separación de Casos j=i y j≠i

**Problema**: El teorema de ortogonalidad tiene comportamiento diferente según si los índices son iguales o no.

**Decisión**: Crear dos teoremas separados:
```lean
theorem sum_self_eq_n -- Caso j = i: suma = n
theorem sum_diff_eq_zero -- Caso j ≠ i: suma = 0
```

**Justificación**:
- El caso j=i tiene una prueba mucho más simple (cada término es 1)
- El caso j≠i requiere la transformación compleja de exponentes
- Mantiene el código más legible y mantenible

### DD-043: Lema de Exponentes Separado

**Problema**: La prueba de equivalencia de exponentes mod n era muy compleja.

**Decisión**: Crear `exp_mod_eq` como lema separado:
```lean
lemma exp_mod_eq {n : ℕ} (hn : n > 0) (j i k : ℕ) (hj : j < n) (hi : i < n) :
    (j * k + n - (i * k) % n) % n = (((j + n - i) % n) * k) % n
```

**Justificación**:
- Aísla la aritmética pura de Nat del resto de la prueba
- Permite probar por casos (j ≥ i vs j < i) de forma limpia
- El lema es reutilizable si se necesita en otros contextos

### DD-044: Manejo Explícito del Orden de Multiplicación

**Problema**: `Nat.div_add_mod` devuelve `i * k = n * (i * k / n) + i * k % n` pero necesitábamos `(i * k / n) * n`.

**Decisión**: Usar `Nat.mul_comm` explícitamente para convertir:
```lean
have h_ik_eq : i * k = (i * k / n) * n + r := by
  rw [hr_def]
  have h := Nat.div_add_mod (i * k) n
  rw [Nat.mul_comm] at h
  exact h.symm
```

**Justificación**:
- Mathlib define `Nat.div_add_mod` con `n * q` no `q * n`
- La conversión explícita es más clara que intentar reordenar implícitamente
- Evita confusiones futuras sobre el orden

### DD-045: Uso de `Nat.mul_sub_right_distrib` en lugar de `Nat.sub_mul`

**Problema**: `Nat.sub_mul` no existe en Mathlib/Lean 4.

**Decisión**: Usar `Nat.mul_sub_right_distrib`:
```lean
-- Correcto:
have h_sub_mul : (j - i) * k = j * k - i * k := Nat.mul_sub_right_distrib j i k

-- Incorrecto (no existe):
-- Nat.sub_mul j i k
```

**Justificación**:
- `Nat.mul_sub_right_distrib` es el nombre correcto en Mathlib
- Encontrado usando `exact?` en un archivo de prueba

---

## Problemas Encontrados y Soluciones

### P1: `omega` no maneja expresiones con módulo

**Problema**:
```lean
have h : (j*k + (n - r)) % n = ((j-i)*k) % n := by omega -- FALLA
```

**Síntoma**: "omega could not prove the goal"

**Solución**: Descomponer la prueba usando lemmas de `Nat.add_mod`, `Nat.mod_self`, etc.:
```lean
have h1 : j * k + n - r = j * k - r + n := by omega
rw [h1, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
```

### P2: `ring` no funciona para Nat con restas

**Problema**:
```lean
have h_dk2 : d * k = j * k + n * k - i * k := by
  rw [h_dk, h_nmi_k]; ring -- FALLA
```

**Síntoma**: "unsolved goals" porque `ring` no entiende subtracción truncada de Nat.

**Solución**: Proporcionar cotas explícitas y usar `omega`:
```lean
have h_dk2 : d * k = j * k + n * k - i * k := by
  rw [h_dk, h_nmi_k]
  have h_nk_gt_ik : n * k > i * k := Nat.mul_lt_mul_of_pos_right (by omega : i < n) hk_pos
  omega
```

### P3: `Nat.mul_sub_one` tiene el patrón invertido

**Problema**:
```lean
rw [Nat.mul_sub_one] -- Espera n * (m - 1) pero tenemos n * m - n
```

**Síntoma**: "tactic 'rewrite' failed, did not find instance of the pattern"

**Solución**: Usar `Nat.mul_sub_left_distrib` con conmutatividad:
```lean
rw [Nat.mul_comm (i * k / n) n]
rw [← Nat.mul_sub_left_distrib]
```

### P4: `ring_nf` falla para Nat

**Problema**:
```lean
_ = j * k + n - r + n * (k - 1 - i * k / n) := by ring_nf -- FALLA
```

**Síntoma**: "unsolved goals"

**Solución**: Probar la igualdad de forma explícita:
```lean
have h_eq : k - i * k / n - 1 = k - 1 - i * k / n := by omega
rw [h_eq]
```

### P5: `simp` no simplifica dentro de `set` definitions

**Problema**:
```lean
set r := (i * k) % n with hr_def
-- Después de subst hk donde hk : k = 0
simp [hk] -- No simplifica r a 0
```

**Síntoma**: Goal todavía contiene `r` sin simplificar

**Solución**: Probar explícitamente que r = 0:
```lean
have hr_zero : r = 0 := by rw [hr_def, hk]; simp
simp only [hk, hr_zero, ...]
```

### P6: `Nat.add_mul_mod_self_right` requiere orden específico

**Problema**:
```lean
rw [Nat.add_mul_mod_self_right] -- Pattern: (x + y * z) % z
-- Pero tenemos: (x + n * m) % n -- n está a la izquierda
```

**Síntoma**: "tactic 'rewrite' failed, did not find instance of the pattern"

**Solución**: Usar comutatividad primero:
```lean
rw [Nat.mul_comm n (k - 1 - i * k / n), Nat.add_mul_mod_self_right]
```

---

## Estructura Final del Archivo OrthogonalityProof.lean

```lean
namespace AmoLean.NTT

/-! ## Part 1: Self-sum equals n -/

lemma term_self_eq_one  -- ω^m * ω^(n - m%n) = 1
theorem sum_self_eq_n   -- Σ_k ω^(ik) * ω^(n - (ik)%n) = n

/-! ## Part 2: Different indices sum to zero -/

theorem sum_fin_eq_sum_range  -- Conversión Fin n ↔ range n
theorem diff_mod_pos          -- (j+n-i) % n > 0 cuando j ≠ i
lemma term_eq_pow_diff_mod    -- ω^(jk) * ω^(n-(ik)%n) = ω^((jk+n-(ik)%n)%n)
lemma rhs_exp_mod             -- ω^(d*k) = ω^((d*k)%n)
lemma exp_mod_eq              -- Igualdad de exponentes mod n (CORE LEMMA)
lemma term_eq_pow_diff        -- ω^(jk) * ω^(n-(ik)%n) = ω^(((j+n-i)%n)*k)
theorem sum_diff_eq_zero      -- Σ_k ... = 0 cuando j ≠ i

/-! ## Part 3: Main orthogonality theorem -/

theorem ntt_orthogonality_sum -- Σ_k = n si j=i, 0 si j≠i (S12)

end AmoLean.NTT
```

---

## Conexión con S13

Una vez probado S12 (`ntt_orthogonality_sum`), el teorema S13 (`intt_ntt_identity_finset`) se completa automáticamente:

```lean
theorem intt_ntt_identity_finset {n : ℕ} (hn : n > 1) {ω n_inv : F}
    (hω : IsPrimitiveRoot ω n)
    (h_inv : n_inv * (n : F) = 1)
    (a : Fin n → F) (i : Fin n) :
    intt_coeff_finset ω n_inv (fun k => ntt_coeff_finset ω a k) i = a i := by
  -- ... pasos de reorganización ...
  have h_ortho : ∀ j : Fin n, ... = if j = i then (n : F) else 0 :=
    fun j => ntt_orthogonality_sum hn hω j i  -- ← Usa S12
  simp_rw [h_ortho]
  -- ... colapso de suma y simplificación final ...
```

La prueba de S13 ya estaba escrita esperando S12. Al completar S12, S13 compila sin modificaciones.

---

## Arquitectura de Capas Actualizada

```
CAPA 1: FUNDAMENTOS                    COMPLETA
├── primitive_root_two_eq_neg_one
├── twiddle_*_factor lemmas
└── pow_eq_pow_mod

CAPA 2: DFT SPLITTING                  COMPLETA
├── evens_length, odds_length
├── evens_get, odds_get
└── foldl_split_parity

CAPA 3: COOLEY-TUKEY SPLITTING         COMPLETA
├── cooley_tukey_upper_half (S8)
├── cooley_tukey_lower_half (S9)
└── ntt_coeff_upper/lower_half_split

CAPA 4: TEOREMA PRINCIPAL              COMPLETA
├── NTT_recursive_unfold
├── NTT_recursive_getElem_*
└── ct_recursive_eq_spec (S10)

CAPA 5: ORTOGONALIDAD                  COMPLETA  <<< NUEVO
├── term_self_eq_one
├── sum_self_eq_n
├── exp_mod_eq
├── term_eq_pow_diff
├── sum_diff_eq_zero
└── ntt_orthogonality_sum (S12)        <<< COMPLETADO

CAPA 6: IDENTIDAD INTT (Finset)        COMPLETA  <<< NUEVO
└── intt_ntt_identity_finset (S13)     <<< COMPLETADO

CAPA 7: IDENTIDAD INTT (List)          PENDIENTE
├── ntt_intt_identity (Spec.lean)
└── ntt_intt_recursive_roundtrip (S11)
    └── Requiere bridge List ↔ Finset
```

---

## Métricas de la Sesión

| Métrica | Valor |
|---------|-------|
| Sorries cerrados | 2 (S12, S13) |
| Lemas auxiliares creados | 7 |
| Líneas de código | ~320 (OrthogonalityProof.lean) |
| Iteraciones del archivo | ~15 (múltiples correcciones) |
| Consultas QA utilizadas | 1 (estrategia algebraica) |

---

## Archivos Modificados

| Archivo | Cambios |
|---------|---------|
| `AmoLean/NTT/OrthogonalityProof.lean` | Reescritura completa con estrategia QA |
| `docs/project/QA_CONSULTATION_S12_S13.md` | Documento de consulta al QA |

---

## Lecciones Clave Aprendidas

1. **No luchar contra Nat**: Cuando la aritmética de naturales se vuelve compleja con restas, buscar propiedades algebraicas alternativas.

2. **omega tiene límites**: `omega` es un solver de Presburger (aritmética lineal) y no puede manejar módulo (`%`) ni multiplicaciones no lineales.

3. **Nombres de lemas en Mathlib**: Los nombres no siempre son intuitivos:
   - `Nat.sub_mul` no existe → usar `Nat.mul_sub_right_distrib`
   - `Nat.mul_sub_one` tiene patrón `n * (m-1)` no `n*m - n`

4. **Orden de multiplicación importa**: `Nat.div_add_mod` usa `n * q`, no `q * n`. Siempre verificar con `#check`.

5. **`set` no se simplifica automáticamente**: Después de `subst`, las definiciones de `set` no se actualizan. Probar igualdades explícitamente.

6. **Separar casos simplifica pruebas**: El caso j=i es trivial; el caso j≠i es complejo. Separarlos evita mezclar lógica innecesariamente.

7. **Consultar al QA temprano**: La estrategia algebraica del QA fue la clave. Sin ella, habríamos seguido luchando con aritmética de Nat.

---

## Trabajo Pendiente

### Sorries en NTT Core
- **S11**: `ntt_intt_recursive_roundtrip` - Requiere bridge List ↔ Finset
- **S14**: `parseval` - Opcional, baja prioridad
- `ntt_intt_identity` (Spec.lean) - Misma dependencia que S11

### Sorries en Radix4
- Múltiples axiomas pendientes

### Sorries en Goldilocks
- ~25 sorries para axiomas algebraicos de CommRing/Field

---

## Próximos Pasos Recomendados

1. **Bridge List ↔ Finset**: Crear teoremas que conecten `ntt_coeff` (List.foldl) con `ntt_coeff_finset` (Finset.sum). Esto desbloqueará S11.

2. **INTT_spec = INTT via Finset**: Probar que `INTT_spec` es equivalente a una versión basada en Finset.

3. **Completar S11**: Con el bridge, usar `intt_ntt_identity_finset` para probar el roundtrip de listas.

---

## Apéndice: Consulta y Respuesta del QA

Ver documento completo en: `docs/project/QA_CONSULTATION_S12_S13.md`

**Pregunta clave**: ¿Cómo probar `pow_transform'` cuando omega falla y rw no encuentra patrones?

**Respuesta clave del QA**:
> "El insight clave es: ω^n = 1, así que ω^(n-x) es el inverso de ω^x. No necesitas probar igualdades complicadas de Nat - solo necesitas mostrar que los exponentes son congruentes módulo n."
