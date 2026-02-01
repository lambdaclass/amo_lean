# Sesion 3: Eliminacion de Sorries - Teorema S10 Completado

**Fecha**: 2026-02-01
**Objetivo**: Completar el teorema central `ct_recursive_eq_spec` (S10)
**Resultado**: EXITO - S10 probado sin sorries

---

## Resumen Ejecutivo

Esta sesion completo exitosamente el **teorema central S10** (`ct_recursive_eq_spec`), que establece que `NTT_recursive` produce resultados identicos a `NTT_spec`. Este es el teorema mas importante del modulo NTT, demostrando la correccion del algoritmo Cooley-Tukey O(n log n).

### Progreso Final

| Teorema | Estado | Archivo |
|---------|--------|---------|
| `NTT_recursive_unfold` | PROBADO | CooleyTukey.lean:158 |
| `NTT_recursive_getElem_upper` | PROBADO | CooleyTukey.lean:177 |
| `NTT_recursive_getElem_lower` | PROBADO | CooleyTukey.lean:189 |
| `NTT_recursive_getElem_none` | PROBADO | CooleyTukey.lean:209 |
| `ct_recursive_eq_spec` (S10) | PROBADO | Correctness.lean:163 |

---

## Decisiones de Diseno Tomadas

### DD-038: Casos sobre Exponente en lugar de Match sobre Lista

**Problema**: El intento inicial de usar `match h : input` fallaba porque no permitia una induccion natural sobre la longitud.

**Decision**: Usar `cases exp` donde `input.length = 2^exp`:
```lean
obtain ⟨exp, hexp⟩ := h_pow2
cases exp with
| zero => -- Base case: length = 1
| succ exp' => -- Inductive case: length >= 2
```

**Justificacion (sugerida por QA)**:
- La induccion sobre el exponente es mas natural para NTT
- Permite derivar automaticamente `h_evens_len : (evens input).length = 2^exp'`
- El caso base `exp = 0` corresponde exactamente a `input.length = 1`

---

### DD-039: Unfolding Lemmas para Exposicion de Estructura

**Problema**: `NTT_recursive` usa `match h : a with` que complica los rewrites directos.

**Decision**: Crear cuatro unfolding lemmas que exponen la estructura:

```lean
-- Descompone NTT_recursive en upper ++ lower
theorem NTT_recursive_unfold (ω : F) (a : List F) (ha : a.length >= 2) :
    NTT_recursive ω a =
    let half := a.length / 2
    let E := NTT_recursive (ω * ω) (evens a)
    let O := NTT_recursive (ω * ω) (odds a)
    let upper := (List.range half).map fun k =>
      E[k]?.getD 0 + ω ^ k * O[k]?.getD 0
    let lower := (List.range half).map fun k =>
      E[k]?.getD 0 - ω ^ k * O[k]?.getD 0
    upper ++ lower

-- Acceso a elemento en mitad superior
theorem NTT_recursive_getElem_upper (ω : F) (a : List F) (ha : a.length >= 2)
    (k : Nat) (hk : k < a.length / 2) :
    (NTT_recursive ω a)[k]? = some (E[k]?.getD 0 + ω^k * O[k]?.getD 0)

-- Acceso a elemento en mitad inferior
theorem NTT_recursive_getElem_lower (ω : F) (a : List F) (ha : a.length >= 2)
    (heven : 2 ∣ a.length) (k : Nat) (hk_ge : k >= a.length / 2) (hk_lt : k < a.length) :
    (NTT_recursive ω a)[k]? = some (E[k - half]?.getD 0 - ω^(k-half) * O[k - half]?.getD 0)

-- Fuera de rango devuelve none
theorem NTT_recursive_getElem_none (ω : F) (a : List F) (k : Nat)
    (hpow2 : ∃ e, a.length = 2^e) (hk : k >= a.length) :
    (NTT_recursive ω a)[k]? = none
```

**Justificacion (sugerida por QA)**:
- Evita repetir la logica de match en cada uso
- Permite usar `rw [NTT_recursive_unfold]` limpiamente
- Los getElem lemmas simplifican el razonamiento elemento-a-elemento

---

### DD-040: Caso Especial n=2 para Lower Half

**Problema**: El teorema `cooley_tukey_lower_half` requiere `n > 2`, pero cuando `exp' = 0` tenemos `n = 2`.

**Decision**: Manejar n=2 como caso especial con prueba directa:
```lean
cases exp' with
| zero =>
    -- n = 2, prueba directa usando primitive_root_two_eq_neg_one
    -- omega = -1, omega^2 = 1
    -- NTT_spec 1 [x] = [x]
| succ e =>
    -- n >= 4, usar cooley_tukey_lower_half
```

**Justificacion**:
- Para n=2: evens = [a], odds = [b], NTT es trivial
- El caso n=2 puede probarse directamente expandiendo definiciones
- Evita modificar `cooley_tukey_lower_half` que ya funciona para n > 2

---

### DD-041: List.ext_getElem? para Igualdad de Listas

**Problema**: Necesitamos probar `NTT_recursive ω input = NTT_spec ω input` como igualdad de listas.

**Decision**: Usar `List.ext_getElem?` para igualdad elemento-a-elemento:
```lean
apply List.ext_getElem?
intro k
by_cases hk_lt_half : k < half
· -- Caso upper half: usar cooley_tukey_upper_half
· -- Caso lower half o fuera de rango
```

**Justificacion (sugerida por QA)**:
- Evita manejar explicitamente la longitud
- Permite case split natural sobre k
- Funciona bien con los unfolding lemmas

---

## Problemas Encontrados y Soluciones

### P1: omega no puede manejar exponentes

**Problema**: `omega` fallaba al probar `2^(e+2) >= 4`

**Sintoma**:
```
omega could not prove the goal:
No usable constraints found...
```

**Solucion**: Proporcionar cota explicita usando `Nat.one_le_pow`:
```lean
have h2e : 2^(e+2) >= 4 := by
  have he1 : 2^e >= 1 := Nat.one_le_pow e 2 (by norm_num)
  have : 2^(e+2) = 2^e * 4 := by simp only [Nat.pow_succ, Nat.pow_add]; omega
  omega
```

---

### P2: IsPrimitiveRoot.one colision de namespaces

**Problema**: Nuestro proyecto tiene `IsPrimitiveRoot` personalizado que colisiona con Mathlib.

**Sintoma**: `IsPrimitiveRoot.one` no se encuentra o tiene tipo incorrecto.

**Solucion**: Construir directamente la estructura:
```lean
exact ⟨by ring, fun d hd _ => by omega⟩
```

---

### P3: NTT_spec_singleton usa notacion inst.add/inst.mul

**Problema**: `NTT_spec_singleton` devuelve `[inst.add inst.zero (inst.mul a (omega^0))]`, no `[a]`.

**Sintoma**: `simp only [pow_zero, mul_one, zero_add]` no simplificaba.

**Solucion**: Usar `congr 1` para entrar en la lista, luego `show` para explicitar tipos:
```lean
have hE : NTT_spec (ω * ω) [a] = [a] := by
  rw [h_omega_sq, NTT_spec_singleton]
  congr 1
  show (0 : F) + a * ((1 : F) ^ 0) = a
  ring
```

---

### P4: ntt_coeff usa foldl, no Finset.sum

**Problema**: Al intentar usar `Finset.sum_range_succ`, el goal tenia `List.foldl`.

**Sintoma**: `simp only [Finset.sum_range_succ]` no hacia progreso.

**Solucion**: Expandir foldl manualmente para n=2:
```lean
unfold ntt_coeff
simp only [List.length_cons, List.length_nil]
have hr2 : List.range 2 = [0, 1] := by native_decide
rw [hr2]
simp only [List.foldl_cons, List.foldl_nil]
```

---

## Estructura Final de ct_recursive_eq_spec

```lean
theorem ct_recursive_eq_spec (ω : F) (input : List F)
    (h_pow2 : ∃ k, input.length = 2^k)
    (hω : IsPrimitiveRoot ω input.length) :
    NTT_recursive ω input = NTT_spec ω input := by

  obtain ⟨exp, hexp⟩ := h_pow2

  cases exp with
  | zero =>
      -- Base: length = 1
      -- Usar ntt_eq_singleton

  | succ exp' =>
      -- Inductive: length = 2^(exp'+1) >= 2

      -- 1. Establecer propiedades de longitud
      have h_len_ge2 : input.length >= 2
      have h_even : 2 ∣ input.length
      have h_evens_len : (evens input).length = 2^exp'
      have h_odds_len : (odds input).length = 2^exp'

      -- 2. Probar que ω² es primitivo para sublistas
      have hω_sq : IsPrimitiveRoot (ω * ω) (evens input).length

      -- 3. Hipotesis inductiva
      have ih_evens : NTT_recursive (ω*ω) (evens input) = NTT_spec (ω*ω) (evens input)
      have ih_odds : NTT_recursive (ω*ω) (odds input) = NTT_spec (ω*ω) (odds input)

      -- 4. Unfold y probar elemento-a-elemento
      rw [NTT_recursive_unfold ω input h_len_ge2]
      apply List.ext_getElem?
      intro k

      by_cases hk_lt_half : k < half
      · -- Upper half: usar cooley_tukey_upper_half
      · by_cases hk_lt_n : k < n
        · -- Lower half: case split n=2 vs n>2
          cases exp' with
          | zero => -- n=2, prueba directa
          | succ e => -- n>2, usar cooley_tukey_lower_half
        · -- Fuera de rango: ambos none

termination_by input.length
decreasing_by
  -- evens/odds tienen longitud < input.length para input.length >= 2
```

---

## Arquitectura de Capas Actualizada

```
CAPA 1: FUNDAMENTOS                    COMPLETA
├── primitive_root_two_eq_neg_one
├── primitive_root_two_sq
├── twiddle_*_factor lemmas
├── E/O_getElem_some
└── Helper lemmas (inst_*_eq_*)

CAPA 2: DFT SPLITTING                  COMPLETA
├── evens_length, odds_length
├── evens_get, odds_get
├── foldl_split_parity
├── ntt_term_even/odd_index

CAPA 3: COOLEY-TUKEY SPLITTING         COMPLETA
├── cooley_tukey_upper_half (S8)
├── cooley_tukey_lower_half (S9)
├── ntt_coeff_upper/lower_half_split
└── NTT_spec_upper/lower_half_eq

CAPA 4: TEOREMA PRINCIPAL              COMPLETA
├── NTT_recursive_unfold
├── NTT_recursive_getElem_*
└── ct_recursive_eq_spec (S10)         <<< COMPLETADO

CAPA 5: IDENTIDAD INTT                 PENDIENTE
├── intt_ntt_identity_finset (S12)
├── ntt_intt_identity (S13)
└── ntt_intt_recursive_roundtrip (S11)
```

---

## Metricas de la Sesion

| Metrica | Valor |
|---------|-------|
| Sorries cerrados | 1 (S10 - el teorema central) |
| Lemas auxiliares creados | 4 (unfolding lemmas) |
| Lineas de codigo | ~250 (Correctness.lean) + ~70 (CooleyTukey.lean) |
| Tiempo de sesion | ~4 horas |
| Consultas QA utilizadas | 2 (plan de batalla, estrategia de prueba) |

---

## Archivos Modificados

| Archivo | Cambios |
|---------|---------|
| `AmoLean/NTT/CooleyTukey.lean` | +70 lineas: Unfolding lemmas (158-216) |
| `AmoLean/NTT/Correctness.lean` | Reescritura completa de ct_recursive_eq_spec (163-399) |

---

## Lecciones Clave Aprendidas

1. **Unfolding lemmas antes de probar**: Crear lemmas que exponen la estructura interna de una funcion recursiva antes de intentar el teorema principal.

2. **Induccion sobre exponente, no sobre lista**: Para algoritmos NTT donde length = 2^k, inducir sobre k es mas limpio que inducir sobre la estructura de la lista.

3. **Casos especiales requieren tratamiento especial**: El caso n=2 no podia usar teoremas que requieren n>2. Una prueba directa es mas simple que generalizar los teoremas existentes.

4. **omega no entiende exponentes**: Proporcionar cotas explicitas usando lemas como `Nat.one_le_pow`.

5. **Seguir el plan del QA**: La estrategia de 3 pasos del QA (verificar terminacion, crear unfolding lemma, usar induccion fuerte + List.ext) fue exactamente lo que funciono.

---

## Trabajo Pendiente

### Sorries en NTT Core (prioridad alta)
- S11: `ntt_intt_recursive_roundtrip` - Depende de S12/S13
- S12: `intt_ntt_identity_finset` - Requiere ortogonalidad de sumas
- S13: `ntt_intt_identity` - Reduccion de S12 a listas
- S14: `parseval` - Propiedad opcional

### Sorries en Radix4 (prioridad media)
- S15: `NTT_radix4_singleton` - Trivial
- S16: `NTT_radix4_nil` - Trivial
- S17: `combineRadix4_uses_butterfly4` - Media

### Axiomas Radix4 (prioridad baja)
- 7 axiomas que requieren definiciones completas

### Sorries en Goldilocks (prioridad baja)
- 25 sorries para axiomas algebraicos de CommRing/Field
- Verificados computacionalmente, falta prueba formal
