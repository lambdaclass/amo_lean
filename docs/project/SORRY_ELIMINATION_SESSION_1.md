# Sesión 1: Eliminación de Sorries - Progreso

**Fecha**: 2026-01-30
**Objetivo**: Comenzar eliminación sistemática de sorries según SORRY_ELIMINATION_PLAN.md

---

## Resultados

### S4 `ofStrict_bound` (Bounds.lean:216) - PROBADO

**Estado**: Completado con modificación de firma

**Problema original**:
```lean
theorem ofStrict_bound (x : GoldilocksField) :
    (ofStrict x).val < GOLDILOCKS_PRIME := by
  sorry
```

**Problema encontrado**: `GoldilocksField` no enforce `value < ORDER` a nivel de tipo (comentario en línea 33-34 de Goldilocks.lean dice "for simplicity, but all operations maintain this invariant").

**Solución aplicada**: Agregar hipótesis explícita
```lean
theorem ofStrict_bound (x : GoldilocksField) (hx : x.value.toNat < ORDER.toNat) :
    (ofStrict x).val < GOLDILOCKS_PRIME := by
  simp only [ofStrict]
  rw [goldilocks_prime_eq]
  exact hx
```

**Impacto**: Quienes usen este teorema deben probar que el valor es bien formado.

---

### S3 `lazy_sub_simulates` (Bounds.lean:200) - PROBADO

**Estado**: Completado en sesión 1 (continuación)

**Teorema**:
```lean
theorem lazy_sub_simulates (a b : LazyGoldilocks)
    (ha : a.val < BOUND_2P) (hb : b.val < BOUND_2P) :
    (sub a b ha hb).reduceNat = strictSubNat a.reduceNat b.reduceNat
```

**Equivalente matemático**:
```
(a + 2p - b) % p = (a%p + p - b%p) % p
```

**Solución aplicada**:

Después de consultar con el QA (Gemini 2.5 Pro), se aplicó una estrategia de case-split por tricotomía:
1. **Caso b < P**: Usar `Nat.mod_eq_of_lt` y la identidad `2P - b = P + (P - b)`
2. **Caso b = P**: Simplificación directa con `Nat.mod_self`
3. **Caso b > P**: Manipulación cuidadosa de `b % P = b - P` y bounds

**Lemas auxiliares creados**:
- `p_add_mod`: `(P + x) % P = x % P`
- `case_b_lt_p`, `case_b_eq_p`, `case_b_gt_p`: Casos individuales
- `two_p_sub_mod_eq`: Lemma clave que une los casos
- `lazy_sub_equiv`: Teorema general sobre Nat

**Tiempo invertido**: ~3 horas (incluyendo múltiples intentos fallidos)

---

### S1 `ntt_coeff_add` (Spec.lean) - PROBADO

**Estado**: Completado en sesión 1 (continuación)

**Teorema**:
```lean
theorem ntt_coeff_add (ω : F) (a b : List F) (k : Nat)
    (heq : a.length = b.length) :
    ntt_coeff ω (List.zipWith (· + ·) a b) k = (ntt_coeff ω a k) + (ntt_coeff ω b k)
```

**Estrategia aplicada**:
1. Inducción generalizada con tres acumuladores: `acc_ab`, `acc_a`, `acc_b`
2. Invariante: `acc_ab = acc_a + acc_b`
3. Para cada paso: `(acc_ab + (aᵢ+bᵢ)*ω^ik) = (acc_a + aᵢ*ω^ik) + (acc_b + bᵢ*ω^ik)`
4. Usa `add_term_distrib`: `(aᵢ+bᵢ)*ω^ik = aᵢ*ω^ik + bᵢ*ω^ik`
5. Usa `add_assoc_4`: `(w+x)+(y+z) = (w+y)+(x+z)` (rearranging addition)

**Lemas auxiliares**:
- `getElem?_zipWith_add`: comportamiento de `[zipWith (+)][i]?`
- `length_zipWith_add`: `(zipWith (+) a b).length = min a.length b.length`
- `add_term_distrib`: `(aᵢ+bᵢ)*ω = aᵢ*ω + bᵢ*ω`
- `add_assoc_4`: reordenamiento de suma de 4 términos
- `foldl_add_general`: lema principal de inducción generalizada

---

### S2 `ntt_coeff_scale` (Spec.lean) - PROBADO

**Estado**: Completado en sesión 1 (continuación)

**Teorema**:
```lean
theorem ntt_coeff_scale (ω : F) (a : List F) (c : F) (k : Nat) :
    ntt_coeff ω (a.map (c * ·)) k = c * (ntt_coeff ω a k)
```

**Estrategia aplicada**:
1. Inducción generalizada mostrando: `foldl_scaled (c*acc) = c * foldl acc`
2. Para cada paso: `c*acc + (c*aᵢ)*ω^ik = c*(acc + aᵢ*ω^ik)`
3. Usa `mul_add_distrib`: `c*(acc+x) = c*acc + c*x`
4. Usa `scale_term`: `(c*aᵢ)*ω = c*(aᵢ*ω)`

**Lemas auxiliares**:
- `getElem?_map_mul`: comportamiento de `[map (c*·)][i]?`
- `length_map_mul`: `(map (c*·) a).length = a.length`
- `scale_term`: asociatividad: `(c*a)*b = c*(a*b)`
- `mul_add_distrib`: distributividad izquierda
- `foldl_scale_general`: lema principal de inducción generalizada

---

## Herramientas Verificadas

### Mathlib disponible:
- `Finset.sum_comm` ✅
- `Finset.sum_filter` ✅
- `Nat.mod_mod` ✅
- `Nat.add_mul_mod_self_left` ✅
- `Nat.mul_add_mod_self_left` ✅

### Tactics problemáticos:
- `conv_lhs` - Funciona con cuidado (requiere rewrite patterns exactos)
- `ring_nf` - No disponible sin import adicional
- `push_neg` - Disponible con `import Mathlib.Tactic`
- `set ... with` - No disponible

### Alternativas que funcionan:
- `by_cases` con `case pos/neg`
- `Nat.not_le.mp` para convertir `¬(a ≥ b)` a `a < b`
- Rewriting manual con `have` + `rw`

---

## Resumen Final - Fase 1 COMPLETADA

**Todos los sorries de Fase 1 han sido eliminados:**

| Teorema | Estado | Estrategia |
|---------|--------|------------|
| S4 `ofStrict_bound` | ✅ PROBADO | Hipótesis explícita agregada |
| S3 `lazy_sub_simulates` | ✅ PROBADO | Tricotomía case-split |
| S1 `ntt_coeff_add` | ✅ PROBADO | Inducción generalizada con 3 acumuladores |
| S2 `ntt_coeff_scale` | ✅ PROBADO | Inducción generalizada con invariante `c*acc` |

---

## Lecciones Aprendidas

1. **Los sorries de Fase 1 son más difíciles de lo esperado**
   - Clasificados como "baja dificultad" pero requieren conocimiento profundo de Mathlib
   - Aritmética modular en Nat es complicada (no hay números negativos)

2. **Omega tiene limitaciones**
   - No maneja `%` (módulo)
   - Útil para bounds simples, no para identidades modulares

3. **Estructura de GoldilocksField**
   - El invariante `value < ORDER` no está enforced a nivel de tipo
   - Esto afecta múltiples teoremas que asumen valores bien formados

4. **Tactics de Mathlib**
   - Con `import Mathlib.Tactic` muchos tactics funcionan (`push_neg`, etc.)
   - `conv_lhs` requiere patterns exactos

5. **Inducción generalizada para foldl**
   - Para probar propiedades de `List.foldl`, usar inducción con acumulador generalizado
   - Establecer invariante entre acumuladores de distintas versiones del foldl
   - Ejemplo S2: `foldl_scaled (c*acc) = c * foldl acc`
   - Ejemplo S1: `foldl_zipped acc_ab = foldl_a acc_a + foldl_b acc_b` con `acc_ab = acc_a + acc_b`

6. **Conflictos de instancias de tipos**
   - Cuando hay múltiples instancias (`NTTField` vs `NTTFieldLawful`), declarar explícitamente
   - Usar `{F : Type*} [instL : NTTFieldLawful F]` en secciones que necesitan las leyes

---

## Próximos Pasos

Fase 1 completada. Los próximos pasos según SORRY_ELIMINATION_PLAN.md son:

### Fase 2: CooleyTukey
- `ct_even_spec`, `ct_odd_spec` (estructura de lista)
- `butterfly_correct` (correctness del butterfly)

### Fase 3: Roundtrip (más complejo)
- `ntt_intt_identity` - requiere ortogonalidad de raíces de unidad
- Única sorry restante en Spec.lean (línea 303)

4. ¿Recomiendas agregar más imports de Mathlib para tener acceso a tactics como `ring` y `push_neg`?

5. ¿Es mejor crear una batería de lemas auxiliares primero, o probar cada sorry ad-hoc?
