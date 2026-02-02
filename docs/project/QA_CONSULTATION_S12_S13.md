# Consulta al QA: Estrategias para S12/S13 - Ortogonalidad y Roundtrip NTT

**Fecha**: 2026-02-02
**Contexto**: Eliminación de sorries en el módulo NTT de AMO-Lean

---

## 1. OBJETIVO GENERAL

Completar la cadena de pruebas para demostrar la identidad fundamental del NTT:
```
INTT(NTT(x)) = x
```

Esta identidad requiere probar la **ortogonalidad de raíces de unidad**:
```
Σ_k ω^(jk) * ω^(n - (ik mod n)) = n  si j = i
                                 = 0  si j ≠ i
```

---

## 2. ESTADO ACTUAL DEL PROYECTO

### Teoremas ya probados (funcionando):
- `ct_recursive_eq_spec` (S10): NTT_recursive = NTT_spec ✓
- `orthogonality_sum_lt`: Σₖ ω^(d·k) = n si d=0, sino 0 ✓
- `powSum_nonzero`: Σᵢ ω^(i·j) = 0 para 0 < j < n ✓
- `pow_eq_pow_mod`: ω^k = ω^(k % n) ✓
- Todos los teoremas de CooleyTukey.lean ✓

### Sorries pendientes:
- **S12**: `ntt_orthogonality_sum` - Teorema de ortogonalidad con dos índices
- **S13**: `intt_ntt_identity_finset` - INTT(NTT(x))ᵢ = xᵢ
- **S11**: `ntt_intt_recursive_roundtrip` - Composición del roundtrip

---

## 3. PROBLEMA PRINCIPAL: `pow_transform'`

### El teorema que necesito probar:
```lean
theorem pow_transform' {ω : F} {n : ℕ} (hn : n > 0) (hω : IsPrimitiveRoot ω n)
    (j i k : ℕ) (hj : j < n) (hi : i < n) :
    ω ^ (j * k) * ω ^ (n - (i * k) % n) = ω ^ (((j + n - i) % n) * k)
```

### Lo que esto significa matemáticamente:
- LHS: ω^(jk) · ω^(n - (ik mod n))
- RHS: ω^(((j+n-i) mod n) · k)

Usando `pow_eq_pow_mod`, basta probar que los exponentes son congruentes módulo n:
```
(j*k + (n - (i*k) % n)) % n = (((j + n - i) % n) * k) % n
```

### Por qué es difícil:

1. **Aritmética de naturales con restas**:
   - En ℕ, `a - b` puede ser 0 si b > a (truncamiento)
   - Expresiones como `n - (i*k % n)` requieren verificar que `i*k % n ≤ n`

2. **`omega` no maneja exponentes ni módulos complejos**:
   ```lean
   -- omega falla en:
   have h : (j*k + (n - r)) % n = ((j-i)*k) % n := by omega -- FALLA
   ```

3. **`rw` no encuentra patrones dentro de sumas**:
   ```lean
   have h3 : i * k = (i * k / n) * n + r
   -- Este rw falla:
   _ = (j - i) * k + ((i * k / n) * n + r + (n - r)) := by rw [h3] -- FALLA
   ```
   El `rw` no puede sustituir `i * k` cuando está dentro de una expresión más grande.

4. **Orden de multiplicación en Mathlib**:
   - `Nat.div_add_mod m n` devuelve `n * (m / n) + m % n = m`
   - Pero necesito `(m / n) * n + m % n = m`
   - Requiere `Nat.mul_comm` extra en cada uso

5. **Casos j ≥ i vs j < i**:
   - Cuando j ≥ i: `(j + n - i) % n = j - i`
   - Cuando j < i: `(j + n - i) % n = j + n - i`
   - Cada caso requiere pruebas diferentes

---

## 4. ESTRATEGIAS INTENTADAS (FALLIDAS)

### Estrategia 1: calc chains con rw
```lean
calc j * k + (n - r)
    = (j - i) * k + i * k + (n - r) := by rw [h_sub]
  _ = (j - i) * k + ((i * k / n) * n + r) + (n - r) := by rw [h_ik_decomp]  -- FALLA
  ...
```
**Problema**: `rw` no sustituye dentro de subexpresiones.

### Estrategia 2: simp only con hipótesis locales
```lean
simp only [h3] at goal  -- A veces simplifica de más o de menos
```
**Problema**: Comportamiento impredecible.

### Estrategia 3: Usar congr
```lean
have hstep2 : ... := by
  congr 2
  exact h3
```
**Problema**: `congr` no siempre descompone como esperamos.

### Estrategia 4: Prueba directa con omega
```lean
have h_final : (j * k + (n - r)) % n = ((j - i) * k) % n := by omega
```
**Problema**: omega no maneja `%` en expresiones complejas.

---

## 5. TEOREMAS EXISTENTES QUE PODRÍAN AYUDAR

En `RootsOfUnity.lean` ya tenemos:
```lean
-- ω^k = ω^(k % n)
theorem pow_eq_pow_mod (h : IsPrimitiveRoot ω n) (hn : n > 0) (k : ℕ) :
    ω ^ k = ω ^ (k % n)

-- Σᵢ ω^(i·j) = 0 para 0 < j < n
theorem powSum_nonzero {n : ℕ} (hn : n > 1) (hω : IsPrimitiveRoot ω n)
    (hj_pos : 0 < j) (hj_lt : j < n) :
    powSum ω n j = 0
```

En `Properties.lean`:
```lean
-- Σₖ ω^(d·k) = n si d=0, sino 0
theorem orthogonality_sum_lt {n : ℕ} (hn : n > 1) {ω : F}
    (hω : IsPrimitiveRoot ω n) (d : ℕ) (hd_lt : d < n) :
    (Finset.range n).sum (fun k => ω ^ (d * k)) =
    if d = 0 then (n : F) else 0
```

---

## 6. PREGUNTAS ESPECÍFICAS PARA EL QA

### P1: Estrategia alternativa para `pow_transform'`
¿Existe una forma más elegante de probar la congruencia de exponentes?
- ¿Debería trabajar en ℤ en lugar de ℕ para evitar problemas de truncamiento?
- ¿Hay algún teorema de Mathlib que maneje directamente `(a + (n - b%n)) % n`?

### P2: Uso de `orthogonality_sum_lt` existente
Ya tenemos probado que `Σₖ ω^(d·k) = n si d=0, sino 0`.
¿Puedo derivar `ntt_orthogonality_sum` de este teorema sin probar `pow_transform'`?

La conexión sería:
```
ω^(jk) * ω^(n - (ik mod n)) = ω^((j-i)k mod n) = ω^(d*k) donde d = (j-i) mod n
```

### P3: Arquitectura de la prueba
¿Es mejor:
a) Probar `pow_transform'` directamente (lo que estoy intentando)
b) Usar un lema intermedio sobre exponentes en ℤ y luego convertir
c) Usar `native_decide` para casos específicos pequeños y generalizar
d) Otra arquitectura completamente diferente

### P4: Manejo de `Nat.div_add_mod`
El orden de multiplicación `n * (m/n)` vs `(m/n) * n` causa muchos problemas.
¿Hay una forma sistemática de manejar esto, o debería crear un lema wrapper?

### P5: Priorización
Si `pow_transform'` resulta muy difícil, ¿debería:
- Dejarlo como axioma temporal y avanzar con S13/S11?
- O es fundamental resolverlo primero?

### P6: Preservación de trabajo previo
En sesiones anteriores cerramos exitosamente varios sorries importantes:

**Sesión 3 - Teoremas cerrados:**
- `NTT_recursive_unfold` (CooleyTukey.lean:158)
- `NTT_recursive_getElem_upper` (CooleyTukey.lean:177)
- `NTT_recursive_getElem_lower` (CooleyTukey.lean:189)
- `NTT_recursive_getElem_none` (CooleyTukey.lean:209)
- `ct_recursive_eq_spec` (S10) (Correctness.lean:163)

**Sesiones 1-2 - Teoremas cerrados:**
- `cooley_tukey_upper_half` (S8)
- `cooley_tukey_lower_half` (S9)
- `powSum_nonzero`
- `orthogonality_sum_lt`
- Todos los lemmas de splitting (evens/odds)

**Preguntas:**
- ¿Cuáles de estos teoremas ya probados son directamente útiles para S12/S13?
- ¿Cómo puedo estructurar la prueba de `ntt_orthogonality_sum` para reutilizar `orthogonality_sum_lt` que ya funciona?
- ¿Hay algún camino que evite crear nuevo código complejo y en su lugar componga los teoremas existentes?

**IMPORTANTE**: No quiero romper ninguno de estos teoremas que ya funcionan. La solución debe ser aditiva, no modificar archivos que ya compilan correctamente.

---

## 7. CÓDIGO ACTUAL DE `pow_transform'` (con errores)

```lean
theorem pow_transform' {ω : F} {n : ℕ} (hn : n > 0) (hω : IsPrimitiveRoot ω n)
    (j i k : ℕ) (hj : j < n) (hi : i < n) :
    ω ^ (j * k) * ω ^ (n - (i * k) % n) = ω ^ (((j + n - i) % n) * k) := by
  rw [← pow_add]
  conv_lhs => rw [hω.pow_eq_pow_mod hn]
  conv_rhs => rw [hω.pow_eq_pow_mod hn]
  congr 1
  -- Goal: (j * k + (n - (i * k) % n)) % n = ((j + n - i) % n * k) % n

  set r := (i * k) % n with hr_def
  set d := (j + n - i) % n with hd_def

  by_cases h_jgei : j ≥ i
  · -- Case j ≥ i: necesito probar (j*k + (n-r)) % n = ((j-i)*k) % n
    -- AQUÍ ES DONDE FALLAN TODAS LAS ESTRATEGIAS
    sorry
  · -- Case j < i: necesito probar (j*k + (n-r)) % n = ((j+n-i)*k) % n
    sorry
```

---

## 8. RESTRICCIONES

1. **No romper código existente**: CooleyTukey.lean, Spec.lean, RootsOfUnity.lean funcionan
2. **Mantener arquitectura**: La estructura de capas del proyecto debe preservarse
3. **Evitar axiomas innecesarios**: Preferir pruebas completas sobre `sorry`
4. **Compatibilidad Mathlib**: Usar teoremas de Mathlib cuando sea posible

---

## 9. ARCHIVOS RELEVANTES

- `/AmoLean/NTT/OrthogonalityProof.lean` - Archivo con los errores actuales (7 errores)
- `/AmoLean/NTT/Properties.lean` - Contiene `intt_ntt_identity_finset` con sorry
- `/AmoLean/NTT/RootsOfUnity.lean` - Teoremas base de raíces de unidad
- `/docs/project/SORRY_ELIMINATION_SESSION_3.md` - Documentación de sesión anterior exitosa

---

Agradezco cualquier insight o estrategia alternativa que el QA pueda sugerir.
