# Bloque Central: Eliminación de Axiomas Fundacionales de Goldilocks Field

**Proyecto**: amo-lean
**Fecha**: 2026-02-11
**Archivo objetivo**: `AmoLean/Field/Goldilocks.lean` (1346 líneas, actualizado)
**Lean**: 4.16.0, Mathlib v4.16.0
**Complejidad**: max (5 axiomas fundacionales, máximo fan-out del proyecto)
**Este archivo es la fuente de verdad incremental para el progreso del Bloque Central.**

---

## Objetivo

Eliminar los 5 axiomas fundacionales de `AmoLean/Field/Goldilocks.lean` que soportan las instancias CommRing y Field de GoldilocksField:

| # | Axioma | Línea orig | Estado | Línea actual |
|---|--------|-----------|--------|-------------|
| 1 | `goldilocks_prime_is_prime` | 45 | **ELIMINADO** (theorem, Lucas) | 85 |
| 2 | `goldilocks_canonical` | 319 | **ELIMINADO** (theorem, subtype) | 444 |
| 3 | `reduce128_correct` | 539 | **ELIMINADO** (theorem, modular decomp) | 760 |
| 4 | `toZMod_pow` | 765 | PENDIENTE (axiom) | ~1032 |
| 5 | `toZMod_inv` | 781 | PENDIENTE (axiom) | ~1048 |

---

## Hallazgo Crítico de Soundness

**`goldilocks_canonical` es técnicamente FALSO para el struct actual.**

`GoldilocksField` es un struct bare con un campo `value : UInt64`. Nada impide construir `⟨ORDER⟩` o `⟨⟨ORDER_NAT, isLt_proof⟩⟩`, violando `a.value.toNat < ORDER_NAT`. El axiom introduce unsoundness. La solución es refactorear a struct con proof field o subtype.

---

## DAG de Dependencias

```
goldilocks_prime_is_prime ──→ Fact (Nat.Prime ORDER_NAT) ──→ ZMod es Field
                                                             │
goldilocks_canonical ──→ toZMod_injective ──→ toZMod_add/neg/sub/mul ──→ CommRing
                                                             │
reduce128_correct ──→ mul_val_eq ──→ toZMod_mul ─────────────┘
                                                             │
toZMod_pow ──→ npow_succ (CommRing) + zpow_succ' (Field) ───┤
                                                             │
toZMod_inv ──→ mul_inv_cancel (Field) ───────────────────────┘
```

**Orden topológico seguro**:
1. prime (independiente, de-risk obligatorio)
2. canonical (refactor, habilita todo lo demás)
3. reduce128 (habilita multiplicación)
4. toZMod_pow (usa toZMod_mul)
5. toZMod_inv (usa toZMod_pow + Fermat)

---

## Plan de Trabajo (Orden Topológico)

### GATE: De-risk `goldilocks_prime_is_prime`

**Ejecución**: SECUENCIAL (orquestador — riesgo máximo)

**Target**: Probar `Nat.Prime ORDER_NAT` donde ORDER_NAT = 2^64 - 2^32 + 1 = 18446744069414584321

**Estrategia escalonada** (probar en orden, parar al primer éxito):

1. **`norm_num`** (30s de-risk):
   ```lean
   theorem goldilocks_prime_is_prime : Nat.Prime ORDER_NAT := by norm_num [ORDER_NAT, ORDER]
   ```
   Si funciona → done. Probabilidad: 30% (posible timeout para 64-bit).

2. **`native_decide`** (30s de-risk):
   ```lean
   theorem goldilocks_prime_is_prime : Nat.Prime ORDER_NAT := by native_decide
   ```
   Mathlib implementa `Decidable (Nat.Prime n)` via `minFac` que prueba factores hasta √n.
   √p ≈ 2^32 ≈ 4.3×10⁹ iteraciones. Native code: ~4-10 segundos. Probabilidad: 60%.

3. **Pocklington manual** (contingencia si 1 y 2 fallan):
   p-1 = 2^32 × 3 × 5 × 17 × 257 × 65537 (factorización completa, todos Fermat primes + small primes)

   Para witness a=7 (conocido como raíz primitiva de Goldilocks):
   - Verificar `7^(p-1) mod p = 1` (by native_decide)
   - Para cada factor primo q de p-1: `gcd(7^((p-1)/q) - 1, p) = 1` (by native_decide)

   Requiere:
   - Formalizar Pocklington criterion como lema auxiliar (~50-80 líneas)
   - O encontrarlo en Mathlib (buscar `Pocklington` o `Nat.Prime.of_*`)

   Cada `native_decide` individual computa ~64 squarings mod p → microsegundos.

**Criterio de éxito**: `lake env lean AmoLean/Field/Goldilocks.lean` compila sin sorry para `goldilocks_prime_is_prime`.

**Si falla tras 4 intentos**: Escalar a /ask-lean con el goal exacto y errores.

---

### Bloque 1: Subtype Refactor de GoldilocksField

**Ejecución**: SECUENCIAL (cambio arquitectural — afecta todo el archivo)

**Objetivo**: Eliminar axioma `goldilocks_canonical` refactoreando el tipo para llevar prueba de canonicidad.

**Cambio de tipo**:
```lean
-- ANTES (unsound — axiom requerido)
structure GoldilocksField where
  value : UInt64

axiom goldilocks_canonical (a : GoldilocksField) : a.isCanonical

-- DESPUÉS (sound — invariante por construcción)
structure GoldilocksField where
  value : UInt64
  h_canonical : value.toNat < ORDER.toNat := by omega
```

**Sub-pasos**:

| # | Acción | Impacto | Dificultad |
|---|--------|---------|------------|
| 1.1 | Añadir campo `h_canonical` al struct | Rompe todos los constructores | BAJA |
| 1.2 | Actualizar `zero`, `one` | `⟨0, by native_decide⟩`, `⟨1, by native_decide⟩` | BAJA |
| 1.3 | Actualizar `ofUInt64` | Probar ambas ramas < ORDER | BAJA |
| 1.4 | Actualizar `ofNat` | Via ofUInt64 | BAJA |
| 1.5 | Actualizar `add` | Probar resultado < ORDER (ya en `add_val_eq`) | MEDIA |
| 1.6 | Actualizar `sub` | Probar ambas ramas < ORDER | MEDIA |
| 1.7 | Actualizar `neg` | Probar ambas ramas < ORDER | BAJA |
| 1.8 | Actualizar `reduce128` | Probar `(x % ORDER_NAT).toUInt64.toNat < ORDER` | MEDIA |
| 1.9 | Actualizar `mul`, `square` | Via reduce128 | BAJA |
| 1.10 | Actualizar `pow` | Via mul (inducción) | BAJA |
| 1.11 | Actualizar `inv`, `div` | Via pow | BAJA |
| 1.12 | Eliminar axioma `goldilocks_canonical` | Reemplazar por `a.h_canonical` | BAJA |
| 1.13 | Actualizar `deriving` y `DecidableEq` | Puede necesitar instancia manual | MEDIA |
| 1.14 | Actualizar constantes (`P_MINUS_1`, `P_MINUS_2`, etc.) | Añadir proofs | BAJA |
| 1.15 | Actualizar tests `#eval` al final del archivo | Ajustar constructores | BAJA |

**Regla de seguridad**: Compilar después de cada sub-paso. NO acumular más de 2 cambios sin compilar.

**Patrón de prueba para operaciones** (ejemplo `add`):
```lean
def add (a b : GoldilocksField) : GoldilocksField :=
  let sum := a.value.toNat + b.value.toNat
  let reduced := if sum >= ORDER.toNat then sum - ORDER.toNat else sum
  ⟨reduced.toUInt64, by
    have ha := a.h_canonical
    have hb := b.h_canonical
    simp only [Nat.toUInt64, UInt64.toNat_ofNat]
    split_ifs with h
    · -- sum ≥ ORDER: reduced = sum - ORDER < ORDER (since sum < 2*ORDER)
      have : reduced < ORDER.toNat := by omega
      have : reduced < UInt64.size := by omega
      rw [Nat.mod_eq_of_lt (by omega)]
      exact this
    · -- sum < ORDER: reduced = sum < ORDER
      have : reduced < UInt64.size := by omega
      rw [Nat.mod_eq_of_lt (by omega)]
      exact (by omega)⟩
```

**Impacto en código externo**: Buscar en el proyecto todos los usos de `GoldilocksField` fuera de `Goldilocks.lean`:
- `AmoLean/NTT/BabyBear.lean` — no usa GoldilocksField directamente
- `AmoLean/FRI/Fields/BN254.lean` — no usa GoldilocksField
- Posibles usos en tests — ajustar constructores

**Criterio de éxito**: `goldilocks_canonical` eliminado como axioma. `lake build` compila limpio.

---

### Bloque 2: `reduce128_correct`

**Ejecución**: SECUENCIAL (prueba más compleja, riesgo alto)

**Target**: Probar que `reduce128` preserva congruencia mod ORDER:
```lean
theorem reduce128_correct (x_lo x_hi : UInt64) :
    (GoldilocksField.reduce128 x_lo x_hi).value.toNat % ORDER_NAT =
    (x_lo.toNat + x_hi.toNat * 2^64) % ORDER_NAT
```

**Descomposición en sub-lemas**:

| # | Lema | Descripción | Táctica principal |
|---|------|-------------|-------------------|
| 2.1 | `reduce128_zero_hi` | Caso x_hi = 0 (YA PROBADO, línea 453) | — |
| 2.2 | `goldilocks_identity` | `2^64 ≡ EPSILON (mod ORDER)` i.e. `2^64 % ORDER = EPSILON` | Ya probado como `pow_64_mod_order` |
| 2.3 | `goldilocks_identity_96` | `2^96 ≡ -1 (mod ORDER)` | Ya probado como `pow_96_mod_order` |
| 2.4 | `uint64_decomp` | `x.toNat = (x &&& EPSILON).toNat + (x >>> 32).toNat * 2^32` | Ya probado (línea 500) |
| 2.5 | `reduce128_congruence_nonzero` | Caso x_hi ≠ 0: la fórmula `term1 - term2 + term3` es congruente | ring + mod arithmetic |
| 2.6 | `reduce128_intermediate_bounds` | Bounds del intermediate para probar que % ORDER es correcto | omega |
| 2.7 | `reduce128_toUInt64_roundtrip` | `(result % ORDER_NAT).toUInt64.toNat = result % ORDER_NAT` | Nat.mod_lt + Nat.mod_eq_of_lt |

**Estrategia para 2.5** (el sub-lema clave):

La cadena algebraica es:
```
x_lo + x_hi * 2^64
  = x_lo + (x_hi_lo + x_hi_hi * 2^32) * 2^64          -- uint64_decomp en x_hi
  = x_lo + x_hi_lo * 2^64 + x_hi_hi * 2^96             -- distribuir
  ≡ x_lo + x_hi_lo * EPSILON + x_hi_hi * (ORDER-1)     -- pow_64_mod_order + pow_96_mod_order
  ≡ x_lo + x_hi_lo * EPSILON - x_hi_hi                  -- ORDER ≡ 0 (mod ORDER)
  (mod ORDER)
```

Donde `x_hi_lo = x_hi &&& EPSILON` y `x_hi_hi = x_hi >>> 32`.

El `intermediate` en el código es exactamente `x_lo + x_hi_lo * EPSILON - x_hi_hi` (con manejo de underflow). Y `result = intermediate % ORDER`.

Táctica: `conv` + `rw` con las identidades existentes + `omega` para bounds.

**Lemas Mathlib necesarios**:
- `Nat.add_mul_mod_self` — para eliminar múltiplos de ORDER
- `Nat.mul_mod`, `Nat.add_mod` — para aritmética modular
- `Nat.mod_mod_of_dvd` — si necesario
- `pow_64_mod_order`, `pow_96_mod_order`, `uint64_decomp` — YA EXISTENTES en el archivo

**Criterio de éxito**: `reduce128_correct` probado, `mul_val_eq` compila sin cambios.

---

### Bloque 3: `toZMod_pow`

**Ejecución**: SECUENCIAL (dependencia estricta de Bloque 2)

**Target**:
```lean
theorem toZMod_pow (a : GoldilocksField) (n : Nat) :
    toZMod (GoldilocksField.pow a n) = (toZMod a) ^ n
```

**Estrategia**: Strong induction on `n` matching the binary exponentiation structure.

```lean
theorem toZMod_pow (a : GoldilocksField) (n : Nat) :
    toZMod (GoldilocksField.pow a n) = (toZMod a) ^ n := by
  -- Strong induction: for all m < n, the property holds
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    match n with
    | 0 => simp [GoldilocksField.pow, toZMod_one]  -- pow a 0 = one
    | 1 => simp [GoldilocksField.pow]                -- pow a 1 = a
    | n + 2 =>
      simp only [GoldilocksField.pow]
      -- halfExp = (n+2)/2, halfPow = pow a halfExp
      -- squared = square halfPow = mul halfPow halfPow
      have h_half_lt : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
      have ih_half := ih ((n + 2) / 2) h_half_lt
      -- toZMod (square halfPow) = (toZMod halfPow)^2 = ((toZMod a)^halfExp)^2
      rw [GoldilocksField.square]
      split_ifs with h_even
      · -- Even case: result = squared
        rw [toZMod_mul, ih_half, ← pow_mul]
        congr 1
        omega  -- 2 * ((n+2)/2) = n+2 when even
      · -- Odd case: result = mul squared base
        rw [toZMod_mul, toZMod_mul, ih_half, ← pow_mul, ← pow_succ]
        congr 1
        omega  -- 2 * ((n+2)/2) + 1 = n+2 when odd
```

**Lemas Mathlib necesarios**:
- `pow_mul` — `a^(m*n) = (a^m)^n`
- `pow_succ` — `a^(n+1) = a^n * a`
- `Nat.div_lt_self` — terminación
- `Nat.mul_div_cancel` o `Nat.two_mul_div_two_of_even` — aritmética de paridad

**Riesgo**: La estructura `match` del `pow` puede dificultar `simp`. Puede necesitar `unfold` manual. Dificultad: MEDIA.

**Criterio de éxito**: `toZMod_pow` probado, `npow_succ` en CommRing compila.

---

### Bloque 4: `toZMod_inv`

**Ejecución**: SECUENCIAL (depende de Bloque 3)

**Target**:
```lean
theorem toZMod_inv (a : GoldilocksField) :
    toZMod (GoldilocksField.inv a) = (toZMod a)⁻¹
```

**Estrategia**: Directa via toZMod_pow + Fermat's Little Theorem.

```lean
theorem toZMod_inv (a : GoldilocksField) :
    toZMod (GoldilocksField.inv a) = (toZMod a)⁻¹ := by
  simp only [GoldilocksField.inv]
  split_ifs with h
  · -- Case a.value == 0: inv returns zero
    simp only [beq_iff_eq] at h
    have : a = ⟨0, ...⟩ := ... -- a.value = 0
    simp [toZMod_zero, GoldilocksField.zero, inv_zero]
  · -- Case a.value ≠ 0: inv = pow a (ORDER-2)
    rw [toZMod_pow]
    -- Goal: (toZMod a) ^ (ORDER_NAT - 2) = (toZMod a)⁻¹
    -- Use ZMod.pow_card_sub_two_eq_inv (Fermat's Little Theorem in ZMod)
    -- Requires: Fact (Nat.Prime ORDER_NAT) — from goldilocks_prime_is_prime
    symm
    exact ZMod.pow_card_sub_two_eq_inv (toZMod a)
```

**Lemas Mathlib necesarios**:
- `ZMod.pow_card_sub_two_eq_inv` — Fermat's Little Theorem: `a^(p-2) = a⁻¹` en ZMod p
- `inv_zero` — `0⁻¹ = 0` en un campo

**Riesgo**: BAJO. La prueba es directa una vez que toZMod_pow está probado.

**Criterio de éxito**: Todos los 5 axiomas eliminados. `lake build` pasa limpio.

---

## Pre-Benchmarks (Criterios de Éxito)

| Bloque | Métrica | Target | Método |
|--------|---------|--------|--------|
| GATE | `goldilocks_prime_is_prime` compila | Sin sorry | `lake env lean Goldilocks.lean` |
| 1 | `goldilocks_canonical` eliminado | 0 axiomas canonical | grep axiom |
| 2 | `reduce128_correct` probado | Sin sorry | `lake env lean Goldilocks.lean` |
| 3 | `toZMod_pow` probado | Sin sorry | `lake env lean Goldilocks.lean` |
| 4 | `toZMod_inv` probado | Sin sorry | `lake env lean Goldilocks.lean` |
| FINAL | Axiomas en Goldilocks.lean | **0** | `grep -c "^axiom" Goldilocks.lean` |
| FINAL | Build completo | PASS | `lake build` |
| FINAL | Tiempo compilación | < 120s | `time lake build` |

---

## Protocolo de Escalación

- **Intento 1-2**: Resolución directa con tácticas conocidas
- **Intento 3**: Buscar en Mathlib (/ask-dojo) + revisar lecciones (L-015 a L-020)
- **Intento 4**: Consultar /ask-lean con goal exacto y errores
- **Si persiste**: Reformular el teorema (agregar hipótesis, simplificar enunciado)

---

## Lecciones Aplicables

| ID | Lección | Aplicación |
|----|---------|------------|
| L-015 | ZMod casting patterns | toZMod_pow, toZMod_inv |
| L-016 | `decide` vs `native_decide` para hechos computacionales | goldilocks_prime |
| L-017 | Probar canonicidad por operación | Bloque 1 refactor |
| L-019 | `Function.Injective.commRing/field` | Mantener estrategia existente |
| L-082 | Axiom auditing: cada axiom debe tener plan de eliminación | Este plan |
| L-134 | DAG de de-risking: orden topológico = orden de trabajo | GATE first |
| L-136 | De-risk nodo crítico con sketch antes de auxiliares | Primality sketch |

---

## Bibliografía Relevante

- Pocklington criterion para primalidad certificada
- Goldilocks field: Plonky2/Plonky3 reference implementation
- Binary exponentiation correctness via strong induction
- ZMod.pow_card_sub_two_eq_inv (Fermat's Little Theorem en Mathlib)

---

## Feedback QA (3 rondas Gemini)

**Recomendación**: APPROVED WITH MANDATORY REVISIONS

**Issues resueltos**:
1. Estrategia de primalidad: norm_num → native_decide → Pocklington (escalonada)
2. Canonicidad: subtype/proof-field refactor (no axiom)
3. reduce128: descomposición en 3+ sub-lemas

**Mejoras adoptadas del QA**:
- Probar norm_num primero (puede ser trivial en Mathlib reciente)
- Decomposición explícita de reduce128 en lemas intermedios
- Separar prueba abstracta (congruencia mod) de verificación de implementación (UInt64)

---

## Progreso (Incremental)

| Bloque | Estado | Fecha | Notas |
|--------|--------|-------|-------|
| GATE: prime | **COMPLETADO** | 2026-02-11 | Lucas primality + zpowMod |
| Bloque 1: canonical refactor | **COMPLETADO** | 2026-02-11 | Subtype + 7 sorry eliminados |
| Bloque 2: reduce128 | **COMPLETADO** | 2026-02-11 | 6 sub-lemas, descomp. modular |
| Bloque 3: toZMod_pow | PENDIENTE | — | Strong induction on binary exp |
| Bloque 4: toZMod_inv | PENDIENTE | — | Fermat via toZMod_pow |

**Resumen**: 3/5 axiomas eliminados, 0 sorry, 2 axiomas restantes (`toZMod_pow`, `toZMod_inv`). `lake build` OK.

---

## Notas de Implementación: GATE (goldilocks_prime_is_prime)

**Estrategia ganadora**: Opción 3 (Pocklington/Lucas manual)

Las opciones 1 (norm_num) y 2 (native_decide directo) fallaron:
- `norm_num`: stack overflow para primos > 25 bits
- `native_decide` sobre `Nat.Prime`: ~4×10⁹ trial divisions, impracticable

**Solución implementada** (líneas 55-110):

1. **`zpowMod`**: Exponenciación modular binaria O(log n) directamente en `ZMod ORDER_NAT`.
   Definida recursivamente con caso par/impar, compilable por `native_decide`.

2. **`zpowMod_eq_pow`**: Prueba de equivalencia `zpowMod a n = a ^ n` por inducción fuerte,
   con `pow_add` y `pow_succ` para los casos par/impar.

3. **`prime_dvd_eq`**: Lema auxiliar — si `p` es primo y divide a otro primo `q`, entonces `p = q`.

4. **Prueba principal**: Usa `lucas_primality` de Mathlib (`Mathlib.NumberTheory.LucasPrimality`).
   - Witness: `a = 7` (raíz primitiva de Goldilocks)
   - Factorización: `p-1 = 2^32 × 3 × 5 × 17 × 257 × 65537`
   - Cada verificación: `rw [← zpowMod_eq_pow]; native_decide` (~64 multiplicaciones mod p, microsegundos)
   - Enumeración de factores: cadena recursiva de `Nat.Prime.prime.dvd_mul`

**Lección clave**: Para primos grandes, definir exponenciación eficiente en ZMod y usar `native_decide`
sobre ella. `native_decide` directo sobre `Nat.Prime` es inviable (O(√p) trial divisions).

---

## Notas de Implementación: Bloque 1 (Subtype Refactor + Canonicity Proofs)

### Paso 1: Refactor del struct (sesión anterior)

Cambio de:
```lean
structure GoldilocksField where
  value : UInt64
```
A:
```lean
structure GoldilocksField where
  value : UInt64
  h_lt : value.toNat < ORDER.toNat
```

- Añadidas instancias manuales: `DecidableEq` (con `cases`/`simp_all`), `Repr`, `Hashable`
- `goldilocks_canonical` convertido de axiom a theorem: `a.h_lt`
- Actualizados constructores en todo el proyecto (~15 archivos):
  - Constantes: `⟨valor, by native_decide⟩`
  - Dinámicos: `GoldilocksField.ofUInt64` o `GoldilocksField.ofNat`
- Cambios en proofs: `↓reduceIte` → `dif_pos` donde `ofUInt64` usa `dite`

### Paso 2: Eliminación de los 7 sorry de canonicidad (sesión actual)

Cada operación aritmética necesita probar que su resultado tiene `.toNat < ORDER.toNat`.

| # | Operación | Ubicación | Estrategia de prueba |
|---|-----------|-----------|---------------------|
| 1 | `ofUInt64` else | línea 178 | `UInt64.toNat_sub_of_le` + `n.toNat < UInt64.size ≤ 2*ORDER` → omega |
| 2 | `add` | línea 207 | `show` para unfold let + `split_ifs` en la condición `sum ≥ ORDER` + omega |
| 3 | `sub` if | línea 224 | `UInt64.toNat_sub_of_le` + `a.h_lt` → omega |
| 4 | `sub` else | línea 230 | `UInt64.toNat_sub_of_le` + `simp [UInt64.toNat_add]` + `Nat.mod_eq_of_lt` → omega |
| 5 | `neg` | línea 248 | `UInt64.toNat_sub_of_le` + `a.value ≠ 0` (vía `UInt64.ext`) → omega |
| 6 | `reduce128` | línea 287 | `Nat.mod_lt` (resultado = `intermediate % ORDER`) + roundtrip `toUInt64.toNat` |
| 7 | `ofZMod` | línea 431 | `ZMod.val_lt` + `Nat.toUInt64/UInt64.toNat_ofNat` roundtrip |

**Cambios a definiciones**:
- `neg`: `if a.value == 0` → `if h : a.value = 0` (dite, para acceder a `h : a.value ≠ 0` en else)
- `sub`: `if a.value >= b.value` → `if h : a.value >= b.value` (dite, para acceder al ordering)
- `add`: Misma estructura (let/if), proof usa `show` para unfold let bindings + `split_ifs`

**Lemas helper añadidos**:
- `toUInt64_toNat_of_lt` (private): `n < UInt64.size → n.toUInt64.toNat = n`
  (vía `simp [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt]`)

**Lemas UInt64 usados repetidamente**:
- `UInt64.toNat_sub_of_le`: `y ≤ x → (x - y).toNat = x.toNat - y.toNat`
- `UInt64.toNat_add`: `(x + y).toNat = (x.toNat + y.toNat) % UInt64.size`
- `UInt64.le_iff_toNat_le`: conversión entre orderings UInt64 y Nat
- `UInt64.lt_iff_toNat_lt`: idem para `<`

**Gotchas importantes**:
1. **`a.h_lt` no está automáticamente en scope de omega** — siempre hacer `have ha := a.h_lt` explícitamente
2. **Let bindings son opacos para split_ifs** — usar `show <expanded form>` para unfold antes de `split_ifs`
3. **`private theorem` no cruza bloques namespace** — inlinear en el segundo bloque `GoldilocksField`
4. **`rw` falla en tipos dependientes de structs** — usar `simp only [...]` cuando hay `h_lt` en el struct
5. **`native_decide; omega` es un chain que no funciona** — usar líneas separadas: `by native_decide` + `omega`
6. **`UInt64.toNat_add` puede causar maxRecDepth con `rw`** — usar `simp only [UInt64.toNat_add, ...]` en su lugar

**Proofs downstream que se verificaron sin cambios**:
- `add_val_eq`, `neg_val_eq`, `sub_val_eq` (usan `split_ifs`, compatible con `dite`)
- `toZMod_add/neg/sub/mul` (usan `toZMod_injective` pattern)
- `zero_add`, `add_zero` (usan `↓reduceIte` sobre el `if` interno del let, no cambió)
- `one_mul`, `mul_one` (usan `dif_pos`)
- CommRing + Field instances completas

---

## Notas de Implementación: Bloque 2 (reduce128_correct)

### Arquitectura de la prueba

El axioma `reduce128_correct` se descompuso en 6 sub-lemas organizados por dependencia:

```
x_hi_hi_bound / x_hi_lo_bound    ← FUNDACIONAL (bounds 32-bit)
          │
          ▼
reduce128_intermediate_bound      ← Intermediate < 2*ORDER
          │
          ▼
reduce128_algebraic               ← x_lo + x_hi*2^64 ≡ x_lo + x_hi_lo*ε + x_hi_hi*(p-1)
          │
          ▼
reduce128_no_underflow            ← Rama term1 ≥ term2 preserva congruencia
reduce128_underflow               ← Rama term1 < term2 preserva congruencia
          │
          ▼
reduce128_correct (ENSAMBLAJE)    ← Compone todo: by_cases x_hi=0, unfold, branch
```

### Sub-lemas implementados (líneas 643-808)

| # | Lema | Línea | Táctica clave | Dificultad |
|---|------|-------|---------------|------------|
| 0a | `x_hi_hi_bound` | 644 | `Nat.div_lt_of_lt_mul` + `native_decide` | BAJA |
| 0b | `x_hi_lo_bound` | 651 | `Nat.and_pow_two_sub_one_eq_mod` + `Nat.mod_lt` | BAJA |
| 1 | `reduce128_intermediate_bound` | 657 | `nlinarith` para term3 bound, `omega` con valores numéricos | MEDIA |
| 2 | `reduce128_algebraic` | 685 | `Nat.mul_mod` + `pow_64/96_mod_order` + `suffices`/`calc` | ALTA |
| 3a | `reduce128_no_underflow` | 717 | `Nat.add_mul_mod_self_right` + `omega` con `key` | MEDIA |
| 3b | `reduce128_underflow` | 736 | `Nat.add_mul_mod_self_right` + `omega` con `key`+`key2` | MEDIA-ALTA |
| 4 | `reduce128_correct` | 760 | `by_cases` + `unfold` + `simp` + composición | ALTA |

### Estrategia algebraica

La prueba se estructura en 3 capas:

1. **Capa modular** (`reduce128_algebraic`): Usa `Nat.mul_mod` y las identidades `2^64 ≡ ε` y `2^96 ≡ p-1` para reescribir `x_lo + x_hi * 2^64` como `x_lo + x_hi_lo * ε + x_hi_hi * (p-1)` módulo p.

2. **Capa de branches** (`reduce128_no_underflow`/`reduce128_underflow`): Muestra que ambas ramas del `if` (con y sin underflow) computan un valor congruente a la expresión algebraica. La clave: `term1 - term2 + term3 ≡ term1 + term3 + term2*(p-1)` porque `term2*(p-1) + term2 = term2*p ≡ 0`.

3. **Capa de ensamblaje** (`reduce128_correct`): Split en `x_hi = 0` (usa `reduce128_zero_hi` existente) y `x_hi ≠ 0` (unfold + composición de sub-lemas).

### Gotchas y lecciones aprendidas

| # | Gotcha | Solución | Lección ID |
|---|--------|----------|------------|
| G1 | `← Nat.mul_mod` no matchea tras `rw [pow_64_mod_order]` porque el segundo factor ya no tiene `% p` | Usar `conv_lhs/conv_rhs` con `Nat.mul_mod` y `Nat.mod_eq_of_lt` en paralelo | L-183 |
| G2 | `omega` no puede resolver `term2*(ORDER-1)` vs `term2*ORDER - term2` (no-lineal para omega) | Probar `key : term2 * ORDER = term2 * (ORDER-1) + term2` con `conv + ring`, luego omega ve la relación lineal entre átomos | L-184 |
| G3 | `ring` falla para `2^64 + (2^64 - 2^32 + 1) = 2 * (2^64 - 2^32 + 1)` — ecuación era FALSA | Siempre verificar aritméticamente las igualdades antes de usar `ring`. Usar `nlinarith` con bounds numéricos o `omega` con `rw [h_ord_val]` | L-185 |
| G4 | `ORDER.toNat` y `ORDER_NAT` no unifican para `Nat.mod_mod_of_dvd` | Probar `h_val : result.value.toNat = intermediate % ORDER_NAT` por separado con `simp only [ORDER_NAT, ...]` | L-186 |
| G5 | `beq_iff_eq` tiene tipo `(a == b) = true ↔ a = b`, no aplica a `= false` | Usar `simp [beq_iff_eq, h_zero]` que maneja ambas polaridades | L-187 |
| G6 | `simp only []` puede fallar con "no progress" tras unfold | Verificar si el simp es necesario; a veces el unfold ya simplificó | L-188 |

### Lemas Mathlib usados (no existentes previamente en el archivo)

| Lema | Uso |
|------|-----|
| `Nat.mul_mod a b n` | `(a*b) % n = (a%n * (b%n)) % n` — reescribir exponentes grandes |
| `Nat.add_mod a b n` | `(a+b) % n = (a%n + b%n) % n` — separar suma en componentes |
| `Nat.add_mul_mod_self_right a b n` | `(a + b*n) % n = a % n` — eliminar múltiplos de ORDER |
| `Nat.mod_mod_of_dvd n (dvd_refl _)` | `(a % n) % n = a % n` — idempotencia de mod |
| `Nat.mod_eq_of_lt` | `a < n → a % n = a` — simplificar mod cuando valor es canónico |
| `Nat.sub_add_cancel` | `n ≥ m → n - m + m = n` — reconvertir ORDER-1+1 a ORDER |

### Métricas

- **Líneas añadidas**: ~170 (de L643 a L808)
- **Tiempo de compilación**: incremental, <30s por paso
- **Intentos fallidos**: 3 (ring en igualdad falsa, ← Nat.mul_mod, beq pattern)
- **Escalación**: No fue necesaria (ni /ask-lean ni /ask-dojo)

---

## Contexto para Reanudar en Nueva Sesión

### Estado actual del archivo

- **Archivo**: `AmoLean/Field/Goldilocks.lean` (1346 líneas)
- **Axiomas eliminados**: 2/5 (`goldilocks_prime_is_prime`, `goldilocks_canonical`)
- **Axiomas pendientes**: 3 (`reduce128_correct` L664, `toZMod_pow` L890, `toZMod_inv` L906)
- **Sorry**: 0
- **Build**: `lake build` pasa limpio (solo warnings de unused vars en NTT/Radix4/)

### Próximo paso: Bloque 2 — `reduce128_correct`

```lean
-- Línea 664:
axiom reduce128_correct (x_lo x_hi : UInt64) :
    (GoldilocksField.reduce128 x_lo x_hi).value.toNat % ORDER_NAT =
    (x_lo.toNat + x_hi.toNat * 2^64) % ORDER_NAT
```

**Sub-lemas YA existentes en el archivo** (no hay que crearlos):
- `pow_64_mod_order` (L614): `2^64 % ORDER_NAT = EPSILON.toNat`
- `pow_96_mod_order` (L618): `2^96 % ORDER_NAT = ORDER_NAT - 1`
- `uint64_decomp` (L624): `x.toNat = (x &&& EPSILON).toNat + (x >>> 32).toNat * 2^32`
- `reduce128_zero_hi` (L577): caso `x_hi = 0` ya probado

**Lo que falta probar**: caso `x_hi ≠ 0` — la cadena algebraica:
```
x_lo + x_hi * 2^64
  ≡ x_lo + x_hi_lo * EPSILON - x_hi_hi (mod ORDER)
  = intermediate (con manejo de underflow)
  → result = intermediate % ORDER
```

**Estrategia**: Ver sección "Bloque 2" arriba. El sub-lema clave es 2.5 (congruencia nonzero).

### Archivos modificados (para referencia de git)

Todos los cambios están en `AmoLean/Field/Goldilocks.lean` y los archivos de constructores
actualizados en la sesión anterior (NTT/, Tests/, Bench/).

### Instrucciones para nueva sesión

```
Lee Bloque_central_plan.md (este archivo) como contexto.
Lee AmoLean/Field/Goldilocks.lean líneas 252-290 (def reduce128) y 577-665 (sub-lemas + axiom).
Continúa con Bloque 2: eliminar el axioma reduce128_correct.
```

---

*Creado: 2026-02-11*
*Última actualización: 2026-02-11 (GATE + Bloque 1 completados, 7 sorry eliminados)*
*Próxima actualización: al completar Bloque 2 (reduce128_correct)*
