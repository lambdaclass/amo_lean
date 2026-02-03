# Sesion 7: Plan Estrategia B - Isomorfismo ZMod para GoldilocksField

**Fecha**: 2026-02-03
**Objetivo**: Cerrar ~22 sorries en GoldilocksField usando isomorfismo a ZMod p
**Estado**: PLANIFICACION COMPLETADA - Pendiente implementacion

---

## Resumen Ejecutivo

Esta sesion elaboro el plan de ataque para eliminar los sorries restantes en GoldilocksField
usando la **Estrategia B**: transferencia de propiedades via isomorfismo a `ZMod ORDER_NAT`.

### Consultas Realizadas

| Fuente | Hallazgo Clave |
|--------|----------------|
| **/lean-search** | `ZMod.val_injective`, `ZMod.val_add`, `ZMod.val_mul`, `ZMod.val_cast_of_lt` |
| **/ask-lean** | Patron `add_val_eq` - probar primero ecuacion a nivel Nat |
| **/collab-qa** | Alerta sobre `goldilocks_canonical` axioma; sub-plan para `reduce128` |
| **Bibliografia** | Paper Trieu 2025 - usa isomorfismo similar en Coq/Fiat-Crypto |

### Estado Actual

```
PROBADO (via toZMod_injective + ring):
  add_assoc, mul_assoc, left_distrib, right_distrib

PROBADO (directo):
  zero_add, add_zero, add_comm, mul_comm, zero_mul, mul_zero, one_mul, mul_one
  toZMod_injective

PENDIENTE (22 sorries):
  toZMod_* (8), CommRing (8), Field (5), Helper (1)
```

---

## Decisiones de Diseno

### DD-023: Canonicidad por Operacion (vs Axioma Global)

**Contexto**: El plan inicial proponia un axioma `goldilocks_canonical : forall x, x.value.toNat < ORDER.toNat`.

**Feedback QA**: "El axioma goldilocks_canonical es una debilidad. Si alguna operacion produce un valor no canonico, el axioma seria falso."

**Decision**: Probar canonicidad para cada operacion individualmente:
- `add_canonical`
- `neg_canonical`
- `mul_canonical` (depende de `reduce128_correct`)

**Justificacion**:
1. Maximiza confianza en la verificacion
2. Identifica exactamente donde puede fallar la canonicidad
3. El esfuerzo adicional es moderado (la mayoria son `split_ifs + omega`)

**Consecuencias**: Mas trabajo de prueba, pero base mas solida.

### DD-024: Patron ZMod.val_injective

**Contexto**: Probar `toZMod_add` directamente causa timeouts por `Nat.rec` interno de ZMod.

**Decision**: Usar el patron:
```lean
theorem toZMod_add (a b : GoldilocksField) :
    toZMod (a + b) = toZMod a + toZMod b := by
  apply ZMod.val_injective
  simp only [toZMod, ZMod.val_add]
  rw [ZMod.val_cast_of_lt (add_canonical a b)]
  rw [ZMod.val_cast_of_lt (a_canonical)]
  rw [ZMod.val_cast_of_lt (b_canonical)]
  exact add_val_eq a b
```

**Justificacion**:
1. Evita trabajar con ZMod directamente
2. Reduce el problema a aritmetica de Nat
3. Patron recomendado por /lean-search y /ask-lean

**Fuente**: Teoremas ZMod.val_add, ZMod.val_mul de Mathlib

### DD-025: Sub-plan para reduce128_correct

**Contexto**: `reduce128` implementa reduccion modular usando la identidad de Goldilocks: `2^64 ≡ 2^32 - 1 (mod p)`.

**Feedback QA**: "reduce128_correct es el cuello de botella. Requiere sub-lemas intermedios."

**Decision**: Descomponer en 3 lemas:
1. `goldilocks_modulus_property`: `2^64 % p = EPSILON + 1`
2. `decomposition_128`: Descomposicion de producto 128-bit
3. `reduce128_step`: Paso principal de reduccion

**Estructura**:
```lean
theorem goldilocks_modulus_property :
    (2^64 : Nat) % ORDER.toNat = EPSILON.toNat + 1 := by native_decide

theorem reduce128_step (lo hi : UInt64) :
    (lo.toNat + hi.toNat * 2^64) % ORDER.toNat =
    (lo.toNat + hi.toNat * (EPSILON.toNat + 1)) % ORDER.toNat := by
  rw [Nat.add_mul_mod_self_right]

theorem reduce128_correct (lo hi : UInt64) :
    (reduce128 lo hi).toNat = (lo.toNat + hi.toNat * 2^64) % ORDER.toNat := by
  simp [reduce128]
  -- Aplicar reduce128_step
  ...
```

**Justificacion**: Divide complejidad, permite pruebas incrementales.

### DD-026: Orden de Ataque Topologico

**Decision**: Seguir orden de dependencias estricto:

```
Nivel 0: uint64_sub_toNat (helper)
         |
Nivel 1: add_canonical, neg_canonical
         |
Nivel 2: add_val_eq, neg_val_eq
         |
Nivel 3: toZMod_add, toZMod_neg
         |
Nivel 4: reduce128 sub-lemas
         |
Nivel 5: mul_canonical, mul_val_eq
         |
Nivel 6: toZMod_mul, toZMod_sub, etc.
         |
Nivel 7: CommRing via transferencia
         |
Nivel 8: toZMod_inv
         |
Nivel 9: Field via transferencia
```

**Justificacion**: Evita trabajo perdido por dependencias no resueltas.

---

## Lecciones Aprendidas de Consultas

### L-015: ZMod.val_injective es la Clave

**Fuente**: /lean-search

**Problema**: ZMod usa `Nat.rec` internamente, causando:
- `ring` timeout (5+ minutos)
- `norm_cast` maximum recursion depth
- Simplificacion incompleta

**Solucion**: No trabajar con ZMod directamente. Usar:
```lean
apply ZMod.val_injective
-- Ahora el goal es sobre Nat, no ZMod
```

**Teoremas clave de Mathlib**:
- `ZMod.val_injective`: inyectividad de `.val`
- `ZMod.val_add`: `(a + b).val = (a.val + b.val) % n`
- `ZMod.val_mul`: `(a * b).val = (a.val * b.val) % n`
- `ZMod.val_cast_of_lt h`: si `x < n`, entonces `(x : ZMod n).val = x`

### L-016: Patron add_val_eq (Ecuacion a Nivel Nat)

**Fuente**: /ask-lean (DeepSeek)

**Insight**: Separar la prueba en dos niveles:
1. **Nivel Nat**: `(a + b).value.toNat = (a.value.toNat + b.value.toNat) % ORDER.toNat`
2. **Nivel ZMod**: Usar el resultado anterior + `ZMod.val_cast_of_lt`

**Ventaja**: El nivel Nat es pura aritmetica (omega, split_ifs), sin complejidad de ZMod.

```lean
-- Nivel Nat
theorem add_val_eq (a b : GoldilocksField) :
    (a + b).value.toNat = (a.value.toNat + b.value.toNat) % ORDER.toNat := by
  simp only [HAdd.hAdd, Add.add, add]
  split_ifs with h <;> omega

-- Nivel ZMod (usa add_val_eq)
theorem toZMod_add (a b : GoldilocksField) :
    toZMod (a + b) = toZMod a + toZMod b := by
  apply ZMod.val_injective
  rw [ZMod.val_add, ZMod.val_cast_of_lt, ZMod.val_cast_of_lt, ZMod.val_cast_of_lt]
  exact add_val_eq a b
```

### L-017: Canonicidad Explicita vs Implicita

**Fuente**: /collab-qa (Gemini QA)

**Problema**: Un axioma `goldilocks_canonical` que afirma canonicidad global es:
1. Dificil de auditar (¿realmente todas las operaciones preservan canonicidad?)
2. Potencialmente falso si alguna operacion tiene bug

**Solucion**: Probar canonicidad para cada operacion:
```lean
theorem add_canonical (a b : GoldilocksField) :
    (a + b).value.toNat < ORDER.toNat := by ...

theorem neg_canonical (a : GoldilocksField) :
    (-a).value.toNat < ORDER.toNat := by ...

theorem mul_canonical (a b : GoldilocksField) :
    (a * b).value.toNat < ORDER.toNat := by ...
```

**Beneficio**: Cada lema de canonicidad es una mini-verificacion de la implementacion.

### L-018: Descomposicion de reduce128

**Fuente**: /collab-qa (Gemini QA)

**Problema**: `reduce128` es complejo porque:
- Usa la identidad de Goldilocks (2^64 ≡ 2^32 - 1)
- Tiene multiples pasos de reduccion
- Mezcla aritmetica de 64 y 128 bits

**Solucion**: Descomponer en lemas atomicos:
1. **Propiedad del modulo**: `2^64 % p = epsilon + 1`
2. **Descomposicion**: `lo + hi * 2^64 = ...`
3. **Paso de reduccion**: un paso de la cadena

**Estructura sugerida**:
```lean
-- 1. Base: la identidad de Goldilocks
theorem goldilocks_modulus_property :
    (2^64 : Nat) % ORDER.toNat = EPSILON.toNat + 1 := by native_decide

-- 2. Un paso de reduccion
theorem reduce128_step (lo hi : UInt64) :
    (lo.toNat + hi.toNat * 2^64) % ORDER.toNat =
    (lo.toNat + hi.toNat * (EPSILON.toNat + 1)) % ORDER.toNat := by
  conv_lhs => rw [show (2^64 : Nat) = ORDER.toNat + EPSILON.toNat + 1 by native_decide]
  rw [Nat.add_mul_mod_self_left]

-- 3. Teorema completo
theorem reduce128_correct : ...
```

### L-019: Transferencia de Instancias via Inyectividad

**Fuente**: /lean-search + /ask-lean

**Insight**: Mathlib tiene `Function.Injective.commRing` y `Function.Injective.field`:
```lean
def Function.Injective.commRing {α : Type*} [CommRing β] (f : α → β)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) ... : CommRing α
```

**Aplicacion**: Una vez probados `toZMod_zero`, `toZMod_one`, `toZMod_add`, `toZMod_mul`, `toZMod_neg`:
```lean
instance : CommRing GoldilocksField :=
  toZMod_injective.commRing toZMod
    toZMod_zero toZMod_one toZMod_add toZMod_mul toZMod_neg ...
```

**Beneficio**: CommRing y Field se obtienen "gratis" una vez probados los homomorfismos.

---

## Inventario de Sorries (22)

### Por Subfase

| Subfase | Sorries | Dependencia Critica |
|---------|---------|---------------------|
| F1.S1: Helpers | 1 | - |
| F1.S1: Canonicidad | 3 | reduce128 para mul |
| F1.S2: val_eq | 4 | Canonicidad |
| F1.S3: toZMod_* | 8 | val_eq |
| F1.S4: CommRing | 8 | toZMod_* |
| F1.S5: Field | 5 | CommRing + toZMod_inv |

### Lista Detallada

```
Helper:
  [ ] uint64_sub_toNat

Canonicidad:
  [ ] add_canonical
  [ ] neg_canonical
  [ ] mul_canonical (requiere reduce128_correct)

val_eq:
  [ ] add_val_eq
  [ ] neg_val_eq
  [ ] mul_val_eq
  [ ] sub_val_eq

toZMod_*:
  [ ] toZMod_add
  [ ] toZMod_neg
  [ ] toZMod_mul
  [ ] toZMod_sub
  [ ] toZMod_ofNat
  [ ] toZMod_pow
  [ ] toZMod_inv

CommRing:
  [ ] neg_add_cancel
  [ ] nsmul_succ
  [ ] zsmul_succ'
  [ ] zsmul_neg'
  [ ] sub_eq_add_neg
  [ ] natCast_succ
  [ ] intCast_negSucc
  [ ] npow_succ

Field:
  [ ] mul_inv_cancel
  [ ] zpow_succ'
  [ ] zpow_neg'
  [ ] nnqsmul_def
  [ ] qsmul_def
```

---

## Riesgos Identificados

| Riesgo | Probabilidad | Impacto | Mitigacion |
|--------|--------------|---------|------------|
| reduce128_correct muy complejo | Media | Alto | Sub-lemas + axioma temporal si necesario |
| Timeouts en lake build | Media | Bajo | Imports selectivos de Mathlib |
| Canonicidad falla para alguna op | Baja | Alto | Tests computacionales ya pasan |
| ZMod.val_* no disponibles | Muy Baja | Medio | Ya verificados en /lean-search |

---

## Proximos Pasos

1. **Implementar F1.S1**: Helpers y canonicidad (add, neg)
2. **Implementar F1.S2.C1-C2**: add_val_eq, neg_val_eq
3. **Implementar F1.S3.C1-C2**: toZMod_add, toZMod_neg
4. **CHECKPOINT**: 7 sorries cerrados
5. **Atacar reduce128**: Sub-lemas + reduce128_correct
6. **Completar resto**: mul_canonical → mul_val_eq → toZMod_mul → CommRing → Field

---

## Referencias

- **Paper**: "Formally Verified Number-Theoretic Transform" (Trieu et al., 2025)
- **Mathlib**: `Data.ZMod.Basic`, `Algebra.Ring.Equiv`
- **Sesiones anteriores**: SORRY_ELIMINATION_SESSION_1-6.md
- **Lecciones**: LECCIONES_QA.md secciones 9, 15-19

---

*Documentado antes de implementacion para trazabilidad completa.*
