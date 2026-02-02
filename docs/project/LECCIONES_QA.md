# Lecciones del QA para Verificacion Formal en Lean 4

**Proyecto**: AMO-Lean NTT - Eliminacion de Sorries
**Periodo**: Enero-Febrero 2026
**Proposito**: Documentar estrategias e ideas valiosas proporcionadas por el QA para ser incorporadas como skills permanentes.

---

## Indice de Lecciones

1. [Estrategia General de Eliminacion de Sorries](#1-estrategia-general)
2. [Manejo de Recursion y Terminacion](#2-recursion-y-terminacion)
3. [Patrones de Induccion para NTT](#3-patrones-de-induccion)
4. [Bridge Lemmas y Capas de Abstraccion](#4-bridge-lemmas)
5. [Manejo de Instance Diamonds](#5-instance-diamonds)
6. [Tecnicas Especificas de Lean 4](#6-tecnicas-lean4)
7. [Anti-patrones a Evitar](#7-anti-patrones)
8. [Cuerpos Finitos y Caracteristica](#8-cuerpos-finitos) ← CRITICO
9. [Estrategia del Homomorfismo (Goldilocks)](#9-homomorfismo)
10. [Tacticas para Expresiones Grandes (Radix-4)](#10-radix4)

---

## 1. Estrategia General de Eliminacion de Sorries

### 1.1 Mapear Dependencias Primero

Antes de atacar cualquier sorry, construir un grafo de dependencias:

```
S4 (ofStrict_bound) ─────────────────────────┐
S3 (lazy_sub_simulates) ─────────────────────┼──> S5, S6 ──> S7
S1, S2 (ntt_coeff_add/scale) ────────────────┘

S8 (cooley_tukey_upper) ──┬──> S10 (ct_recursive_eq_spec)
S9 (cooley_tukey_lower) ──┘          │
                                     v
                          S11, S12, S13 (identidades)
```

**Leccion**: Resolver sorries en orden topologico. Intentar S10 sin tener S8/S9 es perder tiempo.

### 1.2 Clasificar por Dificultad REAL

La dificultad estimada al inicio casi siempre esta mal. Re-evaluar despues de:
- Leer el codigo involucrado
- Identificar lemas de Mathlib disponibles
- Considerar type class constraints

| Clasificacion | Criterio |
|---------------|----------|
| BAJA | Solo requiere simp/ring/omega |
| MEDIA | Requiere induccion simple o case split |
| ALTA | Requiere induccion estructural + lemas auxiliares |
| MUY ALTA | Requiere cambio de estrategia o lemas no disponibles |

### 1.3 Regla de los 30 Minutos

Si un sorry no avanza en 30 minutos:
1. Parar y documentar donde estas bloqueado
2. Buscar un lema auxiliar que simplifique el problema
3. Considerar si la formulacion del teorema es correcta
4. Consultar QA para estrategia alternativa

---

## 2. Recursion y Terminacion

### 2.1 Verificar Terminacion ANTES de Probar Correccion

```lean
-- PRIMERO: Verificar que esto compila
def NTT_recursive (ω : F) (a : List F) : List F :=
  ...
termination_by a.length
decreasing_by
  all_goals
    simp only [evens, odds, List.length_cons]
    omega

-- DESPUES: Probar propiedades
theorem ct_recursive_eq_spec : NTT_recursive ω input = NTT_spec ω input
```

**Leccion**: Si la funcion no termina en Lean, no puedes probar nada sobre ella.

### 2.2 Usar `termination_by` con Medida Explicita

```lean
termination_by input.length  -- BIEN: medida explicita

termination_by  -- MAL: deja a Lean adivinar (puede fallar)
```

### 2.3 Probar Decrecimiento con omega Cuando Sea Posible

```lean
decreasing_by
  all_goals
    simp only [h_evens_len, h_odds_len, hexp, Nat.pow_succ]
    omega  -- omega es muy poderoso para aritmetica natural
```

---

## 3. Patrones de Induccion para NTT

### 3.1 Induccion sobre Exponente, NO sobre Lista

Para NTT donde `input.length = 2^k`:

```lean
-- BIEN: Induccion sobre exponente
obtain ⟨exp, hexp⟩ := h_pow2
cases exp with
| zero => -- length = 1, caso base
| succ exp' => -- length >= 2, caso inductivo

-- MAL: Match sobre lista
match h : input with
| [] => ...
| [x] => ...
| x :: y :: xs => ...  -- Dificil relacionar con 2^k
```

**Razon**: `evens input` y `odds input` tienen longitud `2^(exp-1)`, lo cual es directo con induccion sobre exp.

### 3.2 Crear Unfolding Lemmas

Antes del teorema principal, crear lemmas que expongan la estructura interna:

```lean
-- Unfolding lemma
theorem NTT_recursive_unfold (ω : F) (a : List F) (ha : a.length >= 2) :
    NTT_recursive ω a =
    let E := NTT_recursive (ω * ω) (evens a)
    let O := NTT_recursive (ω * ω) (odds a)
    upper E O ++ lower E O

-- Ahora el teorema principal puede usar:
rw [NTT_recursive_unfold ω input h_len_ge2]
```

### 3.3 Usar List.ext_getElem? para Igualdad de Listas

```lean
-- Probar igualdad elemento a elemento
apply List.ext_getElem?
intro k
-- Ahora solo necesitas probar que el k-esimo elemento coincide
```

---

## 4. Bridge Lemmas y Capas de Abstraccion

### 4.1 Arquitectura de Capas

Organizar pruebas en capas de abstraccion:

```
CAPA 1: Aritmetica de twiddle factors
        (pow_mul, pow_add, twiddle_half_eq_neg_one)
             |
             v
CAPA 2: Splitting de sumas
        (foldl_split_parity, ntt_term_even_index, etc.)
             |
             v
CAPA 3: Recurrencia Cooley-Tukey
        (cooley_tukey_upper_half, cooley_tukey_lower_half)
             |
             v
CAPA 4: Teorema principal
        (ct_recursive_eq_spec)
```

### 4.2 Construir Bridge Lemmas Primero

Antes de atacar un teorema complejo, identificar y probar los "puentes":

```lean
-- Bridge: conecta ntt_term con evens
theorem ntt_term_even_index (ω : F) (a : List F) (k m : Nat) (hm : m < (evens a).length) :
    ntt_term ω a k (2 * m) = ntt_term (ω * ω) (evens a) k m

-- Bridge: conecta ntt_term con odds
theorem ntt_term_odd_index (ω : F) (a : List F) (k m : Nat) (hm : m < (odds a).length) :
    ntt_term ω a k (2 * m + 1) = ω^k * ntt_term (ω * ω) (odds a) k m
```

### 4.3 Helpers para Notacion inst.* vs *

```lean
-- Cuando la definicion usa inst.mul pero los lemas usan *
@[simp] theorem inst_mul_eq_mul (a b : F) : inst.mul a b = a * b := rfl
@[simp] theorem inst_add_eq_add (a b : F) : inst.add a b = a + b := rfl
@[simp] theorem inst_zero_eq_zero : inst.zero = (0 : F) := rfl
```

---

## 5. Manejo de Instance Diamonds

### 5.1 Problema

Cuando hay multiples type class instances que proveen la misma operacion:

```lean
variable [NTTField F] [CommRing F]
-- Ambos proveen: Mul F, Add F, etc.
```

### 5.2 Sintomas

- `rw [mul_comm]` falla con "pattern not found"
- `simp` no simplifica expresiones que deberian ser triviales
- Errores de unificacion misteriosos

### 5.3 Solucion: Usar Instancia Unica

```lean
-- BIEN: Una sola fuente de verdad
variable [NTTFieldLawful F]  -- NTTFieldLawful extiende NTTField y CommRing

-- MAL: Multiples fuentes
variable [NTTField F] [CommRing F]
```

### 5.4 Solucion Alternativa: calc Blocks con have

Cuando no puedes cambiar las instances:

```lean
calc inst.mul (inst.pow ω k) (inst.mul aᵢ p)
    = ω^k * (aᵢ * p) := by simp only [inst_mul_eq_mul, inst_pow_eq_pow]
  _ = aᵢ * (ω^k * p) := by ring
  _ = inst.mul aᵢ (inst.mul (inst.pow ω k) p) := by simp only [inst_mul_eq_mul, inst_pow_eq_pow]
```

---

## 6. Tecnicas Especificas de Lean 4

### 6.1 omega es Poderoso pero Limitado

```lean
-- omega PUEDE probar:
-- - Aritmetica lineal sobre Nat/Int
-- - Divisibilidad simple
-- - Desigualdades con +, -, *, / por constantes

-- omega NO PUEDE probar:
-- - Nada con exponentes: 2^k >= 4
-- - Multiplicacion de variables: a * b >= c * d
```

**Solucion para exponentes**:
```lean
have h2e : 2^(e+2) >= 4 := by
  have he1 : 2^e >= 1 := Nat.one_le_pow e 2 (by norm_num)
  have : 2^(e+2) = 2^e * 4 := by simp [Nat.pow_succ, Nat.pow_add]; omega
  omega  -- Ahora omega puede usar la igualdad
```

### 6.2 simp only vs simp

```lean
simp only [h1, h2, h3]  -- BIEN: controlado, predecible
simp                     -- MAL: puede simplificar demasiado o muy poco
simp [*]                 -- PELIGROSO: puede hacer cosas inesperadas
```

### 6.3 native_decide para Calculos Finitos

```lean
-- Para hechos que son decidibles computacionalmente
have hr2 : List.range 2 = [0, 1] := by native_decide
example : 3 + 4 = 7 := by native_decide

-- PERO: no funciona con variables libres
-- example (a b : Nat) : a + b = b + a := by native_decide  -- FALLA
```

### 6.4 congr para Entrar en Estructuras

```lean
-- Goal: [f x] = [g x]
congr 1
-- Goal: f x = g x

-- Goal: some (a + b) = some (c + d)
congr 1
-- Goal: a + b = c + d
```

### 6.5 show para Explicitar Tipos

```lean
-- Cuando Lean no unifica tipos automaticamente:
show (0 : F) + a * ((1 : F) ^ 0) = a
ring  -- Ahora ring sabe los tipos
```

---

## 7. Anti-patrones a Evitar

### 7.1 NO: Atacar Teorema Principal sin Lemas Auxiliares

```lean
-- MAL: Intentar probar S10 directamente con 500 lineas de tactica
theorem ct_recursive_eq_spec : ... := by
  induction input with ...  -- 500 lineas, todo mezclado

-- BIEN: Construir capas
theorem unfolding_lemma : ...  -- 20 lineas
theorem upper_half : ...       -- 30 lineas
theorem lower_half : ...       -- 30 lineas
theorem ct_recursive_eq_spec : ... := by
  rw [unfolding_lemma]
  apply List.ext_getElem?
  -- usar upper_half y lower_half
```

### 7.2 NO: Ignorar Errores de Terminacion

```lean
-- MAL: Agregar sorry a decreasing_by
decreasing_by sorry  -- "ya lo arreglare despues"

-- La funcion puede no terminar realmente, y nunca podras probar nada
```

### 7.3 NO: Mezclar Representaciones

```lean
-- MAL: Usar List.foldl en definicion pero Finset.sum en pruebas
-- Requiere lema de conversion que puede ser complejo

-- BIEN: Elegir una representacion y mantenerla
-- O crear bridge lemmas explicitos entre representaciones
```

### 7.4 NO: Olvidar Casos Especiales

```lean
-- MAL: Asumir que n >= 4 cuando el teorema dice n >= 2
theorem lower_half (hn : n > 2) : ...  -- Pero caller tiene n = 2

-- BIEN: Verificar que las precondiciones coinciden
-- O manejar casos especiales explicitamente
cases exp' with
| zero => -- n = 2, caso especial
| succ e => -- n >= 4, usar teorema general
```

---

## Resumen: Checklist Pre-Prueba

Antes de atacar cualquier sorry:

- [ ] Verificar dependencias: Estan probados los sorries de los que depende?
- [ ] Leer el codigo: Que hace exactamente la funcion/teorema?
- [ ] Identificar lemas: Que lemas de Mathlib o propios necesito?
- [ ] Verificar terminacion: Si es recursivo, termina correctamente?
- [ ] Crear unfolding lemmas: Puedo exponer la estructura interna?
- [ ] Construir bridge lemmas: Que puentes necesito entre representaciones?
- [ ] Elegir estrategia de induccion: Sobre que variable/estructura induzco?
- [ ] Manejar casos especiales: Hay casos borde que requieren tratamiento especial?
- [ ] Documentar el plan: Escribir los pasos antes de implementar

---

## Anexo: Comandos Utiles

```lean
-- Ver el goal actual con tipos explicitos
#check @nombre_teorema

-- Ver que simp rules aplican
set_option trace.Meta.Tactic.simp true

-- Ver informacion de instancias
#print instances Mul

-- Encontrar lemas sobre un concepto
#check @List.foldl
```

---

## 8. Cuerpos Finitos y Caracteristica (CRITICO)

### 8.1 La Trampa de la Division por N

Para probar `INTT(NTT(x)) = x`, necesitamos dividir por `n` (el tamaño de la lista).

```lean
-- ⚠️ INCORRECTO: Falta hipotesis
theorem intt_ntt_identity (ω : F) (a : List F)
    (hω : IsPrimitiveRoot ω a.length) :
    INTT ω (NTT ω a) = a

-- ✓ CORRECTO: Hipotesis explicita
theorem intt_ntt_identity (ω : F) (a : List F)
    (hn : (a.length : F) ≠ 0)  -- ← CRITICO
    (hω : IsPrimitiveRoot ω a.length) :
    INTT ω (NTT ω a) = a
```

**Razon**: En un cuerpo finito `𝔽_p`, la division por `n` solo es posible si `n ≢ 0 (mod p)`.

**Contexto Goldilocks**: `p ≈ 2^64`, `n ≤ 2^32`, asi que es seguro, pero Lean necesita la hipotesis.

### 8.2 Lemas de Mathlib para Series Geometricas

```lean
-- Para probar ortogonalidad de raices de unidad:
-- ∑_{m=0}^{N-1} ω^{m(j-k)} = N si j=k, 0 si j≠k

-- Usar:
#check Finset.geom_sum_eq
#check Finset.sum_pow_mul_eq_zero_of_ne

-- La serie geometrica: ∑_{i=0}^{n-1} r^i = (1 - r^n)/(1 - r) para r ≠ 1
-- Si ω es raiz N-esima primitiva y j ≠ k:
-- ω^{(j-k)N} = (ω^N)^{j-k} = 1^{j-k} = 1
-- Entonces numerador = 1 - 1 = 0
```

---

## 9. Estrategia del Homomorfismo (Goldilocks)

### 9.1 El Problema: Sorries en Axiomas Algebraicos

Los sorries en `add_assoc`, `mul_comm`, `distrib`, etc. hacen que:
- `ring` puede fallar silenciosamente
- `simp` puede dejar goals en estado inconsistente
- Las pruebas de alto nivel son fragiles

### 9.2 La Solucion Elegante: Proyeccion a ZMod

En lugar de probar axiomas bit a bit (infierno de UInt64):

```lean
-- 1. Definir proyeccion canonica
def toZMod (x : GoldilocksField) : ZMod p :=
  ⟨x.value.toNat, ...⟩

-- 2. Probar que respeta operaciones
theorem toZMod_add (a b : GoldilocksField) :
    toZMod (a + b) = toZMod a + toZMod b := by
  -- Solo necesita mostrar que la reduccion modular es correcta
  ...

theorem toZMod_mul (a b : GoldilocksField) :
    toZMod (a * b) = toZMod a * toZMod b := by
  ...

-- 3. Los axiomas se HEREDAN automaticamente de ZMod p
-- add_assoc, mul_comm, distrib, etc. son gratis!
```

**Ventaja**: Cierra 25 sorries de golpe con matematicas elegantes.

### 9.3 Verificar Inyectividad

```lean
-- Para que la herencia funcione, necesitamos:
theorem toZMod_injective : Function.Injective toZMod := by
  intro a b hab
  -- a.value mod p = b.value mod p
  -- Como 0 ≤ value < p, esto implica a = b
  ...
```

---

## 10. Tacticas para Expresiones Grandes (Radix-4)

### 10.1 Cuando `ring` se Ahoga

Las expresiones Radix-4 expanden mucho (4 salidas por butterfly). Si `ring` falla:

```lean
-- Opcion 1: linear_combination
-- Mas eficiente para igualdades lineales
linear_combination h1 + 2 * h2 - h3

-- Opcion 2: Dividir en sub-casos
-- Una prueba por cada salida del butterfly
theorem radix4_output_0 : ... := by ...
theorem radix4_output_1 : ... := by ...
theorem radix4_output_2 : ... := by ...
theorem radix4_output_3 : ... := by ...

theorem radix4_correct := by
  constructor
  · exact radix4_output_0
  constructor
  · exact radix4_output_1
  ...
```

### 10.2 Simplificacion Incremental

```lean
-- En lugar de un solo ring gigante:
calc expresion_compleja
    = paso_1 := by ring
  _ = paso_2 := by ring
  _ = resultado := by ring
```

---

## Resumen: Checklist Pre-Prueba (Actualizado)

Antes de atacar cualquier sorry:

- [ ] Verificar dependencias: Estan probados los sorries de los que depende?
- [ ] Leer el codigo: Que hace exactamente la funcion/teorema?
- [ ] Identificar lemas: Que lemas de Mathlib o propios necesito?
- [ ] Verificar terminacion: Si es recursivo, termina correctamente?
- [ ] Crear unfolding lemmas: Puedo exponer la estructura interna?
- [ ] Construir bridge lemmas: Que puentes necesito entre representaciones?
- [ ] Elegir estrategia de induccion: Sobre que variable/estructura induzco?
- [ ] Manejar casos especiales: Hay casos borde que requieren tratamiento especial?
- [ ] **NUEVO: Hipotesis de caracteristica**: Si divido por n, tengo `(n : F) ≠ 0`?
- [ ] **NUEVO: Axiomas base estables**: Los axiomas algebraicos tienen sorry?
- [ ] Documentar el plan: Escribir los pasos antes de implementar

---

## Anexo: Comandos Utiles

```lean
-- Ver el goal actual con tipos explicitos
#check @nombre_teorema

-- Ver que simp rules aplican
set_option trace.Meta.Tactic.simp true

-- Ver informacion de instancias
#print instances Mul

-- Encontrar lemas sobre un concepto
#check @List.foldl

-- Ver si un tipo tiene CommRing
#check (inferInstance : CommRing GoldilocksField)
```

---

*Este documento es un recurso vivo. Agregar nuevas lecciones aprendidas en cada sesion de trabajo.*
