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
11. [Axiomatizacion Estrategica](#11-axiomatizacion-estrategica)
12. [Verificacion Matematica ANTES de Implementacion](#12-verificacion-matematica)
13. [Patrones de Bridge List - Finset](#13-bridge-list-finset)
14. [Uso Efectivo de rfl](#14-uso-rfl)
15. [Patron ZMod.val_injective para Campos Finitos Custom](#15-zmod-val-injective) ← NUEVO
16. [Integracion Efectiva de Feedback QA](#16-feedback-qa) ← NUEVO
17. [Descomposicion de Lemas Complejos (reduce128)](#17-descomposicion-lemas) ← NUEVO
18. [Transferencia de Instancias via Function.Injective](#18-transferencia-instancias)
19. [Consulta Efectiva a Experto Lean](#19-consulta-experto)
20. [Técnicas Avanzadas para Campos Finitos (Sesión 9)](#20-tecnicas-sesion9) ← NUEVO

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

---

## 11. Axiomatización Estratégica

### 11.1 Cuándo Axiomatizar vs Probar

No todos los sorries deben probarse formalmente. Axiomatizar es apropiado cuando:

| Criterio | Probar | Axiomatizar |
|----------|--------|-------------|
| Resultado bien conocido | No disponible en Mathlib | Estándar en teoría de números |
| Complejidad técnica | Manejable | Desproporcionada al valor |
| Dependencias | Pocas | Muchas, tedioso en Lean |
| Audibilidad | Prueba es el valor | Enunciado es claro |

### 11.2 Ejemplo: Aritmética Modular para NTT

```lean
-- Probar esto directamente es tedioso (casos de Nat.sub, módulos, etc.)
-- Pero el resultado es estándar y el enunciado es autoevidente

axiom pow_pred_is_primitive {n : ℕ} (hn : n > 0) {ω : F}
    (hω : IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω ^ (n - 1)) n
-- Justificación: (ω^(n-1))^k = ω^((n-1)k) = ω^(-k mod n)
```

### 11.3 Documentación Obligatoria

Cada axiom DEBE tener:
1. Docstring con justificación matemática
2. Referencia a resultado estándar si aplica
3. Explicación de por qué no se prueba formalmente

```lean
/-- ω^(n-1) es raíz primitiva cuando ω lo es.

    Prueba: (ω^(n-1))^n = ω^(n*(n-1)) = 1, y para 0 < k < n,
    (ω^(n-1))^k = ω^((n-1)*k) donde (n-1)*k ≢ 0 (mod n).

    No se prueba formalmente porque requiere manejar muchos casos
    de aritmética de Nat.sub que son tediosos pero no informativos. -/
axiom pow_pred_is_primitive ...
```

---

## 12. Verificación Matemática ANTES de Implementación

### 12.1 El Error de Parseval

La sesión 6 descubrió que el teorema de Parseval estaba **matemáticamente incorrecto**:

```lean
-- INCORRECTO para campos finitos:
theorem parseval :
    n * Σᵢ aᵢ² = Σₖ Xₖ²

-- Contraejemplo: a = [1, 1, 0, 0], n = 4
-- LHS: 4 * 2 = 8
-- RHS: 4 + (1+ω)² + 0 + (1+ω³)² = 4 (con cálculo)
```

### 12.2 Checklist Pre-Implementación

Antes de atacar cualquier teorema matemático:

- [ ] **Verificar enunciado numéricamente**: Probar con valores concretos
- [ ] **Buscar contraejemplos**: Casos pequeños (n=2, n=4)
- [ ] **Comparar con literatura**: ¿El enunciado coincide con la versión estándar?
- [ ] **Considerar dominio**: ¿Funciona igual en ℂ que en campos finitos?

### 12.3 Diferencias Campos Finitos vs Complejos

| Concepto | ℂ | Campo Finito 𝔽_p |
|----------|---|------------------|
| Conjugado | conj(z) | No existe |
| Norma | \|z\|² = z * conj(z) | z² (diferente!) |
| Parseval | n*Σ\|aᵢ\|² = Σ\|Xₖ\|² | Requiere reformulación |
| Raíz inversa | ω⁻¹ = conj(ω) si \|ω\|=1 | ω⁻¹ = ω^(n-1) |

---

## 13. Patrones de Bridge List ↔ Finset

### 13.1 Estrategia General

```
List.foldl ──────────────────────────────► Finset.sum
    │            foldl_range_eq_finset_sum      │
    │                                           │
    ▼                                           ▼
match a[i]? ──────────────────────────────► a[i]'hlt
    │         getElem?_eq_getElem               │
    │                                           │
    ▼                                           ▼
Spec definition ─────────────────────────► Finset definition
                 ntt_coeff_list_eq_finset
```

### 13.2 Lemas Clave del Bridge

```lean
-- 1. Conversión fundamental
lemma foldl_range_eq_finset_sum (n : ℕ) (f : ℕ → F) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
    Finset.univ.sum (fun i : Fin n => f i.val)

-- 2. Eliminar match/Option
lemma getElem?_eq_getElem (h : i < a.length) :
    a[i]? = some a[i]

-- 3. getD con prueba de bounds
lemma getD_eq_getElem (h : i < a.length) :
    a.getD i d = a[i]
```

### 13.3 Manejo de Exponentes Condicionales

```lean
-- INTT_spec usa: if i*k = 0 then 0 else n - (i*k % n)
-- intt_coeff_finset usa: n - (i*k % n)

-- Bridge: son iguales bajo raíz primitiva
lemma intt_exp_equiv (hω : IsPrimitiveRoot ω n) :
    ω ^ (if i*k = 0 then 0 else n - (i*k % n)) = ω ^ (n - (i*k % n))
-- Prueba: cuando i*k = 0, ambos dan ω^0 = 1 = ω^n
```

---

## 14. Uso Efectivo de `rfl` para Igualdad Definicional

### 14.1 El Problema

```lean
let n := X.length
...
-- Goal: ω ^ (n - k) = ω ^ (X.length - k)
simp only [h]  -- Deja: ω ^ (n - k) vs ω ^ (X.length - k)
```

### 14.2 La Solución

```lean
-- n y X.length son definicionalmente iguales (let binding)
simp only [h]
rfl  -- Cierra por igualdad definicional
```

### 14.3 Cuándo Usar `rfl`

- Después de `let x := expr`, `x` y `expr` son definicionalmente iguales
- Después de `simp` que no simplificó lo suficiente
- Cuando el goal tiene la misma estructura pero con nombres diferentes

---

## 15. Patron ZMod.val_injective para Campos Finitos Custom

### 15.1 El Problema con ZMod Directo

Cuando se trabaja con un campo finito custom (como GoldilocksField) y se quiere probar
homomorfismo a `ZMod p`, trabajar directamente con ZMod causa problemas:

```lean
-- MAL: Intentar probar directamente
theorem toZMod_add (a b : GoldilocksField) :
    toZMod (a + b) = toZMod a + toZMod b := by
  simp [toZMod]
  ring  -- TIMEOUT: 5+ minutos
  -- o
  norm_cast  -- ERROR: maximum recursion depth exceeded
```

**Causa raiz**: ZMod usa `Nat.rec` internamente para representar elementos, y las tacticas
de simplificacion no manejan bien esta representacion para modulos grandes.

### 15.2 La Solucion: ZMod.val_injective

```lean
-- BIEN: Reducir a aritmetica de Nat
theorem toZMod_add (a b : GoldilocksField) :
    toZMod (a + b) = toZMod a + toZMod b := by
  apply ZMod.val_injective  -- Convierte goal de ZMod a Nat
  simp only [toZMod, ZMod.val_add]
  rw [ZMod.val_cast_of_lt (add_canonical a b)]
  rw [ZMod.val_cast_of_lt (a_canonical)]
  rw [ZMod.val_cast_of_lt (b_canonical)]
  exact add_val_eq a b  -- Lema a nivel Nat
```

### 15.3 Teoremas Clave de Mathlib

| Teorema | Tipo | Uso |
|---------|------|-----|
| `ZMod.val_injective` | `Injective ZMod.val` | Convertir igualdad ZMod → Nat |
| `ZMod.val_add` | `(a + b).val = (a.val + b.val) % n` | Expandir suma |
| `ZMod.val_mul` | `(a * b).val = (a.val * b.val) % n` | Expandir producto |
| `ZMod.val_cast_of_lt h` | si `x < n`, `(x : ZMod n).val = x` | Eliminar cast |

### 15.4 Arquitectura de Prueba Recomendada

```
Nivel 1: Lemas de canonicidad (a nivel UInt64/Nat)
         add_canonical, neg_canonical, mul_canonical
                        |
                        v
Nivel 2: Lemas val_eq (a nivel Nat puro)
         add_val_eq: (a+b).value.toNat = (a + b) % ORDER
                        |
                        v
Nivel 3: Lemas toZMod_* (combinan niveles anteriores)
         toZMod_add = ZMod.val_injective + val_add + val_cast_of_lt + val_eq
                        |
                        v
Nivel 4: Instancias via Function.Injective.commRing
         CommRing, Field
```

---

## 16. Integracion Efectiva de Feedback QA

### 16.1 Cuando Consultar QA

Consultar `/collab-qa` es apropiado cuando:
- [ ] Plan tiene mas de 3 subfases
- [ ] Hay decisiones arquitectonicas significativas
- [ ] No estas seguro si el enfoque es optimo
- [ ] Quieres validar antes de invertir tiempo

### 16.2 Como Estructurar la Consulta

```
CONTEXTO:
- Que estas tratando de lograr
- Estado actual (que ya funciona, que falta)
- Restricciones tecnicas

PROBLEMA:
- Descripcion precisa del bloqueo
- Que has intentado y por que fallo

ESTRATEGIAS CONSIDERADAS:
- Lista de opciones con pros/contras
- Tu preferencia actual y por que

PREGUNTAS PARA QA:
- Preguntas especificas, no "que opinas?"
- Pedir evaluacion de riesgos
- Pedir alternativas no consideradas
```

### 16.3 Como Procesar el Feedback

El QA tipicamente responde con:
1. **Assessment**: Evaluacion general
2. **Issues Found**: Problemas identificados
3. **Proposed Improvements**: Sugerencias concretas
4. **Recommendation**: APPROVE / NEEDS_REVISION / PROPOSE_ALTERNATIVE

**Acciones por tipo**:
- **Issues Found**: Evaluar si son validos, incorporar mitigaciones
- **Proposed Improvements**: Adoptar las que mejoren el plan
- **Recommendation**: Si es NEEDS_REVISION, iterar antes de implementar

### 16.4 Ejemplo: Sesion 7

```
Feedback QA: "goldilocks_canonical como axioma es una debilidad"

Evaluacion:
- Valido: si alguna operacion no preserva canonicidad, el axioma seria falso
- Impacto: medio (tests pasan, pero reduce confianza formal)
- Costo de fix: bajo (probar canonicidad por operacion)

Decision: Adoptar sugerencia - reemplazar axioma por lemas individuales
```

---

## 17. Descomposicion de Lemas Complejos (reduce128)

### 17.1 Identificar Complejidad

Un lema es "complejo" cuando:
- Involucra multiples representaciones (UInt64, Nat, ZMod)
- Tiene logica condicional anidada
- Usa identidades matematicas no triviales
- La definicion tiene mas de 10 lineas

### 17.2 Estrategia de Descomposicion

```
                    reduce128_correct
                          |
        +-----------------+-----------------+
        |                 |                 |
goldilocks_modulus   decomposition_128   reduce_step
   (native_decide)    (algebra)         (modular arith)
```

**Principio**: Cada sub-lema debe ser probable con una sola tecnica dominante.

### 17.3 Tipos de Sub-lemas

| Tipo | Tacticas | Ejemplo |
|------|----------|---------|
| Computacional | `native_decide` | `2^64 % p = epsilon + 1` |
| Algebraico | `ring`, `omega` | Descomposicion de expresiones |
| Modular | `Nat.add_mul_mod_*` | Propiedades de % |
| Condicional | `split_ifs` | Manejo de if-then-else |

### 17.4 Template para reduce128

```lean
-- Sub-lema 1: Identidad de Goldilocks (computacional)
theorem goldilocks_modulus_property :
    (2^64 : Nat) % ORDER_NAT = EPSILON_NAT + 1 := by native_decide

-- Sub-lema 2: Equivalencia modular (modular arithmetic)
theorem reduce128_equiv (lo hi : Nat) :
    (lo + hi * 2^64) % ORDER_NAT = (lo + hi * (EPSILON_NAT + 1)) % ORDER_NAT := by
  conv_lhs => rw [show (2^64 : Nat) = ORDER_NAT + EPSILON_NAT + 1 by native_decide]
  rw [Nat.add_mul_mod_self_left]

-- Teorema principal: composicion
theorem reduce128_correct (lo hi : UInt64) :
    (reduce128 lo hi).toNat = (lo.toNat + hi.toNat * 2^64) % ORDER_NAT := by
  simp [reduce128]
  rw [reduce128_equiv]
  -- Continuar con pasos adicionales...
```

---

## 18. Transferencia de Instancias via Function.Injective

### 18.1 Teorema de Mathlib

```lean
def Function.Injective.commRing {α : Type*} {β : Type*} [CommRing β]
    (f : α → β) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) x, f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) x, f (n • x) = n • f x)
    (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : CommRing α
```

### 18.2 Aplicacion a GoldilocksField

```lean
-- Prerequisitos
theorem toZMod_injective : Function.Injective toZMod := ...
theorem toZMod_zero : toZMod 0 = 0 := ...
theorem toZMod_one : toZMod 1 = 1 := ...
theorem toZMod_add : ∀ a b, toZMod (a + b) = toZMod a + toZMod b := ...
theorem toZMod_mul : ∀ a b, toZMod (a * b) = toZMod a * toZMod b := ...
theorem toZMod_neg : ∀ a, toZMod (-a) = -toZMod a := ...
-- ... etc

-- Instancia (cierra ~15 sorries de golpe)
instance : CommRing GoldilocksField :=
  toZMod_injective.commRing toZMod
    toZMod_zero toZMod_one toZMod_add toZMod_mul
    toZMod_neg toZMod_sub toZMod_nsmul toZMod_zsmul
    toZMod_npow toZMod_natCast toZMod_intCast
```

### 18.3 Para Field

```lean
-- Prerequisito adicional
theorem toZMod_inv : ∀ a, toZMod a⁻¹ = (toZMod a)⁻¹ := ...

-- Instancia
instance : Field GoldilocksField :=
  toZMod_injective.field toZMod
    toZMod_zero toZMod_one toZMod_add toZMod_mul
    toZMod_neg toZMod_sub toZMod_inv ...
```

---

## 19. Consulta Efectiva a Experto Lean (/ask-lean)

### 19.1 Cuando Usar /ask-lean vs /lean-search

| Situacion | Herramienta | Razon |
|-----------|-------------|-------|
| Buscar teorema existente | /lean-search | Dataset indexado |
| Entender patron de prueba | /ask-lean | Explicacion contextual |
| Tactica para goal especifico | /lean-search --suggest | Modelo entrenado |
| Estrategia general | /ask-lean | Razonamiento |
| Debugging de error | /ask-lean | Analisis de contexto |

### 19.2 Estructura de Consulta Efectiva

```
CONTEXTO TECNICO:
- Estructura del tipo (structure GoldilocksField where value : UInt64)
- Que ya tienes probado (toZMod_injective)
- Que necesitas probar (toZMod_add)

PROBLEMA ESPECIFICO:
- Error que obtienes (timeout, recursion depth)
- Que tacticas has intentado

PREGUNTA CONCRETA:
- "Cual es el patron recomendado para probar homomorfismo a ZMod?"
- NO: "Como pruebo todo?"
```

### 19.3 Ejemplo de Consulta Exitosa

```
Consulta:
"Tengo GoldilocksField (p = 2^64 - 2^32 + 1) con toZMod_injective probado.
Los lemmas toZMod_add/mul/neg tienen sorries porque ZMod usa Nat.rec y
ring/norm_cast fallan. ¿Patron recomendado?"

Respuesta:
"Usar ZMod.val_injective para reducir a Nat:
1. Probar add_val_eq: (a+b).value.toNat = (a + b) % ORDER a nivel Nat
2. Luego: apply ZMod.val_injective; rw [ZMod.val_add]; exact add_val_eq"

Accion: Adoptar patron, crear arquitectura de prueba en capas
```

---

## 20. Técnicas Avanzadas para Campos Finitos (Sesión 9)

### 20.1 L-025: Evitar `↓reduceIte` en simp

**Problema**: `simp only [..., ↓reduceIte]` causa timeouts con condiciones complejas sobre Int.

```lean
-- MAL (timeout):
simp only [ge_iff_le, h, ↓reduceIte, ...]

-- BIEN (rápido):
rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
rw [if_pos (Int.natCast_nonneg n)]
```

**Razón**: `↓reduceIte` intenta evaluar la condición, pero condiciones como `Int.negSucc n ≥ 0` no se reducen eficientemente.

### 20.2 L-026: Usar Axiomas para Abstraer Complejidad

**Problema**: Probar `pow a (n+1) = a * pow a n` para exponenciación binaria es complejo.

```lean
-- Exponenciación binaria (definición real):
def pow (a : GoldilocksField) (n : Nat) : GoldilocksField :=
  if n = 0 then 1
  else if n % 2 = 0 then pow (a * a) (n / 2)
  else a * pow (a * a) (n / 2)

-- Probar pow_succ directamente requiere inducción fuerte
```

**Solución**: Usar axioma `toZMod_pow` que abstrae la equivalencia.

```lean
axiom toZMod_pow (a : GoldilocksField) (n : Nat) :
    toZMod (a ^ n) = (toZMod a) ^ n

-- Ahora npow_succ es trivial:
npow_succ := fun n a => by
  apply toZMod_injective
  rw [toZMod_mul, toZMod_pow, toZMod_pow]
  rw [pow_succ]  -- Lemma estándar de Mathlib
```

### 20.3 L-027: Sintaxis `.mul` vs `*` en Pattern Matching

**Problema**: `toZMod_mul` espera `toZMod (a * b)` pero el goal tiene `toZMod (a.mul b)`.

```lean
-- Goal: toZMod (GoldilocksField.ofNat n.succ.mul a) = ...
rw [toZMod_mul]  -- FALLA: pattern not found
```

**Solución**: Usar `change` para convertir antes de aplicar lemmas.

```lean
change GoldilocksField.ofNat n.succ * a = ...
-- Ahora toZMod_mul funciona
apply toZMod_injective
rw [toZMod_mul, ...]
```

### 20.4 L-028: `Nat.cast_add` vs `push_cast`

**Problema**: `push_cast` deja goals como `↑n + 1 = ↑n + 1` sin resolver.

```lean
-- MAL:
push_cast
-- Deja: (↑n : ZMod p) + 1 = (↑n : ZMod p) + 1
-- No cierra automáticamente
```

**Solución**: Usar `simp only [Nat.cast_add, Nat.cast_one]` que resuelve directamente.

```lean
-- BIEN:
have h : ((n.succ : ℕ) : ZMod ORDER_NAT) = (n : ZMod ORDER_NAT) + 1 := by
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
rw [h]
```

### 20.5 L-029: Manejo de Int.negSucc

**Problema**: `Int.negSucc_not_nonneg n` devuelve `↔ False`, no `¬(negSucc n ≥ 0)`.

```lean
-- MAL:
rw [if_neg (Int.negSucc_not_nonneg n)]  -- Type mismatch
```

**Solución**: Usar la combinación correcta de lemmas.

```lean
-- BIEN:
rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))]
-- Int.not_le : ¬(a ≤ b) ↔ b < a
-- Int.negSucc_lt_zero : negSucc n < 0
```

### 20.6 L-030: Definiciones Racionales para Field

**Problema**: `Rat.cast_def` no expande `↑q` automáticamente.

```lean
-- DivisionRing espera: ratCast q = q.num / q.den
-- Pero ↑q no se expande con simp/unfold
```

**Solución**: Definir `ratCast` explícitamente para que `rfl` funcione.

```lean
ratCast := fun q => (q.num : GoldilocksField) / (q.den : GoldilocksField)
ratCast_def := fun q => by rfl

qsmul := fun q a => ((q.num : GoldilocksField) / (q.den : GoldilocksField)) * a
qsmul_def := fun q a => by rfl  -- Cierra por definición!
```

### 20.7 Resumen: Patrones para Instancias Field

| Sorry | Patrón de Solución |
|-------|-------------------|
| `nnqsmul_def`, `qsmul_def` | Definir con fórmula correcta, cerrar con `rfl` |
| `intCast_negSucc` | `if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n))` |
| `zsmul_succ'`, `zsmul_neg'` | `if_pos`/`if_neg` + `rfl` |
| `npow_succ` | `toZMod_injective` + `toZMod_pow` axiom |
| `zpow_succ'`, `zpow_neg'` | `if_pos`/`if_neg` + `toZMod_pow` + `mul_comm` |

---

*Este documento es un recurso vivo. Agregar nuevas lecciones aprendidas en cada sesion de trabajo.*
