# Evaluacion Bibliografica para Eliminacion de Sorries

**Fecha**: 2026-01-30
**Objetivo**: Determinar si tenemos la bibliografia necesaria para cerrar todos los sorries

---

## 1. Evaluacion del Libro "A=B"

### Utilidad Directa

| Concepto A=B | Aplicacion | Sorries que ayuda | Nivel de utilidad |
|--------------|------------|-------------------|-------------------|
| **Ortogonalidad (§8)** | `Σ ω^((j-i)k) = n·δ(i,j)` | S12 `intt_ntt_identity_finset` | 🟢 ALTA |
| **Series Geometricas** | `(1-ω)·Σω^k = 1-ω^n` | Ya probado en `sum_of_powers_zero` | ✅ YA USADO |
| **Hipergeometricidad** | Justifica que induccion funciona | S10 `ct_recursive_eq_spec` | 🟡 TEORICO |
| **q-Analogos** | Framework para F_p | Conceptual | 🟡 TEORICO |
| **Zeilberger** | Transitividad de equivalencias | Estrategia general | 🟡 TEORICO |

### Conclusion sobre A=B

**A=B es util pero NO suficiente.**

Lo que A=B nos da:
- ✅ Justificacion teorica de que nuestras estrategias son correctas
- ✅ La identidad de ortogonalidad central
- ✅ Intuicion sobre estructura de sumas NTT

Lo que A=B NO nos da:
- ❌ Tacticas de Lean
- ❌ Lemas de Mathlib
- ❌ Implementacion concreta de pruebas

### Ideas de A=B que SI usaremos

1. **Ortogonalidad como prueba directa** (no via WZ-pairs)
   ```
   INTT(NTT(a))_i = n_inv · Σ_k (Σ_j a_j ω^{jk}) · ω^{-ik}
                  = n_inv · Σ_j a_j · Σ_k ω^{(j-i)k}
                  = n_inv · Σ_j a_j · [n si j=i, 0 si no]
                  = a_i
   ```
   Esta derivacion de A=B es exactamente lo que necesitamos para S12.

2. **Series geometricas** - Ya implementado en `geom_sum_finset` (RootsOfUnity.lean:131)

3. **Induccion fuerte** - Sister Celine confirma que es valida para sumas hipergeometricas

---

## 2. Inventario de Mathlib

### Disponible y Necesario

| Lemma | Ubicacion | Para que sorry | Estado |
|-------|-----------|----------------|--------|
| `Finset.sum_comm` | BigOperators/Group/Finset/Basic.lean:465 | S12 (intercambiar sumas) | ✅ Disponible |
| `Finset.sum_filter` | BigOperators/Group/Finset/Basic.lean:485 | S8, S9 (par/impar) | ✅ Disponible |
| `geom_sum_eq` | Algebra/GeomSum.lean:284 | Ya tenemos version propia | ✅ Disponible |
| `Nat.add_mod` | Data/Nat/Defs | S3, S5, S6 (aritmetica modular) | ✅ Disponible |
| `Nat.mul_mod` | Data/Nat/Defs | S3, S5, S6 | ✅ Disponible |
| `List.foldl_map` | Data/List/Basic | S1, S2 | ✅ Disponible |

### Problema de Compatibilidad: IsPrimitiveRoot

**Nuestra definicion** (RootsOfUnity.lean:40):
```lean
structure IsPrimitiveRoot {M : Type*} [Monoid M] (ω : M) (n : ℕ) : Prop where
  pow_eq_one : ω ^ n = 1
  pow_ne_one_of_lt : ∀ k : ℕ, 0 < k → k < n → ω ^ k ≠ 1
```

**Definicion de Mathlib** (RingTheory/RootsOfUnity/PrimitiveRoots.lean:50):
```lean
structure IsPrimitiveRoot (ζ : M) (k : ℕ) : Prop where
  pow_eq_one : ζ ^ k = 1
  dvd_of_pow_eq_one : ∀ l : ℕ, ζ ^ l = 1 → k ∣ l
```

**Son equivalentes?** SI, para n > 0:
- `pow_ne_one_of_lt` ⟺ `dvd_of_pow_eq_one` (contrareciprocas)

**Impacto**: Podemos usar nuestros lemas directamente, pero si necesitamos lemas de Mathlib sobre `IsPrimitiveRoot`, necesitaremos probar la equivalencia.

### Veredicto Mathlib

**Tenemos TODO lo necesario en Mathlib.** Solo necesitamos:
1. Importar `Mathlib.Algebra.BigOperators.Ring` para `Finset.sum_comm`
2. Posiblemente probar equivalencia de `IsPrimitiveRoot` si usamos lemas de Mathlib

---

## 3. Bibliografia Adicional Necesaria

### Para Cooley-Tukey (S8, S9, S10)

| Recurso | Necesidad | Disponibilidad |
|---------|-----------|----------------|
| CLRS Cap. 30 | Estrategia de prueba | 📚 Libro estandar |
| Cooley-Tukey 1965 | Referencia original | 📄 Paper clasico |

**Contenido necesario de CLRS**:
- Seccion 30.2: "The DFT and FFT"
- Teorema 30.7: Correctness of FFT
- La recurrencia: `X_k = E_k + ω^k·O_k`

**Lo tenemos?** La estrategia ya esta documentada en nuestro codigo (Correctness.lean comentarios). Solo necesitamos implementarla.

### Para Lazy Butterfly (S3-S7)

| Recurso | Necesidad | Disponibilidad |
|---------|-----------|----------------|
| Aritmetica modular basica | Lemas de Nat.mod | ✅ En Mathlib |
| Harvey optimization | Contexto | Ya implementado |

**No necesitamos bibliografia adicional** - es aritmetica modular directa.

### Para Radix-4 (A1-A7)

| Recurso | Necesidad | Disponibilidad |
|---------|-----------|----------------|
| Gentleman & Sande 1966 | Radix-4 original | 📄 Paper clasico |
| Algebra matricial 4x4 | Para A5 butterfly4 | Calculo directo |

**Para A5 `butterfly4_orthogonality`**: La matriz T4 es explicita:
```
T4 = | 1   1   1   1  |
     | 1   ψ  -1  -ψ  |
     | 1  -1   1  -1  |
     | 1  -ψ  -1   ψ  |
```
donde ψ = ω^{N/4}, ψ² = -1.

Verificar T4 · T4^{-1} = I es calculo directo (16 entradas).

---

## 4. Plan de Estudio Previo a Implementacion

### Dia 1: Repaso de Herramientas Mathlib (2-3 horas)

1. **Estudiar `Finset.sum_comm`**
   - Leer definicion y ejemplos
   - Probar en Lean con ejemplo simple
   ```lean
   example : ∑ i in Finset.range 3, ∑ j in Finset.range 2, (i + j) =
             ∑ j in Finset.range 2, ∑ i in Finset.range 3, (i + j) := by
     exact Finset.sum_comm
   ```

2. **Estudiar `Finset.sum_filter`**
   - Entender como separar sumas en pares/impares
   ```lean
   example (s : Finset ℕ) (f : ℕ → ℕ) :
     ∑ x in s, f x = (∑ x in s.filter (· % 2 = 0), f x) +
                     (∑ x in s.filter (· % 2 = 1), f x) := by
     rw [← Finset.sum_filter_add_sum_filter_not]
     congr 1
     -- etc.
   ```

3. **Repasar aritmetica modular en Mathlib**
   - `Nat.add_mod`, `Nat.mul_mod`, `Nat.mod_mod_self`

### Dia 2: Repaso de Ortogonalidad (2 horas)

1. **Releer A=B seccion 8** (Ortogonalidad y Chebyshev)
   - Enfocarse en: `Σ_k ω^{(j-i)k} = n·δ_{ij}`

2. **Verificar que tenemos los ingredientes**:
   - ✅ `powSum_nonzero` (RootsOfUnity.lean:184)
   - ✅ `powSum_zero_mod` (RootsOfUnity.lean:177)
   - ❓ Necesitamos version con indices negativos?

3. **Escribir sketch de prueba para S12**

### Dia 3: Repaso de Cooley-Tukey (2 horas)

1. **Releer CLRS 30.2** o nuestros comentarios en Correctness.lean

2. **Verificar lemas auxiliares**:
   - ✅ `evens`, `odds` definidos en CooleyTukey.lean
   - ✅ `twiddle_half_eq_neg_one` (RootsOfUnity.lean:226)
   - ✅ `squared_is_primitive` (RootsOfUnity.lean:268)

3. **Identificar gaps**:
   - ❓ `evens_length`, `odds_length` probados?
   - ❓ Relacion entre `NTT_spec` sobre evens y suma parcial

---

## 5. Resumen: Que Necesitamos Estudiar

### Prioridad ALTA (antes de empezar)

| Tema | Fuente | Tiempo |
|------|--------|--------|
| `Finset.sum_comm` uso practico | Mathlib docs + experimentos | 1 hora |
| `Finset.sum_filter` para par/impar | Mathlib docs | 1 hora |
| Aritmetica modular Nat | Mathlib Data.Nat | 1 hora |

### Prioridad MEDIA (cuando llegemos a esos sorries)

| Tema | Fuente | Tiempo |
|------|--------|--------|
| Ortogonalidad de A=B | A=B seccion 8 | 1 hora |
| Cooley-Tukey splitting | CLRS 30.2 o nuestros docs | 1 hora |

### Prioridad BAJA (solo si necesario)

| Tema | Fuente | Tiempo |
|------|--------|--------|
| Equivalencia IsPrimitiveRoot | Prueba directa | 2 horas |
| Algebra matricial T4 | Calculo directo | 2 horas |

---

## 6. Conclusion

### Tenemos suficiente bibliografia?

**SI**, con las siguientes notas:

1. **A=B** proporciona el marco teorico necesario
2. **Mathlib** proporciona todos los lemas tecnicos
3. **Nuestro codigo existente** ya tiene muchos ingredientes

### Gaps identificados:

1. **Practica con `Finset.sum_comm`** - necesitamos familiarizarnos
2. **Conexion IsPrimitiveRoot** - puede requerir trabajo adicional
3. **Lemas auxiliares de listas** - verificar que existen

### Recomendacion:

**Proceder con Fase 1 (Fundamentos)** inmediatamente.
Los sorries S1-S4 son aritmetica modular pura y no requieren bibliografia adicional.

Mientras tanto, estudiar `Finset.sum_comm` en paralelo para Fase 3+.

---

## Apendice: Imports Actuales vs Necesarios

### Ya importados en Properties.lean:
```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
```

### Posiblemente necesarios:
```lean
import Mathlib.Algebra.BigOperators.Order  -- para sum_comm completo?
import Mathlib.Data.Nat.ModEq              -- para aritmetica modular
```

### Verificar disponibilidad:
```lean
#check @Finset.sum_comm  -- Debe funcionar con imports actuales
```
