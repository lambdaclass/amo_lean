# Decisiones de Diseño - Verificación NTT Radix-4

## Contexto

Este documento registra las decisiones de diseño tomadas para completar la verificación formal del algoritmo NTT Radix-4 en Lean 4, basadas en el estudio bibliográfico y la revisión QA con Gemini.

---

## 1. Representación del Campo

### Decisión
Usar `ZMod p` donde `p` es primo.

### Justificación
- Mathlib tiene soporte completo para `ZMod p`
- `IsPrimitiveRoot` está bien definido para campos finitos
- Evita complejidad de números complejos

### Precondiciones Formales
```lean
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (N : ℕ) [NeZero N]
variable (hNp : N.Coprime p)  -- Crucial para inversibilidad de N
```

---

## 2. Representación de Raíces de Unidad

### Decisión
Usar la estructura `IsPrimitiveRoot ω N` de Mathlib.

### Justificación
- Proporciona `ω^N = 1` y `ω^k ≠ 1` para `0 < k < N`
- Incluye lema `pow_eq_neg_one` para `ω^(N/2) = -1`
- Bien integrado con teoría de campos finitos

### Lemas Clave de Mathlib
- `IsPrimitiveRoot.pow_eq_one`: `ω^N = 1`
- `IsPrimitiveRoot.pow_ne_one`: `ω^k ≠ 1` para `k < N`
- `IsPrimitiveRoot.pow_eq_neg_one`: `ω^(N/2) = -1` cuando `2 | N`

---

## 3. Especificación vs Implementación

### Decisión
Separar `NTT_spec` (especificación) de `NTT_radix2/radix4` (implementaciones).

### Justificación
- Permite probar corrección de cada implementación por separado
- La equivalencia se prueba por transitividad: `radix2 = spec = radix4`
- Facilita testing con valores concretos

### Estructura
```lean
def NTT_spec (ω : F) (x : Fin N → F) : Fin N → F :=
  fun k => ∑ j : Fin N, x j * ω ^ (k.val * j.val)

def INTT_spec (ω : F) (y : Fin N → F) : Fin N → F :=
  fun k => (N : F)⁻¹ * ∑ j : Fin N, y j * ω ^ (-(k.val * j.val : ℤ))
```

---

## 4. Estrategia de Prueba Cooley-Tukey

### Decisión
Probar upper_half y lower_half separadamente, luego componer.

### Justificación (inspirada en A=B)
- Los términos `ω^(nk)` son hipergeométricos: `ω^(n(k+1))/ω^(nk) = ω^n`
- Esto permite usar estructura de series geométricas
- La separación par/impar es una reindexación natural

### Lemas Auxiliares Necesarios
1. `sum_split_even_odd`: Separar `∑_{k=0}^{2N-1}` en pares + impares
2. `pow_even_index`: `ω^(k*(2j)) = (ω²)^(kj)`
3. `pow_odd_index`: `ω^(k*(2j+1)) = ω^k * (ω²)^(kj)`

---

## 5. Prueba de Ortogonalidad

### Decisión
Probar `roots_of_unity_sum` usando series geométricas.

### Estrategia
```
Si n ≡ 0 (mod N): cada término es 1, suma = N
Si n ≢ 0 (mod N): serie geométrica con razón ω^n ≠ 1
  Σ ω^(nk) = (ω^(nN) - 1) / (ω^n - 1) = (1 - 1) / (ω^n - 1) = 0
```

### Lema Crítico
```lean
lemma omega_pow_sub_one_ne_zero (hω : IsPrimitiveRoot ω N) (hn : ¬ N ∣ n) :
    ω ^ n - 1 ≠ 0
```
Este lema garantiza que el denominador de la serie geométrica no es cero.

---

## 6. Butterfly4 y Matriz T₄

### Decisión
Definir T₄ como matriz explícita 4×4 y verificar propiedades.

### Matriz T₄
```
T₄ = | 1   1   1   1  |
     | 1   ψ  -1  -ψ  |
     | 1  -1   1  -1  |
     | 1  -ψ  -1   ψ  |

donde ψ = ω^(N/4), ψ² = -1
```

### Estrategia de Prueba
- Usar `fin_cases` para verificar cada entrada de la matriz
- La propiedad `ψ² = -1` simplifica drásticamente los cálculos
- Probar `T₄ * T₄⁻¹ = I` entrada por entrada

---

## 7. Terminación de Recursión

### Decisión
Usar `termination_by` con el tamaño del vector.

### Justificación
- En radix-2: `N → N/2` (claramente decrece)
- En radix-4: `N → N/4` (claramente decrece)
- Lean puede verificar automáticamente con `omega`

### Código
```lean
def NTT_radix4 (ω : F) : (n : ℕ) → (Fin n → F) → (Fin n → F)
  | ...
termination_by n => n
decreasing_by all_goals omega
```

---

## 8. Inversibilidad de N en el Campo

### Decisión
Requerir `N.Coprime p` como precondición.

### Justificación
- Para el roundtrip necesitamos dividir por N
- En `ZMod p`, N tiene inverso iff `gcd(N, p) = 1`
- Típicamente `p` es primo grande y `N` es potencia de 2, así que son coprimos

### Formalización
```lean
lemma N_invertible (hNp : N.Coprime p) : IsUnit (N : ZMod p) := by
  rw [ZMod.isUnit_nat_iff]
  exact hNp.symm
```

---

## 9. Orden de Implementación

### Decisión
Implementar en orden topológico de dependencias.

```
Fase 0: Investigar Mathlib
    ↓
Fase 1: Lemas fundamentales
    ↓         ↓
Fase 2     Fase 3
Cooley     Butterfly4
    ↓         ↓
    → Fase 4 ←
      Radix4
        ↓
      Fase 5
    Equivalencia
        ↓
      Fase 6
     Roundtrip
        ↓
      Fase 7
       Tests
```

---

## 10. Conexión con Libro A=B

### Insight Principal
Las sumas NTT son **hipergeométricas**, lo que significa:
- El ratio de términos consecutivos es racional en k
- Esto habilita el arsenal de Zeilberger/WZ

### Aplicaciones Concretas

| Concepto A=B | Uso en NTT |
|--------------|------------|
| Hipergeometricidad | Justifica estructura de serie geométrica |
| WZ-Pairs | Potencial para certificados de identidad |
| Ortogonalidad | Base del roundtrip |
| q-Análogos | Framework natural para F_p |

### Limitación
A=B provee **intuición estructural** pero las pruebas en Lean son directas sobre el campo. No hay automatización de Zeilberger en Mathlib.

---

## Feedback QA Incorporado

| Feedback de Gemini | Acción Tomada |
|-------------------|---------------|
| `omega_ratio` innecesario | Eliminado, usar `ring` directamente |
| Denominador puede ser 0 | Lema `omega_pow_sub_one_ne_zero` explícito |
| INTT no definida | Definición explícita añadida |
| División por N | Precondición `N.Coprime p` |
| Tests unitarios | Fase 7 añadida |
| Casos base | Documentados explícitamente |

---

## Criterios de Éxito

- [ ] 0 `sorry` en todo el proyecto
- [ ] `lake build` exitoso
- [ ] Tests unitarios pasan
- [ ] Documentación completa
