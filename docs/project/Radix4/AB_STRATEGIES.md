# Estrategias del Libro A=B Aplicadas a NTT

## Referencia
"A=B" por Marko Petkovšek, Herbert Wilf, y Doron Zeilberger (1996)

---

## 1. Hipergeometricidad

### Definición
Un término `t(k)` es **hipergeométrico** si `t(k+1)/t(k)` es una función racional en `k`.

### Aplicación a NTT
Los términos de la NTT son `x[j] * ω^(kj)`. El factor `ω^(kj)` satisface:

```
ω^(k(j+1)) / ω^(kj) = ω^k
```

Esto es una constante (no depende de j), que es un caso especial de función racional.

### Implicación
La estructura hipergeométrica permite aplicar técnicas de series geométricas y el algoritmo de Gosper para determinar si las sumas tienen forma cerrada.

---

## 2. Algoritmo de Gosper

### Concepto
Gosper decide algorítmicamente si una suma hipergeométrica tiene una **antidiferencia** (análogo discreto de antiderivada).

### Aplicación a NTT
- Las sumas `Σ ω^(nk)` **no** tienen forma cerrada más simple cuando `n ≠ 0`
- Esto justifica que la NTT es la representación óptima
- Para `n = 0`, la suma sí tiene forma cerrada: `N`

### Uso Práctico
No implementamos Gosper en Lean, pero su teoría justifica nuestra estrategia de prueba directa.

---

## 3. Algoritmo de Zeilberger (Creative Telescoping)

### Concepto
Encuentra automáticamente una **recurrencia lineal** que satisface una suma definida:

```
P₀(n)·S(n) + P₁(n)·S(n+1) + ... + Pₐ(n)·S(n+d) = 0
```

### Aplicación a NTT
La equivalencia Radix-2 ≡ Radix-4 se puede entender así:
1. Ambos algoritmos computan `S(n) = Σ x[k]·ω^(nk)`
2. Zeilberger mostraría que ambos satisfacen la misma recurrencia
3. Con las mismas condiciones iniciales → mismo resultado

### Implementación en Lean
En lugar de aplicar Zeilberger directamente, usamos la estrategia:
```lean
theorem radix2_eq_radix4 : NTT_radix2 = NTT_radix4 := by
  rw [radix2_eq_spec, radix4_eq_spec]  -- Transitividad via NTT_spec
```

---

## 4. WZ-Pairs (Certificados Racionales)

### Concepto
Para probar una identidad `Σ_k F(n,k) = rhs(n)`, el método WZ encuentra un **certificado** `R(n,k) = G(n,k)/F(n,k)` tal que:

```
F(n,k+1) - F(n,k) = G(n+1,k) - G(n,k)
```

Verificar la identidad se reduce a verificar esta ecuación local.

### Aplicación Potencial a NTT
Para la ortogonalidad `Σ_k ω^(nk) = N·δ(n,0)`, podríamos definir:
- `F(n,k) = ω^(nk)`
- `G(n,k) = ???` (el certificado WZ)

### Estado Actual
No implementamos WZ explícitamente. Las pruebas usan series geométricas directamente, que es el método subyacente que WZ automatizaría.

---

## 5. Método de Sister Celine

### Concepto
Garantiza la **existencia** de recurrencias lineales para funciones hipergeométricas.

### Aplicación a NTT
Confirma teóricamente que las sumas NTT tienen estructura recursiva, justificando que la inducción es una estrategia válida.

### Uso
Proporciona confianza en la estrategia inductiva de Cooley-Tukey.

---

## 6. Álgebras de Operadores Shift

### Concepto
Operadores:
- `N`: shift en n (índice de salida)
- `K`: shift en k (índice de suma)

Las identidades se expresan como ecuaciones operatoriales.

### Aplicación a NTT
La relación butterfly:
```
X[k+N/4] = combinación de Y[k], Y[k+N/4], ...
```

Se expresa como:
```
K^(N/4) · X = T₄ · X
```

### Uso en Lean
No usamos notación operatorial, pero la estructura subyacente guía cómo organizamos los lemas.

---

## 7. q-Análogos

### Concepto
Extensiones de identidades clásicas a casos con parámetro `q`:
- `[n]_q = (1-q^n)/(1-q)` (q-número)
- `[n]_q! = [1]_q·[2]_q·...·[n]_q` (q-factorial)

### Aplicación a NTT
La NTT opera sobre `F_p` (campo finito). Las raíces de unidad en `F_p` son exactamente el caso `q = ω`:
- `ω` es una raíz N-ésima de la unidad
- Las identidades de raíces de unidad son q-análogos especializados

### Insight
```
[N]_ω = (1-ω^N)/(1-ω) = 0/(1-ω) = 0   (para N-ésima raíz)
```

Esta es exactamente la serie geométrica que usamos en la prueba de ortogonalidad.

---

## 8. Ortogonalidad (Conexión con Chebyshev)

### Concepto
Las bases ortogonales satisfacen:
```
<φ_n, φ_m> = c_n · δ(n,m)
```

### Aplicación a NTT
Las raíces de unidad forman una base ortogonal:
```
Σ_k ω^(nk) · ω^(-mk) = Σ_k ω^((n-m)k) = N · δ(n,m)
```

### Uso Crucial
Esta es la identidad central para probar:
```
INTT(NTT(x)) = x
```

---

## 9. Snake Oil Method

### Concepto
Técnica para derivar identidades combinatorias manipulando funciones generatrices.

### Aplicación a NTT
Menos relevante para NTT directamente. Más útil para identidades binomiales.

### Estado
No aplicamos Snake Oil en este proyecto.

---

## Resumen: Qué Usamos de A=B

| Concepto | Uso | Implementación |
|----------|-----|----------------|
| Hipergeometricidad | Justifica series geométricas | Directo |
| Gosper | Confirma no hay forma cerrada | Teórico |
| Zeilberger | Estrategia de equivalencia | Transitividad |
| WZ-Pairs | Potencial futuro | No implementado |
| Sister Celine | Justifica inducción | Teórico |
| Shift Operators | Organización de lemas | Implícito |
| q-Análogos | Framework natural para F_p | Directo |
| Ortogonalidad | Prueba de roundtrip | Directo |

---

## Conclusión

El libro A=B proporciona:
1. **Marco teórico** para entender por qué nuestras estrategias funcionan
2. **Intuición** sobre la estructura de las sumas NTT
3. **Confianza** en que la inducción y series geométricas son los enfoques correctos

Las pruebas en Lean son directas (no automatizadas via Zeilberger), pero la teoría A=B guía su estructura.
