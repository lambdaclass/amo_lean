# Notas: Poseidon Hash para AMO-Lean

## Papers en este directorio

| Archivo | Descripción | Relevancia | Leído |
|---------|-------------|------------|-------|
| `poseidon.pdf` | Paper original USENIX 2021 (Grassi et al.) | CRÍTICO | [x] |
| `poseidon2.pdf` | Versión optimizada 2023 | CRÍTICO | [x] |
| `security of poseidon.pdf` | Análisis formal de seguridad | MUY RELEVANTE | [x] |
| `construction lightweight s boxes.pdf` | Construcción de S-boxes | RELEVANTE | [x] |
| `indexed types.pdf` | Tipos dependientes en Lean | ÚTIL | [x] |
| `verifying higher order functions.pdf` | Verificación formal | CONTEXTUAL | [ ] |
| `algebraic analysis of trivium.pdf` | Criptoanálisis algebraico | MENOS RELEVANTE | [ ] |
| `8 bit sbox based on orbits.pdf` | S-boxes 8-bit | MENOS RELEVANTE | [ ] |
| `feistel vs misty.pdf` | Comparación estructuras | MENOS RELEVANTE | [ ] |
| `non-randomness aes.pdf` | Análisis AES | MENOS RELEVANTE | [ ] |
| `parallel construction collision.pdf` | Construcciones paralelas | MENOS RELEVANTE | [ ] |
| `practical cryptanalysis hummingbird.pdf` | Criptoanálisis específico | NO RELEVANTE | [ ] |
| `verifying functional programs.pdf` | Verificación funcional | CONTEXTUAL | [ ] |
| Otros papers de S-boxes... | Varios | MENOS RELEVANTE | [ ] |

---

## Resumen Ejecutivo

### Decisión Principal: Poseidon2 sobre Poseidon Original

**Recomendación**: Implementar **Poseidon2** en lugar del Poseidon original.

**Razones**:
1. **2-4x más eficiente** en operaciones de campo
2. **Matriz M₄ optimizada**: 8 sumas + 4 multiplicaciones por constante (vs ~t² operaciones)
3. **Compatibilidad**: Misma seguridad, mismos parámetros de S-box
4. **Adopción**: Usado por zkVMs modernos (Plonky3, etc.)

### Estructura HADES

Poseidon usa la estrategia HADES que combina:
- **Full rounds (RF)**: S-box aplicada a TODOS los elementos del estado
- **Partial rounds (RP)**: S-box aplicada solo al PRIMER elemento

```
[RF/2 full rounds] → [RP partial rounds] → [RF/2 full rounds]
```

Esta estructura optimiza el costo manteniendo seguridad contra ataques algebraicos.

---

## Análisis Detallado de Papers Críticos

### 1. poseidon.pdf - Paper Original (CRÍTICO)

**Contribución principal**: Define la función hash Poseidon optimizada para circuitos aritméticos.

**Elementos clave**:
- Estructura HADES con full/partial rounds
- Uso de matriz MDS para difusión
- S-box x^α donde α ∈ {3, 5, 7, ...} (primo con p-1)
- Análisis de seguridad contra ataques diferenciales y algebraicos

**Parámetros recomendados para 128-bit security**:
| Campo | t | RF | RP |
|-------|---|----|----|
| BN254 | 3 | 8 | 56 |
| BN254 | 5 | 8 | 57 |
| Goldilocks | 12 | 8 | 22 |

### 2. poseidon2.pdf - Versión Optimizada (CRÍTICO)

**Mejoras sobre Poseidon original**:

1. **Capa lineal externa (full rounds)**: Matriz M₄ circulante
   ```
   M₄ = circ(2, 1, 1, 1)  // Para t=4
   ```
   - Solo 8 sumas + 4 multiplicaciones escalares
   - Reducción de ~90% en operaciones vs MDS densa

2. **Capa lineal interna (partial rounds)**:
   - Matriz diagonal + vector columna
   - Permite optimización adicional

3. **Misma seguridad**: Los bounds de seguridad se mantienen

**Pseudocódigo Poseidon2**:
```
function poseidon2_permutation(state[t]):
    // Rondas completas iniciales
    for r in 0..RF/2:
        state = add_round_constants(state, rc_ext[r])
        state = sbox_full(state)        // x^5 a TODOS
        state = M_ext × state           // Matriz M₄ externa

    // Rondas parciales
    for r in 0..RP:
        state[0] = state[0] + rc_int[r]
        state[0] = sbox(state[0])       // x^5 solo al primero
        state = M_int × state           // Matriz interna diagonal

    // Rondas completas finales
    for r in 0..RF/2:
        state = add_round_constants(state, rc_ext[RF/2 + r])
        state = sbox_full(state)
        state = M_ext × state

    return state
```

### 3. security of poseidon.pdf - Análisis de Seguridad (MUY RELEVANTE)

**Contribución**: Pruebas formales de los bounds de seguridad.

**Resultados clave**:
- Número mínimo de rondas para resistir ataques diferenciales
- Número mínimo de rondas para resistir ataques algebraicos (Gröbner)
- Justificación del margen de seguridad (2x rondas recomendadas)

**Implicación para AMO-Lean**: Los parámetros del paper son seguros, no necesitamos derivar nuevos.

### 4. construction lightweight s boxes.pdf (RELEVANTE)

**Contribución**: Métodos para construir S-boxes ligeras con buenas propiedades.

**Relevancia para Poseidon**:
- Confirma que x^5 tiene buenas propiedades algebraicas
- Diferencial uniformity δ ≤ 4 para campos primos grandes
- Algebraic degree = 5 (suficiente para seguridad)

**Conclusión**: La S-box x^5 de Poseidon es óptima para circuitos aritméticos.

### 5. indexed types.pdf (ÚTIL)

**Contribución**: Implementación de tipos indexados (dependientes) en lenguajes funcionales.

**Relevancia para AMO-Lean**:
- Técnicas para `Vec t FieldElement` con tamaño verificado en compile-time
- Patrones para matrices de tamaño estático
- Útil para garantizar dimensiones correctas en MDS

---

## Decisiones de Diseño para AMO-Lean

### 1. Extensión de MatExpr

**Necesario**: Añadir constructor `elemwise` para operaciones no-lineales.

```lean
inductive MatExpr where
  | var : String → MatExpr
  | add : MatExpr → MatExpr → MatExpr
  | mul : MatExpr → MatExpr → MatExpr
  | kron : MatExpr → MatExpr → MatExpr
  | elemwise : (FieldElement → FieldElement) → MatExpr → MatExpr  -- NUEVO
```

**Alternativa considerada**: DSL separado para no-linealidad.
**Decisión**: Integrar en MatExpr para mantener un solo sistema de optimización.

### 2. S-box: Square Chain

Para x^5 (α=5), usar descomposición:
```
x^5 = x * (x^2)^2
    = x * x^4
```

**Implementación (3 multiplicaciones)**:
```
t = x * x      // x^2
t = t * t      // x^4
return x * t   // x^5
```

### 3. Representación de Matrices

**Para Poseidon2**:
- **M_ext (externa)**: Matriz circulante M₄, representar como vector [2,1,1,1]
- **M_int (interna)**: Diagonal + columna sparse

**Optimización Kronecker**: Si t > 4, usar M₄ ⊗ I_{t/4} cuando sea aplicable.

### 4. Parámetros a Implementar

**Prioridad 1**: BN254 con t=3 (hash binario estándar)
```lean
structure PoseidonParams where
  t : Nat := 3
  alpha : Nat := 5
  fullRounds : Nat := 8
  partialRounds : Nat := 56
  -- MDS y round constants específicos para BN254
```

**Prioridad 2**: Goldilocks con t=12 (para STARKs)

---

## Fases de Implementación

### Fase 1.1: Extender MatExpr (1-2 semanas)
- Añadir constructor `elemwise`
- Actualizar evaluador
- Actualizar E-Graph con reglas para elemwise

### Fase 1.2: Parámetros Poseidon2 (1 semana)
- Definir estructura `PoseidonParams`
- Implementar generación de round constants
- Implementar matriz M₄ y M_int

### Fase 1.3: Implementación Core (2-3 semanas)
- Función `poseidon2Permutation` en Lean
- Modo sponge para hash de longitud variable
- Tests contra vectores de prueba conocidos

### Fase 1.4: Generación de Código C (2-3 semanas)
- Extender CodeGen para elemwise
- Optimización SIMD para S-box paralela
- Unrolling de rondas

### Fase 1.5: Verificación (1-2 semanas)
- Differential fuzzing contra implementación de referencia
- Pruebas formales de equivalencia Lean ↔ C

---

## Implementaciones de Referencia

- [x] Revisar: https://github.com/HorizenLabs/poseidon2 (Rust, Poseidon2)
- [ ] Revisar: https://github.com/filecoin-project/neptune (Rust, Poseidon original)
- [ ] Revisar: https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom (Circom)
- [ ] Revisar: Plonky3 implementation

---

## Preguntas Resueltas

1. **¿Poseidon vs Poseidon2?** → Poseidon2 (2-4x más eficiente)
2. **¿Qué S-box?** → x^5 con square chain (3 muls)
3. **¿Matriz MDS?** → M₄ circulante de Poseidon2

## Preguntas Pendientes

1. ¿Compatibilidad específica con SP1/RISC Zero? (verificar parámetros exactos)
2. ¿Integración con Fiat-Shamir existente en FRI?
3. ¿Priorizar BN254 o Goldilocks primero?

---

## Notas de Lectura

### 2024-01-26 - Análisis inicial de 18 papers

**Papers estudiados**: poseidon.pdf, poseidon2.pdf, security of poseidon.pdf, construction lightweight s boxes.pdf, indexed types.pdf, y 13 papers adicionales de S-boxes y verificación.

**Conclusión principal**: El camino claro es implementar Poseidon2 usando:
- S-box x^5 con square chain
- Matriz M₄ circulante para capa externa
- Parámetros BN254: t=3, RF=8, RP=56

**Papers de S-boxes (8-bit, Feistel, etc.)**: No directamente aplicables ya que Poseidon usa S-box algebraica x^α, no tablas de lookup. Útiles solo como contexto criptográfico general.

