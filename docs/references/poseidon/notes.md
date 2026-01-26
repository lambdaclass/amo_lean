# Notas: Poseidon Hash para AMO-Lean

## Papers en este directorio

| Archivo | Descripción | Leído |
|---------|-------------|-------|
| `grassi2021_poseidon.pdf` | Paper original USENIX 2021 | [ ] |
| ... | ... | [ ] |

---

## Resumen Ejecutivo

Poseidon es un hash diseñado para ser eficiente en circuitos aritméticos (SNARKs/STARKs).

**Estructura de una ronda:**
```
state' = MDS × (state + round_constants)^α
```

Donde:
- `MDS`: Matriz Maximum Distance Separable (lineal)
- `α`: Exponente S-box, típicamente 5 (no-lineal)
- `round_constants`: Diferentes por ronda (previene ataques)

---

## Secciones Relevantes para AMO-Lean

### Del paper principal:

- **Sección X.X**: [Descripción de qué extraer]
- **Apéndice Y**: [Parámetros concretos]

### Decisiones de diseño:

1. **MatExpr.elemwise**: Necesario para representar `x^α`
   - Alternativa: DSL separado para no-linealidad
   - Decisión: [pendiente]

2. **Representación de MDS**:
   - Opción A: Matriz densa
   - Opción B: Factorización sparse si existe estructura
   - Paper dice: [investigar]

3. **Parámetros a soportar**:
   - Estado t = ? (común: 3, 5, 9, 12)
   - Campo: Goldilocks? BN254?
   - Rondas: full vs partial

---

## Pseudocódigo Extraído

```
// Del paper, Sección X
function poseidon_permutation(state[t]):
    for r in 0..R_f/2:          // Primeras rondas completas
        state = full_round(state, r)
    for r in R_f/2..R_f/2+R_p:  // Rondas parciales
        state = partial_round(state, r)
    for r in ...:               // Últimas rondas completas
        state = full_round(state, r)
    return state

function full_round(state, r):
    state = state + round_constants[r]
    state = sbox(state)         // Aplicar a TODOS los elementos
    state = MDS × state
    return state

function partial_round(state, r):
    state = state + round_constants[r]
    state[0] = sbox(state[0])   // Aplicar solo al PRIMER elemento
    state = MDS × state
    return state
```

---

## Implementaciones de Referencia

- [ ] Revisar: https://github.com/filecoin-project/neptune (Rust)
- [ ] Revisar: https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom (Circom)
- [ ] Revisar: https://github.com/HorizenLabs/poseidon2 (Poseidon2)

---

## Preguntas Abiertas

1. ¿Qué parámetros usar para compatibilidad con SP1/RISC Zero?
2. ¿Poseidon vs Poseidon2? (Poseidon2 es más reciente y eficiente)
3. ¿Cómo integrar con nuestro sistema de Fiat-Shamir?

---

## Notas de Lectura

### [Fecha] - [Paper]

*Añadir notas mientras lees...*
