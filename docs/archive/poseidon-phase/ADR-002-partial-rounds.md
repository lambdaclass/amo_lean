# ADR-002: Representación de Rondas Parciales

## Estado
Aceptado

## Contexto

Poseidon usa dos tipos de rondas:
- **Full rounds**: S-box aplicada a TODOS los elementos del estado
- **Partial rounds**: S-box aplicada SOLO al elemento 0

```
Full Round:    [s0, s1, s2] → [s0^5, s1^5, s2^5]
Partial Round: [s0, s1, s2] → [s0^5, s1, s2]
```

Las rondas parciales son más eficientes (una S-box vs t S-boxes) y proveen suficiente seguridad cuando se intercalan con full rounds.

**El problema**: `MatExpr.elemwise` aplica la operación a TODOS los elementos. ¿Cómo representar la aplicación selectiva?

## Decisión

Usar **Split/Concat** para rondas parciales:

```lean
def partialRound (state : MatExpr α t 1) (rc : Vec t) (mds : Matrix t t) : MatExpr α t 1 :=
  let withRC := MatExpr.add state (MatExpr.const rc)
  -- Split: separar primer elemento del resto
  let (head, tail) := MatExpr.split withRC 1
  -- Aplicar S-box solo al primer elemento
  let head' := MatExpr.elemwise (.pow 5) head
  -- Concat: reunir
  let state' := MatExpr.concat head' tail
  -- Multiplicar por MDS
  MatExpr.mul (MatExpr.const mds) state'
```

## Alternativas Consideradas

### Alternativa A: Matriz diagonal especial

```lean
-- D donde D[0,0] = Sbox y D[i,i] = id para i > 0
| diagSbox : MatExpr α t t
```

**Rechazada** porque:
- Difícil de representar limpiamente en el IR
- No se integra bien con el sistema de tipos
- Requiere nuevo constructor complejo

### Alternativa B: elemwise con máscara

```lean
| elemwise_masked : ElemOp → BitVec n → MatExpr α m n → MatExpr α m n
```

Donde `BitVec n` indica qué elementos afecta.

**Rechazada** porque:
- Añade complejidad al IR
- Requiere reglas E-Graph adicionales para máscaras
- Split/Concat ya existe y es más general

### Alternativa C (Elegida): Split/Concat

Reutiliza constructores existentes de `VecExpr`/`MatExpr`:
- `split : MatExpr α (m+n) 1 → Nat → (MatExpr α m 1 × MatExpr α n 1)`
- `concat : MatExpr α m 1 → MatExpr α n 1 → MatExpr α (m+n) 1`

**Ventajas**:
- No añade complejidad al IR
- El E-Graph no necesita reglas nuevas para el patrón básico
- CodeGen puede detectar el patrón y optimizar

## Consecuencias

### Positivas

1. **Reutilización**: Aprovecha infraestructura existente de Fase 5 (VecExpr).

2. **Composabilidad**: El patrón split→elemwise→concat es genérico y puede usarse para otras operaciones selectivas en el futuro.

3. **Optimización en CodeGen**: El generador puede detectar este patrón específico y emitir código SIMD optimizado (ver ADR-003).

### Negativas

1. **Menos explícito**: La intención "S-box parcial" no es obvia en el IR.

2. **Overhead potencial**: Sin optimización, split/concat genera código subóptimo.

## Patrón de Detección en CodeGen

El CodeGen debe reconocer:

```
concat(elemwise(pow 5, split(x, 1).0), split(x, 1).1)
```

Y generar:

```c
// En lugar de extraer/reinsertar escalar:
state[0] = sbox(state[0]);  // Los demás no cambian

// O con SIMD (ver ADR-003):
__m256i sbox_all = sbox_avx2(state);
state = _mm256_blend_epi64(state, sbox_all, 0b0001);
```

## Notas de Implementación

1. **Split/Concat deben existir en MatExpr**: Verificar que la Fase 5 los implementó, o añadirlos si no.

2. **Invariante de dimensiones**: `split` en posición k de vector de tamaño t produce vectores de tamaño k y t-k. Para rondas parciales, k=1.

3. **E-Graph**: Considerar añadir regla de simplificación:
   ```lean
   concat(split(x, k).0, split(x, k).1) → x  -- Identidad
   ```

---

*Fecha*: Enero 2026
*Autores*: Equipo AMO-Lean
