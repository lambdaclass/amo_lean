# ADR-005: Arquitectura de Fase 3 - Poseidon2 en MatExpr

## Estado
**Aceptado** - Implementado y validado (2026-01-26)

## Contexto

La Fase 3 del proyecto Poseidon requiere expresar la permutación completa de Poseidon2
usando el IR de MatExpr. Esto presenta desafíos únicos que no existían en las fases
anteriores:

### Escala del Problema

| Componente | Tamaño | Impacto |
|------------|--------|---------|
| Matriz MDS (t=12) | 144 elementos | Expansión de términos |
| Round constants | 64 rondas × 12 = 768 valores | Bloat de constantes |
| Rondas totales | 8 full + 56 partial = 64 | Unrolling potencial |
| Multiplicaciones | ~2,264 para Goldilocks t=12 | Grafo gigante |

### Riesgos Identificados

1. **Graph Explosion**: Si MDS se representa como matriz de escalares, las reglas de
   E-Graph la distribuirían sobre operaciones, multiplicando el tamaño del grafo.

2. **Constant Bloat**: Embeber 768 valores de round constants como literales en el
   IR causaría archivos fuente gigantes y compilación lenta.

3. **Dependent Types Hell**: Usar split/concat con tipos dependientes para rondas
   parciales causaría fricción de tipos (`Vector (1 + (t-1))` vs `Vector t`).

4. **IR Unrolling**: Representar 64 rondas explícitamente en el IR generaría árboles
   de expresión masivos.

## Decisión

Adoptamos una estrategia de **abstracciones opacas con metadata para CodeGen**:

### 1. ConstRef: Referencias Simbólicas

Las constantes (MDS, round constants) se referencian simbólicamente, **nunca se embeben**:

```lean
inductive ConstRef where
  | mds (t : Nat) : ConstRef
  | mdsInternal (t : Nat) : ConstRef
  | mdsExternal (t : Nat) : ConstRef
  | roundConst (round : Nat) (t : Nat) : ConstRef
```

CodeGen traduce a arrays externos:
```c
extern const uint64_t POSEIDON_MDS_3[3][3][4];
extern const uint64_t POSEIDON_RC[64][3][4];
```

### 2. MDS como Operación Opaca

`MatExpr.mdsApply` es un constructor que el E-Graph **NO penetra**:

```lean
| mdsApply : (mdsName : String) → (stateSize : Nat) → MatExpr α t 1 → MatExpr α t 1
```

Esto previene la distribución:
```
MDS × (A + B) → [NO se reescribe como MDS×A + MDS×B]
```

### 3. Partial Rounds sin Split/Concat

En lugar de separar el estado con tipos dependientes, usamos `partialElemwise`:

```lean
| partialElemwise : (idx : Nat) → ElemOp → MatExpr α m n → MatExpr α m n
```

Esto aplica la operación solo al índice especificado, evitando toda la
complejidad de tipos dependientes.

### 4. Loops en CodeGen, No Unrolling en IR

El IR almacena **metadata** sobre la estructura de rondas, no la expansión:

```lean
structure PoseidonConfig where
  field : PoseidonField
  stateSize : Nat
  fullRounds : Nat      -- RF
  partialRounds : Nat   -- RP
```

CodeGen genera loops C:
```c
for (int r = 0; r < 4; r++) { poseidon_full_round(state, round++, p); }
for (int r = 0; r < 56; r++) { poseidon_partial_round(state, round++, p); }
for (int r = 0; r < 4; r++) { poseidon_full_round(state, round++, p); }
```

## Alternativas Consideradas

### A. Embedding Literal de Constantes
**Rechazado**: Causaría archivos de 1GB+ y timeouts de compilación.

### B. MDS como Matriz Expandida
**Rechazado**: Causaría explosión del grafo O(t²) por cada operación.

### C. Split/Concat para Partial Rounds
**Rechazado**: Friction de tipos dependientes, errores de unificación.

### D. Unrolling Completo en IR
**Rechazado**: 64 nodos por ronda × 4 ops = 256 nodos mínimo, no escala.

## Consecuencias

### Positivas

1. **Compilación Instantánea**: Los archivos Lean son pequeños (~580 líneas).
2. **Grafo Sparse**: 4 nodos por ronda, independiente del tamaño de MDS.
3. **Tipos Limpios**: Sin casting manual, firmas simples.
4. **Código Cache-Friendly**: Loops en C caben en L1 instruction cache.
5. **Extensible**: Fácil añadir nuevas configuraciones (t=5, t=12, etc.).

### Negativas

1. **Pérdida de Optimización Local**: El E-Graph no puede optimizar dentro de MDS.
2. **Confianza en Constantes Externas**: Los valores de MDS/RC deben ser correctos.
3. **Menos Verificación Formal**: Las operaciones opacas son cajas negras.

### Mitigaciones

- Las constantes externas se validan contra test vectors conocidos.
- Tests diferenciales comparan la salida con implementaciones de referencia.
- Las operaciones opacas tienen semántica bien definida para verificación.

## Validación

Se implementó una suite de validación arquitectónica (`Tests/Poseidon3Validation.lean`):

| Test | Objetivo | Resultado |
|------|----------|-----------|
| 3.1 Instant Check | Elaboración <100ms | PASS |
| 3.2 Type Inference | Firmas sin fricción | PASS |
| 3.3 Topology | Grafo sparse (4 nodos/ronda) | PASS |
| 3.4 Opaqueness | ConstRef sin literales | PASS |
| 3.5 CodeGen Loops | for, no unrolling | PASS |
| 3.6 Correctness | Orden de operaciones | PASS |

### Métricas Clave

| Métrica | Valor | Límite Aceptable |
|---------|-------|------------------|
| Nodos por ronda | 4 | ≤ 10 |
| Tamaño header C | 5,373 chars | < 10,000 |
| Full round calls | 2 | ≤ 3 |
| Partial round calls | 1 | ≤ 2 |
| Muls estimadas (BN254 t=3) | 536 | 400-700 |

## Implementación

### Archivos Creados
- `AmoLean/Protocols/Poseidon/MatExpr.lean` - Implementación principal
- `Tests/Poseidon3.lean` - Tests de integración
- `Tests/Poseidon3Validation.lean` - Validación arquitectónica
- `generated/poseidon2_bn254_t3.h` - Código C generado
- `generated/poseidon2_bn254_t5.h` - Código C generado

### Archivos Modificados
- `AmoLean/Matrix/Basic.lean` - mdsApply, addRoundConst
- `AmoLean/Sigma/Basic.lean` - Kernels nuevos
- `AmoLean/Sigma/Expand.lean` - Expansión de kernels

## Referencias

- Grassi et al., "Poseidon2: A Faster Version of the Poseidon Hash Function"
- HorizenLabs/poseidon2 - Implementación de referencia
- ADR-004: Estrategia CodeGen por capas (contexto previo)

## Historial

| Fecha | Acción | Autor |
|-------|--------|-------|
| 2026-01-26 | Propuesta inicial basada en análisis de riesgos | Equipo |
| 2026-01-26 | Implementación de ConstRef y MDS opaco | Claude |
| 2026-01-26 | Validación arquitectónica (6/6 tests PASS) | Claude |
| 2026-01-26 | ADR aceptado y documentado | Equipo |
