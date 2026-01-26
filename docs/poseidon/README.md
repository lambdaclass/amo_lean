# Fase Poseidon - AMO-Lean

## Overview

Esta fase extiende AMO-Lean para soportar operaciones no-lineales, habilitando la implementación de Poseidon2, un hash ZK-friendly crítico para zkVMs.

**Estado**: En desarrollo
**Prioridad**: #1 Crítico
**Inicio**: Enero 2026

---

## El Problema

AMO-Lean v1.0 (FRI verificado) solo maneja **operaciones lineales**:

```
MatExpr actual: var | add | mul | kron
                 ↓
            Todo es LINEAL
```

Poseidon requiere la **S-box** `x^α` (típicamente α=5), una operación **no-lineal** aplicada elemento por elemento:

```
Poseidon_round(state) = MDS × Sbox(state + round_constants)
                         ↑        ↑
                      LINEAL   NO-LINEAL (x^5)
```

**Sin esta extensión**, AMO-Lean no puede generar:
- Merkle trees (necesarios para commits)
- Fiat-Shamir completo
- Recursión de pruebas

---

## La Solución: Poseidon2

Implementaremos **Poseidon2** (no el original) porque:
- 2-4x más eficiente en operaciones de campo
- Matriz M₄ circulante reduce operaciones ~90%
- Misma seguridad, adoptado por zkVMs modernos

### Estructura de Poseidon2

```
┌─────────────────────────────────────────────────────────┐
│  [RF/2 Full Rounds] → [RP Partial Rounds] → [RF/2 Full] │
└─────────────────────────────────────────────────────────┘

Full Round:   state = M_ext × Sbox(state + rc)    // Sbox a TODOS
Partial Round: state = M_int × Sbox_partial(state + rc)  // Sbox solo a state[0]
```

---

## Extensión del IR

### Nuevo constructor: `elemwise`

```lean
inductive MatExpr (α : Type) : Nat → Nat → Type where
  | var     : String → MatExpr α m n
  | add     : MatExpr α m n → MatExpr α m n → MatExpr α m n
  | mul     : MatExpr α m p → MatExpr α p n → MatExpr α m n
  | kron    : MatExpr α m n → MatExpr α p q → MatExpr α (m*p) (n*q)
  | elemwise : ElemOp → MatExpr α m n → MatExpr α m n  -- NUEVO
```

El tipo garantiza preservación de dimensiones por construcción.

---

## Plan de Implementación

```
┌────────────────────────────────────────────────────────────────┐
│ Paso 0: Prerrequisitos                                         │
│ • ZModSIMD con pow_chain_5 optimizado                          │
├────────────────────────────────────────────────────────────────┤
│ Paso 0.5: Especificación Ejecutable                            │
│ • poseidon2_spec como función pura en Lean                     │
│ • Validar contra test vectors del paper                        │
├────────────────────────────────────────────────────────────────┤
│ Paso 1: Extensión del IR                                       │
│ • Añadir elemwise a MatExpr                                    │
│ • Reglas E-Graph (barrera opaca)                               │
├────────────────────────────────────────────────────────────────┤
│ Paso 2: CodeGen                                                │
│ • S-box escalar (square chain, 3 muls)                         │
│ • S-box SIMD (AVX2 paralelo)                                   │
│ • Patrón split→elemwise→concat → blend                         │
├────────────────────────────────────────────────────────────────┤
│ Paso 3: Poseidon2 en MatExpr                                   │
│ • Full rounds con elemwise                                     │
│ • Partial rounds con split/concat                              │
├────────────────────────────────────────────────────────────────┤
│ Paso 4: Verificación                                           │
│ • Differential fuzzing: spec vs C generado                     │
│ • Prueba formal de equivalencia                                │
├────────────────────────────────────────────────────────────────┤
│ Paso 5: Integración                                            │
│ • MerkleTree con Poseidon2                                     │
│ • Conectar con FRI                                             │
└────────────────────────────────────────────────────────────────┘
```

---

## Documentación

| Archivo | Contenido |
|---------|-----------|
| [ADR-001-elemwise.md](ADR-001-elemwise.md) | Decisión: extensión de MatExpr |
| [ADR-002-partial-rounds.md](ADR-002-partial-rounds.md) | Decisión: split/concat para rondas parciales |
| [ADR-003-codegen-simd.md](ADR-003-codegen-simd.md) | Decisión: estrategia SIMD blend |
| [PROGRESS.md](PROGRESS.md) | Progreso de implementación |

---

## Referencias Bibliográficas

Ver [../references/poseidon/notes.md](../references/poseidon/notes.md) para análisis detallado de papers.

**Papers críticos**:
- `poseidon2.pdf` - Algoritmo a implementar
- `security of poseidon.pdf` - Justificación de parámetros
- `construction lightweight s boxes.pdf` - Propiedades de x^5

---

## Parámetros Target

**Prioridad 1: BN254**
```
t = 3 (estado de 3 elementos)
α = 5 (exponente S-box)
RF = 8 (full rounds)
RP = 56 (partial rounds)
```

**Prioridad 2: Goldilocks**
```
t = 12
α = 7
RF = 8
RP = 22
```

---

*Última actualización: Enero 2026*
