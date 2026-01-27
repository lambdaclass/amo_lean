# Fase Poseidon - AMO-Lean

## Overview

Esta fase extiende AMO-Lean para soportar operaciones no-lineales, habilitando la implementación de Poseidon2, un hash ZK-friendly crítico para zkVMs.

**Estado**: Paso 5 En Progreso (Integración)
**Prioridad**: #1 Crítico
**Inicio**: Enero 2026
**Progreso**: Paso 0.5 ✓ | Paso 1 ✓ | Paso 1.5 ✓ | Paso 2 ✓ | Paso 3 ✓ | Paso 4 ✓ | **Paso 5** ⏳

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
│ Paso 0: Prerrequisitos                               [PARCIAL] │
│ • ZModSIMD con pow_chain_5 optimizado                          │
├────────────────────────────────────────────────────────────────┤
│ Paso 0.5: Especificación Ejecutable                        [✓] │
│ • poseidon2_spec como función pura en Lean                     │
│ • Validar contra test vectors del paper                        │
├────────────────────────────────────────────────────────────────┤
│ Paso 1: Extensión del IR                                   [✓] │
│ • Añadir elemwise a MatExpr                                    │
│ • Reglas E-Graph (barrera opaca arquitectónica)                │
│ • head/tail en VecExpr para rondas parciales                   │
├────────────────────────────────────────────────────────────────┤
│ Paso 1.5: Sanity Tests                                     [✓] │
│ • Semantic check: sbox5 (x^5 mod p)                            │
│ • Optimization check: composición de potencias                 │
│ • Safety check: E-Graph NO prueba (A+B)^2 = A^2+B^2            │
│ • Barrier integrity: elemwise opaco a álgebra lineal           │
├────────────────────────────────────────────────────────────────┤
│ Paso 2: CodeGen (Estrategia por Capas)            [COMPLETADO] │
│ Ver ADR-004 para justificación de la estrategia                │
├────────────────────────────────────────────────────────────────┤
│   2.1: CodeGen Escalar                            [COMPLETADO] │
│   • S-box escalar (square chain, 3 muls)                       │
│   • Funciona para cualquier campo (BN254, Goldilocks)          │
│   • Base para differential fuzzing                             │
├────────────────────────────────────────────────────────────────┤
│   2.2: Pattern Matching Lowering                  [COMPLETADO] │
│   • Detectar concat(elemwise(head...)) → PartialSbox           │
│   • Mantener arquitectura de capas                             │
├────────────────────────────────────────────────────────────────┤
│   2.3: SIMD Goldilocks (Opcional)                 [COMPLETADO] │
│   • Solo campos ≤64 bits (4 elem/YMM)                          │
│   • Blend para partial rounds                                  │
├────────────────────────────────────────────────────────────────┤
│   2.4: Batch SIMD BN254 (Futuro)                  [COMPLETADO] │
│   • 4 hashes independientes en paralelo                        │
│   • Requiere API de batch hashing                              │
├────────────────────────────────────────────────────────────────┤
│ Paso 3: Poseidon2 en MatExpr                      [COMPLETADO] │
│ • Full rounds con elemwise                                     │
│ • Partial rounds con partialElemwise (no split/concat)         │
│ • ConstRef, MDS opaco, loops en CodeGen                        │
├────────────────────────────────────────────────────────────────┤
│ Paso 4: Verificación                             [COMPLETADO]  │
│ • 4a: Test Vector vs HorizenLabs               [✓ COMPLETADO]  │
│ • 4b.1: Spec.lean corregido, 118 vectors       [✓ COMPLETADO]  │
│ • 4b.2: Fuzzing Lean→C 118/118 vectors         [✓ COMPLETADO]  │
│ • 4b.3: Property testing 10/10 props           [✓ COMPLETADO]  │
│ • 4b Ext: Rust Oracle 10,035/10,035 vectors    [✓ COMPLETADO]  │
│ • 4c: Benchmark (C: 100kH/s, Rust: 136kH/s)    [✓ COMPLETADO]  │
│ • 4d: Prueba formal (21 tests, 12 sorry)       [✓ COMPLETADO]  │
├────────────────────────────────────────────────────────────────┤
│ Paso 5: Integración                              [EN PROGRESO] │
│ Ver ADR-007 para estrategia refinada                           │
│ • 5.1: Adaptadores Poseidon2 → HashFn                 [✓]      │
│ • 5.2: Auditoría de domain separation                 [✓]      │
│ • 5.3: Tests End-to-End FRI con Poseidon2             [ ]      │
└────────────────────────────────────────────────────────────────┘
```

---

## Documentación

| Archivo | Contenido |
|---------|-----------|
| [ADR-001-elemwise.md](ADR-001-elemwise.md) | Decisión: extensión de MatExpr |
| [ADR-002-partial-rounds.md](ADR-002-partial-rounds.md) | Decisión: split/concat para rondas parciales |
| [ADR-003-codegen-simd.md](ADR-003-codegen-simd.md) | Estrategia SIMD original (parcialmente superseded) |
| [ADR-004-codegen-strategy.md](ADR-004-codegen-strategy.md) | Estrategia CodeGen por capas |
| [ADR-005-phase3-architecture.md](ADR-005-phase3-architecture.md) | **Arquitectura Fase 3** (ConstRef, MDS opaco, loops) |
| [ADR-006-formal-verification-strategy.md](ADR-006-formal-verification-strategy.md) | **Estrategia Verificación Formal** (Paso 4d) |
| [ADR-007-step5-integration.md](ADR-007-step5-integration.md) | **Estrategia Integración** (Paso 5) |
| [ADR-008-domain-separation-audit.md](ADR-008-domain-separation-audit.md) | **Auditoría Domain Separation** (Paso 5.2) |
| [ADR-009-step53-generic-field-migration.md](ADR-009-step53-generic-field-migration.md) | **Migración Campo Genérico** (Paso 5.3) |
| [migration/PLAN.md](migration/PLAN.md) | Plan detallado de migración |
| [migration/DECISIONS.md](migration/DECISIONS.md) | Log de decisiones de migración |
| [PROGRESS.md](PROGRESS.md) | Progreso de implementación |

## Archivos de Código

| Archivo | Contenido |
|---------|-----------|
| `AmoLean/Protocols/Poseidon/Spec.lean` | Especificación pura de Poseidon2 |
| `AmoLean/Protocols/Poseidon/Params/BN254.lean` | Parámetros para BN254 |
| `AmoLean/Protocols/Poseidon/CodeGen.lean` | CodeGen específico Poseidon |
| `AmoLean/Protocols/Poseidon/MatExpr.lean` | Poseidon2 en MatExpr (Paso 3) |
| `AmoLean/Protocols/Poseidon/Integration.lean` | Adaptadores FRI (Paso 5.1) |
| `AmoLean/Protocols/Poseidon/DomainSeparation.lean` | Domain tags unificados (Paso 5.2) |
| `AmoLean/Matrix/Basic.lean` | ElemOp, elemwise, mdsApply constructor |
| `AmoLean/EGraph/Vector.lean` | MatEGraph con barrera opaca |
| `Tests/ElemwiseSanity.lean` | Tests de sanidad (4/4 pasan) |
| `Tests/TranscriptSecurityAudit.lean` | Auditoría de seguridad (Paso 5.2) |
| `Tests/poseidon_c/` | Tests C para verificación (Paso 4) |
| `AmoLean/FRI/Hash.lean` | CryptoHash typeclass (Paso 5.3 - pendiente) |
| `AmoLean/FRI/Fields/BN254.lean` | Campo BN254 con Poseidon2 (Paso 5.3 - pendiente) |
| `AmoLean/FRI/Fields/TestField.lean` | Campo de testing rápido (Paso 5.3 - pendiente) |

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

*Última actualización: 27 Enero 2026*
*Paso 5 En Progreso - Integración con infraestructura FRI existente*
