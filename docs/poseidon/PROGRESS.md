# Progreso de Implementación - Fase Poseidon

## Estado General

| Paso | Descripción | Estado | Notas |
|------|-------------|--------|-------|
| 0 | Prerrequisitos (ZModSIMD) | Parcial | ZModSIMD existe, falta pow_chain |
| 0.5 | Especificación ejecutable | **Completado** | Spec.lean funcionando sin Mathlib |
| 1 | Extensión IR (elemwise) | **Completado** | head/tail, elemwise, E-Graph, sanity tests ✓ |
| 1.5 | Sanity Tests | **Completado** | 4/4 tests pasan, safe to proceed to CodeGen |
| 2 | CodeGen SIMD | Pendiente | |
| 3 | Poseidon2 en MatExpr | Pendiente | |
| 4 | Verificación | Pendiente | |
| 5 | Integración MerkleTree | Pendiente | |

---

## Paso 0: Prerrequisitos

### Objetivo
Asegurar que ZModSIMD tiene las primitivas necesarias para S-box.

### Checklist
- [ ] `field_mul` escalar funciona correctamente
- [ ] `field_mul_avx2` implementado y testeado
- [ ] `pow_chain_5` optimizado (3 muls)
- [ ] Reducción Montgomery lazy disponible

### Archivos a modificar
- `AmoLean/Matrix/ZModSIMD.lean`

---

## Paso 0.5: Especificación Ejecutable

### Objetivo
Implementar Poseidon2 como función pura en Lean (sin IR) para validación.

### Checklist
- [x] Definir `Params` structure (genérico para cualquier primo p y tamaño t)
- [x] Cargar parámetros BN254 (MDS, round constants placeholder)
- [x] Implementar `poseidon2Permutation : Params p t → State p t → State p t`
- [x] Implementar `poseidon2Hash` con construcción sponge
- [x] S-box con square chain: x^5 = x * (x^2)^2 (3 muls)
- [ ] Cargar round constants completas (actualmente placeholder)
- [ ] Validar contra test vectors del paper Poseidon2
- [ ] Documentar cualquier discrepancia

### Archivos creados
- `AmoLean/Protocols/Poseidon/Spec.lean` - Especificación pura
- `AmoLean/Protocols/Poseidon/Params/BN254.lean` - Parámetros BN254

### Implementación
- Estado: `State p t := Fin t → ZMod p`
- Full round: AddRC → S-box(all) → MDS
- Partial round: AddRC → S-box(first) → MDS
- Permutación: [RF/2 full] → [RP partial] → [RF/2 full]

### Parámetros BN254 t=3
- α = 5, RF = 8, RP = 56
- MDS: [[2,1,1], [1,2,1], [1,1,3]]
- Fuente: HorizenLabs/poseidon2

### Test Vectors
Fuente: Paper Poseidon2, Apéndice (pendiente de cargar)

---

## Paso 1: Extensión del IR

### Objetivo
Añadir constructor `elemwise` a MatExpr y soporte para rondas parciales.

### Checklist
- [x] Añadir `head`/`tail` a VecExpr (para rondas parciales)
- [x] Definir `ElemOp` (pow, custom)
- [x] Añadir `elemwise` a `MatExpr`
- [x] Actualizar lowering (lower) para `elemwise`
- [x] Añadir `sbox` kernel a Sigma
- [x] Actualizar evaluadores
- [x] elemwise como barrera opaca en E-Graph (arquitectónico)

### Archivos modificados
- `AmoLean/Vector/Basic.lean` - Añadido head/tail a VecExpr
- `AmoLean/Matrix/Basic.lean` - Añadido ElemOp y elemwise
- `AmoLean/EGraph/Vector.lean` - Soporte elemwise en MatEGraph (barrera opaca)
- `AmoLean/Sigma/Basic.lean` - Kernel sbox, lowering de elemwise
- `AmoLean/Sigma/Expand.lean` - Expansión de S-box (square chain: 3 muls)
- `AmoLean/Verification/Semantics.lean` - Evaluador para sbox
- `Tests/ElemwiseSanity.lean` - Tests de sanidad (4 tests, todos pasan)

### Implementación

**VecExpr** ahora tiene:
```lean
| head : VecExpr α (n + 1) → VecExpr α 1
| tail : VecExpr α (n + 1) → VecExpr α n
```

**MatExpr** ahora tiene:
```lean
inductive ElemOp where
  | pow : Nat → ElemOp      -- x^n (S-box para α=5)
  | custom : String → ElemOp

| elemwise : ElemOp → MatExpr α m n → MatExpr α m n
```

**Barrera opaca**: elemwise no se penetra por reglas de álgebra lineal - esto es arquitectónico (no hay reglas que miren dentro).

---

## Paso 1.5: Sanity Tests

### Objetivo
Verificar la robustez de la extensión elemwise antes de proceder al CodeGen.

### Checklist
- [x] Test 1: Semantic Check - sbox5 (x^5) computa correctamente
- [x] Test 2: Optimization Check - E-Graph requiere regla explícita de composición
- [x] Test 3: Safety Check (CRÍTICO) - E-Graph NO prueba (A+B)^2 = A^2 + B^2
- [x] Test 4: Barrier Integrity - elemwise no se distribuye sobre adición

### Archivo creado
- `Tests/ElemwiseSanity.lean`

### Resultados
```
╔════════════════════════════════════════════════════════════╗
║          ELEMWISE SANITY TESTS - Phase Poseidon            ║
╚════════════════════════════════════════════════════════════╝

=== Test 1: Semantic Check (sbox5) ===
  PASS: sbox5(0) = 0
  PASS: sbox5(1) = 1
  PASS: sbox5(2) = 15
  PASS: sbox5(3) = 5
  PASS: sbox5(4) = 4
  PASS: sbox5(5) = 14
  PASS: sbox5(16) = 16
  All semantic checks PASSED

=== Test 2: Optimization Check (elemwise composition) ===
  Are equivalent before composition rule? false
  Are equivalent after manual merge? true
  Composition check PASSED

=== Test 3: Safety Check (CRITICAL) ===
  SAFETY CHECK PASSED
  E-Graph correctly does NOT claim (x+y)^2 = x^2 + y^2

=== Test 4: Elemwise Barrier Integrity ===
  BARRIER INTEGRITY PASSED
  E-Graph correctly keeps elemwise opaque.

╔════════════════════════════════════════════════════════════╗
║  SUMMARY: 4 passed, 0 failed                              ║
║  STATUS: ALL TESTS PASSED - Safe to proceed to CodeGen     ║
╚════════════════════════════════════════════════════════════╝
```

### Problemas Encontrados y Soluciones

#### Problema 1: Sintaxis `let open` no soportada en Lean 4
**Error**: `unexpected token 'open'; expected ':=', '_', 'rec' or identifier`
**Causa**: Intenté usar `let open AmoLean.EGraph in` dentro de un bloque `do`
**Solución**: Mover los `open` statements al nivel de módulo con `open ... (...)` al inicio

#### Problema 2: Axioma `sorry` bloqueaba evaluación
**Error**: `aborting evaluation since the expression depends on the 'sorry' axiom`
**Causa**: `#eval` estándar rechaza código con dependencias de sorry
**Solución**: Usar `#eval!` para forzar evaluación

#### Problema 3: Valor esperado incorrecto para 5^5 mod 17
**Error**: Test fallaba con `sbox5(5) = 14, expected 3`
**Causa**: Cálculo manual inicial erróneo
**Solución**: Recalculado: 5^5 = 3125, 3125 mod 17 = 14. Corregido en tests.

---

## Paso 2: CodeGen

### Objetivo
Generar código C/SIMD para elemwise y S-box.

### Checklist
- [ ] Generar S-box escalar (square chain)
- [ ] Generar S-box AVX2
- [ ] Detectar patrón split→elemwise→concat
- [ ] Generar blend para rondas parciales
- [ ] Tests de correctitud vs evaluador Lean

### Archivos a modificar
- `AmoLean/CodeGen.lean`

### Código esperado
```c
// Full round
state = sbox_avx2(state);

// Partial round
__m256i sbox_all = sbox_avx2(state);
state = _mm256_blend_epi64(state, sbox_all, 0b0001);
```

---

## Paso 3: Poseidon2 en MatExpr

### Objetivo
Expresar Poseidon2 completo usando el IR extendido.

### Checklist
- [ ] Full round como MatExpr
- [ ] Partial round con split/concat
- [ ] Poseidon2 permutation completa
- [ ] Modo sponge para hash de longitud variable
- [ ] Verificar que E-Graph no explota con expresión completa

### Archivos a crear
- `AmoLean/Protocols/Poseidon/MatExpr.lean`

---

## Paso 4: Verificación

### Objetivo
Validar correctitud de código generado.

### Checklist
- [ ] Differential fuzzing: `poseidon2_spec` vs C generado
- [ ] Benchmark vs implementación Rust de referencia
- [ ] Prueba formal: `eval(poseidon2_matexpr) = poseidon2_spec`
- [ ] Documentar cualquier `sorry`

### Framework de testing
Usar framework de fuzzing de Fase 6.

---

## Paso 5: Integración

### Objetivo
Conectar Poseidon2 con el resto del sistema.

### Checklist
- [ ] MerkleTree usando Poseidon2
- [ ] Fiat-Shamir usando Poseidon2
- [ ] Conectar con FRI para commits completos
- [ ] Tests end-to-end

### Archivos a crear/modificar
- `AmoLean/Protocols/MerkleTree.lean`
- `AmoLean/FRI/Commit.lean` (actualizar)

---

## Registro de Cambios

| Fecha | Cambio | Autor |
|-------|--------|-------|
| 2026-01-26 | Documentación inicial creada | Equipo |
| 2026-01-26 | Paso 0.5: Spec.lean (sin Mathlib, compila rápido) | Equipo |
| 2026-01-26 | Paso 1.0: head/tail añadidos a VecExpr | Equipo |
| 2026-01-26 | Paso 1.1: ElemOp y elemwise añadidos a MatExpr | Equipo |
| 2026-01-26 | Paso 1.2: elemwise en MatEGraph como barrera opaca | Equipo |
| 2026-01-26 | Paso 1.3: sbox kernel, lowering, evaluadores actualizados | Equipo |
| 2026-01-26 | Paso 1.5: Tests de sanidad (4/4 pasan) - Ready for CodeGen | Equipo |

---

## Notas y Observaciones

*Añadir notas durante la implementación...*

---

## Bloqueos Actuales

*Ninguno por ahora*

---

## Decisiones Tomadas

Ver ADRs en este directorio:
- [ADR-001-elemwise.md](ADR-001-elemwise.md)
- [ADR-002-partial-rounds.md](ADR-002-partial-rounds.md)
- [ADR-003-codegen-simd.md](ADR-003-codegen-simd.md)
