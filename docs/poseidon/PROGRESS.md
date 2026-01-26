# Progreso de Implementación - Fase Poseidon

## Estado General

| Paso | Descripción | Estado | Notas |
|------|-------------|--------|-------|
| 0 | Prerrequisitos (ZModSIMD) | Pendiente | |
| 0.5 | Especificación ejecutable | Pendiente | |
| 1 | Extensión IR (elemwise) | Pendiente | |
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
- [ ] Definir `PoseidonParams` structure
- [ ] Cargar parámetros BN254 (MDS, round constants)
- [ ] Implementar `poseidon2_spec : Vec t Field → Vec t Field`
- [ ] Validar contra test vectors del paper Poseidon2
- [ ] Documentar cualquier discrepancia

### Archivos a crear
- `AmoLean/Protocols/Poseidon/Spec.lean`
- `AmoLean/Protocols/Poseidon/Params/BN254.lean`

### Test Vectors
Fuente: Paper Poseidon2, Apéndice

---

## Paso 1: Extensión del IR

### Objetivo
Añadir constructor `elemwise` a MatExpr.

### Checklist
- [ ] Definir `ElemOp` (pow, custom)
- [ ] Añadir `elemwise` a `MatExpr`
- [ ] Actualizar `eval` para `elemwise`
- [ ] Añadir reglas E-Graph (fusión, constant folding)
- [ ] Verificar que E-Graph no explota (métricas)
- [ ] Tests unitarios

### Archivos a modificar
- `AmoLean/Sigma/MatExpr.lean`
- `AmoLean/EGraph/Rules.lean`

### Reglas E-Graph
```lean
elemwise f (elemwise g x) → elemwise (f ∘ g) x
elemwise op (const c) → const (apply op c)
-- NO: elemwise (pow 5) x → x * x * x * x * x
```

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
