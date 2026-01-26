# Progreso de Implementación - Fase Poseidon

## Estado General

| Paso | Descripción | Estado | Notas |
|------|-------------|--------|-------|
| 0 | Prerrequisitos (ZModSIMD) | Parcial | ZModSIMD existe, falta pow_chain |
| 0.5 | Especificación ejecutable | **En progreso** | Spec.lean + Params/BN254.lean creados |
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
| 2026-01-26 | Paso 0.5: Spec.lean y Params/BN254.lean | Equipo |

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
