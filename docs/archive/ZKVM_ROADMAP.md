# AMO-Lean: Roadmap hacia Integración zkVM

**Fecha**: 2026-01-28
**Versión**: 2.0 (Post-Poseidon)

---

## Resumen Ejecutivo

AMO-Lean es un compilador verificado de expresiones matemáticas a código optimizado. El objetivo es que AMO-Lean pueda ser utilizado como componente de una zkVM, tanto para **generación offline de pruebas** como para **verificación en tiempo de ejecución**.

### Estado Actual

| Componente | Estado | Uso en zkVM |
|------------|--------|-------------|
| FRI Protocol (Prover + Verifier) | ✅ **Completo** | Verificación de low-degree |
| Poseidon2 Hash (BN254) | ✅ **Completo** | Merkle commits, Fiat-Shamir |
| Campo Genérico (`FRIField F`) | ✅ **Completo** | Multi-campo |
| E-Graph + Saturation | ✅ **Completo** | Optimización de expresiones |
| CodeGen C/AVX2 | ✅ **Completo** | Prover nativo |

### Próximas Fases

| Prioridad | Fase | Objetivo | Impacto en zkVM |
|-----------|------|----------|-----------------|
| **#1** | Optimización de Performance | 10-100x speedup | Provers viables |
| **#2** | Más Campos y Hashes | Goldilocks, BLAKE3 | Compatibilidad |
| **#3** | Verificación Formal | Proofs de soundness | Confianza |
| **#4** | API de Integración | Interfaz para zkVMs | Usabilidad |

---

## Fase 1: Optimización de Performance (Prioridad #1)

### 1.1 Backend CUDA/GPU

**Problema**: BN254/Poseidon2 toma ~113s para degree 4096. Para trazas de zkVM reales (millones de filas), esto es inaceptable.

**Solución**: Backend GPU para operaciones masivamente paralelas.

**Entregables**:
1. `GPUExpr` IR con anotaciones de memoria (global/shared/register)
2. Lowering de MatExpr → CUDA kernels
3. Montgomery multiplication optimizada para GPU
4. Merkle tree paralelo

**Métricas de éxito**:
| Operación | CPU Actual | GPU Target |
|-----------|------------|------------|
| FRI fold (deg 4096) | ~113s | <5s |
| Merkle tree (1M leaves) | ? | <1s |
| Poseidon2 batch | ~350 hashes/s | >100K hashes/s |

**Obstáculos técnicos**:
- Aritmética modular 256-bit en GPU (no tiene instrucciones nativas)
- Coalesced memory access para Merkle trees
- Bank conflicts en shared memory

**Referencias**:
- "Montgomery Multiplication on GPUs" (Emmart et al.)
- CUDA C Programming Guide, Chapters 5-6
- Volkov "Better Performance at Lower Occupancy"

### 1.2 AVX-512 Backend

**Para CPUs con soporte AVX-512**: 2x speedup adicional sobre AVX2.

**Entregables**:
1. Detectar AVX-512 en compilación
2. 512-bit vector operations
3. Mask registers para operaciones condicionales

**Beneficio**: Mejora incremental en hardware Intel/AMD moderno.

### 1.3 Paralelización Multi-core

**Problema**: El prover actual es single-threaded.

**Solución**:
- Merkle tree construction paralelo (cada subárbol independiente)
- FRI rounds paralelizables por query
- Poseidon2 batch hashing

**Entregables**:
1. `async` prover API
2. Thread pool para Merkle construction
3. Batch Poseidon2 con paralelismo

---

## Fase 2: Más Campos y Hashes (Prioridad #2)

### 2.1 Campo Goldilocks

**Motivación**: STARKs (Plonky3, RISC0) usan campo Goldilocks (p = 2^64 - 2^32 + 1).

**Estado actual**: Placeholder en `AmoLean/FRI/Fields/Goldilocks.lean`

**Pendiente**:
1. Obtener parámetros Poseidon2 para Goldilocks (t=12, α=7)
2. Implementar aritmética de campo optimizada (usa propiedades de p)
3. Validar contra implementaciones de referencia

**Beneficio**: Compatibilidad con ecosistema STARK.

### 2.2 Hash BLAKE3

**Motivación**: Algunos sistemas usan BLAKE3 en lugar de Poseidon por velocidad.

**Entregables**:
1. `CryptoHash` instance para BLAKE3
2. Wrapper sobre implementación C optimizada
3. Benchmarks comparativos

**Trade-off**: BLAKE3 es más rápido pero no es algebraic-friendly (verificación en-circuit más cara).

### 2.3 Rescue-Prime

**Motivación**: Alternativa a Poseidon usada en algunos sistemas.

**Entregables**:
1. Especificación ejecutable en Lean
2. `CryptoHash` instance
3. Parámetros para BN254 y Goldilocks

---

## Fase 3: Verificación Formal (Prioridad #3)

### 3.1 Soundness del FRI Protocol

**Estado actual**: Tests empíricos (E2E, soundness tests).

**Objetivo**: Pruebas formales en Lean.

**Entregables**:
1. `theorem fri_soundness`: Si el verifier acepta, el polinomio es low-degree con alta probabilidad
2. `theorem merkle_binding`: No se puede abrir un commitment a dos valores diferentes
3. `theorem fiat_shamir_security`: Transcript replay produce mismos challenges

**Dificultad**: Requiere formalizar probabilidad y argument de reducción.

### 3.2 Correctness de CodeGen

**Estado actual**: Differential fuzzing valida output.

**Objetivo**: Prueba de que código C generado preserva semántica.

**Entregables**:
1. `theorem codegen_correct : ∀ e, eval (exprToC e) = denote e`
2. Semántica operacional de C subset
3. Preservación de propiedades aritméticas

### 3.3 Ausencia de Information Leakage

**Objetivo**: Probar que el prover no filtra información del witness.

**Entregables**:
1. Análisis de flujo de información
2. `theorem zero_knowledge`: Output del prover es simulable

---

## Fase 4: API de Integración zkVM (Prioridad #4)

### 4.1 Trace Verification Interface

**Caso de uso**: Una zkVM genera una traza de ejecución. AMO-Lean verifica que la traza satisface constraints.

**API propuesta**:
```lean
/-- Constraint system for zkVM trace verification -/
structure ConstraintSystem (F : Type) [FRIField F] where
  /-- Number of columns in the trace -/
  width : Nat
  /-- Constraints as polynomial equations over trace columns -/
  constraints : List (TracePolynomial F)
  /-- Boundary constraints (initial/final values) -/
  boundaries : List (BoundaryConstraint F)

/-- Verify a trace satisfies all constraints -/
def verifyTrace {F : Type} [FRIField F] [CryptoHash F]
    (system : ConstraintSystem F)
    (trace : Array (Array F))  -- rows × columns
    : IO (VerifyResult F)
```

### 4.2 Commitment Scheme Interface

**Caso de uso**: zkVM necesita commitments Merkle con hash específico.

**API propuesta**:
```lean
/-- Generic polynomial commitment -/
structure PolyCommitment (F : Type) where
  root : F
  degree : Nat

/-- Commit to a polynomial (its evaluations) -/
def commit {F : Type} [FRIField F] [CryptoHash F]
    (evaluations : Array F)
    : IO (PolyCommitment F × MerkleTree F)

/-- Open commitment at specific points -/
def openAt {F : Type} [FRIField F] [CryptoHash F]
    (commitment : PolyCommitment F)
    (tree : MerkleTree F)
    (indices : List Nat)
    : IO (List (F × MerkleProof F))
```

### 4.3 Prover/Verifier Library

**Caso de uso**: zkVM integra AMO-Lean como biblioteca.

**Entregables**:
1. Header-only C library generada
2. Rust bindings via FFI
3. Python bindings para prototipado
4. Documentación de integración

### 4.4 Runtime vs Offline Mode

**Offline (Prover)**:
- Máxima optimización (GPU, paralelo)
- Puede tomar minutos/horas
- Genera proof compacto

**Runtime (Verifier)**:
- Debe ser rápido (< 1s)
- Código simple, auditable
- Puede correr en constrained environments

**API diferenciada**:
```lean
/-- Offline prover configuration -/
structure ProverConfig where
  useGPU : Bool := true
  parallelism : Nat := 8
  optimizationLevel : Nat := 3

/-- Runtime verifier configuration -/
structure VerifierConfig where
  /-- Strict mode: reject any anomaly -/
  strict : Bool := true
  /-- Log level for debugging -/
  logLevel : Nat := 0
```

---

## Timeline Estimado

| Fase | Componente | Duración | Dependencias |
|------|------------|----------|--------------|
| 1.1 | CUDA Backend | 3-4 meses | - |
| 1.2 | AVX-512 | 2-3 semanas | - |
| 1.3 | Multi-core | 3-4 semanas | - |
| 2.1 | Goldilocks | 2-3 semanas | Parámetros externos |
| 2.2 | BLAKE3 | 1-2 semanas | - |
| 2.3 | Rescue-Prime | 3-4 semanas | - |
| 3.1 | FRI Soundness | 2-3 meses | - |
| 3.2 | CodeGen Correctness | 1-2 meses | - |
| 4.1 | Trace Verification | 1 mes | - |
| 4.2 | Commitment API | 2 semanas | - |
| 4.3 | Library Bindings | 1 mes | - |

**Total estimado**: 8-12 meses para completar todas las fases.

---

## Priorización para zkVM

Si el objetivo es **usar AMO-Lean en una zkVM de producción**, recomiendo:

### Corto plazo (1-2 meses)
1. **Multi-core parallelization** - Speedup inmediato con bajo esfuerzo
2. **Trace Verification API** - Interfaz clara para integración
3. **Goldilocks field** - Compatibilidad con STARKs

### Mediano plazo (3-6 meses)
1. **CUDA backend** - 10-100x speedup para provers
2. **FRI soundness proofs** - Confianza formal

### Largo plazo (6-12 meses)
1. **Full formal verification** - Auditable y trustless
2. **Production library** - Bindings, docs, testing

---

## Referencias

### Papers Fundamentales
1. Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
2. Grassi et al. "Poseidon2: A New Hash Function for Zero-Knowledge Proof Systems"
3. Willsey et al. "egg: Fast and Extensible Equality Saturation"

### Implementaciones de Referencia
1. [HorizenLabs/poseidon2](https://github.com/HorizenLabs/poseidon2) - Rust
2. [Plonky3](https://github.com/Plonky3/Plonky3) - Goldilocks STARKs
3. [RISC0](https://github.com/risc0/risc0) - zkVM usando STARKs

### Recursos GPU
1. CUDA C Programming Guide
2. "Montgomery Multiplication on GPUs" (Emmart et al.)
3. Volkov "Better Performance at Lower Occupancy"

---

*Última actualización: 2026-01-28*
