# Insights: SIMD Codegen for Finite Field Arithmetic via AVX2/NEON

**Fecha**: 2026-03-20
**Dominio**: lean4
**Estado del objeto**: upgrade (infraestructura escalar existente, SIMD por agregar)

## 1. Análisis del Objeto de Estudio

AMO-Lean tiene un motor de e-graph verificado (14,700 LOC, 0 sorry) con codegen escalar a C y Rust. La infraestructura SIMD existe parcialmente:

- `Sigma/SIMD.lean` (264 LOC): genera butterflies AVX para doubles (pipeline SPIRAL), NO para campos finitos u32
- `EnhancedCostModel.lean`: modelo de costos con SIMD lanes (NEON=4, AVX2=8) pero solo como metadata
- `MixedExprToStmt.lean` + `MixedExprToRust.lean`: codegen escalar completo (17 constructores MixedExpr)
- `C_AVX512/Basic.lean`: stub comentado (39 LOC)
- `BitVecBridge.lean` (718 LOC, 41 theorems): bridge Nat↔BV ya probado — base para SIMD semantics

**Plonky3 SIMD reference** (local en `verification/plonky3/plonky3_source/monty-31/src/`):
- `x86_64_avx2/utils.rs`: Montgomery REDC vectorizado con `_mm256_mul_epu32`, `_mm256_add_epi32`, `_mm256_sub_epi32`
- `aarch64_neon/utils.rs`: NEON con `vmull_u32`, `vmlsq_n_u32`, `vsraq_n_u32`
- Ambos usan **lazy reduction** en butterflies (Harvey-style)

### Keywords
AVX2, NEON, SIMD intrinsics, finite field arithmetic, BabyBear, Montgomery REDC, Solinas fold, NTT butterfly, FRI fold, vectorization, codegen, MixedExpr, u32 lane packing, lazy reduction

### Gaps Identificados
1. **No hay MixedExpr → SIMD codegen**: el path MixedExpr → C/Rust es escalar
2. **No hay reglas de reescritura SIMD**: el e-graph no sabe que 8 operaciones paralelas = 1 instrucción SIMD
3. **Plonky3 usa Montgomery en SIMD, no Solinas fold**: la comparación directa requiere adaptar el fold a intrinsics
4. **FRI fold SIMD**: no hay papers ni implementaciones de FRI fold vectorizado en la biblioteca

## 2. Lecciones Aplicables

### Lecciones Críticas

| ID | Lección | Impacto |
|---|---------|---------|
| **L-567** | native_decide timeout en campos grandes — usar #eval oracle | No intentar verificar SIMD con native_decide |
| **L-692** | Butterfly arithmetic: Nat.add_mod + div_add_mod + omega | Patrón reutilizable para probar SIMD butterfly correctness |
| **L-310** | Three-typeclass codegen architecture (CodeGenerable, BackendEmitter, CodeGenSound) | Agregar SIMDBackendEmitter como nueva instancia |
| **L-297** | Three-part contract: fuel + result semantics + frame | Aplicar a SIMD codegen: fuel=N_lanes, result=lane-wise eval, frame=register preservation |
| **L-614** | Operator-level compat, NO syntactic equality para codegen | No probar que el string C_SIMD = string C_scalar; probar que evalúan igual |
| **L-513** | Compositional pipeline: probar cada stage preserva invariante | SIMD pipeline: vectorize → emit intrinsics → verify lane-wise |

### Anti-patrones a Evitar
- **Syntactic codegen equality** (L-614): No probar `emitSIMD(x) == emitScalar(x)` como strings
- **native_decide en campos grandes** (L-567): Verificar con #eval, no con decide
- **Monolithic soundness** (L-311): Descomponer en fuel + result + frame
- **Vectorizar Goldilocks intra-hash** (ADR-004): 64-bit mul en AVX2 = 4-way split, 1.33x MÁS LENTO que escalar

## 3. Bibliografía Existente Relevante

### Documentos Clave

| Paper | Carpeta | Relevancia |
|-------|---------|-----------|
| **van der Hoeven & Lecerf (2024)** "Implementing NTTs" | ntt/ | Codelets + Kronecker segmentation + auto-generation para AVX/AVX-512/NEON |
| **Seiler (2018)** "Faster AVX2 NTT for Ring-LWE" | ntt/ | Modified Montgomery reduction para AVX2 integer, lazy reduction, 4.2x speedup |
| **Longa & Naehrig (2016)** "Speeding up NTT" | ntt/ | K-RED modular reduction para p = k·2^m + 1, AVX2 benchmarks |
| **Almeida et al. (2023)** "Formally Verifying Kyber Episode IV" | verificacion/ | **CRÍTICO**: Primera NTT AVX2 verificada formalmente (Jasmin/EasyCrypt) |
| **Polubelova et al. (2020)** "HACLxN: Verified Generic SIMD Crypto" | verificacion/ | Metodología F*/Low* para SIMD verificado multi-plataforma (NEON/AVX/AVX-512) |
| **Trieu (2025)** "Formally Verified NTT" | verificacion/ + ntt/ | NTT formalizada en Rocq + code extraction a C verificado |
| **Fortin et al. (2020)** "High Performance SIMD Modular Arithmetic" | cuda-gpu/ | Patrones SIMD para aritmética modular en campos finitos |

### Gaps Bibliográficos
1. No hay papers sobre **BabyBear/Goldilocks SIMD** específicamente (solo Kyber q=3329)
2. No hay papers sobre **FRI fold + SIMD**
3. No hay papers sobre **Lean 4 → SIMD intrinsics codegen**
4. Cobertura NEON débil (solo van der Hoeven 2024)

## 4. Estrategias y Decisiones Previas

### Estrategia Ganadora: SIMD Decision Tree

```
If field_bit_width ≤ 32 (BabyBear, Mersenne31):
  ✓ Intra-hash SIMD viable — 8 elements per YMM register
  → AVX2: _mm256_add_epi32, _mm256_mullo_epi32
  → NEON: vadd_u32, vmul_u32

Else if field_bit_width = 64 (Goldilocks):
  ✗ Intra-hash SIMD NOT worth it — 64-bit mul = 4-way split overhead
  → Batch SIMD: process 4 independent hashes per register

Else if field_bit_width > 64 (BN254):
  ✗ Impossible — 1 element fills entire YMM register
  → Batch SIMD: one limb per hash per register
```

**Implicación**: BabyBear (31-bit) es el MEJOR candidato para SIMD intra-hash. 8 BabyBear elements en un registro YMM de 256-bit.

### Estrategia Ganadora: Skeleton + Kernel (DD-024)

| Componente | Implementación | Verificación |
|------------|---------------|-------------|
| **Loop structure** (NTT stages, stride) | Manual C | No verificado |
| **Kernel** (butterfly, reduction) | Generado desde Lean | Formalmente probado |
| **Composición** | Bridge theorem | Soundness proof |

**Implicación para SIMD**: El kernel SIMD (butterfly vectorizado) es generado y verificado. El loop structure (cómo iterar sobre los datos) es manual.

### Benchmark de Referencia: AMO-Lean vs Plonky3

| Operación | AMO-Lean | Plonky3 | Resultado |
|-----------|----------|---------|-----------|
| BabyBear reduction | 0.33 ns | 0.76 ns | **AMO-Lean 56.7% faster** |
| BabyBear multiply | 4.45 ns | 5.31 ns | **AMO-Lean 16.1% faster** |
| BabyBear butterfly (Harvey) | 5.46 ns | 6.56 ns | **AMO-Lean 16.8% faster** |
| NTT N=4096 | 109.5 µs | 65.9 µs | Plonky3 1.66x faster (SIMD) |

**Insight clave**: AMO-Lean gana en operaciones escalares individuales, pierde en NTT completa porque Plonky3 usa SIMD. Cerrar este gap requiere SIMD codegen.

### Errores Evitados
- **Vectorizar Goldilocks mul intra-hash**: AVX2 64-bit mul = 4-way split = 1.33x más lento que escalar (ADR-004)
- **Derivar loops NTT del e-graph**: Demasiado complejo; separar skeleton (manual) + kernel (generado) (DD-024)
- **Nat.omega en aritmética unbounded**: Timeout; usar cancel_left_of_coprime + bounds (Fase 17)

## 5. Nueva Bibliografía Encontrada

Sección omitida (--skip-online)

## 6. Insights de Nueva Bibliografía

Sección omitida (sin descargas nuevas)

## 7. Síntesis de Insights

### Hallazgos Clave

1. **BabyBear es el candidato ideal para SIMD intra-hash**: 31-bit field → 8 elements per YMM → true vectorización. Goldilocks no vale la pena (64-bit mul overhead).

2. **Plonky3 AVX2 source está local y extractable**: `monty-31/src/x86_64_avx2/utils.rs` tiene ~280 LOC con todas las intrinsics documentadas. Se puede usar como referencia directa.

3. **La ventaja escalar de AMO-Lean (56.7% en reduction) desaparece a nivel NTT**: Plonky3 es 1.66x más rápido en NTT N=4096 gracias a SIMD. Con SIMD codegen, AMO-Lean recuperaría esa ventaja.

4. **No hay papers sobre FRI fold SIMD**: Es trabajo original. El FRI fold es una operación de evaluación polinomial que puede vectorizarse lane-wise (cada lane procesa un punto de evaluación independiente).

5. **BitVecBridge ya cubre Nat↔BV isomorphism** (718 LOC, 41 theorems): Base para probar correctness de operaciones SIMD lane-wise sin re-probar aritmética modular.

6. **La estrategia Skeleton + Kernel es la correcta para SIMD**: Generar solo el kernel SIMD (butterfly + reduce), el loop structure es manual C. Esto reduce el scope del codegen SIMD a ~200 LOC.

7. **Almeida et al. (2023) verifican AVX2 NTT para Kyber en Jasmin/EasyCrypt**: Precedente real de SIMD verificado formalmente. Adaptable a BabyBear (diferente primo, misma estructura).

8. **HACLxN (2020) tiene la metodología para SIMD multi-plataforma**: F*/Low* con proof reuse entre scalar y vectorized variants. Aplicable a nuestro caso: probar scalar, derivar SIMD.

### Riesgos Identificados

| Riesgo | Impacto | Mitigación |
|--------|---------|-----------|
| AVX2 `_mm256_mullo_epi32` tiene throughput limitado (2 cycles en Skylake) | Mul puede ser bottleneck | Usar lazy reduction (Harvey) para evitar muls innecesarios |
| NEON 32-bit mul tiene diferente latency que AVX2 | Code path diverge entre targets | Abstraer intrinsics detrás de SIMDConfig (como Sigma/SIMD.lean) |
| Montgomery REDC en SIMD es diferente a Solinas fold en SIMD | Plonky3 usa Montgomery SIMD; nosotros usamos Solinas fold SIMD — comparación no es apple-to-apple | Implementar AMBOS y benchmarkear |
| FRI fold SIMD es trabajo original sin referencia | Podría tener edge cases no anticipados | Prototipar primero en C, luego generar desde Lean |

### Recomendaciones para Planificación

**Fase 1 (1 día): MixedExprToSIMD.lean — BabyBear AVX2**
- Mapear los 7 MixedExpr constructores relevantes (add, mul, shift, and, sub, const, witness) a intrinsics `epi32`
- Solinas fold SIMD: `vpsrld` + `vpmulld` + `vpand` + `vpaddd`
- Template: misma estructura que `exprToRust` pero con `__m256i` types
- ~200 LOC

**Fase 2 (1 día): Butterfly SIMD + Benchmark**
- 8 butterflies BabyBear en paralelo con AVX2
- Benchmark contra Plonky3's `monty-31/src/x86_64_avx2/packing.rs`
- Verificar correctness con #eval oracle (no formal proof aún)
- ~150 LOC codegen + ~100 LOC benchmark

**Fase 3 (1 día): NEON backend + FRI fold SIMD**
- NEON intrinsics para ARM (uint32x4_t, 4 lanes)
- FRI fold: vectorizar `fold(poly, alpha, domain)` lane-wise
- ~200 LOC

**Fase 4 (opcional, 1 día): Formal verification del SIMD kernel**
- Probar que SIMD kernel evalúa lane-wise igual que escalar
- Usar BitVecBridge existente como base
- ~100 LOC proofs

### Recursos Prioritarios

1. **Plonky3 AVX2 source**: `verification/plonky3/plonky3_source/monty-31/src/x86_64_avx2/utils.rs` — todas las intrinsics con comments
2. **Seiler (2018)**: "Faster AVX2 NTT" — modified Montgomery + lazy reduction para integer AVX2
3. **Almeida et al. (2023)**: "Formally Verifying Kyber" — methodology para verificar SIMD NTT
4. **AMO-Lean `Sigma/SIMD.lean`**: Patrón existente para SIMD codegen (adaptar de doubles a u32)
5. **AMO-Lean `BitVecBridge.lean`**: 41 theorems bridge Nat↔BV para verificación de SIMD lane ops

## 8-10. Secciones omitidas (--depth standard)
