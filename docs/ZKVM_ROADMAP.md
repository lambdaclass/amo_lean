# AMO-Lean: Ruta de Trabajo hacia zkVM

## Documento de Planificación Técnica

**Versión**: 1.0
**Fecha**: Enero 2026
**Autores**: Equipo AMO-Lean

---

## Resumen Ejecutivo

Este documento presenta la planificación detallada para evolucionar AMO-Lean desde su estado actual (compilador FRI verificado) hacia una herramienta capaz de generar primitivos criptográficos optimizados para zkVMs de producción.

**Priorización basada en impacto para zkVM:**

| Prioridad | Componente | Tiempo | Impacto |
|-----------|------------|--------|---------|
| #1 CRÍTICO | Poseidon/Rescue Hash | 6-10 semanas | Habilita recursión eficiente |
| #2 ALTO | Backend CUDA/GPU | 3-6 meses | 10-100x speedup en proof generation |
| #3 MEDIO | Variantes AVX-512 | 2-3 semanas | 2x speedup incremental |
| #4 BAJO | FRI Query Phase | 4-6 semanas | Completa el protocolo |

---

## 1. Poseidon/Rescue Hash Integration

### 1.1 Contexto y Motivación

Poseidon es un hash "ZK-friendly" diseñado para ser eficiente dentro de circuitos aritméticos. Es el estándar de facto para:
- Recursión de pruebas (una prueba verifica otra)
- Árboles de Merkle en zkVMs
- Compromisos de estado

**Por qué es crítico**: Sin Poseidon optimizado, la recursión de pruebas es prohibitivamente lenta, limitando la escalabilidad de cualquier zkVM.

### 1.2 Desafío Técnico Principal

Poseidon combina operaciones lineales y no-lineales:

```
Poseidon_round(state) = MDS × (state + round_constants)^α
```

Donde:
- `MDS`: Matriz de difusión (Maximum Distance Separable) — **LINEAL**, compatible con Kronecker
- `^α`: S-box, típicamente x⁵ — **NO LINEAL**, rompe nuestra representación actual

**El problema**: Nuestra arquitectura `MatExpr` está optimizada para operaciones lineales (productos Kronecker). Las S-boxes requieren extender el IR.

### 1.3 Plan de Implementación por Fases

#### Fase 1.1: Extensión de MatExpr (Semanas 1-2)

**Objetivo**: Añadir soporte para operaciones element-wise no-lineales.

**Entregables**:
```lean
-- Nuevo constructor en MatExpr
inductive MatExpr (α : Type) : Nat → Nat → Type where
  | ...existing constructors...
  | elemwise : (Expr α → Expr α) → MatExpr α n n
  | diagMap : (Expr α → Expr α) → VecExpr α n → MatExpr α n n
```

**Obstáculos técnicos**:
1. **Preservación de tipos dependientes**: El constructor `elemwise` debe preservar dimensiones
   - *Técnica*: Usar índices fantasma (phantom indices) como en Xi & Pfenning
   - *Bibliografía*: "Dependent Types in Practical Programming" (POPL 1999)

2. **Interacción con E-Graph**: Las operaciones no-lineales complican el e-matching
   - *Técnica*: Tratar `elemwise` como nodo opaco, sin expansión
   - *Bibliografía*: Willsey et al. "egg: Fast and Extensible Equality Saturation"

**Testing Fase 1.1**:
- [ ] Unit tests: `elemwise` preserva dimensiones
- [ ] Property test: `elemwise id = identity`
- [ ] Integration test: Composición con operaciones lineales

#### Fase 1.2: Implementación de Poseidon Round (Semanas 3-4)

**Objetivo**: Implementar una ronda de Poseidon usando el nuevo IR.

**Entregables**:
```lean
/-- Constantes de Poseidon para estado de tamaño t -/
structure PoseidonParams (t : Nat) where
  mds : Matrix t t           -- Matriz MDS
  roundConstants : Array (Vec t)  -- Constantes por ronda
  fullRounds : Nat           -- Rondas completas
  partialRounds : Nat        -- Rondas parciales
  alpha : Nat := 5           -- Exponente S-box

/-- Una ronda completa de Poseidon -/
def poseidonFullRound (params : PoseidonParams t) (round : Nat)
    (state : MatExpr α t 1) : MatExpr α t 1 :=
  let withConstants := MatExpr.add state (params.roundConstants.get! round)
  let afterSbox := MatExpr.elemwise (fun x => Expr.pow x params.alpha) withConstants
  MatExpr.matmul params.mds afterSbox
```

**Obstáculos técnicos**:
1. **Matrices MDS grandes**: Para t=12 (común en zkVMs), la matriz tiene 144 elementos
   - *Técnica*: Representación sparse si hay estructura, o precomputación
   - *Bibliografía*: Grassi et al. "Poseidon: A New Hash Function for Zero-Knowledge Proof Systems"

2. **Overflow en campos finitos**: x⁵ puede causar overflow
   - *Técnica*: Usar representación Montgomery para aritmética modular
   - *Bibliografía*: Montgomery "Modular Multiplication Without Trial Division"

**Testing Fase 1.2**:
- [ ] Test vectors oficiales de Poseidon
- [ ] Comparación con implementación de referencia (Circom)
- [ ] Fuzzing diferencial contra poseidon-rs

#### Fase 1.3: Optimización de S-boxes (Semanas 5-6)

**Objetivo**: Optimizar x⁵ para diferentes backends.

**Entregables**:
```lean
/-- Estrategias de exponenciación -/
inductive SboxStrategy where
  | naive      : SboxStrategy  -- x * x * x * x * x
  | squareChain : SboxStrategy  -- x² → x⁴ → x⁵ (3 muls)
  | lookupTable : Nat → SboxStrategy  -- Tabla precalculada (para campos pequeños)

/-- Seleccionar estrategia óptima -/
def selectSboxStrategy (fieldSize : Nat) (simdWidth : Nat) : SboxStrategy :=
  if fieldSize ≤ 2^16 then SboxStrategy.lookupTable fieldSize
  else SboxStrategy.squareChain
```

**Obstáculos técnicos**:
1. **Trade-off memoria vs computación**: Lookup tables usan memoria pero son O(1)
   - *Técnica*: Cost model que considera cache sizes
   - *Bibliografía*: Agner Fog "Instruction Tables" (latencias reales de CPU)

2. **SIMD para exponenciación**: AVX2 no tiene instrucción de potencia
   - *Técnica*: Vectorizar la cadena de cuadrados
   - *Bibliografía*: Intel Intrinsics Guide

**Testing Fase 1.3**:
- [ ] Benchmark: naive vs squareChain vs lookupTable
- [ ] Verificar equivalencia numérica entre estrategias
- [ ] Profile con perf/vtune para cache misses

#### Fase 1.4: Full Poseidon + CodeGen (Semanas 7-9)

**Objetivo**: Poseidon completo con generación de código C optimizado.

**Entregables**:
- `poseidonHash : PoseidonParams → Array FieldElement → FieldElement`
- `generatePoseidonC : PoseidonParams → String` (código C)
- Proof anchors para cada componente

**Obstáculos técnicos**:
1. **Rondas parciales**: Poseidon usa rondas parciales (solo una S-box) para eficiencia
   - *Técnica*: Modelar como caso especial de `elemwise`
   - *Bibliografía*: Poseidon paper, Appendix B

2. **Padding y dominio de separación**: Hash debe manejar inputs de longitud variable
   - *Técnica*: Sponge construction estándar
   - *Bibliografía*: NIST SP 800-185 (SHA-3 derived functions)

**Testing Fase 1.4**:
- [ ] Full test suite contra implementaciones canónicas
- [ ] Fuzzing con inputs aleatorios de varias longitudes
- [ ] Verificar proof anchors contra especificación

#### Fase 1.5: Verificación Formal (Semana 10)

**Objetivo**: Teoremas que conectan implementación con especificación.

**Entregables**:
```lean
theorem poseidon_permutation_correct (params : PoseidonParams t) (input : Vec t) :
  evalPoseidon params input = reference_poseidon params input

theorem poseidon_sponge_absorb (params : PoseidonParams t) (msg : Array FieldElement) :
  spongeAbsorb params msg satisfies_sponge_security
```

**Obstáculos técnicos**:
1. **Propiedades criptográficas difíciles de probar**: Resistencia a colisiones requiere asunciones
   - *Técnica*: Probar propiedades estructurales, no criptográficas
   - *Bibliografía*: Barthe et al. "Computer-Aided Cryptographic Proofs"

**Testing Fase 1.5**:
- [ ] Teoremas compilan sin sorry (o con sorry documentados)
- [ ] Differential fuzzing: Lean eval == C binary

---

## 2. Backend CUDA/GPU

### 2.1 Contexto y Motivación

La industria de ZK se está moviendo hacia proof generation en GPUs:
- Granjas de GPUs como servicio (proof marketplaces)
- Paralelismo masivo: miles de hilos vs decenas en CPU
- Potencial de 10-100x speedup

### 2.2 Desafío Técnico Principal

Las GPUs tienen una jerarquía de memoria diferente:

```
CPU: RAM ←→ L3 ←→ L2 ←→ L1 ←→ Registros

GPU: Global Memory (lenta, grande)
         ↕
     Shared Memory (rápida, pequeña, por bloque)
         ↕
     Registers (muy rápida, por hilo)
```

Nuestro IR actual no modela movimiento de datos entre niveles de memoria.

### 2.3 Plan de Implementación por Fases

#### Fase 2.1: Diseño de GPUExpr IR (Semanas 1-3)

**Objetivo**: Nuevo IR que modela jerarquía de memoria GPU.

**Entregables**:
```lean
/-- Niveles de memoria GPU -/
inductive MemLevel where
  | global   : MemLevel  -- DDR, alta latencia
  | shared   : MemLevel  -- Por bloque, baja latencia
  | register : MemLevel  -- Por hilo

/-- Expresiones GPU con anotaciones de memoria -/
inductive GPUExpr where
  | load   : MemLevel → Address → GPUExpr
  | store  : MemLevel → Address → GPUExpr → GPUExpr
  | compute : Kernel → List GPUExpr → GPUExpr
  | sync   : GPUExpr  -- __syncthreads()
  | parallel : Nat → Nat → GPUExpr → GPUExpr  -- gridDim, blockDim
```

**Obstáculos técnicos**:
1. **Coalesced memory access**: Accesos a global memory deben ser coalescentes
   - *Técnica*: Análisis de patrones de acceso en tiempo de compilación
   - *Bibliografía*: CUDA C Programming Guide, Chapter 5

2. **Bank conflicts en shared memory**: 32 banks, accesos al mismo bank serializan
   - *Técnica*: Padding automático de arrays en shared memory
   - *Bibliografía*: "Optimizing Parallel Reduction in CUDA" (Harris, Nvidia)

**Testing Fase 2.1**:
- [ ] Unit tests: GPUExpr bien formado
- [ ] Análisis estático de coalescing
- [ ] Simulación de bank conflicts

#### Fase 2.2: Lowering MatExpr → GPUExpr (Semanas 4-7)

**Objetivo**: Transformar operaciones matriciales a kernels GPU.

**Entregables**:
```lean
/-- Convertir producto Kronecker a kernel paralelo -/
def lowerKronToGPU (A : MatExpr m n) (B : MatExpr p q) : GPUExpr :=
  GPUExpr.parallel
    (gridSize := m * p)
    (blockSize := 256)
    (GPUExpr.compute kroneckerKernel [lowerToGPU A, lowerToGPU B])
```

**Obstáculos técnicos**:
1. **Tiling para shared memory**: Matrices grandes no caben en shared
   - *Técnica*: Algoritmos de tiled matrix multiplication
   - *Bibliografía*: Volkov "Better Performance at Lower Occupancy"

2. **Sincronización entre bloques**: GPU no tiene sync global fácil
   - *Técnica*: Múltiples kernel launches para fases
   - *Bibliografía*: "Cooperative Groups" (CUDA 9+)

**Testing Fase 2.2**:
- [ ] Correctness: GPU result == CPU result
- [ ] Performance: Medir GFLOPS, memory bandwidth
- [ ] Occupancy analysis con nvprof

#### Fase 2.3: Generación de CUDA C (Semanas 8-12)

**Objetivo**: Generar código CUDA compilable y eficiente.

**Entregables**:
```cuda
// Código generado por AMO-Lean
__global__ void fri_fold_kernel(
    const uint64_t* __restrict__ input,
    uint64_t* __restrict__ output,
    uint64_t alpha,
    size_t n
) {
    __shared__ uint64_t shared_input[512];

    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Coalesced load to shared memory
    if (idx * 2 + 1 < n * 2) {
        shared_input[threadIdx.x * 2] = input[idx * 2];
        shared_input[threadIdx.x * 2 + 1] = input[idx * 2 + 1];
    }
    __syncthreads();

    // Compute
    if (idx < n) {
        output[idx] = shared_input[threadIdx.x * 2]
                    + alpha * shared_input[threadIdx.x * 2 + 1];
    }
}
```

**Obstáculos técnicos**:
1. **Aritmética modular en GPU**: GPUs no tienen uint64 mul nativo eficiente
   - *Técnica*: PTX assembly para umul.wide
   - *Bibliografía*: "Montgomery Multiplication on GPUs" (Emmart et al.)

2. **Divergencia de warps**: Branches en kernel causan serialización
   - *Técnica*: Predicación en lugar de branches
   - *Bibliografía*: CUDA Best Practices Guide

**Testing Fase 2.3**:
- [ ] Compilación exitosa con nvcc
- [ ] Correctness vs implementación CPU
- [ ] Benchmark vs implementaciones estado del arte (bellman, plonky3)

#### Fase 2.4: Optimización y Profiling (Semanas 13-18)

**Objetivo**: Alcanzar performance competitiva con implementaciones manuales.

**Entregables**:
- Kernels optimizados para Poseidon, FRI fold, Merkle
- Dashboard de performance
- Documentación de trade-offs

**Obstáculos técnicos**:
1. **Memory-bound vs compute-bound**: Diferentes kernels tienen diferentes bottlenecks
   - *Técnica*: Roofline analysis
   - *Bibliografía*: Williams et al. "Roofline Model"

2. **Multi-GPU**: Scaling a múltiples GPUs
   - *Técnica*: NCCL para comunicación
   - *Bibliografía*: "Scaling Deep Learning on GPU Clusters"

**Testing Fase 2.4**:
- [ ] Roofline plot para cada kernel
- [ ] Comparación con prover de referencia (Stone, Plonky3)
- [ ] Tests de regresión de performance

---

## 3. Variantes AVX-512

### 3.1 Contexto y Motivación

AVX-512 ofrece registros de 512 bits (8 doubles o 8 uint64), potencialmente 2x sobre AVX2.

### 3.2 Desafío Técnico Principal

**Thermal throttling**: Muchos CPUs reducen frecuencia 10-20% cuando usan AVX-512 intensivamente.

### 3.3 Plan de Implementación por Fases

#### Fase 3.1: Infraestructura AVX-512 (Semana 1)

**Objetivo**: Detectar soporte y configurar generación condicional.

**Entregables**:
```lean
/-- Detectar capacidades SIMD en runtime -/
structure SIMDCapabilities where
  hasAVX2 : Bool
  hasAVX512F : Bool
  hasAVX512DQ : Bool  -- Double/Quad word
  hasAVX512IFMA : Bool  -- Integer FMA (para Montgomery)

/-- Seleccionar backend según capabilities -/
def selectSIMDBackend (caps : SIMDCapabilities) (kernel : Kernel) : CodeGen :=
  if caps.hasAVX512IFMA && kernel.needsMontgomery then avx512IFMAGen
  else if caps.hasAVX512F then avx512Gen
  else if caps.hasAVX2 then avx2Gen
  else scalarGen
```

**Obstáculos técnicos**:
1. **Runtime dispatch**: Seleccionar versión óptima en runtime
   - *Técnica*: Function multi-versioning (GCC/Clang __attribute__((target)))
   - *Bibliografía*: Intel Architecture Optimization Manual

**Testing Fase 3.1**:
- [ ] Detección correcta en varios CPUs
- [ ] Fallback graceful si no hay soporte

#### Fase 3.2: Kernels AVX-512 (Semana 2)

**Objetivo**: Portar kernels existentes a AVX-512.

**Entregables**:
```c
// FRI fold con AVX-512
void fri_fold_avx512(size_t n, const uint64_t* input,
                     uint64_t* output, uint64_t alpha) {
    __m512i valpha = _mm512_set1_epi64(alpha);

    for (size_t i = 0; i < n; i += 8) {
        // Cargar 16 elementos (8 pares)
        __m512i even = _mm512_loadu_si512(&input[i * 2]);
        __m512i odd = _mm512_loadu_si512(&input[i * 2 + 8]);

        // Deinterleave
        __m512i evens = _mm512_unpacklo_epi64(even, odd);
        __m512i odds = _mm512_unpackhi_epi64(even, odd);

        // output = even + alpha * odd
        __m512i prod = _mm512_mullo_epi64(valpha, odds);
        __m512i result = _mm512_add_epi64(evens, prod);

        _mm512_storeu_si512(&output[i], result);
    }
}
```

**Obstáculos técnicos**:
1. **Alineación 64 bytes**: AVX-512 requiere alineación estricta para loads/stores alineados
   - *Técnica*: `aligned_alloc(64, size)` o pragmas de alineación
   - *Bibliografía*: Intel Intrinsics Guide

**Testing Fase 3.2**:
- [ ] Correctness vs versión escalar
- [ ] Benchmark vs AVX2

#### Fase 3.3: Cost Model con Thermal Awareness (Semana 3)

**Objetivo**: Decidir cuándo usar AVX-512 considerando throttling.

**Entregables**:
```lean
/-- Cost model que considera thermal throttling -/
structure AVX512CostModel extends CostModel where
  thermalPenalty : Float := 0.85  -- 15% frequency reduction typical
  transitionCost : Nat := 1000   -- Cycles para cambiar de modo

/-- Decidir si usar AVX-512 para un kernel -/
def shouldUseAVX512 (model : AVX512CostModel) (kernel : Kernel) : Bool :=
  let avx512Cost := kernel.computeCost / 2 * model.thermalPenalty + model.transitionCost
  let avx2Cost := kernel.computeCost
  avx512Cost < avx2Cost
```

**Obstáculos técnicos**:
1. **Variabilidad entre CPUs**: Throttling varía significativamente
   - *Técnica*: Benchmarking adaptativo en warmup
   - *Bibliografía*: Agner Fog "Microarchitecture of Intel/AMD CPUs"

**Testing Fase 3.3**:
- [ ] Benchmark en varios CPUs (Xeon, desktop)
- [ ] Verificar que selección automática es óptima

---

## 4. FRI Query Phase

### 4.1 Contexto y Motivación

La Query Phase verifica la proximidad:
1. El verificador envía índices aleatorios
2. El prover responde con valores y Merkle proofs
3. El verificador chequea consistencia

### 4.2 Desafío Técnico Principal

**Patrón de acceso aleatorio**: A diferencia de Commit (secuencial, vectorizable), Query hace saltos aleatorios en memoria, causando cache misses.

### 4.3 Plan de Implementación por Fases

#### Fase 4.1: Modelado de Query (Semanas 1-2)

**Objetivo**: Definir tipos y operaciones para Query phase.

**Entregables**:
```lean
/-- Índices de query (generados por verificador vía Fiat-Shamir) -/
structure QueryIndices where
  indices : Array Nat
  round : Nat

/-- Respuesta del prover -/
structure QueryResponse where
  values : Array FieldElement
  merkleProofs : Array MerkleProof
  siblingValues : Array FieldElement

/-- Verificar una query -/
def verifyQuery (commitment : MerkleRoot) (query : QueryIndices)
    (response : QueryResponse) : Bool :=
  -- Verificar Merkle proofs
  response.merkleProofs.all (verifyMerkleProof commitment) &&
  -- Verificar consistencia de fold
  verifyFoldConsistency query.indices response.values response.siblingValues
```

**Obstáculos técnicos**:
1. **Generación de índices determinística**: Debe ser reproducible
   - *Técnica*: Derivar de transcript usando squeeze
   - *Bibliografía*: FRI paper, Section 4

**Testing Fase 4.1**:
- [ ] Roundtrip: commit → query → verify
- [ ] Verificar que índices son determinísticos

#### Fase 4.2: Optimización de Merkle Proofs (Semanas 3-4)

**Objetivo**: Minimizar accesos a memoria en verificación.

**Entregables**:
```lean
/-- Batch multiple Merkle proofs para amortizar accesos -/
def batchMerkleProofs (root : MerkleRoot) (indices : Array Nat)
    (tree : FlatMerkle) : Array MerkleProof :=
  -- Ordenar índices para localidad de acceso
  let sortedIndices := indices.qsort (· < ·)
  -- Extraer proofs compartiendo nodos comunes
  extractBatchedProofs root sortedIndices tree
```

**Obstáculos técnicos**:
1. **Prefetching**: Indicar al CPU qué memoria necesitaremos
   - *Técnica*: `__builtin_prefetch` basado en patrón de queries
   - *Bibliografía*: "What Every Programmer Should Know About Memory" (Drepper)

**Testing Fase 4.2**:
- [ ] Benchmark: batched vs naive
- [ ] Profile cache misses con perf

#### Fase 4.3: CodeGen para Query (Semanas 5-6)

**Objetivo**: Generar código C optimizado para verificación.

**Entregables**:
- `generateQueryVerifier : QueryParams → String`
- Código con prefetching hints
- Proof anchors para verificación

**Obstáculos técnicos**:
1. **Branch prediction**: Verificación tiene muchos branches
   - *Técnica*: Branchless comparisons donde sea posible
   - *Bibliografía*: "Branch Prediction" (Patterson & Hennessy)

**Testing Fase 4.3**:
- [ ] Differential fuzzing vs implementación Lean
- [ ] Benchmark en diferentes tamaños de árbol

---

## Dependencias y Orden de Ejecución

```
                    ┌─────────────────┐
                    │   Estado Actual │
                    │   (FRI Commit)  │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌──────────┐   ┌──────────┐   ┌──────────┐
       │ AVX-512  │   │ Poseidon │   │  Query   │
       │ (3 sem)  │   │ (10 sem) │   │ (6 sem)  │
       └────┬─────┘   └────┬─────┘   └────┬─────┘
            │              │              │
            │              ▼              │
            │       ┌──────────┐          │
            │       │   CUDA   │          │
            │       │ (6 meses)│          │
            │       └────┬─────┘          │
            │              │              │
            └──────────────┼──────────────┘
                           ▼
                    ┌──────────────┐
                    │ zkVM-Ready   │
                    │  AMO-Lean    │
                    └──────────────┘
```

**Camino crítico**: Poseidon → CUDA (máxima duración)

**Paralelizable**: AVX-512 y Query pueden desarrollarse en paralelo con Poseidon.

---

## Métricas de Éxito

| Hito | Métrica | Target |
|------|---------|--------|
| Poseidon | Throughput | ≥ 1M hashes/segundo (CPU) |
| AVX-512 | Speedup vs AVX2 | ≥ 1.5x |
| CUDA | Speedup vs CPU | ≥ 10x |
| Query | Verificación | < 100ms para árbol de 2^20 hojas |
| Correctness | Tests | 100% passing, differential fuzzing |
| Verificación | Sorry count | Mínimo, documentados |

---

## Bibliografía Completa

### Criptografía ZK
1. Grassi et al. "Poseidon: A New Hash Function for Zero-Knowledge Proof Systems" (USENIX 2021)
2. Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity" (ICALP 2018)
3. Ames et al. "Ligero: Lightweight Sublinear Arguments Without a Trusted Setup" (CCS 2017)

### Optimización SIMD/GPU
4. Intel Architecture Optimization Reference Manual
5. CUDA C Programming Guide (Nvidia)
6. Harris "Optimizing Parallel Reduction in CUDA"
7. Volkov "Better Performance at Lower Occupancy"
8. Emmart et al. "Montgomery Multiplication on GPUs"

### Compiladores y Verificación
9. Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
10. Gross et al. "Accelerating Verified-Compiler Development with a Verified Rewriting Engine" (ITP 2022)
11. Xi & Pfenning "Dependent Types in Practical Programming" (POPL 1999)

### Performance
12. Drepper "What Every Programmer Should Know About Memory"
13. Agner Fog "Instruction Tables" y "Microarchitecture"
14. Williams et al. "Roofline: An Insightful Visual Performance Model"

---

*Documento generado: Enero 2026*
*Próxima revisión: Al completar Fase 1 (Poseidon)*
