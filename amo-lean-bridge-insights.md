# Insights: SIMD Vectorization + NTT Bridge + Finite Field Optimization for AMO-Lean

**Fecha**: 2026-03-19
**Dominio**: lean4
**Estado**: upgrade (extendiendo capacidades existentes de v3.5.1)

## 1. Análisis del Objeto de Estudio

AMO-Lean tiene un e-graph verificado que optimiza reducciones modulares para 4 campos finitos (BabyBear, Mersenne31, KoalaBear, Goldilocks), genera C per-hardware (ARM, RISC-V, FPGA), con soundness chain 0 sorry. El objetivo es extenderlo para:

1. **Más operaciones primitivas**: mul modular completo, inversión, exponenciación, batch/SIMD
2. **NTT bridge**: conectar la spec formal NTT/FRI con la aritmética bitwise optimizada
3. **Cost models calibrados**: instrucciones combinadas (barrel shifter), SIMD widths
4. **Output ejecutable**: Rust importable, no solo strings C
5. **Benchmark**: evidencia medida de que la optimización importa

**Keywords**: SIMD vectorization, NTT butterfly, finite field arithmetic, modular reduction, Montgomery REDC, Barrett reduction, lazy reduction, Kronecker substitution, e-graph equality saturation, cost model extraction, Harvey butterfly, Solinas fold, shift-add decomposition, translation validation, verified codegen

## 2. Lecciones Aplicables

### Críticas (5)
- **L-311 (Soundness Contract)**: Pipeline.sound = (fuel, result eval, frame). Base para toda composición.
- **L-513 (Pipeline Composition)**: saturate→costFn→extract: probar cada etapa preserva invariante, componer en ~30 líneas. Patrón exacto para NTT multi-etapa.
- **L-567 (native_decide perf)**: BLOQUEANTE para campos >2^60. Usar `#eval` + axioma documentado.
- **L-512 (Three-Tier Architecture)**: Shell (IO) → Core (verified, total) → Bridge (composition).
- **L-516 (Mirror Inductive)**: Patrón para extraer SIMD ops verificadas desde e-graph.

### Anti-patrones
- native_decide en campos grandes (L-567)
- Identity passes silenciosos (L-311, L-512)
- Nested sub-patterns que bloquean equation compiler (L-478)
- Diamond typeclass instances (evitar con evalOp concreta)

### Técnicas reutilizables
- Three-Part Contract (L-311, L-297): fuel + result + frame
- Bridge Decomposition (L-329, L-315): scalar + loop + mem
- Fuel-Based Totality (L-554): inducción sobre combustible
- Cost Model Tightness (L-467): DP=cost → rfl, luego lower_bound

## 3. Bibliografía Relevante (48 documentos)

### Papers clave descargados (Wave 2)
| Paper | Año | Relevancia directa |
|-------|-----|-------------------|
| **Diospyros** (VanHattum, ASPLOS 2021) | 2021 | egg + cost model → SIMD auto-vectorización DSP. 3.1x speedup. |
| **Isaria** (Thomas, ASPLOS 2024) | 2024 | Sintetiza rewrite rules desde ISA specs. Fases: Expansion→Compilation→Optimization. |
| **HACLxN** (Polubelova, CCS 2020) | 2020 | SIMD crypto verificado en F*: 1 spec, 4 backends (Neon/AVX/AVX2/AVX512). |
| **Jasmin Kyber AVX2** (Almeida, TCHES 2023) | 2023 | Primera verificación formal completa de NTT AVX2 (Kyber). 6 representaciones intermedias. |
| **SPIRAL NTT** (Bowers, CGO 2023) | 2023 | NTT vectorizada generada por SPIRAL para multi-word integers. |
| **Kronecker Substitution** (Dumas, 2008) | 2008 | Pack field polynomials en machine words. REDQ para extracción simultánea. |
| **Lazy NTT** (Longa-Naehrig, 2016) | 2016 | K-RED: reducción retrasada en NTT. Seminal para Kyber/Dilithium. |
| **AVX2 NTT** (Seiler, 2018) | 2018 | Montgomery signed 16-bit + lazy reduction AVX2. Base de todas las impl modernas. |

### Papers de FINITEFIELDS analizados
| Paper | Hallazgo clave |
|-------|---------------|
| Sturtivant-Frandsen (1993) | Aritmética FF y Boolean son polinomialmente equivalentes → justifica mezclar arith+bitwise en e-graph |
| Dumas-Pernet (2012) | fgemm: lift a FP, multiply con BLAS, reduce mod p. Kronecker substitution para packed reduction. |
| Plank (2013) | SPLIT decomposition: `a*b = a*b_hi*2^k XOR a*b_lo` → rewrite rule para e-graph |
| Guajardo-Paar | Karatsuba para Fp2: 3 muls en vez de 4 → e-graph rewrite rule |

### Gaps identificados
1. FPGA-GPU co-design unified cost models
2. Constraint-based SIMD layout synthesis
3. Crypto-specific contextual rewriting rules
4. Verified treewidth computation
5. Cross-lane SIMD verification (shuffles/permutations)
6. Incremental e-graph compilation
7. Machine-assisted rule inference para finite fields
8. Multi-target backend synthesis unificado

## 4. Estrategias Ganadoras de Proyectos Previos

### Top 5
1. **NodeOps Typeclass Parametrizado** (OptiSat): motor genérico instanciable sin cambios
2. **Bridge Multi-Capa** (AMO-Lean Fases 13-17): Layer1 (CV) → Layer2 (CryptoEquiv) → Layer3 (hardware)
3. **ZMod Isomorphism** (AMO-Lean N17): `toZMod : MixedNodeOp → ZMod p` con natCast_injective
4. **Firewall `_aux`**: develop → verify separately → migrate complete
5. **Phased Saturation** (Herbie PLDI 2015): Phase1 algebraic → Phase2 bitwise → Phase3 shift-add

### Errores evitados
- native_decide en primes grandes (timeout >30min)
- Identity passes (`:= id`) disfrazados de completitud
- Diamond typeclass instances
- Importar librerías internas como dependencia lake
- Field-specific rules hardcodeadas (parametrizar por `(p : Nat) [Fact (Nat.Prime p)]`)

## 5. Nueva Bibliografía (8 papers descargados)

Todos descargados a `~/Documents/claudio/biblioteca/` e indexados. Grafo conceptual actualizado: 1945 nodos, 1557 aristas, 547 documentos.

## 6. Teoremas Extraídos (30 total, 7 grupos)

| Grupo | Teoremas | Tema | Dificultad |
|-------|----------|------|-----------|
| **A: NTT Core** | 7 | Butterfly, convolution, CRT iso | easy-hard |
| **B: Modular Reduction** | 6 | Montgomery, Barrett, K-RED, Shoup | easy-medium |
| **C: Lazy Reduction** | 5 | Overflow bounds, delayed safety | easy-medium |
| **D: Kronecker/Packing** | 4 | Encode, decode, REDQ, BabyBear pack | easy-hard |
| **E: SIMD Bridge** | 5 | Lane independence, vectorized NTT, cost | medium-hard |
| **F: Verified Pipeline** | 3 | Spec-impl refinement, rewrite preservation | hard |

### Orden de dependencias (7 fases)
1. Foundations (A1, A2, C1, C2, C4, E5, D4) — sin deps
2. Modular Reduction (B1-B6) — builds on bitwise
3. Lazy Reduction (C3, C5) — builds on Phase 1+2
4. NTT Structure (A3-A7) — builds on Phase 1
5. Kronecker (D1-D3) — independiente
6. SIMD Bridge (E1-E5) — builds on Phase 2+4
7. Pipeline (F1-F3) — capstone

## 7. Síntesis de Insights

### Hallazgos clave (Top 10)

1. **Lazy reduction es el multiplicador**: Longa-Naehrig K-RED ahorra 50% de reducciones modulares en NTT. Cada butterfly sin reducción intermedia = 1 multiplicación modular menos. Para NTT de 2^20, eso son ~10M operaciones ahorradas.

2. **Kronecker packing duplica throughput**: 2 BabyBear (31-bit) en 1 u64 → aritmética packed con una sola instrucción MUL. Dumas (2008) + REDQ para extracción simultánea.

3. **Lane independence es EL teorema SIMD**: HACLxN demuestra que una vez probado `simd_lane_independence`, toda operación pointwise se vectoriza gratis. Reduce N proofs a 1 proof + 1 structural theorem.

4. **6 representaciones intermedias (Almeida 2023)**: El NTT verificado de Kyber usa spec → iterative → merged → reduced → Montgomery → AVX2. Cada paso es un refinement theorem. AMO-Lean necesita una cadena similar.

5. **Diospyros pattern**: e-graph + cost model auto-vectoriza 3.1x sobre bibliotecas DSP. El pattern exact es: scalar rules → SIMD lowering rules → cost extraction. AMO-Lean ya tiene el e-graph + cost extraction; falta SIMD lowering.

6. **Isaria sintetiza reglas desde ISA**: No escribir reglas SIMD a mano — sintetizarlas desde la spec de la ISA. AMO-Lean podría usar Ruler (OOPSLA 2021) para inferir reglas de rewrite para cada target.

7. **Harvey butterfly elimina reducciones**: Input [0,2p) → output [0,2p) con 1 conditional sub. Zero full reductions dentro del butterfly. Probado en BitwiseLean (C5).

8. **El gap que AMO-Lean llena**: {rewrite rules verificadas} + {SIMD cost model} + {e-graph extraction} + {campos finitos} = combinación que NO existe en ninguna herramienta.

9. **Bridge theorem pattern**: Nat-level proof (omega, decide) → lift via natCast_injective a ZMod → compose con pipeline soundness. Ya validado en Fases 13-17.

10. **fgemm approach** (Dumas-Pernet): lift finite field ops a floating point, multiply con BLAS, reduce mod p. Potencialmente poderoso para GPU.

### Riesgos
1. native_decide timeout en campos >60 bits (mitigación: pruebas algebraicas)
2. SIMD cross-lane ops rompen lane independence (mitigación: separar pointwise de shuffle)
3. Cost model drift vs hardware real (mitigación: benchmark automático)
4. Explosión de reglas SIMD (mitigación: phased saturation + UCB1 scoring)

### Recomendaciones para implementación

**Fase inmediata (ROI más alto)**:
1. Agregar `mulGate(a,b) → reduce(mulGate(a,b))` como rewrite rule (trivial, habilita cadena mul+reduce)
2. Implementar butterfly como MixedExpr: `addGate(witness_a, mulGate(witness_w, witness_b))` con reduce intermedio
3. Benchmark automático: compilar C generado, medir ciclos, comparar con Plonky3

**Fase media**:
4. Lazy reduction: no reducir después de cada butterfly, acumular y reducir cada k pasos
5. Kronecker packing: 2 BabyBear en u64
6. Cost model calibrado con instrucciones reales (barrel shifter ARM, MULX x86)

**Fase largo plazo**:
7. SIMD lane independence theorem + vectorized extraction
8. NTT bridge completo: spec → impl via 6 refinements
9. Output Rust importable para Plonky3

## 8. Formalización en BitwiseLean

### Resumen

| Métrica | Valor |
|---------|-------|
| Archivos creados | 2 |
| Teoremas nuevos | 16 |
| Probados | 16 |
| Sorry | 0 |
| LOC nuevos | 394 |
| Build | 1132 jobs, 0 errors |

### Archivos generados

**BitwiseLean/NTTButterfly.lean** (227 LOC, 10 teoremas):
- `butterfly_ct_correct` (A1): CT butterfly mod p correctness
- `butterfly_ct_mod` (A1+): sum property (a+wb) + (a-wb) = 2a mod p
- `butterfly_gs_correct` (A2): GS butterfly mod p correctness
- `lazy_ct_add_bound` (C1): inputs < 2q → sum < 4q
- `lazy_gs_add_bound` (C2): inputs < q → sum < 2q
- `delayed_reduction_bound` (C4): k additions → sum ≤ k*B
- `delayed_reduction_strict` (C4+): strict variant
- `babybear_pack_lo` (D4): low 31 bits extraction
- `babybear_pack_hi` (D4+): high 32 bits extraction

**BitwiseLean/LazyReduction.lean** (167 LOC, 6 teoremas):
- `harvey_butterfly_output_bound` (C5): sum stays in [0, 2p)
- `harvey_butterfly_diff_bound` (C5+): diff stays in [0, 2p)
- `harvey_butterfly_mod_correct` (C5++): conditional sub preserves mod p
- `harvey_two_stage_bound`: compositionality across stages
- `harvey_full_butterfly_invariant`: both branches in [0, 2p)
- `harvey_canonicalize`: final [0,2p) → [0,p)

**BitwiseLean total**: 1688 LOC, ~90 declarations, 0 sorry, 0 axioms.

## 9. Fuentes Clave (lectura recomendada)

1. **Seiler 2018** — AVX2 NTT con lazy reduction + Montgomery signed. EL paper más relevante.
2. **Longa-Naehrig 2016** — K-RED seminal para delayed reduction en NTT.
3. **Diospyros 2021** — Pattern exacto para e-graph + SIMD auto-vectorización.
4. **HACLxN 2020** — Metodología de verificación SIMD: 1 spec → N backends.
5. **Almeida 2023** — Blueprint de verificación NTT: 6 refinements spec→AVX2.
6. **Dumas 2008** — Kronecker substitution para packing field elements.
7. **Harvey 2014** — Butterfly con representación redundante, elimina full reductions.
