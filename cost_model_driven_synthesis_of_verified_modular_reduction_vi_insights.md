# Insights: Cost-Model-Driven Synthesis of Verified Modular Reduction via E-graph Equality Saturation

**Fecha**: 2026-03-17
**Dominio**: lean4
**Estado del objeto**: upgrade (AMO-Lean v3.1.0 → v3.2.0)
**Profundidad**: deep (Waves 1-5)

---

## 1. Analisis del Objeto de Estudio

### Resumen

Extender AMO-Lean v3.1.0 (que ya verifica equivalencia bitwise via E-graph) para que el E-graph SINTETICE automaticamente la mejor implementacion bitwise dado un primo p y un modelo de costos del hardware target (ARM, RISC-V, FPGA). La infraestructura existente (MixedNodeOp, extractF, saturateF, ILPEncode) cubre ~45% del trabajo. Los gaps criticos son: CostModel typeclass parametrico, extractILP para MixedNodeOp, phased saturation, y generador de reglas desde estructura del primo.

### Keywords

CostModel typeclass, parametric extraction, phased saturation, Solinas primes, pseudo-Mersenne reduction, ILP extraction, hardware latency, ARM Cortex-A76, RISC-V U74, FPGA DSP48E2, multi-level reduction, field synthesis, KoalaBear prime, cost-driven rule scheduling, DAG optimization

### Estado

**Upgrade de v3.1.0** — Alternativa A complete (verification). Alternativa B adds synthesis.

### Gaps (10 areas)

| Area | Severidad | Estado |
|------|-----------|--------|
| 1. Hardware cost models | CRITICAL | Datos obtenidos (ARM/RISC-V/FPGA) |
| 2. Parametric extraction | CRITICAL | ILPEncode tiene costFn param, falta instanciar |
| 3. Phased saturation | HIGH | saturateF single-phase, falta phasing |
| 4. Cost model validation | MEDIUM | No non-vacuity para cost-driven |
| 5. Multi-target support | HIGH | Single hardcoded cost model |
| 6. Rule generation from primes | MEDIUM | 3 rules hardcoded |
| 7. ILP for MixedNodeOp | HIGH | extractILP solo CircuitNodeOp |
| 8. Bitwise-hardware bridge | MEDIUM | Nat semantics, no instruction mapping |
| 9. Cost model realism | MEDIUM | No latency/throughput distinction |
| 10. Reduction composition | LOW | Standalone fold rules |

---

## 2. Lecciones Aplicables

### Criticas

| ID | Titulo | Aplicacion |
|----|--------|------------|
| L-513 | Compositional pipeline decomposition | saturate → costModel → extractILP como chain independiente |
| L-527 | Non-recursive ILP extraction | extractILP retorna solo nodo, fuel_independent via rfl |
| L-311 | Three-part soundness contract | fuel + result + frame para pipeline |
| L-517 | Unified ExtractionStrategy dispatch | .greedy vs .ilp vs .costDriven en un inductive |
| L-478 | Flat patterns avoid splitter blocking | Refactorizar si MixedNodeOp crece |

### Anti-patrones

- L-567: native_decide para primos grandes (>2^100) — usar algebraic proofs
- L-418: No crear typeclass si solo 1 instancia — esperar 2+
- Identity passes disfrazados (:= id) en pipeline stages

---

## 3. Bibliografia Existente Relevante

### Documentos Clave

| Paper | Relevancia |
|-------|------------|
| egg (Willsey 2021) | Cost function pluggable, extraction algorithm |
| TENSAT (Yang 2021) | ILP extraction para optimizacion con cost model |
| e-boost (Yin 2025) | ILP + warm-start + adaptive heuristics |
| Mind the Abstraction Gap (Vohra 2025) | Performance model global para ML compilers |
| Fiat-Crypto (Erbsen 2019) | Sintesis verificada de aritmetica modular |
| CryptOpt (Kuepper 2023) | Random search + verified compilation |
| SPORES (Wang 2020) | Cost-aware E-graph extraction via constraint solver |

### Nuevos Papers Descargados (Wave 2)

| Paper | Path | Dato Clave |
|-------|------|-----------|
| ARM Cortex-A76 Optimization Guide | hardware-cost-models/ | MUL32=2cyc, MUL64=4cyc, ADD/AND/shift=1cyc |
| SiFive U74 RISC-V Manual | hardware-cost-models/ | MUL=3cyc, ALU=1cyc, DIV=6-68cyc |
| Xilinx DSP48E2 User Guide | hardware-cost-models/ | 27x18 multiplier, 2-6cyc pipelined |
| SPORES (VLDB 2020) | egraphs-treewidth/ | Cost-aware extraction via constraint solver |
| Granger-Moss Generalized Mersenne (2011) | criptografia/ | Cyclic convolution 2x faster reduction |

---

## 4. Estrategias Ganadoras

| Estrategia | Fuente | Aplicacion |
|------------|--------|------------|
| costFn como parametro de pipeline | OptiSat (PipelineSoundness.lean) | Pass CostModel instance through saturate→extract |
| ParameterRegime struct + native_decide | VeriHE (Params.lean) | HardwareCost struct with concrete ARM/RISC-V/FPGA |
| encodeEGraph con cost objective | OptiSat (ILPEncode.lean) | Σ cost(n) · s_n como funcion objetivo ILP |
| Certificate validation via decidable checks | OptiSat (ExtractSpec.lean) | checkSolution_sound para ILP certificates |
| Bridge theorem per algorithm | AMO-Lean Fase 17 | Cada reduccion tiene bridge to ZMod |

### ILP Infrastructure Already Exists

- ILP.lean: ILPVar, LinTerm, ILPProblem, ILPSolution — domain-independent
- ILPEncode.lean: encodeEGraph with costFn parameter — needs MixedNodeOp instantiation
- ILPSolver.lean: MPS export + external solver — fully operational
- ExtractSpec.lean: extractILP_correct — proven for CircuitNodeOp

---

## 5. Hardware Cost Data (from Wave 2)

### ARM Cortex-A76

| Instruction | Latency | Throughput |
|-------------|---------|------------|
| ADD/SUB (basic) | 1 cyc | 3/cyc |
| AND/EOR/ORR | 1 cyc | 3/cyc |
| LSL/LSR/ASR | 1 cyc | 3/cyc |
| MADD 32-bit | 2 cyc | 1/cyc |
| MADD 64-bit | 4 cyc | 1/3 cyc |
| UMULH 64-bit | 5 cyc | 1/4 cyc |
| UDIV 32-bit | 5-12 cyc | variable |
| LDR (L1 hit) | 4 cyc | 2/cyc |

### RISC-V SiFive U74

| Instruction | Latency |
|-------------|---------|
| ALU (ADD/AND/XOR/SLL/SRL) | 1 cyc |
| MUL/MULH | 3 cyc |
| DIV/REM | 6-68 cyc |
| Load (cache hit) | 3 cyc |

### FPGA DSP48E2

| Parameter | Value |
|-----------|-------|
| Multiplier | 27x18 bits |
| Pipeline latency | 2-6 cyc |
| Accumulator | 48-bit |
| Equivalent LUTs | ~hundreds |

### Cost Ratios

| Target | MUL:ADD ratio | Implication |
|--------|--------------|-------------|
| ARM A76 (32-bit) | 2:1 | Prefer shifts+adds for small constants |
| ARM A76 (64-bit) | 4:1 | Strong incentive to avoid 64-bit mul |
| RISC-V U74 | 3:1 | Moderate; shifts always preferred |
| FPGA DSP48E2 | 1:1 to 3:1 | DSP multiply is "free" if DSP available |

---

## 6. KoalaBear Prime

- **p = 2^31 - 2^24 + 1 = 2130706433**
- Form: 2^31 - c where c = 2^24 - 1
- Two-adicity: 24 (NTT domain up to 2^24)
- Poseidon2 S-box degree: d = 3 (vs d = 7 for BabyBear)
- Reduction: identical to BabyBear pattern (pseudo-Mersenne fold)
- fold: x % p = ((x >>> 31) * (2^24 - 1) + (x &&& (2^31 - 1))) % p

---

## 7. Sintesis de Insights

### Hallazgos Clave

1. **ILP infrastructure is 90% ready**: ILPEncode already takes costFn parameter. Only needs MixedNodeOp instantiation + multi-dimensional cost.

2. **Hardware costs are concrete and documented**: ARM MUL32=2, RISC-V MUL=3, FPGA MUL=1-3. No more guessing.

3. **Solinas primes generalize all 4 ZK fields**: Mersenne31, BabyBear, KoalaBear, Goldilocks all have form 2^a - 2^b + 1. ONE parametric rule covers all.

4. **Cost ratios drive strategy selection**: ARM 64-bit mul is 4x expensive → strong incentive for Solinas fold. FPGA has "free" DSP multiply → Montgomery may be cheaper.

5. **Phased saturation is proven effective**: Herbie's 3-iteration bound + SPORES constraint solver approach = bounded, cost-aware saturation.

6. **VeriHE ParameterRegime pattern**: Concrete struct + instances + monotonicity via native_decide. Directly applicable to HardwareCost.

7. **OptiSat's pipeline decomposition**: saturateF ⊥ computeCostsF ⊥ extractF. Each stage independently proven. Extend with costModel parameter.

8. **Novel contribution**: NO paper combines cost models + E-graph synthesis + verification + modular reduction. This is a first.

9. **SPORES cost-aware extraction**: Constraint solver approach for globally optimal extraction. More principled than egg's greedy.

10. **KoalaBear extends coverage to 4 ZK fields** without new infrastructure — same SolinasConfig pattern.

### Riesgos

| Riesgo | Probabilidad | Mitigacion |
|--------|-------------|------------|
| Multi-dimensional cost makes ILP intractable | BAJA | Aggregate to single Nat (weighted sum) |
| Phased saturation changes semantics | BAJA | Each phase independently preserves CV |
| Cost model inaccuracy (superscalar effects) | MEDIA | Validate against benchmarks |
| SolinasConfig doesn't cover all primes | BAJA | Barrett as fallback for non-Solinas |

### Recomendaciones para Planificacion

1. **CostModel como structure (no typeclass)** — solo 3 instancias concretas, seguir L-418
2. **SolinasConfig unifica 4 campos** — parametric fold rule covers Mersenne31/BabyBear/KoalaBear/Goldilocks
3. **ILP adaptation es incremental** — encodeEGraph ya toma costFn, solo cambiar la funcion
4. **Phased saturation via wrapper** — NO modificar saturateF, crear phasedSaturateF que lo llama 2 veces con diferentes reglas
5. **Composicion via Nat.mod transitivity** — (a % p = b % p) ∧ (b % p = c % p) → (a % p = c % p)

---

## 8-10. Formalizacion en BitwiseLean

*(Resultados de Wave 5 — en progreso)*

Archivos nuevos:
- `BitwiseLean/KoalaBearFold.lean` — KoalaBear fold rule (p = 2^31 - 2^24 + 1)
- `BitwiseLean/SolinasFold.lean` — Parametric Solinas reduction (covers all 4 ZK primes)
- `BitwiseLean/CostModel.lean` — HardwareCost structure + ARM/RISC-V/FPGA instances
