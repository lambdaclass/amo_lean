# TRZK: Architecture

## Next Version: 3.11.0

### Bound-aware Discovery Engine v3.11.0

**Contents**: Transform TRZK from hardcoded optimizations to automatic discovery platform.
Add `conditionalSub` constructor to MixedNodeOp, connect bounds to sideCondCheck in
e-graph saturation, extend NTTStrategy with twoStepGoldilocks.

**Vision**: The e-graph discovers optimizations like AC-6 (conditional subtract for
bounded inputs) AUTOMATICALLY for any field, without per-field `if k > 32` hardcoding.
Test: add Stark252 field with ZERO field-specific rules → e-graph discovers optimal reduction.

**5 Phases**:
- F5 (1d): Emisión reduce128 — uint64_t temps post-split instead of __uint128_t (~20 LOC, ~15% speedup)
- F1 (1d): Bound-aware codegen — pass stage.outputBoundK to butterfly, dispatch by bounds (DONE)
- F4 (0.5d, parallel): twoStepGoldilocks in NTTStrategy (~15 LOC, very low risk) (DONE)
- F2 (3-4d): conditionalSub in MixedNodeOp (~300 LOC mechanical, 23rd constructor)
- F3 (1d): Bound-aware sideCondCheck — boundAwareEqStep in tieredStep (~40 LOC)

**Key infrastructure verified by 3 audit agents**:
- sideCondCheck IS wired in saturation (MixedSaturation.lean:32-35), NOT dead code
- soundness proofs already handle sideCondCheck (MixedEMatchSoundness.lean:1713)
- buildBoundLookup exists (BoundPropagation.lean:72) for reading bounds from DAG
- tieredStep runs relStep BEFORE new layer (bounds are fresh)

#### DAG (3.11.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N311.6 F5: Emisión reduce128 (uint64_t post-split temps) | FUND | — | pending |
| N311.1 F1: Bound-aware codegen (boundK parameter) | FUND | — | done |
| N311.2 F4: twoStepGoldilocks NTTStrategy | PAR | — | done |
| N311.3 F2: conditionalSub in MixedNodeOp (~300 LOC) | CRIT | N311.1 | pending |
| N311.4 F3: boundAwareEqStep + reduceToConditionalSub | CRIT | N311.3 | pending |
| N311.5 Test: Stark252 automatic discovery (no hardcode) | HOJA | N311.4 | pending |

#### Formal Properties (3.11.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N311.1 | boundK=0 produces identical codegen to v3.10.1 | PRESERVATION | P0 |
| N311.1 | boundK≤2 activates conditionalSub for ANY field | SOUNDNESS | P0 |
| N311.3 | evalMixedOp(.conditionalSub a p) = if v a >= p then v a - p else v a | SOUNDNESS | P0 |
| N311.3 | mixed_extractable_sound handles conditionalSub arm | SOUNDNESS | P0 |
| N311.4 | boundAwareEqStep discovers conditionalSub when boundK ≤ 2 | SOUNDNESS | P0 |
| N311.5 | Stark252 discovered automatically without field-specific rules | SOUNDNESS | P0 |

#### Bloques

- [ ] **BF1+BF4 — Codegen bounds + NTTStrategy (F1 + F4, parallel)**: F1: Add boundK param to lowerDIFButterflyByReduction, dispatch by bounds. F4: Add .twoStepGoldilocks to NTTStrategy. Gate: validation PASS + conditionalSub activates for bounded inputs.
- [ ] **BF2 — conditionalSub constructor (F2)**: CRIT. Add 23rd MixedNodeOp constructor. ~300 LOC mechanical across 9+ files. Gate: lake build 0 errors, 0 new sorry, benchmark validation PASS.
- [ ] **BF3 — Bound-aware discovery (F3 + Stark252 test)**: CRIT. boundAwareEqStep in tieredStep + reduceToConditionalSub rule + Stark252 automatic discovery test. Gate: e-graph discovers conditionalSub for bounded inputs.

---

## Current Version: 3.10.1 (COMPLETE)


### Phase A: Emission optimization + cache fixes

**Contents**: F5c butterfly Stmt.call closes loop overhead gap. CacheConfig fix + level-aware model improve plan accuracy. Benchmark Rust vs Plonky3.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/NTTPlanSelection.lean`
- `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean`

#### DAG (3.12.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N312.1 A.2: CacheConfig fix (l1DataSize, elementSize, l2MissCycles) | HOJA | — | pending |
| N312.2 A.4: Cache model level-aware with data-reuse | PAR | N312.1 | pending |
| N312.3 A.1: F5c butterfly Stmt.call + loop uint64_t | CRIT | — | pending |
| N312.4 A.5: Benchmark Rust vs Plonky3 Rust | HOJA | N312.3 | pending |

#### Formal Properties (3.12.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N312.1 | CacheConfig l1DataSize=131072 for Apple M-series | PRESERVATION | P0 |
| N312.2 | planCacheCost(R4_plan) < planCacheCost(R2_plan) for N>2^14 | OPTIMIZATION | P1 |
| N312.3 | goldi_butterfly emits uint64_t-only function body | SOUNDNESS | P0 |
| N312.3 | F5c output numerically identical to non-F5c for same input | EQUIVALENCE | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **Emission + Cache**: N312.1, N312.2, N312.3, N312.4

### Phase B: Discovery wiring via selectBestPlanExplored

**Contents**: Connect existing Discovery pipeline to plan competition. selectBestPlanExplored already does oracle→explore→Plan with theorems for 3 fields. Just push as candidate.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/UltraPipeline.lean`

#### DAG (3.12.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N312.5 B.1: selectBestPlanExplored as plan candidate | PAR | N312.2 | pending |

#### Formal Properties (3.12.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N312.5 | Discovery plan competes in selectPlanWith with full cost model | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **Discovery wiring**: N312.5

### Phase C: NTT trick runtime branch

**Contents**: Exploit Goldilocks omega_64=8: twiddles that are powers-of-2 use shift instead of multiply. Runtime popcnt branch in goldi_butterfly.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean`

#### DAG (3.12.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N312.6 C.1: NTT trick runtime popcnt branch | PAR | N312.3 | pending |

#### Bloques

- [ ] **NTT trick**: N312.6

### Phase D: Lazy reduction REAL + prefetch

**Contents**: Fix lazy's 3-layer fiction: safety gate u128, cost model lazy=0, codegen skip reduction. Add software prefetch for early stages.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/BoundPropagation.lean`
- `AmoLean/EGraph/Verified/Bitwise/CrossRelNTT.lean`
- `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean`
- `AmoLean/EGraph/Verified/Bitwise/NTTPlan.lean`
- `AmoLean/EGraph/Verified/Bitwise/BoundIntegration.lean`
- `AmoLean/EGraph/Verified/Bitwise/Discovery/MatPlanExtraction.lean`

#### DAG (3.12.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N312.7 D.1: lazyReductionSafe parametrize wordBits | FUND | — | pending |
| N312.8 D.2+D.3: Cost model lazy=0 + codegen skip reduction | CRIT | N312.7 | pending |
| N312.9 D.4: wordBits propagation to callers | PAR | N312.7 | pending |
| N312.10 D.5: Proofs for lazy passthrough | HOJA | N312.8 | pending |
| N312.11 D.6: Software prefetch for early stages | HOJA | — | pending |

#### Formal Properties (3.12.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N312.7 | lazyReductionSafe(1, goldiP, 128) = true | SOUNDNESS | P0 |
| N312.8 | lowerReductionChoice .lazy emits passthrough (no Solinas fold) | EQUIVALENCE | P0 |
| N312.8 | reductionCostForHW .lazy = 0 (not Solinas cost) | OPTIMIZATION | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [ ] **Lazy + Prefetch**: N312.7, N312.8, N312.9, N312.10, N312.11

---

## Previous Versions

### 3.6.0

### Vectorize Scalar Stages v3.6.0

**Contents**: Vectorize the 2 scalar NTT stages (halfSize=2,1) that consume 48-63% of NEON NTT time. Uses intra-register butterflies with deinterleave/interleave via vuzp/vzip, processing multiple groups per NEON call.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean`
- `Tests/benchmark/`

#### DAG (3.6.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N36.1 emitNeonButterflyDIT_HalfSize2_C | FUND | — | ✓ done |
| N36.2 emitNeonButterflyDIT_HalfSize1_C | FUND | — | ✓ done |
| N36.3 Modify emitStageC dispatch for halfSize<4 | CRIT | N36.1, N36.2 | ✓ done |
| N36.4 Validation: element-by-element vs Python reference | PAR | N36.3 | ✓ done (4/4 PASS, 0% gain) |
| N36.5a CNTVCT per-stage profiling — diagnose why 0% gain | CRIT | N36.4 | ✓ done |
| N36.5b Decision gate — next optimization or pivot based on profiling data | HOJA | N36.5a | ✓ done |

#### Formal Properties (3.6.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N36.1 | halfSize=2 NEON butterfly produces same output as scalar | EQUIVALENCE | P0 |
| N36.2 | halfSize=1 NEON butterfly produces same output as scalar | EQUIVALENCE | P0 |
| N36.3 | No stage falls to scalar fallback for R2 plans | INVARIANT | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Small SIMD Butterfly Kernels**: N36.1, N36.2 — hs2 (2 groups/call) and hs1 (4 groups/call via vld2q/vst2q) implemented
- [x] **Dispatch Integration**: N36.3 — 3-way dispatch in emitStageC (SIMD / hs2 / hs1 / scalar)
- [x] **Validation**: N36.4 — 4/4 PASS (BabyBear+KoalaBear, N=2^16+2^20), correctness confirmed. **Finding: ~0% performance gain** (264μs vs 253μs, within noise). Standalone profiler prediction of 48% scalar bottleneck was WRONG for generated code.
- [x] **CNTVCT Per-Stage Profiling**: N36.5a — N=2^16: uniform (~39μs/stage), hs2/hs1 ~1.3-1.4×. N=2^20: moderate cache penalty (~1.19× early vs late). — Insert ARM cycle counter fence markers between stages in emitted C. Diagnose actual per-stage time distribution. Detalles en TRZK_filosofico.md §N36.5a.
- [x] **Decision Gate**: N36.5b — **DECISION: NTT near-optimal for this codegen arch.** N=2^16 uniform, N=2^20 cache penalty ~19% (moderate, doesn't justify four-step NTT). Pivot to: (1) negacyclic twist merge for free 5-8%, (2) other ZK primitives (FRI fold), (3) formal verification of SIMD path (v3.7.0). — Based on N36.5a data, decide next optimization target. Detalles en TRZK_filosofico.md §N36.5b.


### 3.5.0

### REDC-Schedule v3.5.0

**Contents**: Expand NTTStage decision space: REDCMethod (sqdmulh vs vmull), ILPFactor (dual-butterfly interleaving). Calibrate cost model empirically at each step. Benchmark against Plonky3 real.

**Files**:
- `verification/plonky3/plonky3_shim/src/lib.rs`
- `verification/plonky3/Makefile`
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean`
- `AmoLean/EGraph/Verified/Bitwise/NTTPlan.lean`
- `AmoLean/EGraph/Verified/Bitwise/BoundPropagation.lean`
- `AmoLean/EGraph/Verified/Bitwise/CrossRelNTT.lean`
- `AmoLean/EGraph/Verified/Bitwise/NTTPlanSelection.lean`
- `ARCHITECTURE.md`

#### DAG (3.5.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N35.0 Benchmark vs Plonky3 real (monty-31 BabyBear) | FUND | — | ✓ done |
| N35.1 REDCMethod.sqdmulhMontgomery — 4-lane REDC | CRIT | N35.0 | ✓ done |
| N35.2 Calibrate cost model — REDCMethod empirical (microbench + InstructionProfile) | PAR | N35.1 | ✓ done |
| N35.3 ILPFactor — dual-butterfly interleaving | CRIT | N35.2 | ✓ done |
| N35.4 Calibrate cost model — ILP empirical (compiler auto-interleave check + V0/V1 occupancy) | PAR | N35.3 | ✓ done |
| N35.5 Decision gate: memory optimization (per-stage profiling → late merge vs cache block vs four-step) | HOJA | N35.4 | ✓ done |

#### Formal Properties (3.5.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N35.1 | sqdmulh REDC produces output in [0,p) | SOUNDNESS | P0 |
| N35.1 | REDCMethod transparent to scalar | INVARIANT | P0 |
| N35.3 | ilpFactor=2 produces identical NTT output | EQUIVALENCE | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Plonky3 Real Benchmark**: N35.0
- [x] **sqdmulh REDC Implementation**: N35.1
- [x] **REDC Calibration**: N35.2 — microbench aislado + llvm-mca + InstructionProfile model + effectiveCost calibration. Detalles en TRZK_filosofico.md §B35-2.
- [x] **ILP Interleaving**: N35.3 — implemented, gain ~0% (compiler auto-interleaves)
- [x] **ILP Calibration**: N35.4 — clang -O2 already software-pipelines. ilpDiscount = 0. — compiler auto-interleave check + V0/V1 pipe occupancy + ilpGain model + maxDiscount calibration. Detalles en TRZK_filosofico.md §B35-4.
- [x] **Memory Optimization Decision**: N35.5 — **FINDING: bottleneck is 2 scalar stages (48-63% of NTT time), not cache.** v3.6.0 should vectorize halfSize=2,1 via intra-register trn1/trn2 transposes. — per-stage profiling (N=2^16 + 2^20), evaluate 3 options (late merge / cache block / four-step NTT), decide v3.6.0 scope. Detalles en TRZK_filosofico.md §B35-5.


### 3.4.0

### Harvey-SIMD v3.4.0

**Contents**: Tighten Harvey bound annotation (boundK=2→1), parametrize SIMD butterfly by ReductionChoice, fix Montgomery latent bug. Enables Harvey chaining across all NTT stages for ~50% reduction cost savings in NEON.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/BoundPropagation.lean`
- `AmoLean/EGraph/Verified/Bitwise/BoundIntegration.lean`
- `AmoLean/EGraph/Verified/Bitwise/Discovery/StageContext.lean`
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean`
- `AmoLean/EGraph/Verified/Bitwise/CrossRelNTT.lean`
- `Tests/benchmark/deep_diag.lean`
- `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean`

#### DAG (3.4.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N34.1 Tighten Harvey bound to boundK=1 | FUND | — | ✓ done |
| N34.2 SIMD Harvey butterfly kernel + dispatch | CRIT | N34.1 | ✓ done |
| N34.3 Fix selectReductionForBound Montgomery exclusion | PAR | — | ✓ done |
| N34.4 Validation: chaining + NEON correctness + benchmark | HOJA | N34.1, N34.2, N34.3 | ✓ done |

#### Formal Properties (3.4.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N34.1 | Harvey reduction output is strictly less than p | SOUNDNESS | P0 |
| N34.1 | Harvey chaining: stageBoundFactor enables next stage Harvey eligibility | INVARIANT | P0 |
| N34.2 | SIMD emitter produces distinct butterfly functions for Harvey vs Solinas | EQUIVALENCE | P0 |
| N34.3 | selectReductionForBound never returns Montgomery for SIMD butterfly | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **B34-1 Harvey Bound Tightening**: N34.1
- [x] **B34-2 SIMD Harvey Butterfly**: N34.2
- [x] **B34-3 Montgomery Fix + Validation**: N34.3, N34.4

---

### B34-1: Harvey Bound Tightening (N34.1 — FUNDACIONAL, secuencial)

**Objetivo**: Cambiar `boundAfterReduction .harvey` de 2 a 1 en los 3 sitios donde aparece, alinear con la postcondición probada de `harveyReduceSpec` (output < p), actualizar theorem y examples.

**Justificación**: `harveyReduceSpec` (TrustLeanBridge.lean:363) dice `0 ≤ result < p`. Las 3 ramas del spec dan output < p. El bound anotado como 2 (output < 2p) es una over-approximation conservadora que impide Harvey chaining — solo Stage 0 usa Harvey, el resto cae a Solinas. Con boundK=1, Harvey encadena en TODOS los stages del NTT (invariante estable: Harvey output < p → inputK=1 → butterfly sum < 2p → Harvey eligible).

**Ediciones exactas**:

| # | Archivo | Línea | Cambio |
|---|---------|-------|--------|
| 1 | `BoundPropagation.lean` | 33 | `.harveyReduce _ _ => 2` → `=> 1` |
| 2 | `BoundPropagation.lean` | 152 | `.harvey => 2` → `=> 1` (en `boundAfterReduction`) |
| 3 | `Discovery/StageContext.lean` | 71 | `.harvey => 2` → `=> 1` (en `outputBoundK`) |
| 4 | `BoundPropagation.lean` | 396 | `reductionBoundFactor (.harveyReduce 0 0) = 2 := rfl` → `= 1 := rfl` |
| 5 | `BoundIntegration.lean` | 105 | `\| .harvey => outputK = 2` → `outputK = 1` (en `stage_bound_correct`) |

**Infraestructura existente**:
- `harveyReduceSpec` (TrustLeanBridge.lean:364-368): spec con postcondición `result < p`
- `harvey_1br` theorem (BoundPropagation.lean:51-52): prueba formal `x < 2p → if x ≥ p then x - p else x < p`
- `costAwareReductionForBound` (CrossRelNTT.lean:59-78): ya selecciona Harvey cuando `boundK ≤ 2`
- `extractScheduleFromState` (BoundIntegration.lean:205-241): usa `stageBoundFactor` → se beneficia automáticamente

**Verificación GATE**:
1. `lake build` — 0 errors
2. Verificar chaining: `#eval` de `nttStageBoundAnalysis` con NEON config → todos stages Harvey
3. `computeStageBounds` smoke test puede cambiar (verificar o actualizar línea 393)

**Riesgos**:
- Theorem `stage_bound_correct` (BoundIntegration.lean:99-106) tiene prueba `cases red <;> simp [stageBoundFactor, BoundProp.boundAfterReduction]`. Debería cerrarse con el mismo tactic porque solo depende de la definición — verificar.
- `computeStageBounds [.lazy, .lazy, .solinasFold] 1 = [1, 2, 3, 2]` (línea 393) NO involucra Harvey → no debería romperse.
- El planner sin `hw` (`buildBoundAwareStages` sin HardwareCost) prefiere `.lazy` → no se beneficia del fix. Solo el path `hw = some hwCost` ve Harvey chaining.

---

### B34-2: SIMD Harvey Butterfly (N34.2 — CRÍTICO, secuencial)

**Objetivo**: Parametrizar el butterfly NEON por `ReductionChoice`. Extraer REDC product como helper compartido. Crear variant Harvey. Modificar dispatch per-stage.

**Justificación**: `emitNeonButterflyDIT_C` (SIMDEmitter.lean:65-116) hardcodea Solinas fold para sum/diff. Con N34.1 el plan ya selecciona Harvey para todos los stages, pero el codegen SIMD lo ignora. El scalar path SÍ despacha correctamente via `lowerReductionChoice` (VerifiedPlanCodeGen.lean:72-88).

**Tareas en orden**:

**T2.1 — Extraer helper `emitNeonProductREDC`** (~30 LOC extraídas, 0 LOC nuevas)
- Mover SIMDEmitter.lean líneas 74-102 (producto REDC: vmull → REDC sub → branchless fixup → wb_red) a una función privada `emitNeonProductREDC (p k c mu : Nat) : String`
- El helper retorna el fragmento C desde `uint32x2_t b_lo` hasta `int32x4_t wb_red`
- `emitNeonButterflyDIT_C` llama al helper + agrega DIT sum/diff + Solinas fold
- `emitNeonButterflyDIT_Harvey_C` (nueva) llama al mismo helper + agrega DIT sum/diff + Harvey reduce

**T2.2 — Crear `emitNeonButterflyDIT_Harvey_C`** (~25 LOC nuevas)
- Firma: `def emitNeonButterflyDIT_Harvey_C (p : Nat) : String`
- Genera: `static inline void neon_bf_dit_har(int32_t* a_ptr, int32_t* b_ptr, const int32_t* tw_ptr, uint32x4_t p_vec, uint32x4_t mu_vec)`
- Nota: NO necesita `c_vec` ni `mask_k` (esos son Solinas-specific). Sí necesita `mu_vec` para REDC product.
- Cuerpo: `emitNeonProductREDC` + DIT sum/diff (líneas 103-107 reutilizadas) + Harvey reduce:
  ```c
  uint32x4_t ge_s = vcgeq_u32(sum_raw, p_vec);
  uint32x4_t sum_red = vsubq_u32(sum_raw, vandq_u32(ge_s, p_vec));
  uint32x4_t ge_d = vcgeq_u32(diff_raw, p_vec);
  uint32x4_t diff_red = vsubq_u32(diff_raw, vandq_u32(ge_d, p_vec));
  vst1q_s32(a_ptr, vreinterpretq_s32_u32(sum_red));
  vst1q_s32(b_ptr, vreinterpretq_s32_u32(diff_red));
  ```

**T2.3 — Modificar `emitStageC` para dispatch per-stage** (~10 LOC cambio)
- Cambiar firma: agregar parámetro `bfNameHar : String`
- Línea 224: lookup `stage.reduction` para elegir butterfly:
  ```lean
  let bfUsed := match stage.reduction with
    | .harvey => bfNameHar | _ => bfName
  ```
- Línea 233: usar `bfUsed` en vez de `bfName`
- El Harvey butterfly tiene firma distinta (sin c_vec/mask_k) — el call site debe pasar solo `p_vec, mu_vec`
  - Opción A: que Harvey acepte c_vec/mask_k pero los ignore (simpler dispatch)
  - Opción B: dos firmas distintas, dispatch genera call distinto (cleaner C)
  - **Decisión: Opción A** — firma idéntica, Harvey simplemente no usa c_vec/mask_k. Cero cambios en el call site.

**T2.4 — Modificar `emitSIMDNTTC`** (~15 LOC cambio)
- Líneas 279-281: generar ambas butterflies
  ```lean
  let (bfDeclSol, bfNameSol) := (emitNeonButterflyDIT_C p k c mu, "neon_bf_dit")
  let (bfDeclHar, bfNameHar) := (emitNeonButterflyDIT_Harvey_C p, "neon_bf_dit_har")
  ```
- Línea 289-291: emitir ambas en el header
- Líneas 309-310: pasar ambos nombres a `emitStageC`
- Constantes broadcast (líneas 295-307): `p_vec` y `mu_vec` siempre; `c_vec` y `mask_k` solo si algún stage usa Solinas

**Referencia scalar**: `lowerHarveyReduce` (TrustLeanBridge.lean:374-384) es el equivalente scalar con 2-branch. El NEON es 1-conditional branchless (correcto porque inputs siempre < 2p).

**Infraestructura existente**:
- `NTTStage.reduction` (NTTPlan.lean:69): ya lleva `ReductionChoice` per-stage
- `normalizePlan` (VerifiedPlanCodeGen.lean:284-296): ya normaliza stageIdx
- `lowerStageVerified` (VerifiedPlanCodeGen.lean:245-278): scalar fallback ya lee `stage.reduction`

---

### B34-3: Montgomery Fix + Validation (N34.3 + N34.4 — PARALELO+HOJA)

**N34.3 — Fix selectReductionForBound** (~5 LOC cambio)

CrossRelNTT.lean:49-51 puede retornar `.montgomery` cuando `hwIsSimd && boundK > 4`. Montgomery REDC es unsound para sums/diffs. El path activo (`costAwareReductionForBound` línea 62) ya lo excluye, pero `nttStageBoundAnalysis` (línea 115) usa `selectReductionForBound`.

Cambio: agregar parámetro `forProduct : Bool := false` o simplemente reemplazar `.montgomery` por `.solinasFold` en la rama SIMD:
```lean
-- Línea 49-51, actual:
| hwIsSimd || arrayIsLarge => .montgomery
-- Cambiar a:
| hwIsSimd || arrayIsLarge => .solinasFold  -- Montgomery only valid for products
```

Actualizar theorems que dependen del output (verificar con grep).

**N34.4 — Validation** (~40 LOC nuevas en tests)

1. **Chaining smoke test** — `#eval` en deep_diag.lean o nuevo test:
   ```lean
   #eval do
     let cfg := { numStages := 10, prime := 2013265921, hwIsSimd := true, arrayIsLarge := false }
     let schedule := nttStageBoundAnalysis cfg
     let allHarvey := schedule.all fun (_, red, _) => red == .harvey
     IO.println s!"All Harvey: {allHarvey}"  -- expect true
   ```

2. **mkBoundAwarePlan chaining** — verificar que con `arm_neon_simd`:
   ```lean
   #eval do
     let plan := mkBoundAwarePlan 2013265921 (2^16) (some arm_neon_simd)
     let harveyCount := plan.stages.foldl (fun n s => if s.reduction == .harvey then n+1 else n) 0
     IO.println s!"Harvey stages: {harveyCount}/{plan.stages.size}"  -- expect all
   ```

3. **NEON vs scalar comparison** — compilar C con plan all-Harvey, validar output

4. **Benchmark** — `--pipeline ultra --hardware arm-neon` vs baseline (si hay regression → investigate)



---

## Lessons (current)

Project-specific lessons learned during current version.
Generalized lessons should be migrated to `~/Documents/claudio/lecciones/lean4/`.
