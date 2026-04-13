# TRZK: Architecture

## Next Version: 3.13.0

### SPIRAL + Compiler Driver + Path A Migration v3.13.0

**Contents**: Two-step NTT decomposition (SPIRAL-style), compiler driver rewired to Path A,
migration of remaining primitives from string emission to verified codegen, ILP2 interleaving
for Goldilocks. Cleanup of legacy code and dead ends from v3.12.0.

**Vision**: Two-step decomposition is the factorization that Discovery (Fibonacci r2/r4
enumeration) CANNOT find. It decomposes NTT_N = NTT_{N/64} × TwiddleMatrix × NTT_64,
where NTT_64 uses omega_64=8 (power-of-2 root → all 6 inner stages use shifts instead
of multiplies). Outer stages use standard Cooley-Tukey. MatOp e-graph deferred to v3.14.0.

**State post-v3.12.0**: Gap Goldilocks 0.96x (TRZK faster than Plonky3 scalar).
F5c (Stmt.call) resolved emission bottleneck. Discovery wired but N≤1024 only
(Lean interpreter slow). Team feedback (PR #11, #12): Path B codegen copy-paste,
types don't match, verification status unclear. NTT trick reverted (hurts without
two-step), lazy real confirmed dead end.

**Dead ends (DO NOT REPEAT)**:
- Lazy real: storeTrunc corrupts values > p. Requires wideType arrays → 2x memory, kills F5c.
- Prefetch N ≤ 2^14: cache=0 (data fits in L1). Only useful N ≥ 2^16.
- NEON Karatsuba for Goldilocks: scalar mul+umulh = 2 instr vs Karatsuba 12+.
- NTT trick standalone: reverted in v3.12.0 (0.96→1.18x). Only useful WITH two-step.

**4 Phases**:
- Phase E: Cleanup + infrastructure (1-2 days, ~-260 LOC net)
- Phase F: Compiler driver + Path A migration (3-4 days, ~-611 LOC net)
- Phase G: ILP2 for Goldilocks (2-3 days, ~50 LOC)
- Phase H: Two-Step NTT (5-6 days, ~293 LOC)
- Phase I: Optional (prefetch, four-step, Bowers)

**Key infrastructure VERIFIED against code (2025-04-13)**:
- `nttDataIndex` (VerifiedPlanCodeGen:240) has NO offset/stride — H.2 adds them
- `nttTwiddleIndex` (VerifiedPlanCodeGen:246) has NO twiddleOffset — H.2 adds it
- `NTTStage` (NTTPlan:66-74) has NO useShift — H.1 adds it
- `generateCandidates` (NTTPlanSelection:97-126) has 11 candidates — H.11 adds two-step
- `goldi_mul_tw` (VerifiedPlanCodeGen:657), `goldi_butterfly4` (:675), `goldi_reduce128` (:630) EXIST
- `friFoldExpr` (:37), `hornerExpr` (:116) return `MixedExpr` — ready for Path A
- `UnifiedCodeGen` imported by PrimitiveOptimizer — F.2-F.4 removes dependency
- `reductionCostForHW .lazy = 0` (CrossRelNTT:96) — E.1 reverts to Solinas cost

#### DAG (3.13.0)

| Nodo | Tipo | Deps | Files | LOC | Status |
|------|------|------|-------|-----|--------|
| N313.1 E.1: Revert lazy cost model | FUND | — | CrossRelNTT.lean, NTTPlan.lean | ~10 | done |
| N313.2 E.2: Compiled TRZK binary | PAR | N313.1 | lakefile.lean, TRZKGen.lean | ~30 | done |
| N313.3 E.3: Eliminate dead code | PAR | N313.1 | CrossEGraphBridge.lean, BreakdownBridge.lean, UltraPipeline.lean | ~-300 | done |
| N313.4 E.4: Benchmark Rust vs Plonky3 | HOJA | N313.1 | benchmark scripts | ~0 | pending-measurement |
| N313.5 F.1: Compiler driver → UltraPipeline | CRIT | N313.1 | Compile.lean | ~50 | done |
| N313.6 F.2: FRI fold Path A | PAR | N313.1 | PrimitiveOptimizer.lean | ~100 | done |
| N313.7 F.3: Horner Path A | PAR | N313.1 | PrimitiveOptimizer.lean | ~100 | done |
| N313.8 F.4: Dot product Path A | PAR | N313.1 | PrimitiveOptimizer.lean | ~80 | done |
| N313.9 F.5: Remove stale imports (partial — Phase23Integration still uses NTTPlanCodeGen) | HOJA | N313.6, N313.7, N313.8 | Bench.lean, MatNodeOps.lean | ~-4 | done |
| N313.10 F.6: Verification Status README | PAR | N313.5 | README.md | ~30 | done |
| N313.11 F.7: CI benchmark validation | PAR | N313.5 | .github/workflows/ci.yml | ~50 | done |
| N313.12 G.1: ILP2 interleaving Goldilocks F5c | PAR | N313.1 | VerifiedPlanCodeGen.lean | ~50 | done |
| N313.13 H.1-H.6: Two-step infrastructure | FUND | N313.1 | NTTPlan.lean, VerifiedPlanCodeGen.lean, NTTPlanSelection.lean, MatNodeOps.lean | ~43 | done |
| N313.14 H.7-H.9: Python reference + validation (stage-split, not four-step) | CRIT | N313.13 | Tests/benchmark/ | ~85 | done |
| N313.15 H.10-H.12: mkTwoStepPlan (shift stages) + generateCandidates | PAR | N313.13 | NTTPlanSelection.lean | ~45 | done |
| N313.16 H.13-H.17: useShift dispatch + preambles (scope reduced from four-step) | CRIT | N313.14, N313.15 | VerifiedPlanCodeGen.lean, NTTPlanSelection.lean, CrossEGraphProtocol.lean, MatNodeOps.lean | ~25 | done |
| N313.17 H.18-H.19: Validation + benchmark | HOJA | N313.16 | Tests/benchmark/ | ~25 | done |

#### Formal Properties (3.13.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N313.1 | reductionCostForHW .lazy ≠ 0 (matches Solinas cost) | PRESERVATION | P0 |
| N313.1 | costAwareReductionForBound never returns .lazy | PRESERVATION | P0 |
| N313.5 | trzk --target c produces verified C via Path A | SOUNDNESS | P0 |
| N313.6 | FRI fold Path A output numerically identical to Path B | EQUIVALENCE | P0 |
| N313.7 | Horner Path A output numerically identical to Path B | EQUIVALENCE | P0 |
| N313.8 | Dot product Path A output numerically identical to Path B | EQUIVALENCE | P0 |
| N313.9 | grep "import.*UnifiedCodeGen" returns 0 active importers | PRESERVATION | P0 |
| N313.12 | ILP2 output numerically identical to non-ILP2 | EQUIVALENCE | P0 |
| N313.13 | useShift=false produces identical behavior to v3.12 | PRESERVATION | P0 |
| N313.13 | nttDataIndex(offset=0,stride=1) = v3.12 nttDataIndex | PRESERVATION | P0 |
| N313.14 | two_step_ntt == reference_dit_ntt for ALL sizes × inputs | EQUIVALENCE | P0 |
| N313.15 | mkTwoStepPlan.wellFormed = true | SOUNDNESS | P0 |
| N313.15 | planTotalCostWith includes twiddle matrix cost for two-step | SOUNDNESS | P0 |
| N313.16 | lowerTwoStepNTT produces valid C (compiles + runs) | SOUNDNESS | P0 |
| N313.16 | Two-step output numerically identical to standard NTT | EQUIVALENCE | P0 |
| N313.17 | benchmark validation PASS + gap < 0.85x Goldilocks | OPTIMIZATION | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **B1 — E.1 Cleanup Foundation (N313.1)**: FUND, secuencial. Revert lazy cost model: `reductionCostForHW .lazy` = Solinas cost (CrossRelNTT.lean:96), remove `.lazy` from candidates in `costAwareReductionForBound` (L67), restore wellFormed tests. Gate: `lake build` + existing tests PASS. **DONE 2025-04-13.**

- [x] **B2 — E Infrastructure (N313.2, N313.3, N313.4)**: 3 nodos paralelos. E.2: `lake build trzk-gen` nativo. E.3: eliminados CrossEGraphBridge(22 LOC) + BreakdownBridge(146 LOC). E.4: pending-measurement. Gate: `wiring_check.py` W1+W6 PASS, trzk-gen compiles. **DONE 2025-04-13.**

- [x] **B3 — F+G Path A + ILP2 (N313.5, N313.6, N313.7, N313.8, N313.12)**: F.1: Compile.lean rewritten (keyword mode + UltraPipeline). F.2-F.4: PrimitiveOptimizer.lean rewritten (Path A via lowerSolinasFold + lowerHarveyReduce). G.1: F5c ILP2 added (2 Stmt.call per iteration). Gate: `lake build` PASS. **DONE 2025-04-13.**

- [x] **B4 — F Close + Docs (N313.9, N313.10, N313.11)**: F.5: stale imports removed from Bench.lean+MatNodeOps.lean (full delete deferred: Phase23Integration still uses NTTPlanCodeGen). F.6: Verification Status table added to README. F.7: benchmark-validation CI job added. **DONE 2025-04-13.**

- [x] **B5 — H-pre Infrastructure (N313.13)**: FUND, secuencial. H.1: useShift in NTTStage. H.2: offset/stride/twiddleOffset. H.3: butterflyCost useShift. H.4: goldi_butterfly4_shift preamble. H.5: twiddle matrix cost. H.6: Hashable+DecidableEq MatOp. ALL backward compatible. Gate: `lake build` 3136 jobs PASS. **DONE 2025-04-13.**

- [x] **B6 — H De-risk + Plan (N313.14, N313.15)**: H.7-H.9: Python validation — shift NTT == standard NTT (40/40 PASS, Goldilocks+BabyBear). Pow2 analysis: last 2 stages 100%, stage-2-before 50%. H.10-H.12: mkTwoStepPlan with useShift=true for last 4 stages + push in generateCandidates. Four-step deferred to v3.14.0 (DIT bit-reversal permutation complexity). **DONE 2025-04-13.**

- [x] **B7 — H Codegen (N313.16)**: Scope reduced (stage-split, not four-step). useShift dispatch in lowerStageR4 + lowerStageVerified + lowerStageVerified_ILP2. R2 preambles goldi_butterfly_shift (C+Rust). twiddle matrix cost removed (not needed for stage-split). Import fixes (MatNodeOps, CrossEGraphProtocol). Gate: generated C compiles + output matches Python reference 100%. **DONE 2025-04-13.**

- [x] **B8 — H Wire + Benchmark (N313.17)**: Validation: 3/3 PASS (N=128,256,1024 vs Python ref). Performance: shift R2 plan is 13% SLOWER than standard (popcnt branch overhead > shift savings). selectBestPlan correctly picks R4 plan. **Stage-split shift not beneficial; four-step (v3.14.0) needed for real gain. DONE 2025-04-13.**

#### Orden Topológico

```
B1 → B2 → B3 → {B4, B5} → B6 → B7 → B8
```

B4 y B5 son paralelos (B4: F close + docs, B5: H-pre infra). Sin conflictos de archivo.
B3 y B5 NO son paralelos (G.1 y H-pre ambos tocan VerifiedPlanCodeGen.lean).

#### Expectations

```
                      Goldilocks (0.96x)    BabyBear (+62.8%)
Phase E (cleanup):    sin cambio            sin cambio
Phase F (driver+CI):  sin cambio perf       mejor tooling + confianza
Phase G (ILP2):       ~0.80-0.86x           N/A (k≤32)
Phase H (two-step):   ~0.65-0.75x           N/A (solo Goldilocks)
─────────────────     ──────────────        ─────────────────
Acumulativo:          ~0.65-0.80x           +70-85% vs Plonky3
Neto código:          -530 LOC (más limpio, menos legacy)
```

---

## Planned: v3.14.0 — Cost Model Feedback + Four-Step NTT + MatOp E-Graph

**3 Ejes, ~516 LOC, 8-11 días.** Detalle completo en TRZK_spiral_idea.md §3.8.

**State post-v3.13.0**: Infraestructura two-step lista. Stage-split shift +13% slower
(popcnt branch overhead). selectBestPlan correctly picks R4 over two-step R2.
Four-step decomposition needed for real gain (~100% pow2 inner, no runtime check).

#### DAG (3.14.0)

| Nodo | Tipo | Deps | LOC | Status |
|------|------|------|-----|--------|
| N314.1 M.1+M.3: branchCheck + staticShift in butterflyCost | FUND | — | ~15 | done |
| N314.2 M.2: pow2Fraction per stage | PAR | N314.1 | ~15 | done |
| N314.3 M.3: staticShift for four-step | PAR | N314.1 | ~5 | done (combined with M.1) |
| N314.4 M.4: Calibration script | HOJA | — | ~20 | done |
| N314.5 M.5: feedback_loop.py (3-layer) + cost predictions in report | CRIT | N314.1,2 | ~60 | done |
| N314.6 Eje 2a: Python four-step verification | FUND | — | ~70 | done |
| N314.7 DIF butterfly preambles C+Rust | PAR | N314.6 | ~46 | done |
| N314.8 lowerStageDIF dispatch | PAR | N314.7 | ~15 | done |
| N314.9 emitFourStepC (col_DIF + bitrev + twiddle + row_DIF + bitrev) | CRIT | N314.8,6 | ~85 | done |
| N314.10 mkFourStepPlan + twiddle tables | PAR | N314.3,6 | ~50 | pending |
| N314.11 Four-step validation + benchmark | HOJA | N314.9,10 | ~30 | pending |
| N314.12 Eje 3a: NodeOps MatOp instance + laws | FUND | — | ~45 | pending |
| N314.13 Eje 3b: MatExprFlat + Extractable + bridge | PAR | N314.12 | ~30 | pending |
| N314.14 Eje 3c: applyBreakdownInEGraph | CRIT | N314.13 | ~40 | pending |
| N314.15 Eje 3d: UltraPipeline wiring | HOJA | N314.14,9 | ~35 | pending |

#### Bloques

- [x] **B1 — Cost Model Foundation (N314.1+M.3)**: FUND. branchCheck + staticShift. Runtime shift now costs MORE than standard (14 vs 12 R2), matching v3.13.0 measurement. Static shift costs LESS (9, for future four-step). **DONE 2025-04-13.**
- [x] **B2 — Cost Model Extensions (N314.2, N314.3, N314.4)**: M.2: pow2Fraction field + empirical assignment in mkTwoStepPlan. M.3: done in B1. M.4: calibrate_hw.py — measured mul=1.4c shift=1.6c add=1.4c branch=2.5c (latency vs throughput delta explainable). **DONE 2025-04-13.**
- [x] **B3 — Feedback Loop (N314.5)**: CRIT. Cost predictions added to UltraPipeline report. feedback_loop.py extracts + ranks all candidates. Goldilocks 11 candidates, R4 wins (65280), two-step penalized (96256). BabyBear 10 candidates (no two-step). **DONE 2025-04-13.**
- [x] **B4 — Four-step Python verification (N314.6)**: FUND. Both variants verified 6/6 PASS for Goldilocks. (1) Naive four-step: col_DFTs→tw→row_DFTs→unstride=DFT. (2) **DIF+bitrev pipeline (Opción B corrected)**: col_DIF→col_bitrev→tw(ω^(r·c))→row_DIF→row_bitrev→unstride=DFT. Row DIF uses ω_m=ω_64=8 → 100% pow2 → shifts! Overhead: 2 bitrev passes O(N) + 1 twiddle + 1 unstride. Bug was: rows-first order is WRONG (twiddle depends on original col index lost after row DFT); correct order is cols-first. **DONE 2025-04-13.**
- [x] **B5 — DIF preambles + dispatch (N314.7, N314.8)**: R2+R4 DIF shift preambles (C+Rust, ~46 LOC). 3-point dispatch (direction × useShift) in lowerStageR4, lowerStageVerified, lowerStageVerified_ILP2. **DONE 2025-04-13.**
- [x] **B6 — Four-step codegen (N314.9)**: CRIT. `emitFourStepC`: 6-phase C generator (col_DIF + col_bitrev + twiddle + row_DIF + row_bitrev + unstride). N=1024: 1024/1024 match naive DFT. **KEY FINDING**: ref_dit ≠ DFT (different transform, not permutation). Four-step computes DFT, pipeline uses ref_dit → incompatible. Integration deferred to v3.15.0 (pipeline migration to DFT standard). **DONE 2025-04-13.**
- [ ] **B7 — Four-step plan + validation (N314.10, N314.11)**: HOJA. mkFourStepPlan + benchmark gap < 0.85x.
- [ ] **B8 — NodeOps MatOp (N314.12)**: FUND. 7 ctors, 4 laws. Verify no import cycle.
- [ ] **B9 — MatExprFlat + Extractable (N314.13)**: PAR. MatExprFlat ~10 LOC + reconstruct ~10 LOC + bridge ~10 LOC.
- [ ] **B10 — applyBreakdownInEGraph (N314.14)**: CRIT. Inject BreakdownRule into EGraph MatOp.
- [ ] **B11 — UltraPipeline wiring (N314.15)**: HOJA. E-graph plan competes in selectPlanWith.

#### Orden Topológico

```
{B1, B4, B8} (parallel — independent foundations)
  → {B2, B3} + {B5, B9}
  → B6 + B10
  → {B7, B11}
```

#### Expectations

```
                      Goldilocks (0.96x)
Cost model (Eje 1):  sin cambio perf (mejor predicción)
Feedback (Eje 1b):   sin cambio perf (detecta divergencias)
Four-step (Eje 2):   ~0.85x (12% savings, conservador)
MatOp e-graph (3):   sin cambio perf (infra, descubre factorizaciones)
─────────────────     ──────────────
Post-v3.14.0:         ~0.75-0.85x vs Plonky3 scalar
```

---

## Completed: v3.12.0 — F5c Butterfly + Discovery Wiring (Phase A+B)

F5c butterfly Stmt.call resolved Goldilocks emission bottleneck (gap 1.28x→0.96x).
Discovery wired via selectBestPlanExplored. NTT trick reverted (hurts without two-step).
Lazy reduction confirmed dead end (storeTrunc corrupts, kills F5c). Phase C+D abandoned.

## Completed: v3.11.0 — Bound-aware Codegen + NTTStrategy (BF1+BF4)

BF1: boundK param in lowerDIFButterflyByReduction, dispatch by bounds. DONE.
BF4: twoStepGoldilocks added to NTTStrategy. DONE.
BF2+BF3 (conditionalSub + Stark252): deferred to future version.

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
