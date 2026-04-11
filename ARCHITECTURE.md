# TRZK: Architecture

## Next Version: 3.11.0

### Bound-aware Discovery Engine v3.11.0

**Contents**: Transform TRZK from hardcoded optimizations to automatic discovery platform.
Add `conditionalSub` constructor to MixedNodeOp, connect bounds to sideCondCheck in
e-graph saturation, extend NTTStrategy with twoStepGoldilocks.

**Vision**: The e-graph discovers optimizations like AC-6 (conditional subtract for
bounded inputs) AUTOMATICALLY for any field, without per-field `if k > 32` hardcoding.
Test: add Stark252 field with ZERO field-specific rules → e-graph discovers optimal reduction.

**4 Phases**:
- F1 (1d): Bound-aware codegen — pass stage.outputBoundK to butterfly, dispatch by bounds
- F4 (0.5d, parallel): twoStepGoldilocks in NTTStrategy (~15 LOC, very low risk)
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
| N311.1 F1: Bound-aware codegen (boundK parameter) | FUND | — | pending |
| N311.2 F4: twoStepGoldilocks NTTStrategy | PAR | — | pending |
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

### Goldilocks NTT v3.10.1 — Correcciones post-retrospectiva

**Contents**: Fair baseline measurement, branchless reduction, conditional subtract,
dynamic cost caching. Separated verification cost from parallelism cost.

**Key results**:
- AC-2: 3-column table → gap vs Plonky3 scalar is **1.52x** (code quality, not parallelism)
- AC-5+AC-6: Branchless reduction + conditional subtract → **10.4% speedup** (N=2^20)
- AC-1: Dynamic cost cached (`computeDynamicCost` + `mkCachedDynamicCostFn`), not activated (interpreter too slow, static cost already optimal per calibration)

**Gap analysis** (N=2^20):
- TRZK verified C: 121.3 ns/elem
- Plonky3 scalar Rust: 79.7 ns/elem (1.52x faster)
- Plonky3 vectorized: 70.2 ns/elem (1.73x faster)
- Gap is CODE QUALITY (stmtToC output vs Rust idioms), not algorithm

**Pending items SUPERSEDED by next phase analysis**:
- AC-3 (NTT trick viability): superseded by NTTStrategy approach in v3.11 planning
- AC-4 (inline asm evaluation): superseded by bound-aware codegen approach (~20 LOC vs ~300 LOC)
- useDynamicCost activation: superseded by bound-aware codegen (bounds flow to codegen directly, no e-graph saturation needed at emit time)

#### DAG (3.10.1)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N3101.1 AC-2: Plonky3 scalar-only benchmark | FUND | — | done |
| N3101.2 AC-1: Dynamic cost caching (not activated) | PAR | — | done |
| N3101.5 AC-5: Branchless product reduction | PAR | — | done |
| N3101.6 AC-6: Conditional subtract for sum/diff | PAR | N3101.5 | done |
| N3101.3 AC-3: NTT trick viability | GATE | N3101.1 | superseded |
| N3101.4 AC-4: Inline asm evaluation | HOJA | N3101.1 | superseded |

---

## Version: 3.10.0

### Goldilocks NTT v3.10.0 — Stage Specialization + Canal Dinámico + ILP

**Contents**: Close the 1.5-1.8x gap vs Plonky3 for Goldilocks NTT. Three complementary
optimizations: (1) stage specialization for power-of-2 twiddles (~40% of butterflies skip
multiply), (2) connect e-graph dynamic cost to plan selection, (3) ILP explicit interleaving
for the 60% of butterflies that still need full multiply.

**Design**: Twiddle table is already CT standard (`omega^(pair * 2^stage)`, verified 0
mismatches). 39.71% of butterflies have trivial twiddles (14.28% tw=1, 15.61% pow2,
9.81% neg_pow2). Optimization is CODEGEN pure — twiddles are runtime loads, not e-graph
constGate nodes. Plonky3 uses scalar mul+umulh (zero NEON vmull), so NEON Karatsuba
strategy from v3.9.0 is demoted to conditional (Cortex-A76 only).

**Key findings from 4-round adversarial debate (Claude × Gemini × reviewer):**
- Plonky3 PackedGoldilocksNeon: 26 scalar instructions, zero vmull (packing.rs:311-382)
- Apple Silicon: mul/umulh throughput 0.5 cycles (2/cycle, units X3+X4)
- ord_p(2) = 192 = 2^6×3: power-of-2 primitive roots exist for N ≤ 64
- -O2 does NOT auto-interleave scalar butterfly multiplications (verified via asm)
- Our twiddle table IS CT standard (reference_ntt.py:42, 0 mismatches)
- lazy_eq_solinas_cost uses reductionCostForHW directly (NOT Plan.totalCost) — safe

**Lessons applied**: L-733 (DIT/DIF consistency), L-740-745 (64-bit emission bugs),
L-513 (pipeline decomposition soundness), L-201 (native_decide for large primes).

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean` (MODIFY — TA stage specialization + TD ILP2)
- `AmoLean/EGraph/Verified/Bitwise/BoundIntegration.lean` (MODIFY — T12 semanticMatchStep bypass)
- `AmoLean/EGraph/Verified/Bitwise/NTTPlan.lean` (MODIFY — T7 totalCostWith)
- `AmoLean/EGraph/Verified/Bitwise/NTTPlanSelection.lean` (MODIFY — T7 planTotalCostWith)
- `AmoLean/EGraph/Verified/Bitwise/UltraPipeline.lean` (MODIFY — T8 wire useDynamicCost)
- `AmoLean/EGraph/Verified/Bitwise/NTTFactorizationRules.lean` (MODIFY — TB if viable)
- `Tests/benchmark/reference_ntt.py` (MODIFY — TB twiddle gen if viable)

**Constraints**:
- 0 new constructors in MixedNodeOp (TB adds to NTTStrategy, NOT MixedNodeOp)
- 0 sorry in existing theorems
- BabyBear benchmarks ±3% vs v3.7.0
- computeCostsF signature UNTOUCHED
- reductionCostForHW static PRESERVED (dynamic opt-in via useDynamicCost)
- lazy_eq_solinas_cost rfl SAFE (uses reductionCostForHW directly, not Plan.totalCost)

#### DAG (3.10.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N310.1 TA: isPow2Twiddle stage specialization in codegen | FUND | — | pending |
| N310.2 T12: Fix semanticMatchStep dead code | PAR | — | pending |
| N310.3 TB-1: NTT trick viability study (READ ONLY) | GATE | N310.1 | pending |
| N310.4 TB-2: NTT trick implementation | CRIT | N310.3 | pending |
| N310.5 TB-3: NTT trick validation | HOJA | N310.4 | pending |
| N310.6 T7: Plan.totalCostWith parametrization | FUND | N310.1 | pending |
| N310.7 T8: Wire useDynamicCost | PAR | N310.6 | pending |
| N310.8 TC: Benchmark vs Plonky3 | HOJA | N310.7 | pending |
| N310.9 TD: lowerStageVerified_ILP2 + ilpFactor dispatch | CRIT | N310.8 | pending |

#### Formal Properties (3.10.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N310.1 | isPow2Twiddle correctly identifies pow2 twiddles for all stages | SOUNDNESS | P0 |
| N310.1 | Shift butterfly produces same output as multiply butterfly | EQUIVALENCE | P0 |
| N310.1 | BabyBear NTT unchanged (no pow2 twiddles affect BabyBear) | PRESERVATION | P0 |
| N310.6 | Plan.totalCostWith(reductionCostForHW) = Plan.totalCost | EQUIVALENCE | P0 |
| N310.6 | lazy_eq_solinas_cost rfl proof compiles | INVARIANT | P0 |
| N310.7 | useDynamicCost=false → identical plan selection to v3.9.0 | PRESERVATION | P0 |
| N310.9 | ILP2 output = ILP1 output for all N and inputs | EQUIVALENCE | P0 |
| N310.9 | ILP2 performance >= ILP1 for all sizes | OPTIMIZATION | P0 |

> **QA disposition** (Gemini 1-round):
> - "TB needs MixedNodeOp constructor" → DISMISSED: TB adds to NTTStrategy (5 ctors), not MixedNodeOp (315)
> - "lazy_eq_solinas_cost fragility" → ACCEPTED: documented decoupling in T7 comments
> - "BabyBear pow2 impact" → DISMISSED: TA only fires for Goldilocks omega
> - "ILP platform dependency" → ACCEPTED: handled via HardwareCost + ilpFactor per-plan

#### Dependency Graph

```
BA (TA+T12) → ┬─ BB (TB-1→[go?]→TB-2→TB-3)   ← investigation
              └─ BC (T7→T8→TC)                 ← canal dinámico
                        │
                        ▼
                   BD (TD, probable)            ← ILP explícito
```

Critical path: BA(2d) → BC(2d) → BD(2-3d) = ~6-7 days
BB runs parallel with BC. Total with BB: ~11 days.

#### Bloques

- [ ] **Bloque A — Twiddle optimization + cleanup (N310.1 + N310.2)**: FUND+PAR, sequential. N310.1: isPow2Twiddle in lowerStageVerified (~25 LOC). Pre-compute at Lean codegen time: match isPow2Twiddle → emit shift/identity instead of multiply. 39.71% of butterflies benefit. N310.2: bypass semanticMatchStep (2 LOC). Gate: `benchmark.py --validation-only --fields goldilocks,babybear --sizes 14` + performance pre/post comparison.
- [ ] **Bloque B — NTT Trick (N310.3 → N310.4 → N310.5)**: Investigation. TB-1 (READ ONLY): viability of NTT_64 × NTT_{N/64} decomposition. Gate: 1-page go/no-go document. If go → TB-2 (implementation, CRIT) → TB-3 (validation, 100% match zero tolerance).
- [ ] **Bloque C — Canal dinámico (N310.6 + N310.7 + N310.8)**: FUND→PAR→HOJA, sequential. T7: Plan.totalCostWith (~12 LOC across NTTPlan + NTTPlanSelection, risk LOW). T8: wire useDynamicCost (currently dead code). TC: benchmark vs Plonky3 (confirm gap, gate for D).
- [ ] **Bloque D — ILP explícito (N310.9)**: CRIT, PROBABLE. lowerStageVerified_ILP2 (~40 LOC) + ilpFactor dispatch (~5 LOC) + candidate generation (~3 LOC). Gate: ILP2 = ILP1 numerically + ILP2 >= ILP1 performance + gap table vs Plonky3.

---

## Current Version: 3.9.0

### Goldilocks NTT v3.9.0 — Scalar Verificado + Calibración + E-Graph Discovery + SIMD

**Contents**: Enable Goldilocks (p = 2^64 - 2^32 + 1) in the verified pipeline.
Fix 32-bit hardcoded assumptions in Montgomery REDC and temp declarations.
Empirical calibration of cost model. E-graph rules for shift-subtract + Karatsuba.
Dynamic cost channel (opt-in) connecting e-graph extraction to plan costing.
NeonIntrinsic 64-bit constructors for SIMD butterfly.

**Design**: The verified path (TrustLean.Stmt) has hardcoded 32-bit assumptions:
`lowerMontyReduceSub:50` uses `2^32-1` mask, `cTempDecls` emits `int64_t`,
Rust `wideType := "i64"`. The hand-written path works but is not verified.
Fix via: (1) `lowerGoldilocksProductReduce` using shift-subtract with halves
(mirrors OptimizedNTTPipeline.lean:254-263), (2) parametric `wideType` by k.

**Key insight** (from idea document analysis): Codegen (NeonIntrinsic → Stmt.call)
and optimization (MixedNodeOp → e-graph) are INDEPENDENT. NeonIntrinsic has
pattern matches in only 2 functions (toCName, fromCName) in 1 file. Adding 7
constructors = 14 new lines. MixedNodeOp (315 branches, 15+ files) is UNTOUCHED.

**Lessons applied**: L-731 (Goldilocks exceeds Int64Range — unbounded evaluator),
L-732/L-733 (overflow/butterfly bugs invisible to lake build), L-201 (native_decide
only for p<2^32), L-712 (WellFormedPat for Pattern.eval). Expert: Nat.mul_sub_left_distrib
closes shift-subtract proof directly.

**Files**:
- `AmoLean/Bridge/TrustLeanBridge.lean` (MODIFY — add lowerGoldilocksProductReduce)
- `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean` (MODIFY — k>32 branch + wideType)
- `AmoLean/EGraph/Verified/Bitwise/CrossRelNTT.lean` (MODIFY — InstructionProfile)
- `AmoLean/EGraph/Verified/Bitwise/BitwiseVocabulary.lean` (MODIFY — shift-subtract rule)
- `AmoLean/EGraph/Verified/Bitwise/MixedEMatch.lean` (MODIFY — ModularRewriteRule)
- `AmoLean/EGraph/Verified/Bitwise/MixedSaturation.lean` (MODIFY — modular rule application)
- `AmoLean/EGraph/Verified/Bitwise/ReductionAlternativeRules.lean` (MODIFY — fused-cost)
- `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean` (MODIFY — dynamic cost)
- `AmoLean/EGraph/Verified/Bitwise/UltraPipeline.lean` (MODIFY — useDynamicCost flag)
- `AmoLean/EGraph/Verified/Bitwise/Discovery/OracleAdapter.lean` (MODIFY — cache)
- `AmoLean/Bridge/SIMDStmtToC.lean` (MODIFY — 7 NeonIntrinsic constructors)
- `AmoLean/EGraph/Verified/Bitwise/VerifiedSIMDButterfly.lean` (MODIFY — goldilocksButterfly4Stmt)
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean` (MODIFY — k=64 dispatch)
- `Tests/benchmark/bench_goldi_isolated.c` (NEW — calibration micro-benchmark)
- `Tests/benchmark/bench_goldi_calibration.md` (NEW — calibration report)

**Constraints**:
- 0 new constructors in MixedNodeOp (315 pattern branches)
- 0 sorry in existing theorems
- BabyBear benchmarks ±3% vs v3.7.0 after every block
- computeCostsF signature UNTOUCHED (breaks extractF_correct)
- reductionCostForHW static PRESERVED (dynamic is opt-in)
- lazy_eq_solinas_cost (NTTPlan.lean:302-303, rfl) MUST NOT break
- Dynamic cost fallback for known fields (BabyBear, KoalaBear, Mersenne31)

#### DAG (3.9.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N39.1 lowerGoldilocksProductReduce + k>32 branch | FUND | — | pending |
| N39.2 Parametrize C/Rust temp decls by k | FUND | — | pending |
| N39.3 Goldilocks scalar validation (C + Rust) | GATE | N39.1, N39.2 | pending |
| N39.4 bench_goldi_isolated + InstructionProfile + calibration | FUND | N39.3 | pending |
| N39.5 goldilocksShiftSubRule (MixedSoundRule) | PAR | N39.3 | pending |
| N39.6 ModularRewriteRule + goldilocksKaratsuba | CRIT | N39.3 | pending |
| N39.7 patWidenMulOptimize fused-cost pattern rule | PAR | N39.3 | pending |
| N39.8 reductionCostForHW_dynamic + fallback + A/B benchmark | CRIT | N39.4, N39.5, N39.6, N39.7 | pending |
| N39.9 NeonIntrinsic 64-bit + goldilocksButterfly4Stmt | PAR | N39.3 | pending |
| N39.10 Pipeline dispatch k=64 + full benchmark | HOJA | N39.8, N39.9 | pending |

#### Formal Properties (3.9.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N39.1 | lowerGoldilocksProductReduce_correct: output < p for inputs < p² | SOUNDNESS | P0 |
| N39.1 | k≤32 path unchanged (code gen time dispatch, NOT runtime branch) | PRESERVATION | P0 |
| N39.2 | Goldilocks uses __int128/i128, BabyBear uses int64_t/i64 | INVARIANT | P0 |
| N39.3 | Goldilocks NTT output matches Python reference element-by-element | SOUNDNESS | P0 |
| N39.4 | exprCostHW ratio matches measured ratio: mean rel error < 5% | OPTIMIZATION | P0 |
| N39.5 | hi*(2^32-1) = hi*2^32 - hi via Nat.mul_sub_left_distrib | EQUIVALENCE | P0 |
| N39.6 | Karatsuba mod p correct (φ=2^32, 2^64 ≡ 2^32-1 mod p) | SOUNDNESS | P0 |
| N39.6 | E-graph saturation: e-classes < 100k, iterations < 10/expr | INVARIANT | P1 |
| N39.7 | Fused widening-mul pattern lower cost than decomposed | OPTIMIZATION | P1 |
| N39.8 | Dynamic fallback to static for known fields when P99 error > 5 cycles | PRESERVATION | P0 |
| N39.8 | lazy_eq_solinas_cost rfl SAFE: dynamic is separate function | INVARIANT | P0 |
| N39.8 | useDynamicCost=false → bit-identical results vs v3.7.0 | PRESERVATION | P0 |
| N39.9 | All 7 NeonIntrinsics: toCName/fromCName roundtrip (rfl examples) | INVARIANT | P0 |
| N39.9 | goldilocksButterfly4Stmt: allCallsKnown = true | INVARIANT | P0 |
| N39.10 | Full pipeline: goldilocks arm-neon validation PASS | SOUNDNESS | P0 |
| N39.10 | BabyBear ±3% vs v3.7.0 (golden vector suite) | PRESERVATION | P0 |

> **Trust boundary**: Same as v3.7.0. `evalStmt(.call) = none`. NEON 64-bit intrinsics
> are trusted external calls. Structural proofs verify algorithm; intrinsic semantics are TRUSTED.
> New: `lowerGoldilocksProductReduce_correct` theorem required for soundness (QA mandate).

> **QA disposition** (Gemini 2-round adversarial):
> - "runtime branch in hot loop" → DISMISSED: `if k>32` evaluated at Lean code gen time
> - "rfl invariant risk" → DISMISSED: dynamic is separate function, rfl unfolds static only
> - "non-determinism" → DISMISSED: A/B benchmark is validation, not compiler behavior
> - ACCEPTED: theorem-first for N39.1, e-graph bounds for N39.6, statistical thresholds for N39.8

#### Dependency Graph

```
B0 (FUND) Fix bloqueantes ─→ B1 (GATE) Validar scalar
                                   │
                 ┌─────────────────┬┴────────────────┬──────────────┐
                 ▼                 ▼                  ▼              ▼
           B2 (FUND)         B3a (PAR)          B3b (CRIT)     B5 (PAR)
           Calibración       Shift-sub +        Karatsuba      NeonIntrinsic
           empírica          Fused-cost         ModularRule    64-bit
                 │                 │                 │              │
                 └────────┬────────┘                 │              │
                          ▼                          │              │
                    B4 (CRIT) ◄──────────────────────┘              │
                    Canal dinámico                                   │
                          │                                         │
                          └──────────────┬──────────────────────────┘
                                         ▼
                                   B6 (HOJA)
                                   Pipeline + benchmark
```

Critical path: B0(2-3d) → B1(1d) → B2(2-3d) → B4(2-3d) → B6(1-2d) = ~9-12 days
Parallel branches: B3a, B3b, B5 run alongside B2 after B1

#### Bloques

- [ ] **Bloque 0 — Fix 32-bit bloqueantes (N39.1 + N39.2)**: FUND, sequential. N39.1: `lowerGoldilocksProductReduce` in TrustLeanBridge.lean (shift-subtract with halves, ~15 LOC) + `if k > 32` branch at VerifiedPlanCodeGen.lean:110-111. Theorem-first: `lowerGoldilocksProductReduce_correct` BEFORE merge. N39.2: parametrize temp decls at VerifiedPlanCodeGen.lean:366,373-374,392,398-400,409-411. Gate: `lake build` + `benchmark.py --validation-only --fields babybear,koalabear,mersenne31 --sizes 14` (no-regression).
- [ ] **Bloque 1 — Validar scalar Goldilocks (N39.3)**: GATE. Gate: `benchmark.py --validation-only --fields goldilocks --hardware arm-scalar --sizes 14` (C + Rust). PBT: near-overflow inputs, products requiring full 128-bit intermediate.
- [ ] **Bloque 2 — Calibración empírica (N39.4)**: FUND, sequential. `bench_goldi_isolated.c` with 4 variants (fold_mul, fold_shiftsub, fold_halves, NEON Karatsuba 2-lane). Run 1000+ iterations, report std-dev. Build InstructionProfile. Validate exprCostHW ratios: mean relative error < 5%. Gate: calibration report in `bench_goldi_calibration.md`.
- [ ] **Bloque 3a — E-graph rules ligeras (N39.5 + N39.7)**: PAR, agent team. N39.5: goldilocksShiftSubRule via Nat.mul_sub_left_distrib (~15 LOC). N39.7: patWidenMulOptimize via ReductionAlternativeRules (~10 LOC). Gate: `optimizeReduction babybearConfig arm_cortex_a76` produces same strategyName as v3.7.0.
- [ ] **Bloque 3b — Karatsuba ModularRewriteRule (N39.6)**: CRIT, sequential. ModularRewriteRule (~10 LOC in MixedEMatch.lean) + goldilocksKaratsuba. Math: φ=2^32, 2^64 ≡ 2^32-1 (mod p), standard Goldilocks identity (NOT extension field). E-graph bounds: maxNodes:=100000, maxIterations:=10. Gate: `lake build` + BabyBear unchanged + saturation terminates.
- [ ] **Bloque 5 — NeonIntrinsic 64-bit (N39.9)**: PAR, sequential. 7 constructors: add_u64, sub_u64, load2_u64, store2_u64, widening_mul32, narrow_high32, narrow_low32. 14 new lines (toCName + fromCName). `goldilocksButterfly4Stmt` following sqdmulhButterflyStmt pattern. Gate: `lake build` + fromCName roundtrip examples + allCallsKnown.
- [ ] **Bloque 4 — Canal dinámico (N39.8)**: CRIT, sequential. 5-step protocol: (1) compareCosts diagnostic for all (field, hw), (2) `reductionCostForHW_dynamic` with fallback for known fields (P99 error > 5 cycles → static), (3) A/B benchmark BabyBear ≥ A-3%, (4) cache 14→1 saturations, (5) graduation. `useDynamicCost := false` default. lazy_eq_solinas_cost SAFE: dynamic is separate function, rfl unfolds static only. Gate: comparison table + A/B benchmark + useDynamicCost=false identical to v3.7.0.
- [ ] **Bloque 6 — Pipeline + benchmark final (N39.10)**: HOJA. Dispatch emitStageC/Rust for k=64 → goldilocksButterfly4Stmt. neonTempDecls64 for uint64x2_t, uint32x2_t. Golden vector suite for all fields. Gate: `benchmark.py --validation-only --fields goldilocks --hardware arm-neon --sizes 14` PASS + BabyBear ±3% vs v3.7.0.

---

## Version: 3.8.0

### Verified Rust SIMD NTT v3.8.0

**Contents**: Emit Rust NEON NTT from the same verified Stmt IR that produces C NEON.
Reuses v3.7.0 butterflies (Stmt.call sequences) + NeonIntrinsic ADT. New: `simdStmtToRust`
emitter (Rust `core::arch::aarch64` intrinsics in `unsafe` blocks), Rust helpers, and
`emitSIMDNTTRust` pipeline. Enables apple-to-apple benchmark vs Plonky3 monty-31.

**Design**: Extend, don't duplicate. ARM NEON intrinsics have identical names in C and Rust.
The only differences: `unsafe { }` wrapping, tuple struct decomposition (`.0/.1` vs `.val[0]`),
raw pointer setup (`as_ptr().add(i)` vs `&data[i]`), and variable declarations
(`let mut nv0: int32x4_t` vs `int32x4_t nv0`). See TRZK_rust_insights.md §5-6.

**Key reuse from v3.7.0** (zero modification):
- `sqdmulhButterflyStmt`, `hs2ButterflyStmt`, `hs1ButterflyStmt` — Stmt-pure, backend-agnostic
- `NeonIntrinsic` ADT (21 constructors), `isVoid`, `fromCName`, `neonCall`/`neonCallVoid`
- `countCalls`, `collectCallNames`, `allCallsKnown` — structural verification infra
- All 12 theorems in `VerifiedSIMDButterflyProofs.lean` — apply to Rust path too (same Stmt)

**New components**:
- `NeonIntrinsic.toRustCall` — wraps `toCName` in `unsafe { }`
- `simdStmtToRust` — Rust SIMD emitter (gemelo de `simdStmtToC`)
- `neonTempDeclsRust`, `deinterleaveHelperRust`, `interleaveStoreHelperRust`
- `emitStageRust`, `emitSIMDNTTRust` — Rust pipeline (gemelo de C pipeline)
- `UltraConfig.rustSIMD` flag + benchmark wiring

**Lessons applied**: L-730 (audit wiring — no string bypass), L-728 (fuel-free Stmt chains),
L-309 (Rust idioms: `as usize`, unsafe blocks, raw pointers).

**Files**:
- `AmoLean/Bridge/SIMDStmtToC.lean` (MODIFY — add toRustCall + simdStmtToRust)
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean` (MODIFY — add Rust helpers + emitSIMDNTTRust)
- `AmoLean/EGraph/Verified/Bitwise/UltraPipeline.lean` (MODIFY — rustSIMD flag)
- `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean` (MODIFY — Rust SIMD wiring)
- `Tests/benchmark/emit_code.lean` (MODIFY — --rust-simd flag)
- `Tests/benchmark/lean_driver.py` (MODIFY — rust_simd param)
- `Tests/benchmark/benchmark.py` (MODIFY — --rust-simd flag)

#### DAG (3.8.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N38.1 toRustCall + simdStmtToRust emitter | FUND | — | pending |
| N38.2 Rust SIMD helpers + temp declarations | FUND | — | pending |
| N38.3 emitSIMDNTTRust — full Rust SIMD NTT generator | CRIT | N38.1, N38.2 | done |
| N38.4 Pipeline integration (rustSIMD flag + wiring) | CRIT | N38.3 | done |
| N38.5 Validation + benchmark vs Plonky3 | HOJA | N38.4 | done |

#### Formal Properties (3.8.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N38.1 | simdStmtToRust produces non-empty output for all 3 butterflies | INVARIANT | P0 |
| N38.1 | simdStmtToRust delegates non-call Stmt to stmtToRust | EQUIVALENCE | P0 |
| N38.1 | toRustCall wraps every intrinsic in unsafe block | INVARIANT | P0 |
| N38.3 | emitSIMDNTTRust produces compilable Rust for BabyBear 2^14 | INVARIANT | P0 |
| N38.4 | benchmark.py --rust-simd --validation-only PASS (end-to-end chain) | SOUNDNESS | P0 |
| N38.5 | Rust SIMD output validates against Python NTT reference (performance run) | SOUNDNESS | P0 |
| N38.5 | Performance within ±10% of C SIMD verified path | OPTIMIZATION | P1 |
| N38.5 | Plonky3 monty-31 direct comparison with concrete μs numbers | OPTIMIZATION | P0 |

> **Trust boundary**: Identical to v3.7.0. `evalStmt(.call) = none`. The 12 structural
> theorems from v3.7.0 apply unchanged — the Stmt is the same, only the emitter differs.
> Rust intrinsic semantics are trusted (ARM-specified, same as C).

#### Bloques

- [ ] **Bloque 0 — Rust Emitter (N38.1 + N38.2)**: Add `toRustCall` + `simdStmtToRust` to SIMDStmtToC.lean. Add Rust helpers + temp decls to SIMDEmitter.lean. Gate: `lake build` + smoke tests with butterfly → Rust string.
- [ ] **Bloque 1 — Rust NTT Generator (N38.3)**: Create `emitStageRust` + `emitSIMDNTTRust` in SIMDEmitter.lean. Gate: generates complete Rust NTT function for BabyBear 2^14.
- [ ] **Bloque 2 — Pipeline + Benchmark (N38.4 + N38.5)**: Wire rustSIMD flag end-to-end. N38.4 gate: `benchmark.py --rust-simd --validation-only --fields babybear --sizes 14` PASS (full chain). N38.5 gate: performance benchmark + Plonky3 direct comparison with concrete numbers.

#### Bloque 0 Detail — Rust Emitter (N38.1 + N38.2)

**N38.1: toRustCall + simdStmtToRust** (SIMDStmtToC.lean, ~60 líneas nuevas)

Infraestructura reutilizada (0 cambios):
- `NeonIntrinsic` inductive (line 35-64) — 21 constructors
- `toCName` (line 68-89) — used by toRustCall internally
- `isVoid` (line 92-94) — shared for void detection
- `fromCName` (line 119-141) — shared for reverse lookup
- `neonCall`/`neonCallVoid` (line 103-110) — Stmt builders unchanged

Infraestructura nueva:
```lean
/-- Map NeonIntrinsic to Rust unsafe call expression. Same names as C (ARM NEON
    intrinsics are identical in core::arch::aarch64), wrapped in unsafe. -/
def NeonIntrinsic.toRustCall (intr : NeonIntrinsic) (argsStr : String) : String :=
  s!"unsafe \{ {intr.toCName}({argsStr}) }"
```

```lean
/-- Emit Stmt to Rust with NEON intrinsic handling.
    Gemelo of simdStmtToC. Differences:
    - Void: "unsafe { fname(args) };" (no result)
    - Value: "result = unsafe { fname(args) };" (with result)
    - Delegation: stmtToRust (not stmtToC) for non-call Stmt
    - joinCode reused as-is -/
def simdStmtToRust (level : Nat) : Stmt → String
```

Smoke tests: 5+ examples covering value-returning, void, addrOf, delegation, butterfly output.

**N38.2: Rust helpers + temp declarations** (SIMDEmitter.lean, ~50 líneas nuevas)

Infraestructura reutilizada:
- `deinterleaveHelperC` (line 546-554) — template for Rust version
- `interleaveStoreHelperC` (line 560-569) — template for Rust version
- `neonTempDecls` (line 575-580) — template for Rust version

Infraestructura nueva:
```lean
def deinterleaveHelperRust : String  -- uses .0/.1 tuple access (not .val[0])
def interleaveStoreHelperRust : String  -- uses int32x4x2_t(a, b) tuple constructor
def neonTempDeclsRust (numSigned numUnsigned numHalf : Nat) : String
  -- "let mut nv0: int32x4_t; ..." (MaybeUninit::uninit().assume_init() for each)
```

Gate: `lake build SIMDEmitter` + helpers produce non-empty compilable Rust fragments.

#### Bloque 1 Detail — Rust NTT Generator (N38.3)

**N38.3: emitStageRust + emitSIMDNTTRust** (SIMDEmitter.lean, ~120 líneas nuevas)

Infraestructura reutilizada:
- `emitStageC` dispatch structure (line 393-460) — template for Rust dispatch
- `emitSIMDNTTC` orchestrator (line 594-698) — template for Rust orchestrator
- `sqdmulhButterflyStmt` / `hs2ButterflyStmt` / `hs1ButterflyStmt` — IDENTICAL Stmts
- `simdStmtToRust` (from N38.1) — emitter

Infraestructura nueva:
```lean
/-- Emit one NTT stage as Rust code. Dispatches by halfSize:
    ≥4 → sqdmulhButterflyStmt via simdStmtToRust
    =2 → hs2ButterflyStmt via simdStmtToRust
    =1 → hs1ButterflyStmt via simdStmtToRust
    Pointer setup: data.as_mut_ptr().add(offset) for raw ptrs. -/
private def emitStageRust (stage : NTTStage) ... : String

/-- Emit complete Rust SIMD NTT function.
    Structure: use statement + helpers + fn sig + temp decls + const broadcasts + stages.
    Output: unsafe fn with #[cfg(target_arch = "aarch64")]. -/
def emitSIMDNTTRust (plan : Plan) (target : SIMDTarget) (k c mu : Nat)
    (funcName : String) (useSqdmulh : Bool) : String
```

Key Rust-specific differences from C in emitStageRust:
- Pointer setup: `let a_ptr = data.as_mut_ptr().add(idx);` (not `int32_t* a_ptr = &data[idx];`)
- Const broadcast: `unsafe { vdupq_n_u32(p) }` (not `vdupq_n_u32(p)`)
- Loop syntax: `for grp in 0..{numGroups} {` (not `for (size_t grp = 0; ...)`)
- Variable init: `let mut nv0: int32x4_t = unsafe { vdupq_n_s32(0) };` (Rust requires init)

Gate: `emitSIMDNTTRust` produces non-empty Rust for BabyBear 2^14 plan.

#### Bloque 2 Detail — Pipeline + Benchmark (N38.4 + N38.5)

**N38.4: Pipeline wiring** (~30 líneas across 5 files)

| Archivo | Cambio | Líneas |
|---------|--------|--------|
| `UltraPipeline.lean:112` | Add `rustSIMD : Bool := false` to UltraConfig | +1 |
| `UltraPipeline.lean:180` | When rustSIMD, call emitSIMDNTTRust instead of emitSIMDNTTC | +3 |
| `OptimizedNTTPipeline.lean:437` | Add rustSIMD param to optimizedNTTC_ultra | +2 |
| `OptimizedNTTPipeline.lean:557` | Add rustSIMD to genOptimizedBenchRust_ultra_simd | +5 |
| `Tests/benchmark/emit_code.lean:30-55` | Add --rust-simd arg, call Rust SIMD path | +8 |
| `Tests/benchmark/lean_driver.py:22-36` | Pass rust_simd flag to Lean | +3 |
| `Tests/benchmark/benchmark.py:36-45` | Add --rust-simd CLI flag | +3 |

Gate: `benchmark.py --rust-simd --validation-only --fields babybear --sizes 14` **PASS**.
This requires the ENTIRE chain to be connected end-to-end:
benchmark.py → lean_driver.py → emit_code.lean → ultraPipeline → emitSIMDNTTRust →
.rs file → rustc → execution → numerical validation against Python NTT reference.
`lake build` alone is NOT sufficient — the gate is runtime correctness.

**N38.5: Validation + Benchmark vs Plonky3** (~1 día)

1. Performance benchmark:
   `benchmark.py --rust-simd --fields babybear --sizes 14` (full run, not --validation-only)
2. Compare times:
   - Rust SIMD verified (new) vs C SIMD verified (v3.7.0)
   - Performance delta must be within ±10%
3. **Plonky3 direct comparison** (mandatory, not optional):
   - Build `Tests/benchmark/bench_plonky3_comparison/` with `p3-baby-bear`, `p3-ntt`, `p3-monty-31`
   - Run `criterion` benchmark for BabyBear NTT on same N, same hardware
   - Report: our Rust SIMD verified vs Plonky3 monty-31 real (μs + % difference)

Gate: `benchmark.py --rust-simd --fields babybear --sizes 14` **PASS** (validation + performance)
+ Plonky3 comparison report with concrete numbers.

---

### v3.7.0 Planning Detail (Option D: Stmt.call + simdStmtToC)

**Contents**: Route NEON butterflies through TrustLean.Stmt IR using Stmt.call constructor + AmoLean wrapper for void/struct intrinsics. TrustLean expanded with `LowLevelExpr.addrOf` (commit 5d42bae) for pointer emission. Includes cleanup: FRIFoldPlan Montgomery fix + reductionCost migration.

**Design**: Option D — chosen after 6 adversarial debates evaluating Options A/A'/B/C/D/D'. See TRZK_filosofico.md §v3.7.0 for full analysis. Post-Block-1 audit identified `&` emission gap resolved via TrustLean expansion + decision to use Approach A (all butterflies via Stmt, including hs2).

**Files**:
- `AmoLean/Bridge/SIMDStmtToC.lean` (NEW — NeonIntrinsic ADT + simdStmtToC wrapper)
- `AmoLean/EGraph/Verified/Bitwise/VerifiedSIMDButterfly.lean` (NEW — butterflies as Stmt)
- `AmoLean/EGraph/Verified/Bitwise/VerifiedSIMDButterflyProofs.lean` (NEW — structural theorems)
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean` (dispatch + NEON decls + helper)
- `AmoLean/EGraph/Verified/Bitwise/FRIFoldPlan.lean` (C1: Montgomery fix)
- `AmoLean/EGraph/Verified/Bitwise/CrossRelNTT.lean` (C2: reductionCost migration)
- `AmoLean/EGraph/Verified/Bitwise/PrimitivesIntegration.lean` (C2: reductionCost migration)

#### Post-Block-1 Audit Decisions (2026-04-08)

1. **`&` issue resolved**: `LowLevelExpr.addrOf` added to TrustLean (commit 5d42bae). `exprToC (.addrOf v)` emits `"&" ++ varNameToC v`. TRZK dependency updated to consume this. Use `.addrOf` for deinterleaveLoad output pointer args.

2. **Approach A for hs2**: ALL butterflies (sqdmulh, hs1, hs2) go through verified Stmt path. No legacy string-emission exceptions. Requires extending NeonIntrinsic ADT with ~6 constructors for 2-lane ops + `sub_s32`.

3. **`sub_s32` as insurance**: Added to ADT regardless of whether unsigned-only restructuring works. Allows fallback to proven signed subtract if needed.

4. **`neonTempDecls` needs `int32x2_t`**: hs2 uses 2-lane intrinsics. Add `int32x2_t nh0, nh1, ...;` declarations alongside existing `nv*` and `nu*`.

5. **`voidIntrinsicNames` sync risk**: Replace string-list lookup with `fromCName : String → Option NeonIntrinsic` reverse map + `isVoid` query. Single source of truth.

6. **`deinterleaveLoad` docstring**: Fix "each constructor maps to one ARM NEON intrinsic" — deinterleaveLoad maps to a custom C helper, not a hardware intrinsic.

#### DAG (3.7.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| C1 Fix FRIFoldPlan Montgomery bug | FIX | — | done |
| C2 Migrate reductionCost callers to reductionCostForHW | CLEANUP | — | done |
| N37.1 NeonIntrinsic ADT + simdStmtToC wrapper | FUND | — | done |
| N37.2 Deinterleave helper function (vld2q decomposition) | FUND | — | done |
| N37.3 NEON temp variable declarations in emitSIMDNTTC | FUND | — | done |
| N37.4 Rewrite all NEON butterflies as Stmt.call sequences | CRIT | N37.1, N37.2, N37.3 | done |
| N37.5 Connect verified SIMD path to emitStageC pipeline | CRIT | N37.4 | done |
| N37.6 Structural verification theorems + trust boundary doc | CRIT | N37.5 | done |
| N37.7 Benchmark regression check (±3% vs v3.6.0) | HOJA | N37.5 | done |

#### Formal Properties (3.7.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N37.4 | Butterflies produce valid Stmt sequences (all calls use NeonIntrinsic names) | INVARIANT | P0 |
| N37.6 | sqdmulh butterfly has 17 operations (structural count) | EQUIVALENCE | P0 |
| N37.6 | All calls in butterfly use known NEON intrinsics (exhaustive check) | INVARIANT | P0 |
| N37.6 | Data flow pattern matches scalar butterfly (prod→reduce→sum→diff→harvey) | EQUIVALENCE | P1 |
| C1 | FRIFoldPlan never returns Montgomery for sums | SOUNDNESS | P0 |

> **Nota**: Trust boundary: `evalStmt(.call) = none`. NEON intrinsics are trusted
> external calls, same as `stmtToC` is trusted for scalar emission.
> Structural proofs verify the ALGORITHM is correct; intrinsic semantics are TRUSTED.

#### Bloques

- [x] **Bloque 0 — Cleanup (C1 + C2)**: C1 FRIFoldPlan Montgomery fix, C2 reductionCost migration. DONE.
- [x] **Bloque 1 — Foundation (N37.1 + N37.2 + N37.3)**: NeonIntrinsic ADT, deinterleave helper, NEON temp decls. DONE. Post-audit: TrustLean expanded with `LowLevelExpr.addrOf` (commit 5d42bae). Approach A decided for hs2.
- [ ] **Bloque 2 — Butterflies as Stmt (N37.4)**: Rewrite sqdmulh, hs1, hs2 butterflies as Stmt.call sequences. PRE-REQUISITES before butterfly rewrite: (1) extend NeonIntrinsic ADT with `sub_s32` + 2-lane ops for hs2 (`load2_s32`, `store2_s32`, `combine_s32`, `get_low_s32`, `get_high_s32`), (2) add `fromCName` reverse map replacing `voidIntrinsicNames`, (3) extend `neonTempDecls` with `int32x2_t nh*` variables, (4) use `.addrOf` for `deinterleaveLoad` output pointer args. See TRZK_filosofico.md §Post-Block-1 Audit.
- [ ] **Bloque 3 — Pipeline Integration (N37.5)**: Add useVerifiedSIMD dispatch to emitStageC.
- [ ] **Bloque 4 — Verification + Benchmark (N37.6 + N37.7)**: Structural theorems + regression check.

---

## Current Version: 3.7.0 (COMPLETE)


### Verified SIMD Codegen v3.7.0 (Option D: Stmt.call + simdStmtToC)

**Contents**: Route NEON butterflies through TrustLean.Stmt IR using Stmt.call constructor + AmoLean wrapper. TrustLean expanded with `LowLevelExpr.addrOf` (commit 5d42bae). Includes cleanup: FRIFoldPlan Montgomery fix + reductionCost migration. All 9 DAG nodes done. 12 theorems, 0 sorry. Benchmark: verified path +3.9% vs legacy.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/FRIFoldPlan.lean`
- `AmoLean/EGraph/Verified/Bitwise/CrossRelNTT.lean`
- `AmoLean/EGraph/Verified/Bitwise/PrimitivesIntegration.lean`
- `AmoLean/EGraph/Verified/Bitwise/CrossEGraphProtocol.lean`
- `AmoLean/Bridge/SIMDStmtToC.lean`
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean`
- `AmoLean/EGraph/Verified/Bitwise/VerifiedSIMDButterfly.lean`
- `AmoLean/EGraph/Verified/Bitwise/VerifiedSIMDButterflyProofs.lean`
- `Tests/benchmark/`

#### DAG (3.7.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| C1 Fix FRIFoldPlan Montgomery bug | PAR | — | done |
| C2 Migrate reductionCost callers to reductionCostForHW | PAR | — | done |
| N37.1 NeonIntrinsic ADT + simdStmtToC wrapper | FUND | — | done |
| N37.2 Deinterleave helper function | FUND | — | done |
| N37.3 NEON temp variable declarations | FUND | — | done |
| N37.4 Rewrite NEON butterflies as Stmt.call sequences | CRIT | N37.1, N37.2, N37.3 | done |
| N37.5 Connect verified SIMD path to emitStageC | CRIT | N37.4 | done |
| N37.6 Structural verification theorems | CRIT | N37.5 | done |
| N37.7 Benchmark regression check | HOJA | N37.5 | done |

#### Formal Properties (3.7.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N37.4 | Butterflies produce valid Stmt (all calls use NeonIntrinsic names) | INVARIANT | P0 |
| N37.6 | sqdmulh butterfly has 17 operations | EQUIVALENCE | P0 |
| C1 | FRIFoldPlan never returns Montgomery for sums | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **Bloque 0 — Cleanup**: C1, C2. DONE.
- [x] **Bloque 1 — Foundation**: N37.1, N37.2, N37.3. DONE. TrustLean expanded (addrOf). Approach A for hs2.
- [ ] **Bloque 2 — Butterflies as Stmt**: N37.4. Pre-reqs: extend ADT + fromCName + neonTempDecls int32x2_t.
- [ ] **Bloque 3 — Pipeline Integration**: N37.5.
- [ ] **Bloque 4 — Verification + Benchmark**: N37.6, N37.7.

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
