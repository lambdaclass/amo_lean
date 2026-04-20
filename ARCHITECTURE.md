# TRZK: Architecture

## Next Version: 3.18.0

### Differential Fuzzing v3.18.0

**Contents**: Triangular differential fuzzing — TRZK vs Plonky3 vs Python naive —
para validación exhaustiva de correctness. Reemplaza el oracle de 14-24 test points
por ~10,000 inputs (random + edge cases). Detalle completo en `research/TRZK_SBB.md`
§12 (líneas 980-1454).

**Vision**: Cobertura estadística de ~10K inputs vs 14-24 actuales. Detección de
bugs históricos (L-732/L-733/L-739) si reaparecen. Onboarding protegido para colega
nuevo que no tiene intuición sobre gotchas del codegen.

**State post-v3.17.0**: v3.17 merged en spiral (PR #21 pendiente de merge a main).
Working tree `feat/v3.18-fuzzing` tiene commit pre-fuzzing `44bff09` (canonical sizes
14/18/20 + batch NTT caveat). Oracle actual: 14/14 PASS (single input per size).

**Mandatory constraints**:
- Exclusivamente differential fuzzing. SIMD migration, anomalía BabyBear, cleanup
  de warnings at source → v3.19 (§13).
- Triangular (TRZK + Plonky3 + Python naive) para N ≤ 1024;
  2-way (TRZK + Plonky3) para N > 1024 (Python O(N²) inviable a N grande).
- NO tocar código Lean. v3.18 es 100% Python + YAML + Markdown.
- Reutilizar ~70% de infraestructura existente: `oracle_validate.py` functions,
  `plonky3_shim` FFI, `reference_ntt.py` / `test_four_step.py` naive DFT, `field_defs`.
- NO modificar `oracle_validate.py` existente (coexisten: oracle como smoke, fuzz como deep).
- Sizing canónico fuzz: triangular {8, 64, 256, 1024} + 2-way {2^14}.
  NO confundir con sizes de benchmark performance (14/18/20, commit 44bff09).

#### DAG (3.18.0)

| Nodo | Tipo | Deps | Files | LOC | Status |
|------|------|------|-------|-----|--------|
| N318.1 Skeleton differential_fuzz.py (imports + argparse + structure) | HOJA | — | Tests/benchmark/differential_fuzz.py | ~30 Py | pending |
| N318.2 trzk_ntt_with_input (stdin-driven harness, binary cache) | CRIT | N318.1 | Tests/benchmark/differential_fuzz.py | ~50 Py | pending |
| N318.3 edge_cases (~15 patterns: all-zero/all-max/boundary/etc) | HOJA | N318.1 | Tests/benchmark/differential_fuzz.py | ~25 Py | pending |
| N318.4 fuzz_one (3-way N≤1024 / 2-way N>1024) + main orchestration | PAR | N318.2, N318.3 | Tests/benchmark/differential_fuzz.py | ~40 Py | pending |
| N318.5 Validation gate: --mode fast passes against v3.17 baseline | GATE | N318.4 | Tests/benchmark/ | 0 | pending |
| N318.6 CI job differential-fuzzing (fast en push) | HOJA | N318.5 | .github/workflows/ci.yml | ~15 YAML | pending |
| N318.7 BENCHMARKS.md §0 Correctness update con fuzz coverage | HOJA | N318.5 | BENCHMARKS.md | ~10 MD | pending |

#### Formal Properties (3.18.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N318.1 | differential_fuzz.py imports clean, no circular deps | COMPLETENESS | P1 |
| N318.2 | trzk_ntt_with_input produces same output as direct emit_standard.lean for same input | EQUIVALENCE | P0 |
| N318.2 | Binary cache avoids re-compilation per iteration | OPTIMIZATION | P0 |
| N318.3 | edge_cases covers ≥15 distinct patterns per field | COMPLETENESS | P0 |
| N318.3 | edge_cases output is deterministic | PRESERVATION | P0 |
| N318.4 | fuzz_one(N≤1024): TRZK == Plonky3 == Python naive element-by-element | EQUIVALENCE | P0 |
| N318.4 | fuzz_one(N>1024): TRZK == Plonky3 element-by-element | EQUIVALENCE | P0 |
| N318.4 | Seed-reproducibility: same seed → same test sequence | PRESERVATION | P0 |
| N318.5 | --mode fast against v3.17 code: 100% PASS | SOUNDNESS | P0 |
| N318.5 | --mode fast runtime ≤ 60s | OPTIMIZATION | P1 |
| N318.6 | CI job differential-fuzzing passes on PR push | SOUNDNESS | P0 |
| N318.7 | BENCHMARKS.md §0 Correctness documents fuzz coverage | COMPLETENESS | P1 |

#### Blocks (3.18.0)

- [ ] B1 — Foundation (N318.1 + N318.3): skeleton + edge_cases en paralelo. Gate: imports clean, edge_cases() ≥15 tuplas.
- [ ] B2 — Pain point (N318.2, CRIT): trzk_ntt_with_input. Gate: binary cache (1 compile, N runs), output = emit_standard.lean.
- [ ] B3 — Main logic (N318.4): fuzz_one + main. Gate: --help OK, --mode fast N=8 × 10 iters PASS.
- [ ] B4 — Validation gate (N318.5, GATE): --mode fast 100%. Si falla → REVERT.
- [ ] B5 — CI integration (N318.6): job differential-fuzzing en ci.yml. Gate: CI verde.
- [ ] B6 — Docs (N318.7): BENCHMARKS.md §0 Correctness agrega capa fuzz. Gate: markdown válido.

Order: `B1 → B2 → B3 → B4 → B5 → B6`

#### Expectations (3.18.0)

Sin cambios de performance (es correctness pura). Valor: cobertura de ~10K inputs
vs 14-24 actuales. Triangular trust en N ≤ 1024, 2-way en N > 1024. ~150 LOC Python
+ 15 YAML + 10 markdown. ~3h de trabajo total estimado.

---

## Previous Version: 3.17.0

### sbb Trick + Benchmark Fairness v3.17.0

**Contents**: Cerrar el gap Goldilocks con Plonky3 vía truco `sbb` localizado en
`goldi_butterfly` + compiler flag parity + fairness del framework de benchmarking.
NO features algorítmicas nuevas. Detalle completo en `research/TRZK_SBB.md` §11
(plan v4, líneas 515-976).

**Vision**: Bajar Goldilocks 1.28x → ~1.05x vs Plonky3 scalar (~18% ganancia total
= flags 3.5% + Opción B 12.4% + branch hints 1-2%). Dejar el framework de
benchmarks honesto (no hay más "0.45x" engañoso escondiendo scalar vs NEON).
Preparar comparabilidad fair para v3.18 (SIMD migration).

**State post-v3.16.0**: Benchmarks reales vs Plonky3 FFI (24/24 oracle PASS).
Rust Goldilocks compila. Gap medido: BabyBear 0.45x, Goldilocks 1.18x (cifra
engañosa — asimetría de compiler flags + SIMD).

**Mandatory constraints**:
- Fase 2 Opción B tiene blast radius = `goldi_butterfly` ÚNICAMENTE. NO tocar
  `goldi_add`, `goldi_sub`, `goldi_reduce128` original, `goldi_butterfly_shift`,
  `goldi_butterfly4`, `goldi_butterfly4_inverted`.
- NO migrar SIMD (diferida a v3.18 con scope 100-120 LOC).
- NO integrar four-step NTT. NO-GO confirmado empíricamente (6-32% SLOWER a
  m=64 N≤2^18). Re-open conditions en `research/TRZK_SBB.md` §11.8 (requiere
  m ∈ {8,16,32} + malloc + ILP2 + N≥2^20 para reconsiderar).
- M5 (`--profile`) default debe quedar `conservative` para no romper histórico.
- M7 (Plonky3 shim scalar-only) es OPCIONAL — no ejecutar en v3.17.
- Duplicación preambles reduce128 (4 sitios) NO se refactora — technical debt.

#### DAG (3.17.0)

| Nodo | Tipo | Deps | Files | LOC | Status |
|------|------|------|-------|-----|--------|
| N317.1 Fase 0.5: flags permanentes (-O3 -mcpu=apple-m1 -flto) | HOJA | — | Tests/benchmark/compiler.py, Tests/benchmark/benchmark_plonky3.py | ~15 Py | done |
| N317.2 Fase 1: Opción A en paths activos (__builtin_expect + branchless carry) | PAR | — | AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean (L1104-1114 C, L1214-1230 Rust) | ~20 | done |
| N317.3 Fase 2: Opción B localizada (goldi_reduce128_from_product en goldi_butterfly) | CRIT | N317.2 | AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean (goldi_butterfly only) | ~35 | rejected (no-op) |
| N317.4 M1: fix stale comment L1101-1103 (R4 DIT añadido en v3.15.0 B3.5) | HOJA | — | AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean | 3 | done |
| N317.5 M2: dead code shift preambles gated por hasShift | HOJA | — | AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean | 4 | done |
| N317.6 M3: stdPlan dedup en UltraPipeline (extraer una vez, usar 2 veces) | HOJA | — | AmoLean/EGraph/Verified/Bitwise/UltraPipeline.lean (L268-290) | 5 | done |
| N317.7 M4: __builtin_expect en butterflies (add/sub/mul_tw) | HOJA | N317.3 | AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean | 10 | done |
| N317.8 M5: benchmark fairness (--profile conservative/match-plonky3 + metadata) | HOJA | — | Tests/benchmark/compiler.py, Tests/benchmark/benchmark_plonky3.py | ~30 Py | done |
| N317.9 M6: commit four-step bench script como evidencia empírica | HOJA | — | Tests/benchmark/bench_four_step_isolated.py | ~100 Py | done |

#### Formal Properties (3.17.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N317.1 | Goldilocks timing con -O3 -mcpu=apple-m1 -flto ≤ baseline -O2 × 0.965 | OPTIMIZATION | P0 |
| N317.1 | benchmark_plonky3.py usa flags del --profile, no hardcoded | PRESERVATION | P0 |
| N317.2 | Output numérico igual a baseline (oracle validation 24/24 PASS) | PRESERVATION | P0 |
| N317.2 | Si assembly diff muestra 0 cambio → documentar no-op | COMPLETENESS | P1 |
| N317.3 | `goldi_reduce128_from_product(a*b)` con a,b < P produce r ∈ [0, P+NEG_ORDER) | SOUNDNESS | P0 |
| N317.3 | `(r >= P) ? r - P : r` canoniza correctamente (bound proof empírico, 200K/0 fails) | SOUNDNESS | P0 |
| N317.3 | goldi_butterfly output element-by-element igual a baseline | EQUIVALENCE | P0 |
| N317.3 | Speedup Goldilocks ≥ 10% end-to-end (esperado 12.4%) | OPTIMIZATION | P0 |
| N317.4 | Comentario L1101-1103 coincide con preambles realmente emitidos | PRESERVATION | P1 |
| N317.5 | Shift preambles emitidos solo si ∃ stage con useShift=true | PRESERVATION | P1 |
| N317.6 | stdPlan idéntico en C path y Rust path post-dedup | PRESERVATION | P0 |
| N317.7 | __builtin_expect aplicado sin cambio semántico (oracle 24/24 PASS) | PRESERVATION | P0 |
| N317.8 | Default profile = "conservative" (no rompe histórico BENCHMARKS.md) | PRESERVATION | P0 |
| N317.8 | Output reporta flags TRZK + Plonky3 + hw mode explícitamente | COMPLETENESS | P0 |
| N317.9 | Bench script reproducible: `python3 bench_four_step_isolated.py` corre end-to-end | COMPLETENESS | P1 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Verificación ejecutable en `research/RUBRICS.md` § v3.17.

#### Bloques

- [x] **B1 — Warmup cosméticos (N317.4 + N317.5 + N317.6 + N317.9)**: 4 nodos HOJA paralelos. M1: stale comment L1101-1103 actualizado. M2: `goldi_mul_tw` + `goldi_butterfly_shift` gated por `hasShift`. M3: `stdPlan` extraído una vez en UltraPipeline. M6: `bench_four_step_isolated.py` committed (351 LOC, reproduce NO-GO: +60.7%/+70.6%/+33.9% SLOWER a N=2^14/2^16/2^18). Gate: `lake build` 3136 jobs PASS + oracle 14/14. **DONE 2026-04-16.**

- [x] **B2 — Benchmark fairness (N317.8 + absorbed)**: Añadido `--profile conservative\|match-plonky3` a `compile_c`/`compile_rust`. Hardcode `cc -O2` en `benchmark_plonky3.py:158` reemplazado. Metadata completa (flags TRZK + Plonky3 + SIMD asymmetry warning). Absorbido fix pre-existente: `use_standard` default flip False→True en validator.py/lean_driver.py/benchmark.py + `--use-legacy` escape hatch. **Hallazgo emergente**: con flags match-plonky3 el gap Goldilocks EMPEORA a 1.67x porque Plonky3 gana ~41% con -O3+LTO mientras TRZK C gana solo ~17%. **DONE 2026-04-16.**

- [x] **B3 — Flags + Opción A (N317.1 + N317.2)**: N317.1 se redujo a 2 LOC CI cleanup (infra ya instalada en B2). N317.2: `__builtin_expect(borrow,0)` + branchless carry linearization en C preamble L1104-1114 + Rust L1214-1230. Gate: assembly diff **−61 ARM instr (−4.1% static)**, oracle 14/14 PASS, timing median pre/post 552→428μs = −22.6% mejor caso en misma sesión (rango −10 a −22%). **DONE 2026-04-16.**

- [x] **B4 — Opción B localizada (N317.3) — EVALUADO Y DESCARTADO**: aplicado `goldi_reduce128_from_product` (non-canonical 11 instr) + `goldi_butterfly` canonicalize explícito. **Oracle 14/14 PASS + 8/8 edge cases PASS (bound proof validado empíricamente: max r = P+1)**. PERO assembly **idéntico** a post-B3 (1434 → 1434 instr) + timing median −1.2% (dentro varianza 20%). Clang `-O2` inlina ambas formas al mismo código. **Revertido**; comentario in-code documenta el experimento + bound proof preservado en `research/TRZK_SBB.md §11.1`. **DONE 2026-04-16.**

- [x] **B5 — `goldi_add` linearización (N317.7)**: aplicado mismo patrón de N317.2 a goldi_add (flag-merge linearization). `goldi_sub` no tocado (ya lineal). `goldi_mul_tw` gated por hasShift (no emitido en default). Gate: **−31 ARM instr incremental** (1434 → 1403, total acumulado −92 instr −6.2%), oracle 14/14 PASS, timing median pre/post 507→467μs = **−8% Goldilocks match-plonky3**. **DONE 2026-04-16.**

- [x] **B5.5 — Rust-vs-Rust benchmark (nuevo, post-B5)**: creado `emit_standard_rust.lean` (37 LOC) + `trzk_rust_timing()` en benchmark_plonky3.py (~100 LOC) + flag `--lang c\|rust\|both` (~40 LOC). **HALLAZGO CRÍTICO**: TRZK Rust vs Plonky3 Rust Goldilocks ratio = **1.07x** (no 1.69x). El 62 puntos porcentuales del gap era COMPILADOR (clang vs rustc+LTO+codegen-units=1), no algoritmo. Regresión guard: TRZK Rust output == TRZK C output byte-idéntico (32/32 PASS, Goldilocks+BabyBear × N=16..16384). **DONE 2026-04-16.**

- [x] **B6 — BENCHMARKS.md rewrite + PR**: Reescrito BENCHMARKS.md con **Rust-vs-Rust como headline primary**: Goldilocks 1.07x, BabyBear 1.27x (parcialmente fair: TRZK scalar vs Plonky3 NEON). C-vs-Rust como secondary tabla. Fair Comparison Matrix completa. Interpretación honesta: el gap era ~11% compiler + ~7% algoritmo, no 18% todo algorítmico. **DONE 2026-04-16.**

#### Orden Topológico

```
B1 → B2 → B3 → B4 → B5 → B6
```

B1/B2/B3 son paralelos en principio (sin deps), pero el prompt de ejecución
prefiere secuencial para simplificar checkpoint + build confidence. B4 depende
de B3 (N317.3 deps N317.2). B5 depende de B4 (N317.7 deps N317.3).

#### Expectations vs Results (medidos en B6)

```
                              Planificado           Real (B6 final)
Goldilocks (baseline 1.28x) → Target: ~1.05x     →  C-vs-Rust: 1.69x
                                                    **Rust-vs-Rust: 1.07x** ✓
BabyBear (baseline 0.45x)   → N/A (unchanged)    →  C-vs-Rust: 0.97x
                                                    Rust-vs-Rust: 1.27x (NEON asymmetry)
```

**Impacto real de cada bloque**:

```
B1 (cosméticos):            sin cambio perf
B2 (M5 fairness):           REVELA gap real; B2→1.67x match-plonky3 (Plonky3 gana +41% con -O3+LTO
                            vs TRZK +17%). Honestidad incrementada.
B3 (Opción A):              −61 ARM instr, −10-22% Goldilocks C (medición noise 20%).
B4 (Opción B localizada):   EVALUADO Y DESCARTADO. Clang inline ambas formas al mismo assembly
                            (1434 → 1434 instr idéntico). No-op, documentado in-code.
B5 (goldi_add linearización): −31 ARM instr incremental (acumulado −92), −8% Goldilocks C.
B5.5 (Rust-vs-Rust):        HALLAZGO CRÍTICO: el 62% del gap aparente era clang vs rustc+LTO,
                            no algoritmo. Fair gap real = ~7% Goldilocks, ~27% BabyBear (con
                            Plonky3 NEON advantage).
B6 (docs):                  BENCHMARKS.md headline = Rust-vs-Rust fair comparison.
```

**Conclusión**: target original ~1.05x no alcanzado en C-vs-Rust (incorrectly framed). En
Rust-vs-Rust el gap real es 1.07x Goldilocks — **7% de gap algorítmico real**, dentro del rango
razonable. Para cerrar: v3.18 investiga migración SIMD en Rust + `core::hint::unlikely` branch
hints.

#### Re-open conditions four-step (preservadas de `research/TRZK_SBB.md` §11.8)

<!-- Four-step NO-GO con condiciones explícitas. NO ejecutar en v3.17.
     Re-open SOLO si hay caso de uso real para N ≥ 2^20 (e.g., recursive
     proof composition). Requisitos acumulativos para re-abrir:
     1. Fix VLA → malloc en emitFourStepC:L862 (1 línea).
     2. Parametrizar m en emitFourStepC para probar m ∈ {8, 16, 32, 64}.
        Análisis de stride: m=64 → 12.5%, m=32 → 25%, m=16 → 50%, m=8 → 100%
        cache line utilization.
     3. Aplicar ILP2 a Phase 4 (rows) para paridad con flat pipeline.
     4. Benchmark con --profile match-plonky3 (M5 de v3.17).
     5. Testear N ∈ {2^18, 2^20, 2^22}.
     Si con TODAS las correcciones four-step sigue SLOWER en N=2^20 →
     cerrar definitivamente. Evidencia empírica baseline commiteada en
     Tests/benchmark/bench_four_step_isolated.py (N317.9). Gaps arquitectónicos
     pendientes: Plan type no representa four-step, planTotalCostWith sin
     branch four-step, planCacheCost asume flat, generateCandidates no lo
     produce, goldi_butterfly_dif_shift falta en emitCFromPlanStandard,
     emitFourStepC viola [Verified codegen only] (string emission pura). -->

#### Fair Comparison Matrix (ref. `research/TRZK_SBB.md` §11.10)

Post-v3.17 los benchmarks reportados son comparaciones fair **solo para
Goldilocks scalar-vs-scalar**. BabyBear NEON-vs-NEON requiere v3.18. BabyBear
scalar-vs-scalar fair requiere M7 opcional (Plonky3 shim scalar-only, no
ejecutar en v3.17).

---

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

## Next Version: 3.16.0

### Benchmark Framework C + Rust v3.16.0

**Contents**: Puesta a punto del framework de benchmark y testing. NO features nuevas.
Métricas de correctness y performance rigurosas, reproducibles, presentables.
Detalle completo en TRZK_spiral_idea.md §3.10.

**Vision**: Saber dónde estamos vs Plonky3 real. Tener Rust funcional. CI completo.
Los números deben cumplir los 6 requisitos de reporting (§3.10 puntos 0-5).

**State post-v3.15.0**: NTTs correctas (DFT estándar, 36/36 PASS). Pipeline ultra activa
(R4 inverted, ILP2, bound-aware). Rust Goldilocks no compila (type mismatch u64→u128).
Benchmarks comparan contra P3 naive, no Plonky3 real. "0.96x" de v3.12.0 era INVÁLIDO.

**Mandatory constraints**:
- SOLO benchmark/testing. No four-step, no SIMD, no features nuevas.
- Scalar only (C -O2, Rust --release). SIMD → v3.17.0.
- B2 es el ÚNICO bloque que toca codegen. Todo lo demás es infra de test aislada.
- TODO benchmark debe cumplir los 6 requisitos de reporting (§3.10).

#### DAG (3.16.0)

| Nodo | Tipo | Deps | Files | LOC | Status |
|------|------|------|-------|-----|--------|
| N316.1 Oracle Validation (TRZK C vs Plonky3 real via FFI) | CRIT | — | Tests/benchmark/oracle_validate.py | ~130 | done |
| N316.2 Rust type mismatch fix (17 preambles u64→u128) | CRIT | — | VerifiedPlanCodeGen.lean | ~20 | done (Goldilocks) |
| N316.3 Benchmark vs Plonky3 real timing | PAR | — | Tests/benchmark/benchmark_plonky3.py | ~170 | done |
| N316.4 Pipeline value benchmark (baseline vs winner) | PAR | N316.2 | Tests/benchmark/benchmark_pipeline.py | ~130 | done |
| N316.5 Limpieza bench binary + output directory structure | PAR | — | OptimizedNTTPipeline.lean, .gitignore | ~-30 | done |
| N316.6 CI completo (Rust + Oracle gate) | HOJA | N316.1, N316.2 | .github/workflows/ci.yml | ~10 | done |
| N316.7 BENCHMARKS.md final report | HOJA | N316.1-N316.5 | BENCHMARKS.md | ~80 | done |

#### Formal Properties (3.16.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N316.1 | TRZK C output == Plonky3 output element-by-element | EQUIVALENCE | P0 |
| N316.2 | Rust Goldilocks compiles with rustc --release | SOUNDNESS | P0 |
| N316.2 | Rust Goldilocks NTT output == Python standard DFT | EQUIVALENCE | P0 |
| N316.3 | Performance numbers reported with 6 reporting requirements | COMPLETENESS | P0 |
| N316.5 | Bench binary runs without internal correctness check | PRESERVATION | P0 |
| N316.6 | CI: C + Rust scalar + Oracle all PASS | SOUNDNESS | P0 |

#### Bloques

- [x] **B1 — Oracle Validation (N316.1)**: CRIT. oracle_validate.py (TRZK C vs Plonky3 real via FFI ctypes). R2: 14/14 PASS (BabyBear 7/7 + Goldilocks 7/7). R4: 10/10 PASS. Total 24/24. **DONE 2026-04-14.**

- [x] **B2 — Rust Type Fix (N316.2)**: CRIT. Goldilocks: 7 standard preambles → u128 return + u128 index params + internal as u64/as usize casts. bitRevPermutePreambleRust refactored with retType + indexType params. Rust correctness check conditioned (same as C). Gate: Goldilocks Rust 688.0us benchmark PASS. BabyBear Rust: separate transmute boundary issue (i32 vs u32), deferred. **DONE 2026-04-14.**

- [x] **B3 — Plonky3 Real Timing (N316.3)**: PAR. benchmark_plonky3.py: TRZK C scalar vs Plonky3 Rust --release via FFI. After B4 R4-threshold fix: BabyBear **0.45x** (55% faster), Goldilocks **1.18x** (18% slower). R2 uniform at N=2^14. **DONE 2026-04-14.**

- [x] **B4 — Pipeline Value (N316.4)**: PAR. Baseline R2 vs mkMixedRadixPlan R4. FINDING: R4 mixed is SLOWER at N=2^14 (BabyBear 0.61x, Goldilocks 0.68x). R4 inverted overhead > 25% butterfly savings for small N. Same pattern as v3.13.0 stage-split. R4 benefit expected at larger N where cache effects dominate. **DONE 2026-04-14.**

- [x] **B5 — Limpieza (N316.5)**: PAR. Correctness check interno ELIMINADO (C + Rust, ~30 LOC removed). output/latest/ + output/history/ creados. .gitignore updated. Bench binary limpio: BabyBear 369us, Goldilocks 842us sin MISMATCH/PARSE ERROR. **DONE 2026-04-14.**

- [x] **B6 — CI + Report (N316.6 + N316.7)**: HOJA. CI: C scalar + Oracle validation (Plonky3 FFI). BENCHMARKS.md rewritten with 6 reporting requirements. BabyBear **0.45x** (55% faster), Goldilocks **1.18x** (18% slower). **DONE 2026-04-14.**

#### Orden Topológico

```
{B1, B2, B3, B5} (paralelos) → B4 (dep B2) → B6
```

---

## Completed: v3.15.0

### DFT Standard Migration + Plonky3 Match v3.15.0

**Contents**: Migrate from non-standard ref_dit transform (DIT large→small) to standard DFT
(bitrev input + DIT small→large). Create parallel `emitCFromPlanStandard` pipeline.
100% element-by-element match against Plonky3 real. Detalle completo en TRZK_spiral_idea.md §3.9.

**Vision**: `.reverse` on stage ordering + bitrev preamble = DFT standard, with 0 changes to
butterflies, twiddle tables, or lowerStageVerified. ~163 LOC across 4 axes.

**State post-v3.14.0**: Cost model (branchCheck, staticShift, pow2Fraction), feedback loop
functional, four-step NTT (1024/1024 PASS vs naive DFT), DIF preambles, MatOp e-graph wired.
CRITICAL FINDING: ref_dit ≠ DFT (different transform, not permutation). ntt_skeleton.c matches
Plonky3 (64/64 PASS). emitCFromPlanVerified does NOT match Plonky3.

**Dead ends (DO NOT REPEAT)**:
- R4 with `.reverse`: FAIL (4/4 numéricamente). R4 stages cover 2 levels, inverting order breaks.
- DIF butterfly (Opción 3): requires rewriting entire reduction chain + SIMD + R4. ~200 LOC.
- Stage-split shift: +13% overhead (v3.13.0). Runtime popcnt branch > shift savings.
- Matching ref_dit with four-step: impossible (ref_dit ≠ DFT).

**Verified numerical results (DO NOT re-investigate)**:
1. bitrev(input) + DIT stages .reverse = DFT (7/7 PASS, Goldilocks+BabyBear)
2. Existing twiddle table (_init_twiddles_real) works WITHOUT changes with .reverse (3/3 PASS)
3. ntt_skeleton.c = bitrev + small→large DIT = DFT (64/64 match Plonky3)

**Mandatory constraints**:
- R2 only (no R4). Scalar only (no SIMD). useStandardDFT only on scalar path.
- Legacy pipeline (emitCFromPlanVerified) NOT modified.
- lowerStageVerified, nttTwiddleIndex, butterflies NOT modified.
- Codegen validation gate per CLAUDE.md: benchmark.py --validation-only --use-standard.

#### DAG (3.15.0)

| Nodo | Tipo | Deps | Files | LOC | Status |
|------|------|------|-------|-----|--------|
| N315.1 B.1+B.2: Python reference_standard_ntt + naive DFT validation | FUND | — | reference_ntt.py | ~25 | done |
| N315.2 A.1: Preamble bit_reverse_permute C+Rust | FUND | — | VerifiedPlanCodeGen.lean | ~25 | done |
| N315.3 A.3: lowerNTTFromPlanStandard (.reverse) | CRIT | N315.2 | VerifiedPlanCodeGen.lean | ~15 | done |
| N315.4 A.4: emitCFromPlanStandard + emitRustFromPlanStandard | PAR | N315.3 | VerifiedPlanCodeGen.lean | ~30 | done |
| N315.5 A.5: useStandardDFT dispatch + emit_code flag | PAR | N315.4 | UltraPipeline, OptimizedNTTPipeline, emit_code | ~15 | done |
| N315.6 B.3: Benchmark harness --use-standard | PAR | N315.1, N315.5 | benchmark.py, validator.py, lean_driver.py, Bench.lean | ~28 | done |
| N315.7 B.4+B.5: Validation gate vs Python + Plonky3 oracle | GATE | N315.5, N315.6 | Tests/benchmark/ | ~0 | done |
| N315.10 R4 inverted butterfly for standard DFT | CRIT | N315.3 | VerifiedPlanCodeGen.lean | ~20 | done |
| N315.11 R4 inverted preambles C+Rust (goldi_butterfly4_inverted) | PAR | N315.10 | VerifiedPlanCodeGen.lean | ~30 | done |
| N315.12 emitCFromPlanStandard R4 support (decls+preambles+guard) | PAR | N315.11 | VerifiedPlanCodeGen.lean | ~20 | done |
| N315.13 emitRustFromPlanStandard R4 support (mirror) | PAR | N315.11 | VerifiedPlanCodeGen.lean | ~25 | done |
| N315.14 ultraPipeline: use competition winner (R2∨R4 DIT, no lazy) | PAR | N315.12 | UltraPipeline.lean | ~10 | done |
| N315.15 Python R4 standard validation (reference + naive DFT) | FUND | — | reference_ntt.py | ~30 | done |
| N315.16 Validation gate R4 standard vs Python (BabyBear+Goldilocks) | GATE | N315.14, N315.15 | Tests/benchmark/ | ~0 | done |
| N315.17 Fix P3 twiddle dispatch in optimizedNTTC_ultra | CRIT | N315.7 | OptimizedNTTPipeline.lean | ~15 | done |
| N315.18 Flip useStandardDFT := true (cutover) | HOJA | N315.17, N315.16 | UltraPipeline.lean | ~1 | done |
| N315.19 Verify legacy fallback (useStandardDFT=false) | GATE | N315.18 | Tests/benchmark/ | ~0 | done |
| N315.8 D.1: Four-step wiring useStandardDFT=true | PAR | N315.5 | UltraPipeline, VerifiedPlanCodeGen | ~80 | **DEFERRED → v3.16.0** |

#### Formal Properties (3.15.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N315.1 | reference_standard_ntt == naive_dft for all 8 sizes | EQUIVALENCE | P0 |
| N315.3 | lowerNTTFromPlanStandard compiles and produces valid Stmt | SOUNDNESS | P0 |
| N315.4 | emitCFromPlanStandard output C compiles with gcc/clang | SOUNDNESS | P0 |
| N315.5 | useStandardDFT=false → output identical to v3.14.0 | PRESERVATION | P0 |
| N315.7 | Generated C vs Python standard: 0 mismatches | EQUIVALENCE | P0 |
| N315.7 | Generated C vs Plonky3 oracle: 0 mismatches | EQUIVALENCE | P0 |
| N315.10 | R4 inverted butterfly matches 2×R2 reversed (numerical) | EQUIVALENCE | P0 |
| N315.15 | Python R4 standard NTT == naive DFT for R4 plans | EQUIVALENCE | P0 |
| N315.16 | Generated C (R4 plan) vs Python standard: 0 mismatches | EQUIVALENCE | P0 |
| N315.14 | Competition winner with R4 → same perf as legacy R4 | PRESERVATION | P0 |
| N315.17 | P3 twiddle fix: Goldilocks benchmark correctness check PASS | EQUIVALENCE | P0 |
| N315.18 | Post-cutover: default useStandardDFT=true produces DFT | SOUNDNESS | P0 |
| N315.19 | Legacy fallback: useStandardDFT=false → output identical to v3.14.0 | PRESERVATION | P0 |
| N315.8 | Four-step with useStandardDFT=true inner NTT = DFT | SOUNDNESS | **DEFERRED → v3.16.0** |

#### Bloques

- [x] **B1 — Foundations (N315.1 + N315.2)**: 2 FUND parallel. Python reference_standard_ntt (bitrev+small→large) + validate vs naive DFT (16/16 PASS: BabyBear+Goldilocks, N=8..1024). Lean bit_reverse_permute preamble C+Rust (returns dummy 0 for Stmt.call compat). Gate: Python 16/16 PASS + lake build 3136 jobs PASS. **DONE 2026-04-14.**

- [x] **B2 — Lean Pipeline + Dispatch (N315.3 + N315.4 + N315.5)**: 3 nodos secuenciales. lowerNTTFromPlanStandard = bitrev Stmt.call(.user "group") + .reverse. emitCFromPlanStandard/Rust with R2 DIT preambles + bitrev. useStandardDFT flag in UltraConfig + dispatch in ultraPipeline (R2-only mkUniformPlan + ILP2 for Goldilocks) + thread through OptimizedNTTPipeline + emit_code --use-standard. Gate: lake build 3136 jobs PASS. **DONE 2026-04-14.**

- [x] **B3 — Harness + Validation Gate (N315.6 + N315.7)**: --use-standard in harness chain (benchmark.py, validator.py, lean_driver.py, Bench.lean, emit_standard.lean). CRITICAL FINDING: Goldilocks butterfly uses goldi_reduce128 (PZT mod p, NOT Montgomery REDC) → Montgomery twiddles add extra R factor → must pass STANDARD twiddles for Goldilocks. BabyBear uses REDC (R cancels). GATE: 14/14 PASS (BabyBear 7/7 + Goldilocks 7/7, N=8..1024). **DONE 2026-04-14.**

- [x] **B3.5 — R4 Inverted Butterfly + Ultra Competition (N315.10-N315.16)**: CRIT. Habilita R4 y mixed-radix plans en el standard DFT path. Causa raíz del gap R4+.reverse: intra-block level order hardcodeado (inner=L, outer=L+1) pero standard DFT necesita (inner=L+1, outer=L). Fix: nuevo `lowerRadix4ButterflyByReduction_Inverted` que swapea inner/outer + preamble `goldi_butterfly4_inverted`. `emitCFromPlanStandard` + `emitRustFromPlanStandard` extendidos con R4 decls+preambles. `ultraPipeline` dispatch usa competition winner si es R2∨R4 DIT sin lazy (guard contra bounds chain). Python validation R4 PRIMERO (per workflow). Gate: R4 standard 14/14 PASS + performance ≥ legacy R4. ~141 LOC total, 0 cambios a legacy path.

- [x] **B5 — Cutover (N315.17 + N315.18 + N315.19)**: Fix P3 twiddle dispatch en optimizedNTTC_ultra (nttCall pasa tw en vez de tw_mont para Goldilocks cuando useStandardDFT=true, ~5 LOC, pattern de emit_standard.lean L50-70). Mismo fix para Rust path. Flip useStandardDFT := true (1 LOC). Verify legacy fallback. Gate: Bench.lean --field goldilocks sin MISMATCH + benchmark.py --validation-only sin --use-standard (now default) PASS + legacy fallback PASS. ~20 LOC total.

- **B4 — Four-step Wiring (N315.8)**: **DEFERRED → v3.16.0**. Complejidad real ~60-80 LOC (vs ~20 estimados en §3.9). Gaps: (1) twiddle table layout 3 regiones separadas vs flat ~30 LOC ALTO riesgo, (2) preamble DIF faltante ~10 LOC, (3) stack overflow Phase 6 `uint64_t tmp_unstride[N]` ~5 LOC, (4) Goldilocks only, (5) m selection. B3.5 ya cerró el gap de performance con R4 inverted — four-step es optimización adicional para N≥2^14.

#### Orden Topológico

```
B1 → B2 → B3 → B3.5 → B5 → SHIP v3.15.0
```

#### Expectations

```
                      Goldilocks (0.96x)
Eje A (migration):    ~0.96x (R4 inverted + competition winner)
Eje B (validation):   output matches Plonky3 real (DFT standard)
Eje D (four-step):    DEFERRED v3.16.0 (~0.85x target)
─────────────────     ──────────────
Post-v3.15.0:         ~0.85x vs Plonky3 scalar, outputs IDENTICAL
```

---

## Completed: v3.14.0 — Cost Model Feedback + Four-Step NTT + MatOp E-Graph

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
| N314.12 Eje 3a: NodeOps MatOp instance + laws | FUND | — | ~45 | done |
| N314.13 Eje 3b: MatExprFlat + Extractable + bridge | PAR | N314.12 | ~30 | done |
| N314.14 Eje 3c: applyBreakdownInEGraph | CRIT | N314.13 | ~40 | done |
| N314.15 Eje 3d: UltraPipeline wiring | HOJA | N314.14,9 | ~35 | done |

#### Bloques

- [x] **B1 — Cost Model Foundation (N314.1+M.3)**: FUND. branchCheck + staticShift. Runtime shift now costs MORE than standard (14 vs 12 R2), matching v3.13.0 measurement. Static shift costs LESS (9, for future four-step). **DONE 2025-04-13.**
- [x] **B2 — Cost Model Extensions (N314.2, N314.3, N314.4)**: M.2: pow2Fraction field + empirical assignment in mkTwoStepPlan. M.3: done in B1. M.4: calibrate_hw.py — measured mul=1.4c shift=1.6c add=1.4c branch=2.5c (latency vs throughput delta explainable). **DONE 2025-04-13.**
- [x] **B3 — Feedback Loop (N314.5)**: CRIT. Cost predictions added to UltraPipeline report. feedback_loop.py extracts + ranks all candidates. Goldilocks 11 candidates, R4 wins (65280), two-step penalized (96256). BabyBear 10 candidates (no two-step). **DONE 2025-04-13.**
- [x] **B4 — Four-step Python verification (N314.6)**: FUND. Both variants verified 6/6 PASS for Goldilocks. (1) Naive four-step: col_DFTs→tw→row_DFTs→unstride=DFT. (2) **DIF+bitrev pipeline (Opción B corrected)**: col_DIF→col_bitrev→tw(ω^(r·c))→row_DIF→row_bitrev→unstride=DFT. Row DIF uses ω_m=ω_64=8 → 100% pow2 → shifts! Overhead: 2 bitrev passes O(N) + 1 twiddle + 1 unstride. Bug was: rows-first order is WRONG (twiddle depends on original col index lost after row DFT); correct order is cols-first. **DONE 2025-04-13.**
- [x] **B5 — DIF preambles + dispatch (N314.7, N314.8)**: R2+R4 DIF shift preambles (C+Rust, ~46 LOC). 3-point dispatch (direction × useShift) in lowerStageR4, lowerStageVerified, lowerStageVerified_ILP2. **DONE 2025-04-13.**
- [x] **B6 — Four-step codegen (N314.9)**: CRIT. `emitFourStepC`: 6-phase C generator (col_DIF + col_bitrev + twiddle + row_DIF + row_bitrev + unstride). N=1024: 1024/1024 match naive DFT. **KEY FINDING**: ref_dit ≠ DFT (different transform, not permutation). Four-step computes DFT, pipeline uses ref_dit → incompatible. Integration deferred to v3.15.0 (pipeline migration to DFT standard). **DONE 2025-04-13.**
- [ ] **B7 — Four-step plan + validation (N314.10, N314.11)**: HOJA. mkFourStepPlan + benchmark gap < 0.85x.
- [x] **B8 — NodeOps MatOp (N314.12)**: FUND. mapChildren/replaceChildren/localCost + 4 laws (all by cases+simp). EGraph MatOp smoke test: 3 classes, children correct. No import cycle. **DONE 2025-04-13.**
- [x] **B9 — MatExprFlat + Extractable (N314.13)**: MatExprFlat (7 ctors) + matReconstruct + Extractable instance + matExprFlatToTree bridge. Smoke: EGraph(5 classes) → extractAuto → MatExprFlat → FactorizationTree(5 nodes). **DONE 2025-04-13.**
- [x] **B10 — applyBreakdownInEGraph (N314.14)**: CRIT. Injects BreakdownRule.decompose into EGraph MatOp: remaps indices → EClassIds, merges root with NTT class. DFT(8) + CT(2,4) + CT(4,2) → 19 classes. Extraction works (returns cheapest). **DONE 2025-04-13.**
- [x] **B11 — UltraPipeline wiring (N314.15)**: HOJA. MatOp e-graph wired in ultraPipeline: NTT node → applyAllBreakdowns(standardRules) → computeCosts → extract → factorizationToPlan → push to allCandidates. R4 wins (expected — e-graph plan incompatible with ref_dit until v3.15.0). **DONE 2025-04-13.**

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




### v3.20 — Batch NTT Interface (cleanup + SIMD migration + batch emitters + proofs)

**Contents**: Formalización del plan de TRZK_SBB.md §14.13 + research/TRZK_batch_design.md. 8 bloques secuenciales: B0 (v3.19 B5 cleanup debt) → v3.20.a (SIMD legacy → DFT standard + Gate H8) → B1-B6 de v3.20.b (batch interface). Total ~1378 LOC Lean + ~180 otros, estimado 11-15 días. Phase 2 firewall proofs diferido a ronda dedicada post-merge. Plan y decisiones (4 gaps) ya cerrados en pre-coding investigation 2026-04-20; /plan-project invocado en modo formalizador, sin replanificar.

**Files**:
- `AmoLean/EGraph/Verified/Bitwise/SIMDEmitter.lean`
- `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean`
- `Tests/benchmark/oracle_validate.py`
- `.github/workflows/ci.yml`
- `AmoLean/EGraph/Verified/Bitwise/NTTPlan.lean`
- `CLAUDE.md`
- `AmoLean/EGraph/Verified/Bitwise/MixedNodeOp.lean`
- `AmoLean/Bridge/SIMDStmtToC.lean`
- `AmoLean/EGraph/Verified/Bitwise/MemLayout.lean`
- `Tests/batch_golden_test.lean`
- `AmoLean/EGraph/Verified/Bitwise/CostModelDef.lean`
- `Tests/NonVacuity.lean`
- `Tests/batch_offset_tests.lean`
- `Tests/batch_equivalence_tests.lean`
- `Tests/benchmark/benchmark_batch.py`
- `Tests/benchmark/differential_fuzz.py`
- `ARCHITECTURE.md`
- `BENCHMARKS.md`

#### DAG (3.20.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N20.0.1 Eliminar 3 #![allow(...)] band-aids + fix warnings al origen en stmtToRust | HOJA | — | completed ✓ |
| N20.a.1 SIMD migration: stages.reverse + bitRevPermutePreamble en emitCFromPlanStandard + emitRustFromPlanStandard | CRIT | N20.0.1 | completed ✓ |
| N20.a.2 Oracle validator --hardware arm-neon + CI arm-neon-validation job | HOJA | N20.a.1 | completed ✓ |
| N20.a.3 Gate H8 pre-merge PR v3.20.a (5 runs, mean ≤ 820 μs @ N=2^18 BabyBear) | GATE | N20.a.1, N20.a.2 | completed ✓ |
| N20.1.1 NTTPlan.batchWidth field + Plan.withBatch helper + batchPolyOffset + soundness lemma | FUND | N20.a.3 | completed ✓ |
| N20.1.2 Trust Boundary Documentation template en CLAUDE.md | HOJA | — | completed ✓ |
| N20.2.1 3 constructores MixedNodeOp: packedLoadNeon + packedStoreNeon + packedButterflyNeonDIT | FUND | N20.1.1 | completed ✓ |
| N20.2.2 4 NeonIntrinsic variants + toCName/fromCName mappings | HOJA | N20.2.1 | completed ✓ |
| N20.2.3 15 lemmas NodeOps/NodeSemantics instances (cases op sistemático) | CRIT | N20.2.1 | completed ✓ |
| N20.3.1 MemLayout.lean NUEVO módulo con transposeForBatch + untransposeFromBatch + invertibility theorem | FUND | N20.2.3 | pending |
| N20.3.2 emitPackedButterflyNeonDIT_C kernel + isPackedButterflyApplicable dispatch | CRIT | N20.3.1, N20.2.1 | pending |
| N20.3.3 Golden test batch==scalar (invertibility + codegen validation) | GATE | N20.3.1, N20.3.2 | pending |
| N20.4.1 lowerStageVerified_OffsetAware con substitution (+batchPolyOffset substitutor) | FUND | N20.1.1 | pending |
| N20.4.2 lowerNTTFromPlanBatch outer Stmt.for_ + stage composition (B=1 delega a single-vector) | CRIT | N20.4.1 | pending |
| N20.4.3 emitCFromPlanBatch + emitRustFromPlanBatch wrappers con transpose preamble | CRIT | N20.4.2, N20.3.1 | pending |
| N20.4.4 Cost model extension: batchWidthFactor + batchWidthCost + planTotalCostBatch | PAR | N20.1.1 | pending |
| N20.4.5 Gate B4: benchmark.py --batch-width 16 BabyBear N=18 dentro ±5% modelo lineal | GATE | N20.4.3, N20.4.4 | pending |
| N20.5.1 Theorem signatures: lowerNTTFromPlanBatch_correct + auxiliares + emitCFromPlanBatch_sound | FUND | N20.4.3 | pending |
| N20.5.2 Base case B=1 collapse NON-DEFERRABLE (proof by rfl) | CRIT | N20.5.1 | pending |
| N20.5.3 Inductive step _step + main theorem composición | CRIT | N20.5.2 | pending |
| N20.5.4 Firewall _aux lemmas con sorry + TODO Phase 2 (lowerDIFButterflyByReduction_batch_indexing_aux, lowerBitReverseStmt_batch_aux) | FUND | N20.5.1 | pending |
| N20.5.5 3 non-vacuity examples (B=1 babybear, B=4 goldilocks, B=2 mixed reduction) | HOJA | N20.5.3 | pending |
| N20.6.1 Tests Lean: offset soundness + B=1 equivalence + invertibility | HOJA | N20.5.3 | pending |
| N20.6.2 Python benchmark harness benchmark_batch.py (NUEVO archivo) | HOJA | N20.4.3 | pending |
| N20.6.3 Differential fuzzer batch inputs (≥1000 PASS target) | HOJA | N20.6.2 | pending |
| N20.6.4 ARCHITECTURE.md + BENCHMARKS.md §10 Batch performance + Batch Roadmap Phase 2 | HOJA | — | pending |
| N20.6.5 CI batch-validation job | HOJA | N20.6.3 | pending |
| N20.6.6 Gate B6: H8 preservado + batch B=16 N=2^18 ±5% modelo lineal | GATE | N20.6.3, N20.6.5 | pending |

#### Formal Properties (3.20.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N20.1.1 | Plan.batchWidth=1 por default preserva comportamiento single-vector existente (backward compat) | PRESERVATION | P0 |
| N20.1.1 | batchPolyOffset es inyectiva y soundness lemma cubre todos los (polyVar, N, i) | SOUNDNESS | P0 |
| N20.2.1 | Nuevos MixedNodeOp constructores son no-island: packedButterflyNeonDIT tiene consumer explícito en B3 (emitPackedButterflyNeonDIT_C) antes del cierre | INVARIANT | P0 |
| N20.2.1 | evalMixedOp .packedButterflyNeonDIT simplifica a (v a + v b) / 2 (DIT butterfly semántica) | EQUIVALENCE | P1 |
| N20.3.1 | transposeForBatch_inv: transpose ∘ untranspose = id para toda input ≤ N*W elements | INVARIANT | P0 |
| N20.5.2 | lowerNTTFromPlanBatch_B1_collapse: B=1 exactamente equivalente al single-vector path | EQUIVALENCE | P0 |
| N20.5.3 | lowerNTTFromPlanBatch_correct: ∀ B > 0 batch output correcto elemento por elemento | SOUNDNESS | P0 |
| N20.5.4 | Firewall _aux lemmas (stride indexing + bitrev strided) DOCUMENTADAS con TODO Phase 2 + referencia CLAUDE.md § Batch Roadmap Phase 2 | INVARIANT | P0 |
| N20.6.3 | Differential fuzz batch: 100% match TRZK-batch vs P3-batch element-wise para ≥1000 inputs random (N ∈ {2^8, 2^10, 2^14}, B ∈ {4, 8, 16}) | SOUNDNESS | P0 |
| N20.6.6 | Gate H8 preservado: TRZK arm-neon single-vector N=2^18 mean ≤ 820 μs post-batch infra (no regresión vs v3.20.a) | PRESERVATION | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Bloques

- [x] **v3.19 cleanup debt (eliminar #![allow] band-aids)**: N20.0.1 — closed 2026-04-20
- [x] **v3.20.a — SIMD legacy → DFT standard migration + Gate H8**: N20.a.1, N20.a.2, N20.a.3 — closed 2026-04-20
- [x] **Foundations (NTTPlan.batchWidth + Trust Boundary docs)**: N20.1.1, N20.1.2 — closed 2026-04-20
- [x] **MixedNodeOp Extensions (3 constructores + 4 intrinsics + 15 lemmas)**: N20.2.1, N20.2.2, N20.2.3 — closed 2026-04-20
- [ ] **MemLayout + SIMDEmitter (nuevo módulo + packed butterfly kernel)**: N20.3.1, N20.3.2, N20.3.3
- [ ] **Outer Loop Wiring (lowerNTTFromPlanBatch + emitCFromPlanBatch)**: N20.4.1, N20.4.2, N20.4.3, N20.4.4, N20.4.5
- [ ] **Correctness Proofs Phase 1 (bridge theorem + firewall _aux con sorry)**: N20.5.1, N20.5.2, N20.5.3, N20.5.4, N20.5.5
- [ ] **Tests + Bench + Docs (benchmark_batch.py + fuzzer + ARCHITECTURE update)**: N20.6.1, N20.6.2, N20.6.3, N20.6.4, N20.6.5, N20.6.6

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
