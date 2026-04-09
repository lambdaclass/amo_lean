# TRZK: Architecture

## Next Version: 3.8.0

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
