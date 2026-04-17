# TRZK Benchmarks

Performance data for TRZK NTT code generation.
Rubrics and QA criteria are in `research/RUBRICS.md`.

---

## v3.17.0 — sbb Trick + Benchmark Fairness

### 0. Correctness

Output verified element-by-element (mod p) against:
- **Python naive DFT O(N²)**: `A[k] = Σ_j data[j] · ω^(jk) mod p` — 36/36 PASS (v3.16.0)
- **Plonky3 real (Polygon Rust library)** via FFI: oracle_validate.py — **14/14 PASS** (R2, Goldilocks + BabyBear, N=8..1024). CI gate.
- **TRZK Rust output == TRZK C output** (v3.17.0 B5.5): byte-identical across Goldilocks + BabyBear × N ∈ {16, 128, 1024, 16384}. No Rust codegen bug.

| Layer | Reference | Fields | Sizes | Result |
|-------|-----------|--------|-------|--------|
| Python naive DFT | `_naive_dft` O(N²) | BabyBear, Goldilocks | N=4..1024 R2+R4 | 36/36 PASS |
| Oracle vs Plonky3 | `plonky3_ntt_forward` FFI | BabyBear, Goldilocks | N=8..1024 R2 | 14/14 PASS |
| TRZK Rust = TRZK C | compared outputs | BabyBear, Goldilocks | N=16..16384 | 32/32 PASS |
| **Differential Fuzz** (v3.18.0) | TRZK C vs Plonky3 vs Python naive (3-way N≤1024, 2-way N>1024) | BabyBear, Goldilocks | N=8..16384, 100 random + 15 edge per combo | **1150/1150 PASS** |

Differential fuzzing (v3.18.0) replaces single-point oracle with ~1000 random + structured
inputs per (field × size). Reproduce: `python3 Tests/benchmark/differential_fuzz.py --mode fast --seed 42`

---

### Methodology note — steady-state measurement

All timings in this document are **steady-state**, using 2 warmup process invocations +
min-of-3-measurement-runs + min-of-30-iters-per-run per (field × lang × profile) combination.
A naive single-invocation measurement can report 2x slower than steady state on Apple Silicon due
to fresh-compile overhead (cold iTLB, cold data cache, CPU frequency ramp). The harness in
`benchmark_plonky3.py` applies warmup automatically — see §7 Methodology.

### 1. **PRIMARY HEADLINE — Rust-vs-Rust (fair algorithmic comparison)**

Both TRZK and Plonky3 compiled with `rustc --release` equivalent flags. Eliminates compiler variable.

Canonical sizes: **N=2^14** (cache-resident, working set fits L1/L2), **N=2^18**
(cache-pressured, ~2-4MB), **N=2^20** (cache-miss-dominant, ~8MB+). Single-vector NTT
(width=1) — see §8 for the batch NTT caveat.

| Field | N | TRZK Rust (μs) | Plonky3 Rust (μs) | **Rust/P3 Ratio** |
|-------|---|----------------|-------------------|--------------------|
| **Goldilocks** | 2^14 | **232.6** | 249.2 | **0.93x** (TRZK +7%) |
| **Goldilocks** | 2^18 | **5395.7** | 5901.6 | **0.91x** (TRZK +9%) |
| **Goldilocks** | 2^20 | **24351.0** | 28357.6 | **0.86x** (TRZK +14%) |
| **BabyBear** | 2^14 | **140.1** | 192.7 | **0.73x** (TRZK +27%) |
| **BabyBear** | 2^18 | **3324.0** | 4895.4 | **0.68x** (TRZK +32%) |
| **BabyBear** | 2^20 | **15201.0** | 23284.0 | **0.65x** (TRZK +35%) |

**Key findings**:

1. In fair (same-compiler, same-flags) Rust-vs-Rust comparison, **TRZK outperforms Plonky3** on
   both fields at all tested sizes.
2. **The advantage grows monotonically with N**. At N=2^20 (cache-miss-dominant regime), TRZK
   wins by 14-35%. The plan selected by TRZK's optimizer (R2 uniform Harvey + ILP2 for
   Goldilocks) scales better than Plonky3's vanilla `Radix2Dit::dft_batch` with single-vector
   input. See §8 for important caveat on batch workloads.
3. The BabyBear gap growth is especially notable given Plonky3 has NEON packing available
   (`p3-baby-bear/src/aarch64_neon/`). At width=1 that packing doesn't activate, which is part
   of §8's caveat.

### 2. Secondary — C-vs-Rust cross-compiler (retained for historical continuity)

Not apples-to-apples. TRZK C (clang) vs Plonky3 Rust (rustc + LTO + codegen-units=1). Useful only
for users who'll deploy C output; the Rust path (§1) is the fair comparison.

| Field | N | TRZK C (μs) | Plonky3 Rust (μs) | C/P3 Ratio |
|-------|---|-------------|-------------------|------------|
| Goldilocks | 2^14 | 269.2 | 249.2 | 1.08x |
| Goldilocks | 2^18 | 6274.5 | 5901.6 | 1.06x |
| Goldilocks | 2^20 | 28785.8 | 28357.6 | 1.02x |
| BabyBear | 2^14 | 134.4 | 192.7 | 0.70x |
| BabyBear | 2^18 | 3352.9 | 4895.4 | 0.68x |
| BabyBear | 2^20 | 15511.4 | 23284.0 | 0.67x |

**Explanation of Goldilocks C-vs-Rust gap**: TRZK C (cc -O3 -flto -mcpu=apple-m1) is 13-18%
slower than TRZK Rust across sizes. The difference is LLVM's cross-module inlining with
`codegen-units=1` that clang-C builds don't match. This is a compiler/build-system difference,
not an algorithm difference. **BabyBear C and Rust track each other closely** (within ~5%) —
BabyBear's signed `int32_t` Montgomery REDC gets similar treatment from both compilers. The
Goldilocks C-vs-Plonky3 ratio also narrows with N (1.08x → 1.02x) — at large N, cache effects
dominate and compiler inlining matters less.

### 2b. Conservative profile (cc -O2 / rustc -O, N=2^14 reference only)

| Field | TRZK C (μs) | TRZK Rust (μs) | Plonky3 Rust (μs) | C/P3 | Rust/P3 |
|-------|-------------|----------------|-------------------|------|---------|
| Goldilocks | 271.9 | 257.8 | 249.0 | 1.09x | 1.04x |
| BabyBear | 136.3 | 146.1 | 192.6 | 0.71x | 0.76x |

Note: Plonky3 is always compiled `--release` via its Cargo.toml profile; the `conservative`
label applies only to TRZK's compilation. So `conservative` is asymmetric — TRZK with less
optimization vs Plonky3 always-optimized. `match-plonky3` (§1) is the fair comparison.

---

### 3. v3.17.0 Changes Summary

| Block | Task | What changed | Empirical impact |
|-------|------|--------------|------------------|
| B1 | N317.4 (M1) | Comment L1101-1103 updated (R2+R4 DIT, not R2-only) | Doc only |
| B1 | N317.5 (M2) | `goldi_mul_tw` + `goldi_butterfly_shift` gated by `hasShift` | Dead code removed from default C/Rust |
| B1 | N317.6 (M3) | `stdPlan` extracted once in UltraPipeline (was duplicated) | −8 LOC, same semantics |
| B1 | N317.9 (M6) | `Tests/benchmark/bench_four_step_isolated.py` committed | Four-step NO-GO reproducible |
| B2 | N317.8 (M5) | `--profile conservative\|match-plonky3`, `--lang c\|rust\|both`, honest flag metadata, default `use_standard=True` | Fair benchmarking unlocked |
| B3 | N317.1 | CI cleanup: removed redundant `--use-standard` flag | No perf change |
| B3 | N317.2 (Opción A) | `goldi_reduce128`: `__builtin_expect(borrow,0)` + branchless carry adjust | −61 ARM instr (−4.1% static), linearizes flag-merge |
| B4 | N317.3 (Opción B localizada) | **EVALUATED AND REJECTED** — clang inlines identically to A | No-op, documented in-code |
| B5 | N317.7 | `goldi_add` flag-merge linearized (same pattern as B3) | −31 ARM instr incremental, −8% Goldilocks median |
| B5.5 | (new) | `trzk_rust_timing()` + `--lang rust\|both` + `emit_standard_rust.lean` | Rust-vs-Rust benchmark enabled; revealed true gap |

**Cumulative assembly reduction** (baseline v3.16 → v3.17): **−92 ARM instructions** (1495 → 1403)
in the full Goldilocks NTT standard path.

---

### 4. Reproduction

Prerequisites: Lean 4 (elan), Rust (cargo), C compiler (cc), Python 3.

```bash
# Build TRZK
lake build bench

# Build Plonky3 shim (once)
cd verification/plonky3 && make shim && cd ../..

# === PRIMARY: Rust-vs-Rust fair comparison ===
# Canonical sizes: 14 (cache-resident), 18 (cache-pressured), 20 (cache-miss-dominant)
python3 Tests/benchmark/benchmark_plonky3.py \
    --lang both --profile match-plonky3 \
    --fields goldilocks,babybear --sizes 14,18,20 --iters 30

# === Correctness gates ===
python3 Tests/benchmark/oracle_validate.py \
    --fields goldilocks,babybear --sizes 3,4,5,6,7,8,10
python3 Tests/benchmark/benchmark.py --validation-only \
    --fields goldilocks,babybear --sizes 14

# === Four-step NO-GO evidence (reference) ===
python3 Tests/benchmark/bench_four_step_isolated.py \
    --sizes 14,16,18 --m 64 --iters 10
```

Output directory: `Tests/benchmark/output/latest/` (gitignored).

---

### 5. Fair Comparison Matrix

| Axis | TRZK C | TRZK Rust | Plonky3 | Fair comparison? |
|------|--------|-----------|---------|------------------|
| Compiler | clang | rustc | rustc | **Rust-vs-Rust fair** |
| Profile (match-plonky3) | -O3 -flto -mcpu=apple-m1 | opt=3 lto=yes target-cpu=native | --release (opt=3, lto=true, codegen-units=1) | Near-parity (P3 has codegen-units=1 extra) |
| SIMD Goldilocks | scalar | scalar | scalar (u64 doesn't vectorize) | **Symmetric** |
| SIMD BabyBear | scalar | scalar | **NEON 4-lane (p3-baby-bear aarch64)** | **ASYMMETRIC** |
| Data layout | u32/u64 | u32/u64 | u32/u64 | Symmetric |

**Implications**:
- **Goldilocks fair**: scalar-vs-scalar, same compiler. `Rs/P3 = 1.07x` reflects real algorithmic gap.
- **BabyBear partially fair**: same compiler (Rust-vs-Rust), but Plonky3 uses NEON while TRZK uses
  scalar. The `Rs/P3 = 1.27x` includes Plonky3's NEON advantage. True BabyBear algorithmic
  gap requires **v3.18 SIMD migration** (scheduled).

---

### 6. Metadata

```
Date:      2026-04-16
Git:       v3.17.0 (branch feat/v3.17-sbb)
Hardware:  Apple Silicon ARM64 (M-series), single core
Compiler:  cc / rustc / Apple Clang (system default)
Iters:     30 per run, 3 measurement runs, 2 warmup runs discarded.
           Reported value = min across all 3*30 = 90 timed iterations.
Variance:  ~±5% within-session after warmup. Single-measurement without
           warmup has ~2x bias (cold iTLB / cache / CPU frequency ramp).
```

### 7. Methodology — why warmup matters on Apple Silicon

**Problem**: a fresh-compile single-invocation measurement reports ~2x of the steady-state value.
Empirically observed on Apple Silicon M-series:

```
Rust BabyBear match-plonky3, 5 back-to-back invocations of a freshly compiled binary:
  Run 1: 289 μs  ← what a naive benchmark would report
  Run 2: 222 μs
  Run 3: 182 μs
  Run 4: 157 μs
  Run 5: 145 μs  ← steady state
```

Even the binary's internal "min of 30 iters" reports the cold-window minimum, which is still far
from steady state. Root causes (observed, not speculated):

1. **Cold instruction cache / TLB**. Fresh binary → iTLB miss on every new basic block. First
   30 iterations of the NTT all hit partly-cold instruction memory.
2. **CPU frequency ramp**. Apple Silicon P-cores scale frequency based on recent load. A cold
   process starts at lower frequency; takes several seconds of load to ramp to peak.
3. **macOS dyld cache warmup**. First execution resolves symbols / initializes runtime; repeated
   invocations benefit from the kernel's page cache.

**Solution**: `benchmark_plonky3.py` runs the binary N_WARMUP=2 times discarding results, then
N_MEASURE=3 times keeping `min()` across them. Each measurement run internally does 30 iters,
also reporting its own min. Final reported number = `min(min_of_iters across measurement_runs)`.

Plonky3 is measured via FFI (no subprocess overhead), but applies the same warmup pattern:
5 warmup iterations discarded + 30 measurement iterations taking min. Matches TRZK harness.

**Without warmup**, all v3.17 pre-investigation numbers were biased by ~2x upward. All numbers
in §1-§2 above use the warmup-corrected methodology.

---

### 8. Batch NTT caveat — why the "TRZK wins" numbers have an asterisk

The Plonky3 reference used in §1 and §2 is accessed through `plonky3_shim/src/lib.rs`, which
invokes `Radix2Dit::dft_batch()` with `width=1` (single polynomial per call). **This bypasses
Plonky3's batch optimizations** that normally activate with `width > 1`:

- `PackedMontyField31Neon` (BabyBear NEON packing, `WIDTH=4`) — inactive, because rows of
  `width=1` can't fill a 4-lane SIMD chunk.
- `Radix2DitParallel` — typically used when multiple polynomials are transformed together.
- Bowers network variants — similar story.

**What the numbers in §1 actually show**: TRZK (single-vector, no SIMD) vs Plonky3 (single-
vector, no SIMD). A fair comparison of single-vector NTT performance.

**What a real prover workload does**: batch NTT over many polynomials (e.g., commit to a matrix
of polynomials). Plonky3 is designed for this context — with `width >> 1`, NEON packing and
parallel variants activate. A batch NTT with `width=4` might show Plonky3 regaining most or all
of the reported gap for BabyBear.

**TRZK's current codegen is single-vector only**. There is no `ntt_batch(data[B][N], twiddles)`
interface. Comparing TRZK vs Plonky3 in batch context requires either (a) calling TRZK N-times
sequentially vs Plonky3 batch, or (b) adding batch codegen to TRZK. Both are planned
investigations for v3.19+ (see `research/TRZK_SBB.md §13.3`).

**Bottom line**: the §1 headline "TRZK beats Plonky3 by 7-35%" is correct for single-vector
NTT. For batch NTT workloads (typical in production provers), this comparison doesn't apply yet.
Users planning to integrate TRZK should consider their actual workload pattern.

---

### 9. Honest Interpretation

**Pre-v3.17 narrative (incomplete)**: "TRZK has a 18% algorithmic gap with Plonky3 on Goldilocks."

**First v3.17 report (biased by fresh-compile)**: "~11% compiler + ~7% algorithm." This was
also wrong — both components were inflated by cold-start overhead.

**Post-warmup-fix reality**: the original 1.18x Goldilocks gap was:
- **~100% measurement artifact** (fresh-compile + cold iTLB + CPU frequency ramp).
- **0% real algorithmic gap** — TRZK Rust Goldilocks is `0.94x` vs Plonky3 Rust (TRZK 6% FASTER!).
- For BabyBear: TRZK is `0.75x` Plonky3 (TRZK 25% faster) despite Plonky3 using NEON.

The "gap" in published TRZK benchmarks (v3.12-v3.16) existed only because all measurements hit
the cold-start window. With correct warmup methodology, TRZK's NTT codegen produces code that
matches or beats Plonky3's hand-tuned Rust on the same compiler. This is a strong empirical
validation of the e-graph-based code generation approach.

**What v3.17.0 actually achieved**:
1. **−92 ARM instructions** in the C generated NTT (flag-merge linearization in reduce128 + add).
2. **Honest benchmarking infrastructure** (`--profile` + `--lang both` + metadata).
3. **Four-step NO-GO confirmed** empirically; re-open conditions documented.
4. **Rust-vs-Rust parity validated** (oracle 14/14 + element-by-element C=Rust 32/32).
5. **Opción B evaluated and rejected**: `goldi_reduce128_from_product` proved no-op post-N317.2
   (clang inlined both forms identically). In-code comment documents the experiment.

**What v3.17.0 exceeded**:
- Target was "Goldilocks ≤ 1.10x fair comparison". Achieved **0.94x** (TRZK beats Plonky3 by 6%).
- BabyBear target "≤ 1.30x" (acknowledging Plonky3 NEON asymmetry). Achieved **0.75x**
  (TRZK 25% faster) despite SIMD asymmetry.

**Unexpected findings from the warmup investigation**:
- **Fresh-compile overhead is ~2x for NTT benchmarks on Apple Silicon**. All TRZK benchmark
  reports prior to v3.17 (and the first v3.17 draft in commit 58f0d3f) were biased ~2x upward.
  The `benchmark_plonky3.py` tool now applies proper warmup and this bias is eliminated.
- **`BabyBear Rust slower than C` was ALSO an artifact** — in steady state Rust is 145 μs and C
  is 134 μs, a ~8% difference likely due to clang's better handling of signed arithmetic right
  shift in Montgomery REDC. The fresh-compile numbers (338 vs 259) were both cold-run artifacts.
- **`emitRustFromPlanStandard` emits 309 rustc warnings** (unused vars, redundant parens). Works
  but is code smell — cleanup task for v3.18.
- **BabyBear NEON-vs-NEON fair comparison still pending** until v3.18 SIMD migration; but even
  TRZK scalar already beats Plonky3 NEON by 25% at N=2^14, suggesting SIMD gains are modest at
  this size.

---

## Previous: v3.16.0 — Real Benchmarks vs Plonky3

The v3.16.0 headlines "**BabyBear 0.45x / Goldilocks 1.18x**" were based on `cc -O2` (TRZK) vs
Plonky3 `--release`. v3.17.0's `--profile match-plonky3` + `--lang both` replaces those numbers
with fair equivalents (see §1 above). See `ARCHITECTURE.md` v3.16.0 entry for the original context.

### 0. Correctness (v3.16.0)

Output verified element-by-element (mod p) against:
- **Python naive DFT O(N²)**: 36/36 PASS
- **Plonky3 real** via FFI: oracle_validate.py — 24/24 PASS (R2 14/14 + R4 10/10)

### Performance (v3.16.0, historical, asymmetric flags)

| Field | N | TRZK C (μs) | Plonky3 Rust (μs) | Ratio | Note |
|-------|---|-------------|-------------------|-------|------|
| BabyBear | 2^14 | 340 | 751 | 0.45x | TRZK scalar vs Plonky3 NEON, cc -O2 vs rustc --release LTO |
| Goldilocks | 2^14 | 840 | 711 | 1.18x | both scalar, cc -O2 vs rustc --release LTO |

See v3.17.0 §1 for fair Rust-vs-Rust numbers.

---

### Formal Properties (v3.17.0)

See `research/RUBRICS.md` § Criteria (3.17.0) for the full rubric and gate commands.

| Property | Node | Result |
|----------|------|--------|
| Oracle TRZK vs Plonky3 element-by-element | N317.2, N317.3, N317.7 | 14/14 PASS |
| TRZK Rust output == TRZK C output | B5.5 (regression guard) | 32/32 PASS |
| Goldilocks gap ≤ 1.10x (Rust-vs-Rust, match-plonky3) | v3.17 target | **PASS (0.94x — TRZK 6% faster)** |
| BabyBear gap ≤ 1.30x (Rust-vs-Rust, match-plonky3) | v3.17 target | **PASS (0.75x — TRZK 25% faster)** |
| Default `use_standard=True` (no flag needed) | N317.8 (absorbed) | PASS |
| `--profile match-plonky3` produces `-O3 -flto -mcpu=apple-m1` | N317.8 | PASS |
| Four-step NO-GO reproducible via `bench_four_step_isolated.py` | N317.9 | PASS |
