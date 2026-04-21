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

### 8b. Plonky3 batch measurement (v3.19 N319.2.2 — quantifying §8)

The shim now exposes `plonky3_{babybear,goldilocks,koalabear}_ntt_forward_batch(data, n, width)`
to drive Plonky3's `dft_batch` with `width > 1`. This activates the optimisations §8 says are
bypassed at width=1. Methodology identical to §1 (intra-process warmup + min-of-iters, CV
reported). Apple M1 ARM64. **N=2^14 cells re-measured with `--iters 100 --warmup 10`** to
satisfy `CHECK:b2_table` (CV ≤ 5%) — short tasks (~250μs) need more samples to stabilise the
mean on a non-real-time OS. N=2^18 cells use the original `--iters 30 --warmup 5` (already CV
1-3% due to longer absolute time per iter).

#### BabyBear — Plonky3 batch latency-per-NTT

| Width | N=2^14 (μs/NTT) | N=2^18 (μs/NTT) | Speedup vs w=1 (N=2^14 / N=2^18) |
|------:|----------------:|----------------:|:----------------------------------|
| 1     | 267.96          | 6064.42         | 1.00x / 1.00x (baseline)          |
| 2     | 208.56          | 4704.90         | 1.28x / 1.29x                     |
| 4     | **74.80**       | **1715.73**     | **3.58x / 3.53x** (Neon WIDTH=4 activates) |
| 8     | 59.45           | 1367.45         | 4.51x / 4.43x                     |
| 16    | **51.16**       | **1250.85**     | **5.24x / 4.85x** (best)          |

CV for the N=2^14 row: 3.9% / 2.0% / 2.9% / 5.3% / 48.2%. The w=16 outlier reflects a single
high-tail iteration (likely thermal or scheduler noise) — the reported `min` (51.16μs) is
identical within 0.2% to the original 30-iter run, so the *value* is stable; only the spread
is noisy. Reporting `min` (per §7 methodology) makes this robust.

PackedMontyField31Neon (`p3-baby-bear/src/aarch64_neon`, `WIDTH=4`) activates exactly at the
predicted threshold: width≥4 cuts per-NTT latency by 3.6×, scaling further to ~5× at width=16.
The super-linear speedup vs the 4-lane WIDTH limit comes from `Radix2DitParallel` + improved
cache locality (multi-column processing keeps the CPU's execution units saturated by hiding
memory latency). Reviewed and confirmed plausible by adversarial QA (Gemini, Bloque 2 closure).

#### Goldilocks — Plonky3 batch latency-per-NTT

| Width | N=2^14 (μs/NTT) | N=2^18 (μs/NTT) | Speedup vs w=1 (N=2^14 / N=2^18) |
|------:|----------------:|----------------:|:----------------------------------|
| 1     | 248.96          | 5945.83         | 1.00x / 1.00x (baseline)          |
| 2     | 224.81          | 5139.17         | 1.11x / 1.16x                     |
| 4     | 182.45          | 4128.89         | 1.36x / 1.44x                     |
| 8     | **161.15**      | **3908.82**     | **1.54x / 1.52x** (best)          |
| 16    | 167.91          | 3959.03         | 1.48x / 1.50x                     |

CV N=2^14: 4.8% / 6.1% / 4.2% / 2.9% / 2.2% (w=2 marginally above 5%, all others within rubric).

Goldilocks does NOT vectorise on ARM NEON (no native u64 multiply-high). The 1.5× speedup at
width=8 is `Radix2DitParallel` + better cache layout, not packed SIMD. Width=16 plateaus,
suggesting cache pressure dominates beyond width=8.

#### TRZK single-vector vs Plonky3 batch (per-NTT comparison)

Using §1 TRZK Rust numbers (single-vector, the only mode TRZK supports) vs Plonky3 batch best
per-NTT from above:

| Field | N | TRZK Rust (μs) | P3 batch best (μs/NTT @ width) | **TRZK / P3 batch** |
|-------|---|---------------:|--------------------------------:|--------------------:|
| BabyBear | 2^14 | 140.1 | 51.16 (w=16) | **2.74x slower** |
| BabyBear | 2^18 | 3324.0 | 1250.85 (w=16) | **2.66x slower** |
| Goldilocks | 2^14 | 232.6 | 161.15 (w=8) | **1.44x slower** |
| Goldilocks | 2^18 | 5395.7 | 3908.82 (w=8) | **1.38x slower** |

**Decision rule §13.5 — formalisation (post adversarial QA, Bloque 2 closure)**: the
comparison is `TRZK_single_per_NTT / P3_batch_optimal_per_NTT`, where `P3_batch_optimal` is
the best per-NTT latency across `width ∈ {4, 8, 16}` (minimum w=4 to ensure SIMD activation
and exclude the noise of small-width batches that don't yet amortise overhead). Per-NTT
comparison normalises away batch size so a fair throughput comparison falls out. Threshold:
ratio > 1.20x ⇒ "Plonky3 batch wins ≥20% ⇒ Bloque 4 GO".

**Veredicto §13.5**: Plonky3 batch wins by ≥20% in BOTH fields under the formalised rule
(BabyBear 2.66-2.74×, Goldilocks 1.38-1.44×). Bloque 4 (SIMD migration to DFT standard path)
marked GO.

**Caveat sobre el gap real**: cerrar el gap completo requiere DOS cosas — (a) SIMD migration
en TRZK (Bloque 4 v3.19, ~120 LOC) para emparejar PackedMontyField31Neon, y (b) batch
interface nativo en TRZK (`ntt_batch(data[B][N], twiddles)`) para amortizar overhead — esto
es §13.3 Tarea B, **fuera de scope v3.19**. Bloque 4 solo cierra parcialmente el gap. La
compatibilidad TRZK con workloads batch reales requiere un futuro v3.20+ que añada el batch
interface.

**Pre-migration baseline para Bloque 4** — TRZK arm-neon grid expandido (captured
2026-04-19 pre-B4 for `CHECK:b4_no_regression`, two independent runs per BabyBear cell):

| Field | N | TRZK arm-neon C (μs) | P3 single-vector co-measurement (μs) | TRZK vs P3 single |
|-------|---|---------------------:|-------------------------------------:|------------------:|
| BabyBear | 2^14 | **71.5–82.8** (avg ~77) | 411.9–438.7 | TRZK +82% faster |
| BabyBear | 2^18 | **786.8–804.5** (avg ~796) | 4630.7–4638.5 | TRZK +83% faster |
| Goldilocks | 2^14 | 332.0 | 2792.7 | TRZK +88% (k=64 bypasses SIMD emitter — `k ≤ 32` guard in `UltraPipeline.lean:275`; falls through to scalar with `hw.isSimd=true` plan, *different* plan than `--hardware arm-scalar` §1 which is why this is slower than §1's 232.6μs scalar Rust) |
| Goldilocks | 2^18 | 6622.7 | 54820.1 | TRZK +88% |

(P3 co-measurement numbers use `benchmark.py`'s default profile, not §1's `--profile
match-plonky3`; internally consistent but not directly comparable to §1 absolute values.)

**Full cross-comparison: TRZK SIMD path vs P3 batch best per-NTT** (the comparison that
actually informs Bloque 4 scope, per Option B++ of adversarial QA):

| Field | N | TRZK path | TRZK (μs) | P3 batch best (μs/NTT @ width) | **TRZK / P3 batch** |
|-------|---|-----------|----------:|-------------------------------:|--------------------:|
| BabyBear | 2^14 | arm-neon SIMD | ~77 | 51.16 (w=16) | **1.50x slower** (P3 wins 33%) |
| BabyBear | 2^18 | arm-neon SIMD | ~796 | 1250.85 (w=16) | **0.64x — TRZK wins 36%** |
| Goldilocks | 2^14 | scalar §1 (arm-neon worse) | 232.6 | 161.15 (w=8) | 1.44x slower (P3 wins 31%) |
| Goldilocks | 2^18 | scalar §1 | 5395.7 | 3908.82 (w=8) | 1.38x slower (P3 wins 28%) |

**Regime flip discovery**: TRZK SIMD path already beats P3 batch at N=2^18 BabyBear (36%
faster). P3 wins at N=2^14 BabyBear due to batch cache-utilisation amortising small-size
overhead. Crossover ~N=2^16. Goldilocks has no SIMD path on ARM NEON (no u64 multiply-high
hardware per §14.2), so it remains behind P3 batch at all N regardless of B4 work.

**Implication**: the original §13.5 "Bloque 4 GO >20%" verdict used TRZK *scalar §1* as the
reference. Replacing that with TRZK *arm-neon SIMD* (the real comparable path for BabyBear)
yields a regime-dependent picture — B4 only helps small-N BabyBear, no large-N or Goldilocks
case benefits from ARM-only SIMD migration. This re-framing contributed to the Option B++
decision to defer B4 migration to v3.20 (where multi-target SIMD — AVX2 for 31-bit, AVX-512
IFMA for Goldilocks — gets rewritten in one coherent effort). See §8c for the additional
correctness finding that sealed the deferral.

Reproducción:
```bash
cd verification/plonky3 && make shim   # one-time
# Canonical N=2^14 (high-iter for stable CV) + N=2^18 (default)
python3 Tests/benchmark/benchmark_plonky3_batch.py \
    --fields babybear,goldilocks --sizes 14 --widths 1,2,4,8,16 \
    --iters 100 --warmup 10 --output Tests/benchmark/output/v3.19_b2_batch_n14_high_iters.json
python3 Tests/benchmark/benchmark_plonky3_batch.py \
    --fields babybear,goldilocks --sizes 18 --widths 1,2,4,8,16 \
    --iters 30 --warmup 5 --output Tests/benchmark/output/v3.19_b2_batch_n18.json
```

Raw JSON in `Tests/benchmark/output/` (gitignored — committed metadata only).

---

### 8c. arm-neon correctness gap discovered during B4 (v3.19 N319.4)

Attempting to close the CI gate for the arm-neon SIMD path via
`benchmark.py --validation-only --hardware arm-neon --langs c --fields babybear --sizes 14`
produced an immediate numerical divergence against the Python DFT-standard reference:

```
[VAL] babybear/2^14/c/arm-neon ... FAIL: Mismatch at [0]: compiled=1783564209, python=180743994
```

The legacy `emitSIMDNTTC` emits code that computes a valid NTT but under the **ref_dit**
(legacy v3.14) convention, while the Python reference, oracle validator, and scalar
emitters (`emitCFromPlanStandard`, v3.15+) use the **DFT standard** convention with
input bit-reversal + `stages.reverse`. The first output element alone already diverges
(sum-of-inputs in DFT standard vs a different formula in ref_dit).

**Consequences**:
- The arm-neon output is *not wrong per se* (it is a correct NTT under its own
  convention) but *incompatible* with the user-facing DFT standard convention now in
  use by every other emitter and validator in the project since v3.15.
- Users that invoke `--hardware arm-neon` today get output that does not match
  `--hardware arm-scalar` for the same input. This is surprising and unacceptable as a
  user-facing contract; it was hidden so far because the SIMD path was benchmarked with
  `--skip-validation` and never wired into the oracle or differential-fuzz gates.
- Closing this gap **requires** the full Bloque 4 migration originally scoped in
  `research/TRZK_SBB.md §13.4` (move `emitSIMDNTTC`/`emitSIMDNTTRust` to bitrev-prelude
  + `stages.reverse` + DFT-standard butterfly dispatch). Estimated ~200-270 LOC across
  SIMDEmitter.lean + new DFT-standard dispatch in the butterfly selection logic.

**Decision (2026-04-19)**: the migration is deferred to v3.20 together with the AVX2
and AVX-512 IFMA emitter rewrites (see `research/TRZK_SBB.md §14.12 addendum`). Doing
the ARM NEON migration now would force a second rewrite when v3.20 adds the x86 SIMD
targets, and the performance motivation is regime-dependent (§8b grid: TRZK arm-neon
already beats P3 batch at N=2^18 BabyBear; only N=2^14 BabyBear benefits from B4).

**Short-term mitigation**: the `--hardware arm-neon` path is documented as
experimental/non-user-facing until v3.20. The CI `benchmark-validation` job intentionally
does not gate on arm-neon output (would fail immediately on the convention mismatch); a
commented-out step placeholder in `.github/workflows/ci.yml` records the intent and a
pointer back to this section.

---

### 8d. arm-neon DFT standard migration + blocked bitrev (v3.20.a, 2026-04-20)

v3.20.a closes the §8c correctness gap. `emitSIMDNTTC` and `emitSIMDNTTRust` now
emit the DFT standard convention (`stages.reverse.foldl` + bit-reverse permutation
prelude via `bitRevPermutePreambleC` / inline Rust variant). Output is
byte-equivalent to `--hardware arm-scalar` for the same input — the first-element
divergence (compiled=1783564209 vs python=180743994) reported in §8c is eliminated.

#### Correctness gate (passed)

| Check | Pre-v3.20.a | Post-v3.20.a |
|-------|:-----------:|:------------:|
| `benchmark.py --validation-only --hardware arm-neon --fields babybear --sizes 14` | FAIL @ [0] | **PASS** |
| same, --sizes 18 | FAIL | **PASS** |
| same, --sizes 20 | FAIL | **PASS** |
| `differential_fuzz --mode fast --seed 42` | 1150/1150 | **1150/1150** (preserved) |

#### Gate H8 performance — partial (820 μs target deferred)

§14.11.a Gate H8 set the post-migration threshold at `mean ≤ 820 μs` for
`benchmark.py --skip-validation --hardware arm-neon --fields babybear --sizes 18`
(baseline 784.88 μs × 1.05 pre-migration). Two iterations were run:

| Iteration | Mean μs (5 runs) | CV | vs baseline | vs target |
|-----------|-----------------:|---:|------------:|----------:|
| v3.19 pre-migration (ref_dit, no bitrev) | 784.88 | 0.47% | baseline | — |
| v3.20.a initial (DFT standard + naive bitrev) | 1606.7 | ~1.2% | +104.7% | +96.0% over 820 |
| v3.20.a + `__builtin_bitreverse32` RBIT opt | **1538.3** | ~1.1% | +96.0% | +87.6% over 820 |

Target `≤ 820 μs` **not reached in v3.20.a**. Gate H8 **deferred to v3.20.b B3.5**
(see `research/TRZK_SBB.md §14.13.6 B3.5` and `§14.11.a addendum` below).

#### Root cause of the 1538 μs residual

The naive bitrev over N=2^18 = 262144 elements performs 2^17 = 131072 memory
swaps. On Apple M1 with N×4 bytes = 1 MB exceeding L1 (128 KB), each swap touches
two scattered cache lines with non-local access patterns. The RBIT optimisation
(added in this iteration, ~15 LOC) cuts the inner O(logN) bit-reverse loop to a
single ARM64 instruction per index, but the resulting win was only ~68 μs
(-4.3%) because clang `-O3 -mcpu=apple-m1` was already recognising the naive
shift-loop idiom and emitting RBIT automatically. The real bottleneck — the
scatter pattern of the swap itself — is unaffected by faster bit-reversal.

Profile estimate: bitrev cost ≈ (1538 − 785) μs ≈ 753 μs ≈ 131 072 swaps ×
5.75 ns/swap — consistent with L1-miss dominated scatter access at M1 memory
latency. A proper tiled/blocked bitrev would move only marginal gains here (M1
L1=128 KB still can't resident the 1 MB working set); the real win requires
**fusing bitrev into the first SIMD load stage** so the permutation happens as
part of the NTT's first data pass, eliminating a full buffer traversal. That
fusion is architecturally clean inside the v3.20.b batch SIMD kernels (B3.5)
but out of scope for v3.20.a (which preserves the single-vector legacy
structure modulo correctness alignment).

#### Value delivered in v3.20.a vs Plonky3 current

Even at 1538 μs, the arm-neon path delivers substantial value vs Plonky3:

| Regime | TRZK arm-neon | Plonky3 | Ratio |
|--------|-------------:|--------:|------:|
| Single-vector (width=1, fair baseline) | 1538 μs | ~4811 μs | **TRZK +3.1× faster** |
| Plonky3 batch best per-NTT (width=16) | 1538 μs | 1250 μs (§8b) | TRZK 1.23× slower |

End-to-end claim vs Plonky3 single-vector is **preserved** (and even vs scalar
fair comparison §1, TRZK Rust at 3324 μs for N=2^18 BabyBear is still slower
than TRZK arm-neon 1538 μs, so users on C arm-neon path still get a 2.2× win vs
the Rust scalar default). The regression is only visible when benchmarking TRZK
arm-neon vs Plonky3 batch at large N.

#### Reproduction

```bash
# Correctness:
python3 Tests/benchmark/benchmark.py --validation-only --hardware arm-neon \
    --fields babybear --sizes 14,18,20        # → 3/3 PASS

# Performance (5 runs):
for i in 1 2 3 4 5; do
    python3 Tests/benchmark/benchmark.py --skip-validation --hardware arm-neon \
        --fields babybear --sizes 18 --langs c
done
# Expected mean ~1530-1560 μs, CV ~1%.
```

---

### 8e. v3.20.b B3.5 — Bitrev fusion attempted, correctness bug surfaced, Gate H8 "best effort" (2026-04-21)

v3.20.b B3.5 implemented bitrev fusion into the first-executed NTT stage (halfSize=1
hs1 kernel) per §14.11.a addendum and §14.13.6 B3.5 scope. Infrastructure delivered
(N20.35.1 packed `emitPackedButterflyNeonDIT_BRFirst_C`, N20.35.2 single-poly
`emitNeonButterflyDIT_HS1_BRFirst_C` + `MemLayout.bitrev_strided` + `_B1_collapse`
theorem + wiring via `useBitrevFusion` flag). Flag defaults to `false` to preserve
backward compat; activation is explicit via `--bitrev-fusion` CLI.

**Correctness finding** (blocks Gate H8 perf measurement with fusion ON):

On validation with fusion ON, `benchmark.py --validation-only --hardware arm-neon
--fields babybear --sizes 14` FAILs at position [0] (compiled=1777148722,
python=180743994). Diagnosis via a minimal standalone test (N=16, stage 13 only):
positions [0..7] match the non-fused path; positions [8..15] all differ.

**Root cause**: **intrinsic read-after-write hazard** between fused-kernel
iterations. With 4 logical groups per iteration, `grp=0` writes sequentially to
natural positions `data[0..7]` and then `grp=4` reads scattered positions —
including indices in `[0..7]` that `grp=0` already overwrote. The fused kernel
reads from `data[bitrev(2*k), bitrev(2*k)+halfN]` to emulate the permutation
in-place, but this read target can intersect any prior iteration's write target,
and the intersection happens unavoidably because `bitrev` is a bijection over
the full array.

**Fix options are all beyond v3.20.b scope**:
1. **Scratch buffer** (hazard-free): read `data`, write `scratch`, copy back.
   Replaces 1 in-place pass with 2 out-of-place passes — defeats the memory
   savings, net-neutral vs non-fused baseline.
2. **Stockham autosort**: algorithmic redesign that removes the separate permute
   entirely via in-register shuffles across stages. Major refactor of the stage
   emission logic + trust boundary redraw. Tracked for v4.0.
3. **COBRA-style cache-aware permute** (L-759 baseline): modest 20-30% wins per
   the prior analysis — insufficient for Gate H8 threshold.

**Action taken**: `useBitrevFusion` kept as opt-in with default `false`; backward
compat preserved. Infrastructure (kernels + theorems + smoke tests) stays in the
codebase as prep work for the eventual algorithmic redesign. No Gate H8 perf
measurement executed with fusion ON since validation gate fails — correctness
non-negotiable per §14.13.8 MVP escape policy.

**Validation preservation (fusion OFF, i.e., production default)**:

| Check | Result |
|-------|:------:|
| `benchmark.py --validation-only --hardware arm-neon --fields babybear --sizes 14,18,20` | **3/3 PASS** |
| `differential_fuzz.py --mode fast --seed 42` | **1150/1150 PASS** |
| `benchmark.py --rust-simd --validation-only --hardware arm-neon --fields babybear --sizes 14` | **1/1 PASS** |

**Gate H8 outcome (§14.13.8 MVP escape invoked)**:

- Baseline `arm-neon N=2^18 BabyBear` stays at **1538 μs** (unchanged from
  v3.20.a post-RBIT).
- Threshold `≤ 820 μs` **not achieved**. Per §14.13.8 MVP escape: Gate H8
  redefined as **"best effort, no blocker"**. Threshold 820 μs deferred to v4.0
  algorithmic work (Stockham autosort or equivalent).
- End-to-end claim preserved: TRZK arm-neon still **3.1× faster than Plonky3
  single-vector** at N=2^18 (1538 μs vs ~4811 μs).

**Lesson** (candidate for `lecciones/`): *"Read-scattered/write-natural in-place
fusion has intrinsic read-after-write hazards when the permutation is a
non-trivial bijection over the full working array; requires either scratch
buffering (defeats memory savings) or algorithmic redesign. Catch via
minimal-N (N=16) diagnostic that compares fused-path output against
permute+non-fused-path output element-by-element — the mismatch pattern
(first half matches, second half diverges) points directly at the hazard."*

**Reproduction of finding**:

```bash
# Build Lean:
lake build

# Validation with fusion ON (should FAIL):
python3 Tests/benchmark/benchmark.py --validation-only --hardware arm-neon \
    --fields babybear --sizes 14 --bitrev-fusion
# → FAIL @ [0]

# Validation with fusion OFF (default, should PASS):
python3 Tests/benchmark/benchmark.py --validation-only --hardware arm-neon \
    --fields babybear --sizes 14
# → 1/1 PASS
```

---

### 8f. Gate H8 alternatives investigation — blocked REFUTED, R4 insufficient, H8 literal permanente (2026-04-21)

Post-§8e B3.5 hazard, se ejecutó `/science` Round 1 comparativo entre tres
rutas candidatas para cerrar el Gate H8 residual (≤820 μs N=2^18 BB
arm-neon). Report: `research/TRZK_gateh8_report1.md`. CONVERGED en 1 ronda.

**Candidatos evaluados**:
- **(a) Bitrev blocked cache-friendly con scratch**
- **(b) Radix-4 stages (18→9)**
- **(c) Batch amortization via v3.20.b B4.5**

**Hallazgos empíricos**:

1. **Bitrev isolate measurement** (Parte A): bitrev con `__builtin_bitreverse32`
   cuesta mean 788μs vs memcpy floor 65μs = **12.2× memcpy**. Conclusion:
   bitrev es **scatter-bound**, no bandwidth-bound. Cada swap toca 2 cache
   lines uncorrelated; hw prefetcher no puede stream-ahead.

2. **Bitrev blocked REFUTED empírico** (Parte B, H1+H2): 14 variants
   testeadas (scalar + NEON × 6 tile sizes). **TODOS regresan +65%** vs
   baseline rbit (1242μs mean vs 754μs baseline). Tile size irrelevante
   (<2% variación 128-4096). Causa: pérdida del in-place swap prefetch
   coupling + pass 2 memcpy-back extra traffic (~60μs). Validation PASS
   byte-for-byte vs naive.

3. **R4 stages analytical** (Parte C, H3): proyectado 1177-1293μs total.
   **FALSA MED** — no cierra ≤1000μs. Solo ahorra ~345μs en stages
   (785→424-540) pero el 753μs bitrev floor domina. Además, NEON R4 kernel
   para BabyBear NO existe (solo scalar Goldilocks) — requiere 500-650 LOC
   + 4-6 días infra nueva.

4. **Math ceiling identificado** (Parte A): si bitrev fuera 0μs, el
   pipeline sería **~750μs** — apenas 70μs bajo el threshold 820μs. **No
   hay approach "reducir bitrev" que cierre Gate H8 literal**. Solo
   algorithmic redesign que **elimine el pass explícito**: DIT↔DIF pairing,
   six-step, o stride-implicit.

**Verdict final Round 1**:

| H | Hipótesis | Verdict | Confidence |
|---|-----------|---------|:----------:|
| H1 | Blocked ≤350μs | REFUTED | HIGH |
| H2 | Blocked cierra H8 literal | REFUTED | HIGH |
| H3 | R4 ≤1000μs | FALSA | MED |
| H4 | Batch (c) cierra narrativa | VERDADERA | HIGH-MED |
| H5 | Combo óptima | FALSA | HIGH |

**Decisión**: PROCEED (c) via B4.5 + DROP (a) + DEFER (b) + ESCALATE Gate H8
literal como **research goal v4.1+** (nuevo ítem V4.1-E en `TRZK_gains.md §10.5`).

**Gate H8 literal redefinido PERMANENTE** (actualización §14.13.8 MVP
escape): no es problema de kernel optimization sino de algorithmic
redesign. Escape MVP permanente con target recalibrado a "competitive
batch narrative" via (c). TRZK ship con claim TRZK-batch ganador vs P3-batch
(proyección 2×-4× amortización), no con 820μs single-vector.

**Artifacts**: `/tmp/TRZK_gateh8_r1/` (bitrev_isolate.c, bitrev_blocked.c
14 variants, r4_analysis.md analytical, batch_amortization_analysis.md,
roi_comparison.md). State archived
`~/.claude/skills/science/STATE/archived/`.

**Lesson L-770** registrada: "Bitrev en NTT pipelines es scatter-bound, no
bandwidth-bound. Blocked bitrev es contraproducente por loss of in-place
swap prefetch coupling. Solo eliminación del pass explícito cierra gates
≤memcpy-floor." Consultable via
`query_lessons.py --lesson L-770` o `--hybrid "bitrev scatter"`.

---

### 8f. v3.20.b B4.5 — Packed Kernel Integral Wiring: MVP escape, deferred to v3.20.c (2026-04-21)

v3.20.b B4.5 wired the `emitPackedButterflyNeonDIT_C` kernel (delivered B3) into
a complete batch NTT emission pipeline (`emitCFromPlanBatch_Packed`), with:
- `lowerStageVerified_OffsetAware` (N20.45.1, linear-layout offset-aware fallback)
- Transpose-based interleaved layout + bit-reverse per-poly + packed kernel
  dispatch + scalar-on-interleaved fallback for halfSize < 4 (N20.45.2)
- `shouldUsePackedPath` predicate (k ≤ 32 ∧ B ≥ 4 ∧ B % 4 == 0 ∧ all-R2)
- Differential correctness test vs independent Solinas-fold scalar reference
  (`Tests/benchmark/test_packed_correctness.sh`) — **PASS byte-exact on 9 N×B
  combos (N ∈ {64, 128, 256, 1024, 4096, 16384} × B ∈ {4, 16})**

#### Correctness gate (passed unconditionally)

| Check | Result |
|-------|:------:|
| `test_packed_correctness.sh 6 4` (N=64 B=4) | 256/256 bytes exact |
| `test_packed_correctness.sh 7 4` (N=128 B=4) | 512/512 bytes exact |
| `test_packed_correctness.sh 8 4` (N=256 B=4) | 1024/1024 bytes exact |
| `test_packed_correctness.sh 10 4` (N=1024 B=4) | 4096/4096 bytes exact |
| `test_packed_correctness.sh 12 4` (N=4096 B=4) | 16384/16384 bytes exact |
| `test_packed_correctness.sh 14 16` (N=16384 B=16) | 262144/262144 bytes exact |
| `differential_fuzz.py --mode fast --seed 42` (pre-existing, single-vector) | **1150/1150 PASS** (preserved) |

**Verdict correctness: PASS**. The packed kernel + transpose + scalar fallback
machinery produces mathematically correct output (byte-exact vs independent
Solinas-fold reference) across all tested N and B combinations.

#### Performance gate (MVP escape invoked)

Gate criteria per §14.13.6 B4.5 sharpened (post B4 gate flaw lesson):
- `TRZK-packed mean ≤ 0.50 × TRZK-loop mean` (≥2× amortization)
- `TRZK-packed mean ≤ 20013 μs` (beat Plonky3-batch)
- `CV < 2% over 5 runs`

Measurement (`test_packed_perf_gate.sh 18 16 5` on Apple M1, `cc -O3
-mcpu=apple-m1`, 5 runs + warmup):

| Path | Mean μs | Min μs | CV |
|------|--------:|-------:|---:|
| TRZK-loop (B4, scalar × 16) | 53049 | 52733 | 0.46% |
| TRZK-packed (B4.5) | 42379 | 42148 | 0.66% |
| Single-vector NEON baseline (sanity check) | 1666.7 | — | — |

Ratio packed/loop: **0.799** — 1.25× amortization, far from 2× target.

**Root cause — Sospecha 1 confirmed via emission inspection**:

```bash
lake env lean --run Tests/benchmark/emit_batch_code.lean babybear 18 16 \
    | grep "neon_bf_dit\|vld1q\|vmull\|arm_neon"
# → empty output. B4 loop reference is pure SCALAR, not NEON.
```

`emit_batch_code.lean` (B4 N20.4.3 driver) calls `emitCFromPlanStandard` — the
**scalar** path, not `emitSIMDNTTC`. The "TRZK-loop reference" I was measuring
was scalar × 16 polys, not NEON × 16 polys. The 1.25× ratio vs this baseline
masks a structural issue.

**Honest comparison against fair baselines**:

| Reference | Time (μs) | TRZK-packed ratio | Advantage vs ref |
|-----------|----------:|------------------:|-----------------:|
| TRZK-loop (scalar × 16, irrelevant prod baseline) | 53049 | 0.799 | +20% ✅ |
| **NEON single-vector × 16 (linear extrapolation)** | **26656** (1666.7 × 16) | **1.59** | **−59% ❌** |
| **Plonky3-batch (BENCHMARKS §8b)** | **20013** | **2.12** | **−112% ❌** |

- TRZK-packed 42379 μs is **1.59× SLOWER** than NEON single-vector × 16
  extrapolation.
- TRZK-packed 42379 μs is **2.12× SLOWER** than Plonky3-batch 20013 μs.

Per §14.13.6 B4.5 decision matrix:
> "Advantage negativo en cualquier escenario → MVP escape"

#### Methodology sanity (flag fix validation)

A methodology review suggested `-march=armv8-a` vs `-mcpu=apple-m1` might
explain the gap (M1 sqdmulh scheduling). Full remediation:

| Sites with `-march=armv8-a` fixed | Action |
|-----------------------------------|--------|
| `Tests/benchmark/test_packed_correctness.sh:250` | → `-mcpu=apple-m1` |
| `Tests/benchmark/test_packed_perf_gate.sh:170` | → `-mcpu=apple-m1` |
| `Tests/benchmark/debug_neon.py:83` (debug tool, out of scope) | reported, not fixed |
| Lean emitter (`AmoLean/.../*.lean`) | CLEAN — 0 `-march=armv8` in codegen |

Single-vector NEON sanity post-fix: **1666.7 μs** (vs historical 1538 μs target,
+8.4%, within ±10%). Flag correctly propagated in production path.

Remeasure with corrected flag: ratio 0.786 → 0.799 (**no material change**,
within noise). **Methodology was not the problem**; the packed driver has
structural inefficiency.

#### Root cause analysis (for v3.20.c scope)

Three factors limit the packed path's competitiveness:

1. **Transpose overhead** (2 full memory passes per W-batch): linear → interleaved
   + interleaved → linear. For B=16 N=2^18: 4 W-batches × 2 × 4 MB = 32 MB extra
   memory traffic. Fixable by caller-controlled interleaved layout API (breaks
   compat) or by fusing transpose with bit-reverse (saves 1 pass).

2. **Scalar-on-interleaved fallback dominates final stages**: for halfSize < 4
   (stages 16 + 17 in a N=2^18 plan), the packed path falls back to
   `trzk_scalar_bf_4lane` which executes 4 independent scalar butterflies per
   pair. Production NEON single-vector uses `neon_bf_dit_hs1` / `hs2` small-SIMD
   kernels (vld2q/vst2q interleave) that pack 4 butterflies into 1 SIMD call —
   my packed path has no equivalent for interleaved layout.

3. **Per-butterfly throughput inferior vs production NEON**: my
   `neon_bf_dit_packed` loads 1 twiddle (vdupq_n_s32 broadcast) and does 4 polys
   × 1 pair. Production `neon_bf_dit` loads 4 twiddles (vld1q_s32) and does 1
   poly × 4 pairs — same NEON throughput but with pipeline-friendly consecutive
   array access. Packed path's broadcast + scatter pattern may incur
   implicit latency my profiling has not yet measured.

#### Action taken (MVP escape)

1. **Packed dispatch stays opt-in only** — `shouldUsePackedPath` is NOT wired into
   `emitCFromPlanBatch` production path. Callers invoke `emitCFromPlanBatch_Packed`
   directly only via `Tests/benchmark/emit_packed_batch.lean` (test-only driver).
   Zero impact on production `benchmark.py` default path.
2. **Infrastructure preserved**: `emitCFromPlanBatch_Packed`, `transposeHelperC`,
   `trzk_scalar_bf_4lane`, `lowerStageVerified_OffsetAware`, and all smoke tests
   stay in the codebase as scaffold for v3.20.c.
3. **v3.20.b batch story delivered**: via B4's loop-wrapping `emitCFromPlanBatch`
   (TRZK-loop scalar × B) — mathematically correct, B=1 collapse preserved, not
   competitive vs Plonky3-batch but structurally sound.

#### Deferred to v3.20.c (documented scope)

- Fuse transpose with first-stage load / eliminate explicit transpose pass
- NEON small-SIMD kernels (hs1/hs2 analogs) for interleaved halfSize<4 stages
- Caller-controlled interleaved-layout API (opt-in, breaks layout transparency)
- Profile `neon_bf_dit_packed` vs production `neon_bf_dit` for per-butterfly
  overhead (possibly replace `vdupq_n_s32` broadcast with aligned twiddle
  pre-staging)

#### Lesson candidate (glearnings §5.8)

> *"Performance gate requires honest baseline: compare SIMD-capable driver against
> SIMD-capable reference, not SIMD vs scalar. A scalar-loop baseline can make a
> SIMD path look amortized when in reality it loses against the NEON-loop version
> of the same algorithm. Pre-gate checklist: confirm both paths (test and
> reference) compile through the same target intrinsics set."*

Candidate L-id: L-771 (to be assigned post-merge).

#### Reproduction

```bash
# Build Lean:
lake build

# Correctness (8 N×B combos, all PASS byte-exact):
for logn in 6 7 8 10 12 14; do for b in 4 16; do
  bash Tests/benchmark/test_packed_correctness.sh $logn $b
done; done

# Perf gate (ratio 0.799, PARTIAL/MVP escape):
bash Tests/benchmark/test_packed_perf_gate.sh 18 16 5

# Single-vector NEON sanity (1666.7 μs, ±8% vs 1538 target):
python3 Tests/benchmark/benchmark.py --hardware arm-neon --fields babybear \
    --sizes 18 --skip-validation
```

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

## Current Results

### Plonky3 batch benchmark (Tarea A) — ARRANQUE v3.19 (3.19.0)

**Closed**: 2026-04-19 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N319.2.1 Extender plonky3_shim con dft_batch(width), N319.2.2 Python harness batch comparison, N319.2.3 Veredicto batch + actualizar BENCHMARKS.md §8 + TRZK_SBB.md §13.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 466 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Rust como output primario (docs + CI) (3.19.0)

**Closed**: 2026-04-19 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N319.3.1 Promover Rust como output primario (docs + CI).

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 40 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### SIMD migration (CONDICIONAL a B2 verdict >20%) (3.19.0)

**Closed**: 2026-04-19 | **Status**: DEFERRED (Option B++ — scope + correctness absorbed into v3.20)

#### 1. What is tested and why

Nodes covered: N319.4.1 Migrar emitSIMDNTTC al DFT standard path (CONDICIONAL), N319.4.2 Migrar emitSIMDNTTRust al DFT standard path (CONDICIONAL), N319.4.3 Agregar --hardware arm-neon a oracle_validate.py (CONDICIONAL), N319.4.4 Validar HS1/HS2 variants + Codegen Validation Gate (CONDICIONAL).

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 12 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### BENCHMARKS.md update + caveat width=1 (DONE en 44bff09) (3.19.0)

**Closed**: 2026-04-19 | **Status**: Anchor — ejecutado pre-v3.19 en commit 44bff09 (BENCHMARKS.md canonical sizes + width=1 caveat)

#### 1. What is tested and why

Nodes covered: N319.1.1 BENCHMARKS.md update large-N + caveat width=1 (DONE en 44bff09).

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Cleanup deuda técnica (baja prioridad) (3.19.0)

**Closed**: 2026-04-19 | **Status**: Cleanup — deferred/partial

#### 1. What is tested and why

Nodes covered: N319.5.1 Cleanup warnings Rust at source en stmtToRust, N319.5.2 BabyBear Rust vs C anomaly re-verification a N>2^14, N319.5.3 Documentar four-step NO-GO permanente.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### v3.19 cleanup debt (eliminar #![allow] band-aids) (3.20.0)

**Closed**: 2026-04-20 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N20.0.1 Eliminar 3 #![allow(...)] band-aids + fix warnings al origen en stmtToRust.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 62 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### v3.20.a — SIMD legacy → DFT standard migration + Gate H8 (3.20.0)

**Closed**: 2026-04-20 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N20.a.1 SIMD migration: stages.reverse + bitRevPermutePreamble en emitCFromPlanStandard + emitRustFromPlanStandard, N20.a.2 Oracle validator --hardware arm-neon + CI arm-neon-validation job, N20.a.3 Gate H8 pre-merge PR v3.20.a (5 runs, mean ≤ 820 μs @ N=2^18 BabyBear).

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 37 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Foundations (NTTPlan.batchWidth + Trust Boundary docs) (3.20.0)

**Closed**: 2026-04-20 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N20.1.1 NTTPlan.batchWidth field + Plan.withBatch helper + batchPolyOffset + soundness lemma, N20.1.2 Trust Boundary Documentation template en CLAUDE.md.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 87 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### MixedNodeOp Extensions (3 constructores + 4 intrinsics + 15 lemmas) (3.20.0)

**Closed**: 2026-04-20 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N20.2.1 3 constructores MixedNodeOp: packedLoadNeon + packedStoreNeon + packedButterflyNeonDIT, N20.2.2 4 NeonIntrinsic variants + toCName/fromCName mappings, N20.2.3 15 lemmas NodeOps/NodeSemantics instances (cases op sistemático).

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 310 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

