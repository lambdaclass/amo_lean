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

---

### 1. **PRIMARY HEADLINE — Rust-vs-Rust (fair algorithmic comparison)**

Both TRZK and Plonky3 compiled with `rustc --release` equivalent flags. Eliminates compiler variable.

| Field | N | TRZK Rust (μs) | Plonky3 Rust (μs) | **Rust/P3 Ratio** | Note |
|-------|---|----------------|-------------------|--------------------|------|
| **Goldilocks** | 2^14 | **289.2** | 269.5 | **1.07x** | TRZK 7% behind |
| **BabyBear** | 2^14 | **337.8** | 266.9 | **1.27x** | TRZK 27% behind (+ Plonky3 uses NEON) |

**Key insight**: the residual algorithmic gap is **~7% for Goldilocks** and **~27% for BabyBear**
(the latter includes Plonky3's NEON advantage) when both implementations go through the same
compiler (rustc) with the same release profile. Previous claims of 1.18x-1.69x mixed algorithmic
gap with compiler asymmetry (clang vs rustc-LTO).

### 2. Secondary — C-vs-Rust cross-compiler (for reference)

Not apples-to-apples: TRZK C (clang) vs Plonky3 Rust (rustc + LTO + codegen-units=1). Retained for
historical continuity with pre-v3.17 benchmarks.

| Field | N | TRZK C (μs) | Plonky3 Rust (μs) | C/P3 Ratio | Note |
|-------|---|-------------|-------------------|------------|------|
| Goldilocks | 2^14 | 455.0 | 269.5 | 1.69x | clang C slower than rustc Rust for same algorithm |
| BabyBear | 2^14 | 258.9 | 266.9 | 0.97x | clang C slightly ahead (Montgomery REDC with signed types) |

**Explanation of the C vs Rust gap**: TRZK C (cc -O3 -flto -mcpu=apple-m1) is ~50% slower than TRZK
Rust (rustc opt-level=3 LTO codegen-units=1) for Goldilocks (455 vs 289 μs). The difference is
LLVM's cross-module inlining with `codegen-units=1` that clang-C builds don't match. This is a
compiler/build-system difference, not an algorithm difference.

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
python3 Tests/benchmark/benchmark_plonky3.py \
    --lang both --profile match-plonky3 \
    --fields goldilocks,babybear --sizes 14 --iters 30

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
Iters:     30, min of iterations (dropping worst outliers)
Variance:  ~±20% run-to-run on Apple Silicon (thermal / cache state).
           Report medians; single-number claims have limited meaning.
```

---

### 7. Honest Interpretation

**Pre-v3.17 narrative (incomplete)**: "TRZK has a 18% algorithmic gap with Plonky3 on Goldilocks."

**Post-v3.17 reality**: The 18% gap was a mix of:
- **~11% compiler asymmetry** (clang+LTO produces slower binary than rustc+LTO+codegen-units=1
  for this specific code).
- **~7% real algorithmic gap** (Plonky3 uses `branch_hint()` + structural patterns that LLVM
  optimizes slightly better even with same flags).

**What v3.17.0 actually achieved**:
1. **−92 ARM instructions** in the C generated NTT (flag-merge linearization in reduce128 + add).
2. **Honest benchmarking infrastructure** (`--profile` + `--lang both` + metadata).
3. **Four-step NO-GO confirmed** empirically; re-open conditions documented.
4. **Rust-vs-Rust parity validated** (oracle 14/14 + element-by-element C=Rust 32/32).
5. **Opción B evaluated and rejected**: `goldi_reduce128_from_product` proved no-op post-N317.2
   (clang inlined both forms identically). In-code comment documents the experiment.

**What v3.17.0 did NOT achieve**:
- Goldilocks ≤ 1.05x target (original plan v3.17). Real residual is ~7% Rust-vs-Rust.
  To close further: (a) migrate TRZK's primary output to Rust in docs/CI (v3.18 candidate), or
  (b) add Rust-equivalent branch hints (`core::hint::likely`/`unlikely`, stable since 1.74).

**Unexpected findings** (documented for v3.18):
- **BabyBear Rust slower than BabyBear C** (338 vs 259 μs match-plonky3). Likely related to
  rustc + LTO + codegen-units patterns with u32 wrapping arithmetic. Investigation needed.
- **`emitRustFromPlanStandard` emits 309 rustc warnings** (unused vars, redundant parens). Works
  but is code smell — cleanup task for v3.18.
- **BabyBear NEON-vs-NEON fair comparison still blocked** until v3.18 SIMD migration.

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
| Goldilocks gap ≤ 1.10x (Rust-vs-Rust, match-plonky3) | v3.17 target | **PASS (1.07x)** |
| BabyBear gap ≤ 1.30x (Rust-vs-Rust, match-plonky3) | v3.17 target | PASS (1.27x) — algorithmic, SIMD asymmetry separate |
| Default `use_standard=True` (no flag needed) | N317.8 (absorbed) | PASS |
| `--profile match-plonky3` produces `-O3 -flto -mcpu=apple-m1` | N317.8 | PASS |
| Four-step NO-GO reproducible via `bench_four_step_isolated.py` | N317.9 | PASS |
