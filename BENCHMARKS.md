# TRZK Benchmarks

Performance data for TRZK NTT code generation.
Rubrics and QA criteria are in `research/RUBRICS.md`.

---

## v3.16.0 — Real Benchmarks vs Plonky3

### 0. Correctness

Output verified element-by-element (mod p) against:
- **Python naive DFT O(N²)**: `A[k] = Σ_j data[j] · ω^(jk) mod p` — 36/36 PASS
- **Plonky3 real (Polygon Rust library)** via FFI: oracle_validate.py — **24/24 PASS**

| Layer | Reference | Fields | Sizes | Result |
|-------|-----------|--------|-------|--------|
| Python naive DFT | `_naive_dft` O(N²) | BabyBear, Goldilocks | N=4..1024 R2+R4 | 36/36 PASS |
| Oracle vs Plonky3 | `plonky3_ntt_forward` FFI | BabyBear, Goldilocks | N=8..1024 R2 | 14/14 PASS |
| Oracle vs Plonky3 | `plonky3_ntt_forward` FFI | BabyBear, Goldilocks | N=16..1024 R4 | 10/10 PASS |

### 1. Plonky3 Reference

- **Library**: p3-field, p3-dft, p3-goldilocks, p3-baby-bear from `github.com/Plonky3/Plonky3` main branch
- **Algorithm**: `Radix2Dit::dft_batch()` (Radix-2 DIT, scalar)
- **Language**: Rust, `--release` with LTO, `codegen-units=1`, `opt-level=3`
- **FFI**: via `libplonky3_shim.dylib` (cdylib, panic=abort)

### 2. TRZK Implementation

- **Generator**: `emitCFromPlanStandard` via ultra pipeline
- **Algorithm**: Standard DFT (bitrev input + DIT small→large)
- **Plan at N=2^14**: R2 uniform Harvey (R4 disabled at N≤2^14, overhead > savings)
- **BabyBear**: Montgomery REDC for twiddle products, Harvey reduction for sums/diffs
- **Goldilocks**: PZT goldi_reduce128 for twiddle products, standard twiddles (not Montgomery)
- **Languages**: C (`cc -O2`) and Rust (`rustc -O`)

### 3. Artefacts

Benchmark scripts in `Tests/benchmark/`:
- `benchmark_plonky3.py` — TRZK C vs Plonky3 Rust timing
- `benchmark_pipeline.py` — Baseline R2 vs R4 mixed pipeline value
- `oracle_validate.py` — Correctness: TRZK C vs Plonky3 real (FFI)

Output directory: `Tests/benchmark/output/latest/` (gitignored, reproducible).

### 4. Reproduction

```bash
# Prerequisites: Lean 4 (elan), Rust (cargo), C compiler (cc), Python 3

# Build TRZK
lake build bench

# Build Plonky3 shim
cd verification/plonky3 && make shim && cd ../..

# Oracle validation (correctness)
python3 Tests/benchmark/oracle_validate.py --fields babybear,goldilocks --sizes 3,4,5,6,7,8,10

# Performance benchmark vs Plonky3
python3 Tests/benchmark/benchmark_plonky3.py --fields babybear,goldilocks --sizes 14 --iters 10

# Pipeline value (R2 baseline vs R4 mixed)
python3 Tests/benchmark/benchmark_pipeline.py --fields babybear,goldilocks --sizes 14 --iters 10
```

### 5. Metadata

```
Date:      2026-04-14
Git:       v3.16.0 (branch spiral)
Hardware:  Apple Silicon ARM64 (M-series), single core
Compiler:  cc -O2 (Apple Clang) for TRZK C
           rustc --release LTO for Plonky3 Rust
Iters:     10, averaged
```

### Performance: TRZK vs Plonky3 Real

| Field | N | TRZK C (μs) | Plonky3 Rust (μs) | Ratio | Note |
|-------|---|-------------|-------------------|-------|------|
| **BabyBear** | 2^14 | 340 | 751 | **0.45x** | TRZK 55% faster |
| **Goldilocks** | 2^14 | 840 | 711 | **1.18x** | Plonky3 18% faster |

**BabyBear**: TRZK C scalar is significantly faster than Plonky3 Rust scalar.
Montgomery REDC + Harvey reduction + R2 uniform plan.

**Goldilocks**: Plonky3 is 18% faster. Gap explained by reduction strategy:
TRZK uses PZT goldi_reduce128 (~9 ARM instr) while Plonky3 uses an optimized
Goldilocks-specific reduction. Closing this gap requires optimizing the
reduction (sbb trick) or four-step NTT (cache-friendly for large N).

### Pipeline Value: R2 Baseline vs R4 Mixed

| Field | R2 Baseline (μs) | R4 Mixed (μs) | Speedup | Note |
|-------|-------------------|---------------|---------|------|
| BabyBear | 291 | 477 | 0.61x | R4 overhead > savings at N=2^14 |
| Goldilocks | 779 | 1140 | 0.68x | Same — R4 hurts at small N |

**Finding**: R4 inverted butterfly has higher instruction overhead than R2 at N=2^14
(data fits in L1, cache effects don't dominate). R4 benefit expected at N≥2^16
where cache miss reduction compensates for instruction overhead. ultraPipeline
dispatch forces R2 at N≤2^14.

### Historical Context

The "0.96x vs Plonky3" reported in v3.12.0 was **INVALID**. The legacy benchmark
compared two different transforms (Ultra with Montgomery twiddles + PZT reduction
vs P3 with standard twiddles + % p). The correctness check always failed for
Goldilocks but was masked by interpreter timeout. See TRZK_spiral_idea.md §3.9.

---

## v3.15.0 — First Correct Measurements (superseded by v3.16.0)

See git history for v3.15.0 data. All v3.15.0 numbers used P3 naive (not Plonky3 real)
and are superseded by the v3.16.0 measurements above.
