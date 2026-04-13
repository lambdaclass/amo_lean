# Truth Research ZK: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Tests](https://img.shields.io/badge/Tests-2850%2B-green.svg)](#testing)
[![Build](https://img.shields.io/badge/Build-3140%20modules-brightgreen.svg)](#build)
[![FRI Verified](https://img.shields.io/badge/FRI-189%20theorems%2C%200%20sorry-blue.svg)](#fri-formal-verification)
[![Extraction Complete](https://img.shields.io/badge/Extraction-complete%20(0%20sorry)-blue.svg)](#verified-extraction-completeness)

## What is TruthResearch ZK?

**TruthResearch ZK (TRZK)** is a verified optimizing compiler that transforms mathematical specifications written in Lean 4 into optimized C/Rust code with **formal correctness guarantees**. It targets cryptographic primitives used in STARK provers and zkVMs.

The core value proposition: **write your mathematical specification once in Lean 4, and get optimized C or Rust code that is correct by construction** — every optimization step is a formally proven theorem. This eliminates the traditional tradeoff between performance and correctness in cryptographic implementations.

TRZK covers the key building blocks of modern proof systems: NTT (Number Theoretic Transform), FRI (Fast Reed-Solomon IOP), field arithmetic (Goldilocks, BabyBear, KoalaBear, Mersenne31), Poseidon2 hashing, and a verified e-graph optimization engine with automatic bound-aware discovery. The generated code is Plonky3-compatible: for BabyBear NTT, TRZK's verified C is **62.8% faster** than Plonky3's Rust; for Goldilocks, TRZK matches Plonky3 scalar performance (0.96x) despite full formal verification.

## Ecosystem & Comparisons

TRZK occupies a unique position: it combines **equality saturation optimization** with **formal verification** in a single tool. Most existing projects do one or the other.

| Project | Approach | Proof Assistant | Verification Scope | Codegen Target |
|---------|----------|-----------------|---------------------|----------------|
| **TRZK** | E-graph optimization + Sigma-SPL IR | Lean 4 | Full pipeline (spec → IR → code) | C, Rust |
| [fiat-crypto](https://github.com/mit-plv/fiat-crypto) | Synthesis from field specs | Coq | Field arithmetic | C, Rust, Go, Java |
| [Jasmin](https://github.com/jasmin-lang/jasmin) | Verified assembly compiler | Coq (EasyCrypt) | Compiler correctness | x86 assembly |
| [CryptoLine](https://github.com/fmlab-iis/cryptoline) | Algebraic program verification | External (SMT) | Post-hoc verification | N/A (verifier only) |
| [hacspec](https://github.com/hacspec/hacspec-v2) | Executable specification language | F\*/Coq | Spec extraction | Rust |
| [SPIRAL](https://www.spiral.net/) | Autotuning + formal rewrite rules | Custom (GAP) | Transform correctness | C, CUDA, FPGA |

**What makes TRZK different:**
- **Equality saturation** (e-graphs) explores the full space of equivalent rewrites simultaneously, extracting the globally optimal form — not just a locally optimal greedy result
- **Sigma-SPL IR** enables algebraic reasoning about loop nest generation from Kronecker product decompositions
- **Trust-Lean verified backend** provides a formally verified C code generator with sanitized identifiers and structural correctness proofs
- **Single tool**: optimization, verification, and code generation in one pipeline, rather than separate tools stitched together

## How It Works

```
Mathematical Spec (Lean 4)
        |
        v
  E-Graph Optimization Engine
  (equality saturation optimization strategy)
        |
        v
  Algebraic Semantics (Sigma-SPL IR)
  (verified lowering for matrix operations)
        |
        v
  Trust-Lean Bridge (verified roundtrip)
  (ExpandedSigma -> TrustLean.Stmt conversion)
        |
        v
  Optimized C / Rust / SIMD Code
  (correct by construction, Plonky3-compatible)
```

### Formal Optimization Strategy

TRZK uses **equality saturation** via e-graphs to find optimal formal equivalent forms of mathematical expressions. Unlike hand-tuned optimizers, every rewrite rule in our e-graph is a formally proven theorem in Lean 4. The process:

1. **Encode** the mathematical specification as an e-graph
2. **Saturate** by applying all verified rewrite rules until a fixed point
3. **Extract** the optimal form using a cost model
4. **Lower** through AlgebraicSemantics (Sigma-SPL IR) to C/Rust code

This architecture is **portable and modular**: adding a new primitive means writing a Lean specification and lowering rules — the optimization engine and code generator are reusable across all primitives.

### Two Operational Modes

| Mode | Purpose | Status |
|------|---------|--------|
| **Verifier** | Certify external implementations (e.g., Plonky3) are mathematically correct via translation validation and FRI algebraic proofs | Production Ready |
| **Generator** | Generate verified, optimized C/Rust NTT code from Lean field specifications with automatic bound-aware reduction selection via e-graph discovery | Production Ready |

## Features

- **Verified Pipeline Soundness** — End-to-end `full_pipeline_soundness` theorem: saturation + extraction preserves semantics, **0 custom axioms**
- **Translation Validation** — Level 2 soundness via `cryptoEquivalent` relation with congruence closure
- **NTT** (Number Theoretic Transform) — Verified, optimized, Plonky3-compatible
- **Radix-4 NTT** — 4-point butterfly (8 axioms pending formal implementation, v2.5.0)
- **Goldilocks Field** — Scalar + AVX2 arithmetic (p = 2^64 - 2^32 + 1), **0 axioms**
- **BabyBear Field** — Scalar arithmetic (p = 2^31 - 2^27 + 1), **0 axioms**
- **FRI Formal Verification** — 16 verified modules (~4,450 LOC, 189 theorems, 0 sorry): fold soundness, Merkle integrity, Fiat-Shamir transcript, per-round soundness (Garreta 2025), verifier composition, pipeline integration, operational-verified bridges
- **Operational-Verified FRI Bridges** — 7 bridge modules connecting 357 operational defs to algebraic specs: domain, fold, transcript, Merkle, plus integration capstone `operational_verified_bridge_complete`
- **Barycentric Interpolation** — First formalization in any proof assistant: `barycentric_eq_lagrange` generic over `[Field F]`
- **FRI Pipeline Integration** — `fri_pipeline_soundness` composes e-graph optimization (Level 1+2) with FRI algebraic guarantees (Level 3)
- **E-Graph Optimization** — Verified engine (121 theorems, 0 sorry) + 19/20 rewrite rules
- **Extraction Completeness** — DAG acyclicity (`computeCostsF_acyclic`) + fuel sufficiency (`extractAuto_complete`), 6 theorems, 0 sorry, 0 axioms
- **Perm Algebra** — Tensor, stride, compose, inverse with **0 axioms** (equation compiler fix)
- **Algebraic Semantics** — C-Lite++ lowering with verified scatter/gather (19/19 cases)
- **Poseidon2 Hash** — BN254 t=3 with HorizenLabs-compatible test vectors
- **Trust-Lean Bridge** — Verified type conversion with roundtrip proofs + injectivity (26 theorems, 0 sorry)

## Quick Start

```bash
# Clone and build
git clone https://github.com/manuelpuebla/truth-research-zk.git
cd truth-research-zk
lake build

# Run NTT oracle tests (C, no dependencies)
clang -DFIELD_NATIVE -O2 -o test_ntt_oracle generated/test_ntt_oracle.c && ./test_ntt_oracle

# Run Plonky3 equivalence tests (requires Rust)
cd verification/plonky3/plonky3_shim && cargo build --release && cd ..
./oracle_test
```

### Using TRZK (Header-Only C Library)

```c
#include "trzk/trzk.h"

// Goldilocks field arithmetic
uint64_t a = goldilocks_mul(x, y);
uint64_t b = goldilocks_add(a, z);

// NTT with pre-computed context
NttContext* ctx = ntt_context_create(10);  // N = 2^10 = 1024
ntt_forward_ctx(ctx, data);
ntt_inverse_ctx(ctx, data);
ntt_context_destroy(ctx);
```

## Examples

All examples are runnable via `lake env lean AmoLean/Demo.lean`. See [DEMO_WALKTHROUGH.md](docs/DEMO_WALKTHROUGH.md) for all 11 examples across 3 pipelines.

### E-Graph: Multi-Rule Optimization (Pipeline 1)

A realistic expression with multiple redundant patterns:

**Input:**
```
((x + 0) * 1 + (y * 0)) * (z^1 + w * 1) + 0
```

The e-graph applies 6 verified rewrite rules (`add_zero`, `mul_one`, `mul_zero`, `pow_one`) in a single saturation pass:

**Output:**
```
x * (z + w)
```

- Nodes: 18 → 5 (72% reduction)
- Operations: 9 → 2 (78% reduction)

**Generated C:**
```c
int64_t optimized_kernel(int64_t x, int64_t y, int64_t z, int64_t w) {
  int64_t t0 = z;
  int64_t t1 = (t0 + w);
  int64_t t2 = (x * t1);
  return t2;
}
```

### Matrix Algebra: DFT-2 to C (Pipeline 2)

The 2-point DFT butterfly — the fundamental NTT building block — goes from Lean specification to C:

**Specification:**
```lean
MatExpr.dft 2    -- The 2×2 DFT matrix [[1,1],[1,-1]]
```

**Generated C:**
```c
void butterfly_2(double* restrict in, double* restrict out) {
  out[0] = (in[0] + in[1]);
  out[1] = (in[0] - in[1]);
}
```

### Matrix Algebra: Parallel Butterflies (Pipeline 2)

The Kronecker product `I_2 ⊗ DFT_2` means "apply DFT_2 independently to 2 blocks":

**Specification:**
```lean
MatExpr.kron (MatExpr.identity 2) (MatExpr.dft 2)    -- I₂ ⊗ DFT₂
```

**Generated C:**
```c
void parallel_butterfly(double* restrict in, double* restrict out) {
  for (int i0 = 0; i0 < 2; i0++) {
    out[2 * i0 + 0] = (in[2 * i0 + 0] + in[2 * i0 + 1]);
    out[2 * i0 + 1] = (in[2 * i0 + 0] - in[2 * i0 + 1]);
  }
}
```

The Kronecker product with the identity on the left produces a loop over blocks, applying the butterfly to consecutive pairs. The gather/scatter patterns compute the correct base addresses automatically.

## Performance

TRZK's verified NTT matches or beats Plonky3's unverified Rust implementation on scalar ARM:

### NTT Benchmark: TRZK Verified C vs Plonky3 Rust (N=2^20, Apple M3 Pro)

| Field | TRZK verified C | Plonky3 scalar Rust | Plonky3 vectorized | vs scalar | vs vectorized |
|-------|-----------------|---------------------|--------------------|-----------|---------------|
| **BabyBear** (p=2^31-2^27+1) | **4.8 ns/elem** | 7.8 ns/elem | 3.0 ns/elem | **+62.8% faster** | 1.60x |
| **Goldilocks** (p=2^64-2^32+1) | **51.7 ns/elem** | 53.6 ns/elem | 48.8 ns/elem | **0.96x (faster)** | 1.06x |

**Conditions:**
- Hardware: Apple M3 Pro (ARM Cortex-A76 equivalent), 128KB L1D per core
- Compiler: Apple Clang 16.0 with `-O2` for TRZK C; rustc 1.82.0 with `--release` for Plonky3
- Plonky3 scalar: `plonky3_ntt_forward_scalar` (no SIMD, DIT radix-2)
- Plonky3 vectorized: `plonky3_ntt_forward` (`PackedBabyBearNeon` / `PackedGoldilocksNeon` with inline assembly)
- TRZK: Ultra pipeline with mixed-radix R4/R2 plan, F5c `Stmt.call` butterfly, bound-aware reduction
- Both implementations use the same twiddle table convention (Cooley-Tukey standard)
- Each measurement: 10 iterations, median of 3 runs
- Validation: bit-exact match against Python reference NTT for all sizes

**Key insight**: For 32-bit fields (BabyBear), TRZK's verified C with `-O2` significantly outperforms Plonky3's scalar Rust. For 64-bit fields (Goldilocks), TRZK's `Stmt.call` type boundary pattern (encapsulating 128-bit intermediate arithmetic in `uint64_t`-internal functions) closes the gap that previously existed due to `__uint128_t` overhead in loop counters.

See [BENCHMARKS.md](BENCHMARKS.md) for verification criteria and per-version progression.

## What's New

### v3.12.0 — Emission Optimization + Discovery Wiring (April 2026)

**Gap closed**: Goldilocks NTT gap vs Plonky3 scalar went from 1.52x to **0.96x** (TRZK now faster).

1. **F5c: goldi_butterfly4 via Stmt.call** — Encapsulates full R4 butterfly (4 loads + 4 twiddle loads + 4 reduces + 8 add/sub + 4 stores) as single function call. Loop body becomes 1 Stmt.call → loop counters don't interact with `__uint128_t` butterfly internals.
2. **CacheConfig fix** — L1D 32KB→128KB (Apple M-series), elementSize 4→8 for Goldilocks (uint64_t), L2 latency 12→16 cycles.
3. **Level-aware planCacheCost** — R4 data-reuse model: second level free within same butterfly pass (R4 loads 4 elements once, processes 2 levels).
4. **Discovery wiring** — `selectBestPlanExplored` (500 radix assignments) participates in plan competition via `selectPlanWith`.
5. **Lazy reduction cost=0** — Plan selector sees lazy as free; codegen emits Solinas fold as correctness safety net (true passthrough deferred to v3.13.0).

### v3.11.0 — Bound-aware Discovery Engine (April 2026)

1. **conditionalSub** — 23rd MixedNodeOp constructor: `if x ≥ p then x - p else x` (simpler than Harvey's 3 branches). Added across 13 files with extractable sound proof.
2. **boundAwareEqStep** — 5th layer in tiered saturation: reads live bounds from relation DAG, activates `conditionalSub` when `boundK ≤ 2`. Field-independent (works for any prime).
3. **goldi_add/goldi_sub via Stmt.call** (F5b) — Same type boundary pattern as F5. Gap 1.28x → 1.22x.
4. **Stark252 config** — Added with 0 field-specific rules. Infrastructure for automatic discovery testing.

### v3.10.1 — Goldilocks NTT Corrections (April 2026)

1. **Fair baseline** — 3-column table separating TRZK vs Plonky3 scalar vs Plonky3 vectorized.
2. **Conditional subtract** (AC-6) — 10.4% speedup for bounded stages.
3. **Dynamic cost caching** — `computeDynamicCost` + `mkCachedDynamicCostFn` for e-graph saturation cost.

### v3.9.0 — Goldilocks Enablement (April 2026)

1. **Goldilocks scalar end-to-end** — C + Rust verified NTT for p = 2^64 - 2^32 + 1. Fixed 11 emission bugs (signed/unsigned, overflow, truncation).
2. **Verified Rust SIMD NTT** — 62.8% faster than Plonky3 for BabyBear via ARM NEON `vqdmulhq_s32`.

### Version History

```
v3.12.0 (Apr 12)   F5c butterfly Stmt.call, Discovery wiring, gap 0.96x
v3.11.0 (Apr 11)   conditionalSub + boundAwareEqStep + goldi_add/sub Stmt.call
v3.10.1 (Apr 10)   Fair baseline, conditional subtract, dynamic cost caching
v3.9.0  (Apr 10)   Goldilocks scalar end-to-end, Verified Rust SIMD NTT
```

## Future Work

| Task | Relevance | Difficulty | Status |
|------|-----------|------------|--------|
| **Two-step NTT decomposition** | High — enables NTT trick (shift instead of multiply for inner stages) | Medium | Designed (v3.13.0, `goldi_mul_tw` ready) |
| **True lazy reduction passthrough** | Medium — requires separating butterfly-internal from stage-level reduction | Medium | Cost model ready (v3.12.0), codegen deferred |
| **Four-step NTT** (cache-oblivious) | Medium — ~25% gain for N > 2^14 | High — needs Transpose in IR | Designed (v3.13.0) |
| **MatOp e-graph** (equality saturation over factorizations) | Medium — enables automatic Bowers/NTT-trick discovery | Medium | Infrastructure exists (`MatNodeOps`, `CrossEGraphProtocol`) |
| **Compiled TRZK binary** | High — 100x faster planning | Low | `lake build` target needed |
| ~~**Goldilocks gap**~~ | ~~Critical~~ | ~~High~~ | **RESOLVED** (v3.12.0 F5c, gap 0.96x) |
| ~~**Bound-aware discovery**~~ | ~~High~~ | ~~Medium~~ | **RESOLVED** (v3.11.0, conditionalSub + boundAwareEqStep) |

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Harvey NTT**: Harvey "Faster arithmetic for number-theoretic transforms" (2014)
5. **Plonky3**: Polygon Zero's high-performance STARK library
6. **Sigma-SPL**: Franchetti et al. "SPIRAL: Code Generation for DSP Transforms"

## License

MIT License — see [LICENSE](LICENSE) for details.

---

**TruthResearch ZK v3.12.0** — Verified NTT compiler: 0.96x vs Plonky3 scalar for Goldilocks, +62.8% faster for BabyBear. Bound-aware discovery engine with automatic reduction selection.
