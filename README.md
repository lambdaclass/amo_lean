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

TRZK covers the key building blocks of modern proof systems: NTT (Number Theoretic Transform), FRI (Fast Reed-Solomon IOP), field arithmetic (Goldilocks, BabyBear, KoalaBear, Mersenne31), Poseidon2 hashing, and a verified e-graph optimization engine with automatic bound-aware discovery.

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

## Usage

### Quick Start

```bash
# Clone and build
git clone https://github.com/lambdaclass/truth-research-zk.git
cd truth-research-zk
lake build
```

### Generating Optimized NTT Code

TRZK generates verified, optimized **Rust or C** NTT implementations from 4 parameters:

```bash
lake env lean --run Tests/benchmark/emit_code.lean <field> <logN> <lang> <hardware>
```

| Parameter | Options | Description |
|-----------|---------|-------------|
| `field` | `babybear`, `koalabear`, `mersenne31`, `goldilocks` | Prime field |
| `logN` | `10`, `14`, `16`, `20`, `22` | NTT size (N = 2^logN elements) |
| `lang` | `rust`, `c` | Output language (Rust is the primary target since v3.19) |
| `hardware` | `arm-scalar`, `arm-neon`, `x86-avx2` | Hardware target |

#### Choosing the output language

**Rust is the primary recommended output for new integrations** (see `BENCHMARKS.md §1`):
- TRZK Rust beats Plonky3 Rust by **+7-14% Goldilocks** and **+27-35% BabyBear** in fair
  same-compiler `--release` comparison across N ∈ {2^14, 2^18, 2^20}.
- Differential fuzzed against Plonky3 + Python naive (1150/1150 PASS, see `BENCHMARKS.md §0`).
- LTO + `codegen-units=1` cross-module inlining at the `match-plonky3` profile.

Use **C** when integrating with C-native codebases, when downstream code can't link Rust
artefacts, or when the target toolchain doesn't include `rustc`. C output is byte-equivalent
to Rust for the same `(field, logN, hardware)` (regression-guarded — see `BENCHMARKS.md §0`).

**Example: Generate Goldilocks NTT in Rust** (recommended default)

```bash
lake env lean --run Tests/benchmark/emit_code.lean goldilocks 14 rust arm-scalar > goldilocks_ntt.rs
```

The Rust output uses `overflowing_add`/`overflowing_sub` for carry/borrow detection. Compile
with `rustc --release` (or, ideally, the exact `match-plonky3` profile in
`Tests/benchmark/benchmark_plonky3.py:compile_rust`) for the §1 numbers.

**Example: Generate BabyBear NTT in C** (for C-codebase integration)

```bash
lake env lean --run Tests/benchmark/emit_code.lean babybear 14 c arm-scalar > babybear_ntt.c
```

This produces a complete C file with the NTT function and a benchmark harness. The NTT
function itself is self-contained:

```c
static inline uint32_t solinas_fold(int64_t x) { /* verified reduction */ }

void babybear_ntt_ultra(uint32_t* data, const uint32_t* twiddles) {
    /* mixed-radix R4/R2 plan, bound-aware Harvey/Solinas reduction */
    /* generated by e-graph plan competition (10+ candidates evaluated) */
}
```

### Validating Generated Code

TRZK includes a validation harness that compiles the generated code and checks output against a Python reference NTT:

```bash
python3 Tests/benchmark/benchmark.py --validation-only --fields babybear,goldilocks --sizes 14
```

Output:
```
[VAL] babybear/2^14/c/arm-scalar ... PASS (16384 elements)
[VAL] goldilocks/2^14/c/arm-scalar ... PASS (16384 elements)
```

### What Happens Inside

When you run `emit_code.lean`, TRZK executes a multi-phase pipeline:

```
1. Field Configuration        FieldConfig (prime, Solinas constant, Montgomery mu, types)
         |
2. E-Graph Saturation         Bound propagation + reduction alternative rules
         |                    (Harvey, Solinas, Montgomery, conditionalSub — 23 MixedNodeOp constructors)
         |
3. Plan Competition           10-11 candidate plans (R2/R4 × reductions) + Discovery explored plan
         |                    Evaluated by hardware-aware cost model with cache penalty
         |
4. Verified Codegen           Selected plan → TrustLean.Stmt IR → stmtToC/stmtToRust
         |                    F5c Stmt.call type boundary for Goldilocks (uint64_t internals)
         |
5. C / Rust Output            Complete benchmark-ready file with validated NTT function
```

Every optimization in steps 2-4 is either a formally proven rewrite rule or a cost-model-driven selection. The codegen in step 4 uses TrustLean's verified C/Rust backends.

### Supported Fields

| Field | Prime | Element Type | Wide Type | Status |
|-------|-------|-------------|-----------|--------|
| BabyBear | 2^31 - 2^27 + 1 | `uint32_t` | `int64_t` | Production |
| KoalaBear | 2^31 - 2^24 + 1 | `uint32_t` | `int64_t` | Production |
| Mersenne31 | 2^31 - 1 | `uint32_t` | `int64_t` | Production |
| Goldilocks | 2^64 - 2^32 + 1 | `uint64_t` | `__uint128_t` | Production |

### Custom Primitives via MatExpr (Experimental)

TRZK includes an experimental pipeline for custom linear transforms expressed as matrix algebra. The user specifies a transform as a composition of Kronecker products, DFT matrices, and permutations:

```lean
import AmoLean.Sigma.CodeGen

-- Define a custom 4-point transform as DFT-2 butterflies
def myTransform := MatExpr.compose
  (MatExpr.kron (MatExpr.dft 2) (MatExpr.identity 2))   -- stage 2
  (MatExpr.kron (MatExpr.identity 2) (MatExpr.dft 2))   -- stage 1

-- Generate C code
#eval matExprToC myTransform "my_transform"
```

This generates C with verified loop structure from the Kronecker product decomposition. Available constructors: `identity`, `dft`, `ntt`, `twiddle`, `kron`, `compose`, `perm`, `transpose`.

This pipeline does not include the NTT-specific optimizations (plan competition, Stmt.call butterflies, bound-aware reduction). It is suitable for exploring small custom transforms and verifying their structure.

### Verification Status

| Component | Verified | How |
|---|---|---|
| E-graph saturation + extraction | **Yes** | `full_pipeline_soundness`, 0 axioms |
| Rewrite rules | **Yes** | Each rule is a proven theorem |
| Plan → Stmt lowering | **Yes** | `lowerMixedExprFull_evaluates` |
| Stmt → C emission | **Partial** | TrustLean `stmtToC` verified; `Stmt.call` trusted |
| Stmt → Rust emission | **Partial** | TrustLean `stmtToRust` verified (v3.17.0); `Stmt.call` trusted; differential-fuzzed against C output |
| Preamble functions (goldi_*) | **No** | String emission, validated by benchmark + differential fuzzing |
| FRI algebraic proofs | **Yes** | ~230 theorems, 0 sorry |
| Primitive codegen (FRI, Horner, dot) | **Yes** | Path A: `lowerSolinasFold` + `lowerHarveyReduce` |

### In Development

| Feature | Description | Status |
|---------|-------------|--------|
| **Custom fields** | User-defined primes without editing Lean (CLI-driven `FieldConfig`) | Designed |
| **Two-step NTT** | SPIRAL-style decomposition for Goldilocks (v3.13.0 Phase H) | In progress |
| **Poseidon2 codegen** | Verified hash function code generation | Partial |
| **SIMD for 64-bit fields** | ARM NEON for Goldilocks (Karatsuba decomposition infrastructure exists) | Partial |

## What's New

### v3.19.0 — Plonky3 Batch Benchmark + Rust Primary (April 2026)

1. **Plonky3 batch measurement via FFI shim** — new `plonky3_{babybear,goldilocks,koalabear}_ntt_forward_batch(data, n, width)` exposes `Radix2Dit::dft_batch` with tunable width. Activates `PackedMontyField31Neon` (BabyBear NEON, WIDTH=4) which was bypassed by the single-vector shim. See BENCHMARKS.md §8b.
2. **Rust promoted to primary output** — README restructured with Rust-first examples; CI `benchmark-validation` co-gates both `--langs c,rust`. Rationale: TRZK Rust beats Plonky3 Rust by +7-35% in fair same-compiler comparison (BENCHMARKS.md §1).
3. **arm-neon SIMD correctness gap surfaced** — the legacy `emitSIMDNTTC`/`emitSIMDNTTRust` path uses ref_dit (v3.14) convention while the rest of the project uses DFT standard (v3.15+). The migration is deferred to v3.20 together with the batch-emitter rewrite (TRZK_SBB.md §14.12).
4. **Adversarial QA + scope re-framing** — Gemini review during B2/B4 closures exposed methodology gaps (CV violations, ambiguous §13.5 rule, missing baselines). Resolved via `--iters 100` harness tuning, §13.5 formalisation, and Option B++ deferral.

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
v3.19.0 (Apr 19)   Plonky3 batch benchmark (FFI shim dft_batch), Rust primary, arm-neon gap surfaced
v3.18.0 (Apr 17)   Differential fuzzing TRZK vs Plonky3 vs Python naive (1150/1150 PASS)
v3.17.0 (Apr 16)   sbb trick + benchmark fairness (−92 ARM instr, 0.94x Goldilocks, 0.75x BabyBear)
v3.16.0 (Apr 14)   Real Plonky3 FFI oracle (24/24 PASS), fair matrix, C benchmark framework
v3.15.0 (Apr 13)   DFT Standard Migration (bitrev + stages.reverse), Plonky3 algorithmic match
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

**TruthResearch ZK v3.19.0** — Verified NTT compiler in Lean 4 → Rust/C with formal guarantees. Fair Rust-vs-Rust vs Plonky3: TRZK +7-14% Goldilocks, +27-35% BabyBear at N=2^14..2^20. Differential-fuzzed 1150/1150 PASS. Plonky3 batch benchmark via FFI shim informs v3.20 batch-interface scope.
