# AMO-Lean: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Tests](https://img.shields.io/badge/Tests-2850%2B-green.svg)](#testing)
[![Build](https://img.shields.io/badge/Build-3134%20modules-brightgreen.svg)](#build)

## What is AMO-Lean?

**AMO-Lean** is a verified optimizing compiler that transforms mathematical specifications written in Lean 4 into optimized C/Rust code with **formal correctness guarantees**. It targets cryptographic primitives used in STARK provers and zkVMs.

The core value proposition: **write your mathematical specification once in Lean 4, and get optimized C or Rust code that is correct by construction** — every optimization step is a formally proven theorem. This eliminates the traditional tradeoff between performance and correctness in cryptographic implementations.

AMO-Lean currently covers the key building blocks of modern proof systems: NTT (Number Theoretic Transform), FRI (Fast Reed-Solomon IOP), field arithmetic (Goldilocks, BabyBear), Poseidon2 hashing, and a verified e-graph optimization engine. The generated code is Plonky3-compatible and achieves ~60% of hand-optimized Rust throughput with full formal verification.

## Ecosystem & Comparisons

AMO-Lean occupies a unique position: it combines **equality saturation optimization** with **formal verification** in a single tool. Most existing projects do one or the other.

| Project | Approach | Proof Assistant | Verification Scope | Codegen Target |
|---------|----------|-----------------|---------------------|----------------|
| **AMO-Lean** | E-graph optimization + Sigma-SPL IR | Lean 4 | Full pipeline (spec → IR → code) | C, Rust |
| [fiat-crypto](https://github.com/mit-plv/fiat-crypto) | Synthesis from field specs | Coq | Field arithmetic | C, Rust, Go, Java |
| [Jasmin](https://github.com/jasmin-lang/jasmin) | Verified assembly compiler | Coq (EasyCrypt) | Compiler correctness | x86 assembly |
| [CryptoLine](https://github.com/fmlab-iis/cryptoline) | Algebraic program verification | External (SMT) | Post-hoc verification | N/A (verifier only) |
| [hacspec](https://github.com/hacspec/hacspec-v2) | Executable specification language | F\*/Coq | Spec extraction | Rust |
| [SPIRAL](https://www.spiral.net/) | Autotuning + formal rewrite rules | Custom (GAP) | Transform correctness | C, CUDA, FPGA |

**What makes AMO-Lean different:**
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

AMO-Lean uses **equality saturation** via e-graphs to find optimal formal equivalent forms of mathematical expressions. Unlike hand-tuned optimizers, every rewrite rule in our e-graph is a formally proven theorem in Lean 4. The process:

1. **Encode** the mathematical specification as an e-graph
2. **Saturate** by applying all verified rewrite rules until a fixed point
3. **Extract** the optimal form using a cost model
4. **Lower** through AlgebraicSemantics (Sigma-SPL IR) to C/Rust code

This architecture is **portable and modular**: adding a new primitive means writing a Lean specification and lowering rules — the optimization engine and code generator are reusable across all primitives.

### Two Operational Modes

| Mode | Purpose | Status |
|------|---------|--------|
| **Verifier** | Certify external code (e.g., Plonky3) is mathematically correct | Production Ready |
| **Generator** | Generate verified C/Rust code from Lean specs | Production Ready |

## Features

- **Verified Pipeline Soundness** — End-to-end `full_pipeline_soundness` theorem: saturation + extraction preserves semantics, **0 custom axioms**
- **Translation Validation** — Level 2 soundness via `cryptoEquivalent` relation with congruence closure
- **NTT** (Number Theoretic Transform) — Verified, optimized, Plonky3-compatible
- **Radix-4 NTT** — 4-point butterfly (8 axioms pending formal implementation)
- **Goldilocks Field** — Scalar + AVX2 arithmetic (p = 2^64 - 2^32 + 1), **0 axioms**
- **BabyBear Field** — Scalar arithmetic (p = 2^31 - 2^27 + 1), **0 axioms**
- **FRI Protocol** — Folding, Merkle commitments, Fiat-Shamir
- **E-Graph Optimization** — Verified engine (121 theorems, 0 sorry) + 19/20 rewrite rules
- **Perm Algebra** — Tensor, stride, compose, inverse with **0 axioms** (equation compiler fix)
- **Algebraic Semantics** — C-Lite++ lowering with verified scatter/gather (19/19 cases)
- **Poseidon2 Hash** — BN254 t=3 with HorizenLabs-compatible test vectors
- **Trust-Lean Bridge** — Verified type conversion with roundtrip proofs + injectivity (26 theorems, 0 sorry)

## Quick Start

```bash
# Clone and build
git clone https://github.com/manuelpuebla/amo-lean.git
cd amo-lean
lake build

# Run NTT oracle tests (C, no dependencies)
clang -DFIELD_NATIVE -O2 -o test_ntt_oracle generated/test_ntt_oracle.c && ./test_ntt_oracle

# Run Plonky3 equivalence tests (requires Rust)
cd verification/plonky3/plonky3_shim && cargo build --release && cd ..
./oracle_test
```

### Using libamolean (Header-Only C Library)

```c
#include "amolean/amolean.h"

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

AMO-Lean NTT achieves **~60% of Plonky3 throughput** (1.65x slower on average) with full formal verification — 64/64 oracle tests pass with bit-exact match.

See [BENCHMARKS.md](docs/BENCHMARKS.md) for full NTT benchmark tables, test suite results, and verification criteria.

## What's New in v2.3.0

### Changes Since v2.2.0

| Metric | v2.2.0 | v2.3.0 | Change |
|--------|--------|--------|--------|
| **Lines of Code** | ~41,700 | **~43,100** | +1,400 LOC (pipeline + TV + tests) |
| **Pipeline theorems** | 0 | **77** | +77 (verified pipeline, 0 sorry) |
| **Total verified theorems** | 147 | **778** | +631 |
| **Axioms** | 9 | **8** | -1 (Perm axiom eliminated) |
| **Active sorry** | 12 | **12** | Same (Poseidon only) |
| Lean Modules | 3,134 | **3,134** | Same |

### Key Achievements (v2.2.0 -> v2.3.0)

1. **Verified pipeline soundness** (Fase 11, Subfase 1) — `full_pipeline_soundness` and `full_pipeline_contract` proven end-to-end: saturation preserves `ConsistentValuation`, extraction is correct, 0 sorry, 0 custom axioms. 5 new files, 1,991 LOC, 77 declarations.
2. **Translation validation framework** (N11.11) — Level 2 soundness via `cryptoEquivalent` relation (refl/symm/trans + congruence for add/mul/neg/smul). 229 LOC, 11 theorems, 0 axioms.
3. **Perm axiom eliminated** (Corrección 1) — `applyIndex_tensor_eq` is now a theorem, not an axiom. Root cause: nested `inverse` sub-patterns blocked equation compiler splitter. Fix: `applyInverse` helper extraction (~20 LOC change).
4. **Zero-axiom audit** (N11.12) — All 9 key pipeline theorems audited via `#print axioms` = 0 custom axioms. Integration test: 13 examples, 25 `#check`, 190 LOC.

### Previous: v2.2.0 — Trust-Lean Bridge

1. **Trust-Lean integration** — Trust-Lean v1.2.0 added as lake dependency for verified C code generation
2. **Bridge module** (`AmoLean.Bridge.TrustLean`, 544 LOC) — 21 conversion definitions, 26 theorems (roundtrip + injectivity, zero sorry)
3. **Verified C pipeline** — `verifiedCodeGen : ExpandedSigma -> Option String` chains conversion through Trust-Lean's CBackend
4. **Integration tests** (199 LOC) — All 6 constructors, DFT_4 end-to-end, stress test (>100 sub-expressions, 8261 chars of verified C)

### Previous: v2.1.0 — Lean 4.26 + Verified E-Graph Engine

1. **Lean 4.26 migration** — Full codebase migrated (28 API renames, 61 files, 0 regressions)
2. **Verified e-graph engine** — 13 files with 121 theorems, zero sorry (UnionFind, CoreSpec, ILP extraction)
3. **Bridge adapter** — Transparent `Expr Int <-> CircuitNodeOp` mapping
4. **100% op reduction** — Verified optimizer achieves full simplification on all 9 benchmark cases

### Version History

```
v1.0.0 (Feb 6)    17 axioms    35 sorry    AlgebraicSemantics: 8 axioms eliminated
v1.0.1 (Feb 9)    17 axioms    30 sorry    Benchmark audit, 2850+ tests
v1.1.0 (Feb 12)    9 axioms    12 sorry    Goldilocks/BabyBear 0 axioms, Kron 0 sorry
v2.0.0 (Feb 17)    9 axioms    12 sorry    Lean 4.16 → 4.26 migration complete
v2.1.0 (Feb 17)    9 axioms    12 sorry    Verified e-graph engine (121 theorems, 0 sorry)
v2.2.0 (Feb 21)    9 axioms    12 sorry    Trust-Lean bridge (26 theorems, 0 sorry)
v2.3.0 (Feb 27)    8 axioms    12 sorry    Pipeline soundness + Perm axiom eliminated
```

## Future Work

| Task | Relevance | Difficulty | Status |
|------|-----------|------------|--------|
| **NTT Radix-4 axiom elimination** (8 axioms) | High — last remaining axioms | High — requires function implementations | Pending (N11.6-N11.9) |
| **Poseidon formal proofs** (12 sorry) | Medium — currently validated computationally | Medium — Lean match splitter limitation | Tests pass; formal proofs deferred |
| **Mersenne31 field** | High — enables SP1 verification | Medium — architecture supports it | Designed |
| **SlimCheck property testing** | Medium — 0 property tests in 43K LOC | Low — infrastructure exists in Mathlib | Not started |
| ~~**Perm axiom** (1)~~ | ~~Low~~ | ~~Very High~~ | **RESOLVED** (Corrección 1) |

The 12 remaining sorry are isolated to Poseidon2 (Lean match splitter limitation), backed by 21 test vectors. The 8 remaining axioms are all in Radix-4 NTT (opaque interface, pending B35-B37). The entire e-graph pipeline, Perm algebra, and translation validation are **fully axiom-free**.

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

**AMO-Lean v2.3.0** — Verified pipeline soundness, zero custom axioms in the optimization engine.
