# Truth Research ZK: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## What is TruthResearch ZK?

**TruthResearch ZK (TRZK)** is a verified optimizing compiler that transforms mathematical specifications written in Lean 4 into optimized C/Rust code with **formal correctness guarantees**. It targets cryptographic primitives used in STARK provers and zkVMs.

The core idea: **write your mathematical specification once in Lean 4, and get optimized C or Rust code that is correct by construction** — every optimization step is backed by a formally proven theorem. This eliminates the traditional tradeoff between performance and correctness in cryptographic implementations.

TRZK covers the key building blocks of modern proof systems: NTT (Number Theoretic Transform), FRI (Fast Reed-Solomon IOP), field arithmetic (Goldilocks, BabyBear, KoalaBear, Mersenne31), Poseidon2 hashing, and a verified e-graph optimization engine with automatic bound-aware discovery.

## How It Works

```
User Input: field + size + hardware target
        |
        v
  Plan Selection (10-14 candidates)
  (radix-2, radix-4, mixed, per-stage reduction strategies)
        |
        v
  E-Graph Optimization
  (equality saturation with verified rewrite rules)
        |
        v
  Verified Code Lowering
  (MixedExpr → TrustLean.Stmt, with soundness proof)
        |
        v
  Optimized C / Rust / SIMD Code
  (correct by construction)
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

The `trzk` compiler generates optimized C or Rust from a primitive specification:

```bash
lake build trzk

# Generate NTT in C for BabyBear, size 1024
.lake/build/bin/trzk ntt babybear 1024 --target c

# Generate NTT in Rust for Goldilocks, size 16384
.lake/build/bin/trzk ntt goldilocks 16384 --target rust

# Generate FRI fold in C for Goldilocks
.lake/build/bin/trzk fri_fold goldilocks --target c

# Generate Horner polynomial evaluation
.lake/build/bin/trzk horner babybear 7 --target c

# Generate dot product
.lake/build/bin/trzk dot_product mersenne31
```

**Supported primitives**: `ntt`, `fri_fold`, `horner`, `dot_product`
**Supported fields**: `babybear`, `goldilocks`, `mersenne31`
**Supported targets**: `c`, `rust`

**Options:**

| Flag | Description | Default |
|------|-------------|---------|
| `--target c\|rust` | Output language | `c` |
| `--output <path>` | Output file path | stdout |
| `--name <func>` | Function name in generated code | `<primitive>_<field>` |

### Legacy Mode: Matrix Spec Compilation

You can also write a custom algorithm as a matrix expression and compile it:

```bash
.lake/build/bin/trzk my_transform.lean --target c --name my_transform
```

See the `examples/` directory and [DEMO_WALKTHROUGH.md](docs/DEMO_WALKTHROUGH.md) for examples.

### Integration Tests

```bash
lake env lean --run Tests/benchmark/emit_code.lean babybear 14 c arm-scalar > babybear_ntt.c
```

This compiles a DFT₄ spec to C, builds it, and verifies the output against reference test vectors.

## What's New

The project has evolved significantly from its initial verification-focused releases (v1.x–v2.x) into a full optimizing compiler (v3.x). Key changes in the current version on main:

- **Verified SIMD codegen** — NEON and AVX2 butterfly emission through `Stmt.call` with structural correctness proofs. The SIMD path is integrated into the main pipeline and dispatched automatically when the target supports it.
- **Goldilocks field support** — Full NTT pipeline for the 64-bit Goldilocks field (p = 2⁶⁴ − 2³² + 1), including 128-bit product reduction and field-specific cost calibration.
- **REDC scheduling** — Montgomery reduction with `sqdmulh`-based scheduling and ILP interleaving to hide multiplication latency on ARM.
- **Per-stage reduction selection** — The e-graph now selects the cheapest reduction strategy (Solinas, Montgomery, Harvey, conditional subtract) independently for each NTT stage, based on value bounds and hardware costs.
- **`trzk` compiler driver** — CLI entry point that routes primitives to the verified pipeline (NTT via UltraPipeline, FRI fold / Horner / dot product via PrimitiveOptimizer).

## Future Work

- **Close the Goldilocks performance gap** — Improve field arithmetic reduction to match state-of-the-art branchless techniques
- **Cache-friendly NTT for large sizes** — Four-step NTT factorization for sizes where data no longer fits in L1
- **SIMD path modernization** — Migrate the SIMD emitter to the standard DFT codegen path
- **New primitives** — Extend the compiler to optimize polynomial evaluation, FRI fold, and matrix multiplication as first-class primitives
- **Incorporate lambdaworks optimizations** — Layer fusion, Bowers G network, per-stage twiddle models, and compiler flag tuning
- **Broader hardware targets** — AVX-512, GPU codegen paths

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Harvey NTT**: Harvey "Faster arithmetic for number-theoretic transforms" (2014)
5. **Plonky3**: Polygon Zero's high-performance STARK library
6. **SPIRAL**: Franchetti et al. "SPIRAL: Code Generation for DSP Transforms"

## License

MIT License — see [LICENSE](LICENSE) for details.
