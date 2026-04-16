# Truth Research ZK: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## What is TRZK?

**TRZK** (Truth Research ZK) is a verified optimizing compiler that transforms mathematical specifications written in Lean 4 into optimized C and Rust code with formal correctness guarantees. It targets cryptographic primitives used in STARK provers and zkVMs.

The core idea: **write your mathematical specification once in Lean 4, and get optimized C or Rust code that is correct by construction** — every optimization step is backed by a formally proven theorem. This eliminates the traditional tradeoff between performance and correctness in cryptographic implementations.

TRZK currently optimizes NTT (Number Theoretic Transform) implementations across multiple finite fields (BabyBear, KoalaBear, Mersenne31, Goldilocks) with support for scalar and SIMD (NEON, AVX2) targets. Work has begun on extending the compiler to additional cryptographic primitives: polynomial evaluation, FRI fold, and matrix multiplication.

## Ecosystem & Comparisons

TRZK occupies a unique position: it combines **equality saturation optimization** with **formal verification** in a single tool. Most existing projects do one or the other.

| Project | Approach | Proof Assistant | Verification Scope | Codegen Target |
|---------|----------|-----------------|---------------------|----------------|
| **TRZK** | Two-level e-graph optimization + verified codegen | Lean 4 | Full pipeline (spec → IR → code) | C, Rust |
| [fiat-crypto](https://github.com/mit-plv/fiat-crypto) | Synthesis from field specs | Coq | Field arithmetic | C, Rust, Go, Java |
| [Jasmin](https://github.com/jasmin-lang/jasmin) | Verified assembly compiler | Coq (EasyCrypt) | Compiler correctness | x86 assembly |
| [CryptoLine](https://github.com/fmlab-iis/cryptoline) | Algebraic program verification | External (SMT) | Post-hoc verification | N/A (verifier only) |
| [hacspec](https://github.com/hacspec/hacspec-v2) | Executable specification language | F\*/Coq | Spec extraction | Rust |
| [SPIRAL](https://www.spiral.net/) | Autotuning + formal rewrite rules | Custom (GAP) | Transform correctness | C, CUDA, FPGA |

**What makes TRZK different:**
- **Two-level e-graph architecture**: an algorithm-level e-graph explores DFT factorizations (radix-2, radix-4, mixed) while a bit-level e-graph optimizes the arithmetic of each butterfly — they communicate via a cross-e-graph cost protocol to find the globally optimal implementation
- **Automatic search**: given a field and a target hardware, TRZK generates multiple plan candidates and selects the best one using a hardware-aware cost model — new optimizations become candidates automatically
- **Verified codegen**: optimized expressions are lowered through a formally verified path (MixedExpr → TrustLean Stmt → C/Rust), not through string emission
- **Single tool**: optimization, verification, and code generation in one pipeline

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

The compiler automatically decides per-stage reduction strategies (Solinas fold, Montgomery REDC, Harvey, conditional subtract), radix selection, and instruction interleaving based on the cost model for the target hardware.

## Features

- **Verified e-graph optimization engine** — Equality saturation with formally proven rewrite rules; extraction preserves semantics
- **Two-level e-graph architecture** — Algorithm-level (DFT factorizations) and bit-level (arithmetic expressions) e-graphs with cross-level cost queries
- **Hardware-aware cost model** — Per-operation cycle costs for ARM Cortex-A76, x86 Skylake, RISC-V, NEON SIMD, AVX2 SIMD, with register pressure modeling
- **NTT optimization** — Radix-2, radix-4, and mixed strategies with per-stage reduction selection via e-graph
- **Multiple finite fields** — BabyBear, KoalaBear, Mersenne31, Goldilocks with field-specific reduction strategies
- **Verified codegen pipeline** — MixedExpr → TrustLean.Stmt → C/Rust with formal soundness proofs
- **SIMD code generation** — NEON (4-lane) and AVX2 (8-lane) verified butterfly emission via `Stmt.call`
- **FRI protocol infrastructure** — Specification, verification, and codegen foundations for FRI fold
- **Poseidon2 hash** — BN254 specification with test vectors
- **Plonky3 compatibility** — Generated code produces output compatible with Plonky3's NTT

## Quick Start

```bash
# Clone and build
git clone https://github.com/lambdaclass/truth_research_zk.git
cd truth_research_zk
lake build
```

### Compiler Driver

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
./integration_tests/run.sh
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
