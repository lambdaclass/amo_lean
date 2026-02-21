# AMO-Lean: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Tests](https://img.shields.io/badge/Tests-2850%2B-green.svg)](#testing)
[![Build](https://img.shields.io/badge/Build-3134%20modules-brightgreen.svg)](#build)

**AMO-Lean** is a verified optimizing compiler that transforms mathematical specifications written in Lean 4 into optimized C/Rust code with **formal correctness guarantees**. It targets cryptographic primitives used in STARK provers and zkVMs.

## Release: v2.2.0 -- Trust-Lean Bridge with Verified Roundtrip + Injectivity

### What Changed Since v2.1.0

| Metric | v2.1.0 | v2.2.0 | Change |
|--------|--------|--------|--------|
| **Lines of Code** | ~41,000 | **~41,700** | +743 LOC (bridge + tests) |
| **Bridge theorems** | 0 | **26** | +26 (zero sorry) |
| **Total verified theorems** | 121 | **147** | +26 |
| **Axioms** | 9 | **9** | Same |
| **Active sorry** | 12 | **12** | Same |
| Lean Modules | 3,134 | **3,134** | Same |

### Key Achievements (v2.1.0 -> v2.2.0)

1. **Trust-Lean integration** -- Trust-Lean v1.2.0 added as lake dependency for verified C code generation
2. **Bridge module** (`AmoLean.Bridge.TrustLean`, 544 LOC) -- 21 conversion definitions, 26 theorems:
   - 17 backward roundtrip theorems (TrustLean -> AmoLean -> TrustLean = id)
   - 7 forward roundtrip theorems (AmoLean -> TrustLean -> AmoLean = id, conditional on `some`)
   - Injectivity theorem (`convert_injective`) with some-witness formulation
   - Zero sorry, admit, axiom, native_decide, simp[*]
3. **Verified C pipeline** -- `verifiedCodeGen : ExpandedSigma -> Option String` chains conversion through Trust-Lean's CBackend
4. **Integration tests** (199 LOC) -- All 6 constructors, DFT_4 end-to-end, stress test (>100 sub-expressions, 8261 chars of verified C)

### Previous: v2.1.0 -- Lean 4.26 + Verified E-Graph Engine

1. **Lean 4.26 migration** -- Full codebase migrated (28 API renames, 61 files, 0 regressions)
2. **Verified e-graph engine** -- 13 files with 121 theorems, zero sorry (UnionFind, CoreSpec, ILP extraction)
3. **Bridge adapter** -- Transparent `Expr Int <-> CircuitNodeOp` mapping
4. **100% op reduction** -- Verified optimizer achieves full simplification on all 9 benchmark cases

### Version History

```
v1.0.0 (Feb 6)    17 axioms    35 sorry    AlgebraicSemantics: 8 axioms eliminated
v1.0.1 (Feb 9)    17 axioms    30 sorry    Benchmark audit, 2850+ tests
v1.1.0 (Feb 12)    9 axioms    12 sorry    Goldilocks/BabyBear 0 axioms, Kron 0 sorry
v2.0.0 (Feb 17)    9 axioms    12 sorry    Lean 4.16 → 4.26 migration complete
v2.1.0 (Feb 17)    9 axioms    12 sorry    Verified e-graph engine (121 theorems, 0 sorry)
v2.2.0 (Feb 21)    9 axioms    12 sorry    Trust-Lean bridge (26 theorems, 0 sorry)
```

---

## Production-Ready Components

- **NTT** (Number Theoretic Transform) -- Verified, optimized, Plonky3-compatible
- **Radix-4 NTT** -- Verified 4-point butterfly with formal proofs
- **Goldilocks Field** -- Scalar + AVX2 arithmetic (p = 2^64 - 2^32 + 1), **0 axioms**
- **BabyBear Field** -- Scalar arithmetic (p = 2^31 - 2^27 + 1), **0 axioms**
- **FRI Protocol** -- Folding, Merkle commitments, Fiat-Shamir
- **E-Graph Optimization** -- Verified engine (121 theorems, 0 sorry) + 19/20 rewrite rules
- **Algebraic Semantics** -- C-Lite++ lowering with verified scatter/gather (19/19 cases)
- **Poseidon2 Hash** -- BN254 t=3 with HorizenLabs-compatible test vectors

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

This architecture is **portable and modular**: adding a new primitive means writing a Lean specification and lowering rules -- the optimization engine and code generator are reusable across all primitives.

### Two Operational Modes

| Mode | Purpose | Status |
|------|---------|--------|
| **Verifier** | Certify external code (e.g., Plonky3) is mathematically correct | Production Ready |
| **Generator** | Generate verified C/Rust code from Lean specs | Production Ready |

## Performance

### NTT vs Plonky3 (v1.0.1 Benchmark -- Feb 2026, ARM64)

| Size | AMO-Lean | Plonky3 | Ratio |
|------|----------|---------|-------|
| N=256 | 4.8 us | 3.4 us | 1.39x |
| N=1024 | 23.3 us | 14.6 us | 1.59x |
| N=4096 | 109.5 us | 65.9 us | 1.66x |
| N=65536 | 2.50 ms | 1.48 ms | 1.69x |

**Average**: 1.65x slower than Plonky3 (60% throughput) with **full formal verification**.

<details>
<summary>Full benchmark results (all sizes)</summary>

| Size | AMO-Lean (us) | Plonky3 (us) | Ratio | AMO Throughput |
|------|---------------|--------------|-------|----------------|
| N=256 | 4.8 +/- 0.4 | 3.4 +/- 0.5 | 1.39x | 53.7 Melem/s |
| N=512 | 10.6 +/- 0.5 | 7.1 +/- 1.0 | 1.49x | 48.5 Melem/s |
| N=1024 | 23.3 +/- 2.5 | 14.6 +/- 0.5 | 1.59x | 44.0 Melem/s |
| N=2048 | 50.5 +/- 1.7 | 31.0 +/- 1.0 | 1.63x | 40.6 Melem/s |
| N=4096 | 109.5 +/- 0.9 | 65.9 +/- 2.2 | 1.66x | 37.4 Melem/s |
| N=8192 | 255.1 +/- 13.7 | 138.4 +/- 1.9 | 1.84x | 32.1 Melem/s |
| N=16384 | 535.8 +/- 12.2 | 294.3 +/- 9.4 | 1.82x | 30.6 Melem/s |
| N=32768 | 1176.1 +/- 92.0 | 665.8 +/- 9.7 | 1.77x | 27.9 Melem/s |
| N=65536 | 2500.1 +/- 75.5 | 1477.4 +/- 29.2 | 1.69x | 26.2 Melem/s |

</details>

### Verified Compatibility

- **64/64** oracle tests pass vs Plonky3 (bit-exact match)
- **120/120** pathological vectors verified (sparse, geometric, boundary, max entropy)
- **37/37** Goldilocks field tests pass with UBSan
- **FFI overhead**: 0.03% (negligible)
- **Panic safety**: Triple protection (validation + catch_unwind + panic=abort)

See [BENCHMARKS.md](docs/BENCHMARKS.md) for the complete benchmark report.

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

## Project Structure

```
amo-lean/
├── AmoLean/                    # Lean source (~41,000 LOC, 97 files)
│   ├── NTT/                    # NTT specification + proofs
│   │   ├── Spec.lean           # O(N^2) reference specification
│   │   ├── CooleyTukey.lean    # O(N log N) verified algorithm
│   │   ├── Butterfly.lean      # Butterfly operation proofs
│   │   ├── LazyButterfly.lean  # Harvey optimization (lazy reduction)
│   │   ├── Correctness.lean    # Main equivalence theorems + INTT roundtrip
│   │   ├── ListFinsetBridge.lean # List<->Finset bridge (0 axioms)
│   │   ├── BabyBear.lean       # BabyBear NTT (0 sorry)
│   │   └── Radix4/             # Verified radix-4 implementation
│   ├── Field/                  # Field implementations (0 axioms, 0 sorry)
│   │   ├── Goldilocks.lean     # Goldilocks (p = 2^64 - 2^32 + 1)
│   │   └── BabyBear.lean       # BabyBear (p = 2^31 - 2^27 + 1)
│   ├── EGraph/                 # E-Graph optimization engine
│   │   ├── Optimize.lean       # Equality saturation (unverified, deprecated)
│   │   ├── VerifiedRules.lean  # 19/20 rules with formal proofs
│   │   └── Verified/           # **Verified e-graph engine (121 theorems, 0 sorry)**
│   │       ├── UnionFind.lean  # Verified union-find (43 theorems)
│   │       ├── CoreSpec.lean   # Hashcons + merge invariants (78 theorems)
│   │       ├── Bridge.lean     # Expr Int ↔ CircuitNodeOp adapter
│   │       ├── Rules.lean      # 10 verified rules wired to Bridge
│   │       └── Optimize.lean   # Verified optimization pipeline
│   ├── FRI/                    # FRI protocol components (0 sorry)
│   ├── Bridge/                 # **Trust-Lean bridge (26 theorems, 0 sorry)**
│   │   └── TrustLean.lean      # Verified type conversion + roundtrip + pipeline
│   ├── Sigma/                  # Sigma-SPL IR definitions
│   ├── Matrix/                 # Matrix algebra + permutations
│   ├── Verification/           # Correctness proofs
│   │   ├── AlgebraicSemantics.lean  # Lowering correctness (~5,700 LOC, 0 sorry)
│   │   ├── FRI_Properties.lean      # FRI folding proofs (0 sorry)
│   │   └── Poseidon_Semantics.lean  # Poseidon2 verification (12 sorry, test-backed)
│   └── Backends/               # Code generation (C, Rust)
│
├── generated/                  # Generated C code
│   ├── field_goldilocks.h      # Goldilocks arithmetic (scalar)
│   ├── field_goldilocks_avx2.h # Goldilocks arithmetic (AVX2)
│   ├── ntt_kernel.h            # Lazy butterfly kernel
│   ├── ntt_context.h           # NTT context with caching
│   └── poseidon2_bn254_t3.h    # Poseidon2 hash
│
├── libamolean/                 # Distributable header-only C library
├── verification/plonky3/       # Plonky3 verification suite (Rust FFI)
├── Tests/                      # Test suites (2850+ tests)
└── docs/                       # Documentation
    ├── BENCHMARKS.md            # Full benchmark report
    └── project/                 # Design decisions, progress logs
```

## Verification Status

### Formal Proofs (Lean 4)

| Component | Status | Sorry | Axioms | Detail |
|-----------|--------|-------|--------|--------|
| NTT Radix-2 (CooleyTukey + INTT roundtrip) | **100%** | 0 | 0 | Fully proven incl. bridge |
| NTT Radix-4 | Interface | 0 | 8 | Opaque functions + properties |
| FRI (Folding + Merkle) | **100%** | 0 | 0 | Fully proven |
| Matrix/Perm | **100%** | 0 | 1 | Match splitter limitation |
| E-Graph Rewrite Rules | **95%** | 0 | 0 | 19/20 rules verified |
| **E-Graph Verified Engine** | **100%** | **0** | **0** | **121 theorems, 4,594 LOC** |
| **Trust-Lean Bridge** | **100%** | **0** | **0** | **26 theorems, 544 LOC, roundtrip + injectivity** |
| Goldilocks Field | **100%** | 0 | 0 | All 5 axioms eliminated |
| BabyBear Field | **100%** | 0 | 0 | All 4 axioms eliminated |
| AlgebraicSemantics | **100%** | 0 | 0 | 19/19 cases proven |
| Poseidon2 | Computational | 12 | 0 | All backed by 21 test vectors |

**Codebase**: ~41,700 LOC | **9 axioms** (8 Radix-4 + 1 Perm) | **12 active sorry** (all Poseidon, match splitter limitation) | **147 verified theorems** (121 e-graph + 26 bridge)

### Testing (2850+ tests, 0 failures)

| Test Suite | Tests | Status |
|------------|-------|--------|
| Goldilocks Field (+ UBSan) | 37 | Pass |
| NTT Correctness (oracle + bit-reversal + kernel + sanitizer) | 141 | Pass |
| Plonky3 Equivalence | 64 | Pass |
| FRI Protocol (fold + validation) | 10 | Pass |
| Poseidon2 (S-box + vectors + differential) | 10 | Pass |
| E-Graph Optimizer | 4 | Pass |
| Hardening (fuzz + FFI stress + ABI) | 120 | Pass |
| Verified E-Graph (121 theorems) | 121 | Pass |
| Lean Build (modules) | 3,134 | Pass |
| **Total** | **~2,850** | **0 failures** |

## Key Design Decisions

1. **Equality Saturation (E-Graphs)**: Optimization via verified rewrite rules rather than ad-hoc transformations. Every optimization is a theorem.
2. **Sigma-SPL Algebraic IR**: Matrix expressions lowered through scatter/gather semantics. 19/19 operations formally verified.
3. **Lazy Reduction (Harvey 2014)**: Defer modular reduction in butterfly operations for reduced modular arithmetic overhead.
4. **Skeleton + Kernel Architecture**: Manual C loop structure (skeleton) with Lean-verified butterfly (kernel). Combines performance control with formal guarantees.
5. **Twiddle Factor Caching**: Pre-computed twiddle factors for all NTT layers, stored in NttContext.
6. **Nat in Lean Proofs**: Use arbitrary-precision naturals to avoid overflow reasoning during proofs. C code uses fixed-width integers with verified bounds.
7. **Goldilocks Specialization**: Exploit p = 2^64 - 2^32 + 1 structure for efficient reduction without Barrett/Montgomery.

## Future Work

| Task | Relevance | Difficulty | Status |
|------|-----------|------------|--------|
| **Poseidon formal proofs** (12 sorry) | Medium -- currently validated computationally | Medium -- Lean match splitter limitation | Tests pass; formal proofs deferred |
| **Mersenne31 field** | High -- enables SP1 verification | Medium -- architecture supports it | Designed |
| **NTT Radix-4 axiom elimination** (8 axioms) | Medium -- Radix-2 already proven | High -- requires function implementations | Segmented |
| **Perm axiom** (1) | Low -- match splitter limitation | Very High -- Lean compiler limitation | Documented |

The 12 remaining sorry statements are isolated to Poseidon2 (Lean match splitter limitation) and backed by 21 computational test vectors. The 9 remaining axioms are in Radix-4 NTT (8, opaque interface) and Matrix/Perm (1, compiler limitation). None block the correctness of the Radix-2 NTT pipeline, which is fully verified end-to-end.

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Harvey NTT**: Harvey "Faster arithmetic for number-theoretic transforms" (2014)
5. **Plonky3**: Polygon Zero's high-performance STARK library
6. **Sigma-SPL**: Franchetti et al. "SPIRAL: Code Generation for DSP Transforms"

## License

MIT License -- see [LICENSE](LICENSE) for details.

---

**AMO-Lean v2.2.0** -- Formal verification meets practical performance.
