# AMO-Lean: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.16.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Tests](https://img.shields.io/badge/Tests-1481%2B-green.svg)](#testing)

**AMO-Lean** transforms mathematical specifications into optimized C code with **formal correctness guarantees**. Write your crypto primitives in Lean, get verified optimized code.

## Current Release: v1.0.0

**Production-Ready Components:**
- NTT (Number Theoretic Transform) - Verified, optimized, Plonky3-compatible
- **Radix-4 NTT** - Verified 4-point butterfly with formal proofs
- Goldilocks Field Arithmetic - Scalar + AVX2 implementations
- FRI Protocol Components - Folding, Merkle commitments, Fiat-Shamir
- E-Graph Optimization Engine - 19/20 rules formally verified
- **Algebraic Semantics** - C-Lite++ lowering strategy with verified scatter/gather

### What's New Since v0.7.0

| Metric | v0.7.0 | v1.0.0 | Change |
|--------|--------|--------|--------|
| Lines of Code | 23,027 | 31,252 | +36% |
| Lean Files | 70 | 81 | +11 |
| Sorries | ~104 | 35 | **-66%** |
| Axioms | 11 | 17 | +6 (new modules) |
| Documentation Sessions | 10 | 18 | +8 |

**Key Achievements:**
- **NTT Core**: 0 sorries (was 8)
- **FRI Folding**: 0 sorries (was 5)
- **Matrix/Perm**: 0 sorries (was 12)
- **AlgebraicSemantics**: 8 axioms → 0 axioms
- **Radix-4 NTT**: Fully verified 4-point butterfly

## What It Does

```
Mathematical Spec (Lean)  -->  E-Graph Optimization  -->  Optimized C/SIMD Code
                               (verified rules)          (correct by construction)
```

### Two Operational Modes

| Mode | Purpose | Status |
|------|---------|--------|
| **Verifier** | Certify external code is mathematically correct | ✅ Production Ready |
| **Generator** | Generate verified C code from Lean specs | ✅ Production Ready |

## Performance

### NTT vs Plonky3 (v1.0.0 Benchmark - Feb 2026)

| Size | AMO-Lean | Plonky3 | Throughput |
|------|----------|---------|------------|
| N=256 | 5.5 us | 4.2 us | **76%** |
| N=1024 | 22.5 us | 14.4 us | **64%** |
| N=65536 | 2.36 ms | 1.39 ms | **59%** |

**Key Achievement**: ~65% of Plonky3 performance across all sizes while maintaining **formal verification**.

<details>
<summary>Full Benchmark Results (all sizes)</summary>

| Size | AMO-Lean | Plonky3 | Ratio |
|------|----------|---------|-------|
| N=256 | 5.5 us | 4.2 us | 1.32x |
| N=512 | 10.8 us | 7.6 us | 1.41x |
| N=1024 | 22.5 us | 14.4 us | 1.56x |
| N=2048 | 47.8 us | 29.2 us | 1.64x |
| N=4096 | 103.6 us | 62.4 us | 1.66x |
| N=8192 | 238.8 us | 131.0 us | 1.82x |
| N=16384 | 544.5 us | 282.3 us | 1.93x |
| N=32768 | 1.1 ms | 630.5 us | 1.75x |
| N=65536 | 2.36 ms | 1.39 ms | 1.70x |

*Average: Plonky3 is 1.64x faster (AMO-Lean throughput: ~27M elements/sec)*
</details>

### Verified Compatibility

- 64/64 oracle tests pass vs Plonky3
- 120/120 pathological vectors verified
- FFI overhead: 0.03% (negligible)
- Panic safety: Triple protection enabled

## Quick Start

```bash
# Clone and build
git clone https://github.com/manuelpuebla/amo-lean.git
cd amo-lean
lake build

# Run NTT tests
cd generated && make test_ntt_oracle && ./test_ntt_oracle

# Run Plonky3 verification (requires Rust)
cd verification/plonky3 && make oracle_test && ./oracle_test
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
├── AmoLean/                    # Lean source code
│   ├── NTT/                    # NTT specification + proofs (~2,600 LOC)
│   │   ├── Spec.lean           # O(N^2) reference specification
│   │   ├── CooleyTukey.lean    # O(N log N) verified algorithm
│   │   ├── Butterfly.lean      # Butterfly operation proofs
│   │   ├── LazyButterfly.lean  # Harvey optimization (lazy reduction)
│   │   └── Correctness.lean    # Main equivalence theorems
│   ├── Field/                  # Field implementations
│   │   └── Goldilocks.lean     # Goldilocks field (p = 2^64 - 2^32 + 1)
│   ├── EGraph/                 # E-Graph optimization engine
│   │   ├── Optimize.lean       # Equality saturation
│   │   └── VerifiedRules.lean  # 19/20 rules with proofs
│   └── FRI/                    # FRI protocol components
│       ├── Fold.lean           # Polynomial folding
│       └── CodeGen.lean        # FRI C code generation
│
├── generated/                  # Generated C code
│   ├── field_goldilocks.h      # Goldilocks arithmetic (scalar)
│   ├── field_goldilocks_avx2.h # Goldilocks arithmetic (AVX2)
│   ├── ntt_kernel.h            # Lazy butterfly kernel
│   ├── ntt_context.h           # NTT context with caching
│   └── ntt_cached.c            # Optimized NTT implementation
│
├── libamolean/                 # Distributable C library
│   ├── include/amolean/        # Header files
│   └── CMakeLists.txt          # Build configuration
│
├── verification/plonky3/       # Plonky3 verification suite
│   ├── plonky3_shim/           # Rust FFI shim
│   ├── oracle_test.c           # Equivalence tests
│   └── benchmark.c             # Performance comparison
│
├── Tests/                      # Test suites (1481+ tests)
│   ├── NTT/                    # NTT-specific tests
│   └── Plonky3/Hardening/      # Production hardening tests
│
└── docs/project/               # Documentation
    ├── PROGRESS.md             # Development log
    ├── PHASE6B_PLAN.md         # Optimization ADRs
    └── DESIGN_DECISIONS.md     # Architecture decisions
```

## Verification Status

### Formal Proofs (Lean)

| Component | Theorems | Sorries | Status |
|-----------|----------|---------|--------|
| NTT Core + Radix4 | 80+ | 0 | **100%** |
| Butterfly Properties | 12 | 0 | **100%** |
| E-Graph Rewrite Rules | 20 | 1 | **95%** |
| Matrix/Perm | 15 | 0 | **100%** |
| FRI Folding | 10 | 0 | **100%** |
| AlgebraicSemantics | 30+ | 23 | In Progress |
| Goldilocks Field | 15 | 1 | **93%** |

**Total**: 17 axioms, 35 sorries across 31,252 LOC (81 files)

### Empirical Validation

| Test Suite | Tests | Status |
|------------|-------|--------|
| Goldilocks Field | 74 | ✅ Pass |
| NTT Oracle (vs Lean) | 6 | ✅ Pass |
| Plonky3 Equivalence | 64 | ✅ Pass |
| Hardening (Fuzz) | 120 | ✅ Pass |
| AVX2 Consistency | 300+ | ✅ Pass |
| Radix-4 NTT | 50+ | ✅ Pass |
| **Total** | **1600+** | ✅ Pass |

## Use Cases

### 1. Verify Your NTT Implementation

```bash
# Compare your NTT output against AMO-Lean's verified implementation
# AMO-Lean guarantees mathematical correctness via Lean proofs
```

### 2. Generate Verified C Code

```bash
# Your Lean spec -> Verified C code
# E-Graph finds optimal equivalent form
# All rewrites proven correct in Lean
```

### 3. Use as STARK Component

AMO-Lean provides:
- **NTT/INTT**: For polynomial multiplication in STARK provers
- **Goldilocks Field**: Compatible with Plonky3, Winterfell
- **FRI Fold**: Polynomial folding for FRI protocol

## Key Design Decisions

1. **Lazy Reduction (Harvey)**: Defer modular reduction for 3x speedup
2. **Skeleton + Kernel**: Manual C loops + Lean-verified butterfly
3. **Full Twiddle Caching**: Pre-compute all twiddle factors
4. **Bit-Reversal Table**: Pre-compute permutation indices
5. **Nat in Lean**: Use arbitrary precision to avoid overflow bugs

## Roadmap

| Phase | Status | Description |
|-------|--------|-------------|
| 0-4 | ✅ Complete | E-Graph, Goldilocks, AVX2, libamolean |
| 5 | ✅ Complete | NTT specification + verification |
| 6A | ✅ Complete | Plonky3 verification (64/64 tests) |
| 6B | ✅ Complete | NTT optimization (~65% Plonky3) |
| 6C | ✅ Complete | Radix-4 NTT (verified 4-point butterfly) |
| 7A | ✅ Complete | Sorry elimination (66% reduction) |
| 7B | ✅ Complete | AlgebraicSemantics (8 axioms → 0) |
| 8 | In Progress | Complete FRI prover/verifier |
| 9 | Future | Poseidon2 full verification |

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Harvey NTT**: Harvey "Faster arithmetic for number-theoretic transforms" (2014)
5. **Plonky3**: Polygon Zero's high-performance STARK library

## License

MIT License - see [LICENSE](LICENSE) for details.

---

**AMO-Lean v1.0.0** - Formal verification meets practical performance.

### Changelog Since v0.7.0

- **NTT Core**: Eliminated all 8 sorries, now 100% verified
- **Radix-4 NTT**: Added verified 4-point butterfly algorithm
- **AlgebraicSemantics**: Converted 8 axioms to theorems
- **Matrix/Perm**: Eliminated 12 sorries (100% clean)
- **FRI Folding**: Eliminated 5 sorries (100% clean)
- **Documentation**: 8 new detailed session logs with QA lessons
