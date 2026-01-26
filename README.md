# AMO-Lean: Verified Cryptographic Code Compiler

[![Lean 4](https://img.shields.io/badge/Lean-4.16.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Release](https://img.shields.io/badge/Release-v1.0.0--fri--verified-green.svg)](https://github.com/manuelpuebla/amo-lean/releases/tag/v1.0.0-fri-verified)

**AMO-Lean** is a verified compiler that transforms algebraic expressions into optimized C code with formal correctness guarantees. The current release implements the FRI (Fast Reed-Solomon IOP) commit phase with SIMD optimization.

## Current Release: v1.0.0-fri-verified

The first stable release includes:
- **MatExpr IR**: Symbolic algebra with Kronecker product optimization
- **E-Graph Engine**: Equality saturation for automatic optimization
- **C Code Generation**: SIMD-optimized output (AVX2)
- **FRI Protocol**: Complete commit phase implementation
- **Differential Fuzzing**: Testing framework that validates Lean reference against generated C

### Key Achievement
A critical buffer swap bug was discovered and fixed through differential fuzzing, demonstrating the value of our "Transitive Empirical Verification" methodology.

## Project Structure

```
amo-lean/
├── AmoLean/
│   ├── Core.lean           # Re-exports core modules
│   ├── Backends.lean       # Re-exports code generators
│   ├── Protocols.lean      # Re-exports protocol implementations
│   │
│   ├── EGraph/             # [CORE] Equality saturation engine
│   ├── Sigma/              # [CORE] MatExpr symbolic algebra
│   ├── Matrix/             # [CORE] Linear algebra primitives
│   ├── Vector/             # [CORE] Vector operations
│   ├── Meta/               # [CORE] Compile-time utilities
│   │
│   ├── CodeGen.lean        # [BACKEND] C code generation (AVX2)
│   ├── Backends/
│   │   ├── C_AVX512/       # [FUTURE] AVX-512 backend
│   │   └── CUDA/           # [FUTURE] GPU backend
│   │
│   ├── FRI/                # [PROTOCOL] FRI commit phase (stable)
│   ├── Protocols/
│   │   └── Poseidon/       # [FUTURE] ZK-friendly hash
│   │
│   └── Verification/       # Formal proofs and testing
│
├── Benchmarks/             # Differential fuzzing tests
├── generated/              # Generated C code
└── docs/                   # Documentation and reports
```

### Module Organization

| Module | Status | Description |
|--------|--------|-------------|
| `AmoLean.Core` | Stable | E-Graph, MatExpr, linear algebra primitives |
| `AmoLean.Backends` | Stable | C/AVX2 code generation |
| `AmoLean.Protocols` | Stable | FRI commit phase |
| `AmoLean.Verification` | Stable | Formal proofs, fuzzing framework |

## Quick Start

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.16.0)
- [Lake](https://github.com/leanprover/lake)
- GCC with AVX2 support (for generated code)

### Building

```bash
git clone https://github.com/manuelpuebla/amo-lean.git
cd amo-lean
lake build
```

### Running Differential Fuzzing

```bash
# Build and run the FRI differential test
lake build Benchmarks
cd generated
gcc -O3 -march=native -o fri_test fri_test.c fri_protocol.c
./fri_test
```

## Future Work (zkVM Roadmap)

See [ZKVM_ROADMAP.md](docs/ZKVM_ROADMAP.md) for detailed planning.

| Priority | Component | Time | Description |
|----------|-----------|------|-------------|
| #1 Critical | Poseidon Hash | 6-10 weeks | Enables efficient proof recursion |
| #2 High | CUDA Backend | 3-6 months | 10-100x speedup via GPU |
| #3 Medium | AVX-512 | 2-3 weeks | 2x incremental CPU speedup |
| #4 Low | FRI Query Phase | 4-6 weeks | Completes the FRI protocol |

## Documentation

- [FINAL_REPORT.md](docs/FINAL_REPORT.md) - Complete technical report
- [ZKVM_ROADMAP.md](docs/ZKVM_ROADMAP.md) - Future work planning
- [PROJECT_STATUS.md](docs/PROJECT_STATUS.md) - Development history

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Poseidon**: Grassi et al. "Poseidon: A New Hash Function for Zero-Knowledge Proof Systems"

## Contributing

Contributions are welcome, especially in these areas:
- Poseidon hash implementation (Priority #1)
- CUDA backend development (Priority #2)
- Additional protocol implementations

## License

MIT License - see [LICENSE](LICENSE) for details.

## Acknowledgments

- The Lean 4 community and Mathlib contributors
- The egg project for equality saturation foundations
- The Fiat-Crypto team for verified cryptographic code generation methodology
