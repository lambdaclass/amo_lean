# AMO-Lean: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.16.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

**AMO-Lean** transforms mathematical specifications into optimized C code with **formal correctness guarantees**. Write your crypto primitives in Lean, get verified optimized code.

## Core Idea

```
Mathematical Spec (Lean)  →  E-Graph Optimization  →  Optimized C/SIMD Code
                              (verified rules)        (correct by construction)
```

## What It Does

- **Input**: Mathematical specification as `MatExpr` (matrix/vector expressions)
- **Process**: E-Graph equality saturation with proven-correct rewrite rules
- **Output**: Optimized C code that is **guaranteed equivalent** to the spec

## Current Status

| Component | Status | Purpose |
|-----------|--------|---------|
| E-Graph Engine | ✅ Complete | Core optimizer |
| Verified Rewrite Rules | ✅ 12 rules | Correctness guarantees |
| MatExpr + elemwise | ✅ Complete | Non-linear operations (x^5) |
| C/AVX2 CodeGen | ✅ Complete | Code generation |
| FRI Reference Impl | ✅ Complete | Testing oracle |
| Poseidon2 Reference | ✅ Complete | Testing oracle |

**Next Step**: Connect FRI and Poseidon2 specs to the optimization pipeline (see [OPTION_A_ROADMAP.md](docs/OPTION_A_ROADMAP.md))

## Quick Start

```bash
# Clone and build
git clone https://github.com/manuelpuebla/amo-lean.git
cd amo-lean
lake build

# See optimization in action (in Lean editor)
# Open AmoLean.lean - shows E-Graph optimizing expressions

# Run reference implementation tests
# Open Tests/E2EProverVerifier.lean
```

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        OPTIMIZATION PIPELINE                             │
│                                                                          │
│   MatExpr           E-Graph              CodeGen           Output        │
│   (Spec)      →     Saturation     →     C/AVX2      →     .c file      │
│                     (verified                                            │
│                      rules)                                              │
└─────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────┐
│                     REFERENCE IMPLEMENTATIONS                            │
│                     (For testing generated code)                         │
│                                                                          │
│   Poseidon2 Spec (Lean)    FRI Prover/Verifier (Lean)                   │
│   → Test oracle            → Validate proofs from generated C            │
└─────────────────────────────────────────────────────────────────────────┘
```

## Project Structure

```
amo-lean/
├── AmoLean/
│   │
│   │  ═══════════════ OPTIMIZATION PIPELINE ═══════════════
│   ├── Basic.lean              # Expr AST, rewrite rules (verified)
│   ├── Correctness.lean        # Soundness proofs (0 sorry)
│   ├── EGraph/                 # E-Graph + equality saturation
│   ├── Matrix/                 # MatExpr (Kronecker, elemwise)
│   ├── Vector/                 # VecExpr (length-indexed)
│   ├── Sigma/                  # Sigma-SPL intermediate representation
│   ├── CodeGen.lean            # C/AVX2 code generation
│   │
│   │  ═══════════════ REFERENCE IMPLEMENTATIONS ═══════════════
│   ├── Protocols/Poseidon/     # Poseidon2 reference (for testing)
│   │   ├── Spec.lean           # Pure Lean specification
│   │   └── Integration.lean    # FRI adapters
│   └── FRI/                    # FRI reference (for testing)
│       ├── Prover.lean         # Reference prover
│       ├── Verifier.lean       # Reference verifier
│       └── Fields/             # Field implementations
│
├── Tests/                      # Test suites
└── docs/
    ├── STATUS.md               # Current state
    ├── OPTION_A_ROADMAP.md     # Roadmap for formal optimization
    └── poseidon/               # Poseidon2 documentation
```

## Example: E-Graph Optimization

```lean
-- Input expression (unoptimized)
let expr := Expr.mul (Expr.add (Expr.var 0) (Expr.const 0)) (Expr.const 1)
-- Represents: (x + 0) * 1

-- E-Graph finds equivalent forms and extracts cheapest
let optimized := saturateAndExtract expr rules
-- Result: Expr.var 0
-- Represents: x

-- Generate C code
let cCode := exprToC optimized
-- Output: "return x;"
```

## Documentation

- [STATUS.md](docs/STATUS.md) - Current project state
- [OPTION_A_ROADMAP.md](docs/OPTION_A_ROADMAP.md) - **Roadmap for formal optimization**
- [poseidon/PROGRESS.md](docs/poseidon/PROGRESS.md) - Implementation history

## Key Design Decisions

1. **Verified rewrite rules**: Every optimization rule is a theorem proven in Lean
2. **E-Graph for exploration**: Finds all equivalent forms, picks cheapest
3. **MatExpr for crypto**: Supports matrices, vectors, elemwise ops (for Poseidon2)
4. **Reference implementations**: FRI and Poseidon2 in pure Lean for testing

## Current Verification Status

| Component | Verified? | Method |
|-----------|-----------|--------|
| Rewrite rules | ✅ Proven | Lean theorems (0 sorry) |
| E-Graph saturation | ✅ Tested | Extensive testing |
| CodeGen correctness | ⚠️ Empirical | Differential fuzzing |
| FRI soundness | ⚠️ Empirical | E2E tests + soundness tests |

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Poseidon2**: Grassi et al. "Poseidon2: A New Hash Function" (2023)

## License

MIT License - see [LICENSE](LICENSE) for details.
