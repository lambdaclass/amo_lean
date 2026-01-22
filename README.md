# AMO-Lean: Automatic Mathematical Optimizer

[![Lean 4](https://img.shields.io/badge/Lean-4.3.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

**AMO-Lean** is a verified automatic mathematical optimizer written in Lean 4. It transforms algebraic expressions into optimized forms using rewrite rules derived from mathematical theorems, with formal proofs of correctness.

## 🎯 Vision

The goal is to create a verified compiler that can:
1. Take high-level mathematical code (via Hacspec/Rust subset)
2. Apply algebraic optimizations using theorems from Mathlib
3. Generate optimized low-level code (C/Rust) with formal correctness guarantees

This approach is inspired by [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto), which generates verified cryptographic code used in major web browsers.

## 🏗️ Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    SEMANTIC LEVEL (Lean)                        │
│  • Lean.Expr for canonical representation                       │
│  • MetaM for type checking and instance synthesis               │
│  • Mathlib as the source of truth for rewrite rules             │
└─────────────────────────────────────────────────────────────────┘
                              ↕
                    [Projection / Lifting]
                              ↕
┌─────────────────────────────────────────────────────────────────┐
│                   SYNTACTIC LEVEL (OptExpr)                     │
│  • Simplified AST for efficient manipulation                    │
│  • Bottom-up rewriting / E-graph (future)                       │
│  • E-class analyses for semantic tracking                       │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│                   CODE GENERATION                               │
│  • Lowering to three-address code                               │
│  • Pretty printing to C/Rust                                    │
└─────────────────────────────────────────────────────────────────┘
```

## 📁 Project Structure

```
amo-lean/
├── lakefile.lean              # Lake build configuration
├── lean-toolchain             # Lean version specification
├── AmoLean.lean               # Main module
├── ROADMAP.md                 # Detailed development roadmap
└── AmoLean/
    ├── Basic.lean             # Core Expr type and rewrite rules
    ├── Correctness.lean       # Semantic preservation proofs
    ├── MathlibIntegration.lean # Mathlib connection (Phase 2)
    └── CodeGen.lean           # C code generation
```

## 🚀 Quick Start

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.3.0 or later)
- [Lake](https://github.com/leanprover/lake) (comes with Lean 4)

### Building

```bash
git clone https://github.com/YOUR_USERNAME/amo-lean.git
cd amo-lean
lake build
```

### Example Usage

```lean
import AmoLean

open AmoLean.Expr

-- Define variables
def x : Expr Int := var 0
def y : Expr Int := var 1

-- Create an expression: x * 1 + y * 0
def myExpr : Expr Int := add (mul x (const 1)) (mul y (const 0))

-- Simplify it (should become just x)
#eval simplify myExpr

-- Generate C code
#eval exprToC "optimized_func" ["x", "y"] myExpr
```

## 📋 Current Features (Phase 1)

- ✅ Inductive `Expr` type for arithmetic expressions
- ✅ Rewrite rules for algebraic identities:
  - `x + 0 → x`, `0 + x → x`
  - `x * 1 → x`, `1 * x → x`
  - `x * 0 → 0`, `0 * x → 0`
  - `a * (b + c) → a*b + a*c` (distributivity)
- ✅ Bottom-up rewriting engine
- ✅ Fixed-point iteration
- ✅ Basic C code generation
- 🔄 Correctness proofs (in progress)

## 🗺️ Roadmap

### Phase 1: Toy Model ✅
Basic expression optimization with algebraic rules.

### Phase 2: Mathlib Integration
- Connect `Expr` to Mathlib's algebraic structures
- Automatically compile Mathlib theorems to rewrite rules
- Support for `Ring`, `Field`, `CommRing`, etc.

### Phase 3: E-graph and Equality Saturation
- Implement E-graph data structure in pure Lean
- E-class analysis for type tracking
- Optimal extraction

### Phase 4: Cryptographic Applications
- Finite field arithmetic (`ZMod p`, `GF(2^n)`)
- FFT optimization
- FRI/STARKs components

## 📚 References

This project builds on ideas from:

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **Verified Rewriter**: Gross et al. "Accelerating Verified-Compiler Development with a Verified Rewriting Engine" (ITP 2022)
4. **E-graphs as Circuits**: Sun et al. "E-Graphs as Circuits, and Optimal Extraction via Treewidth" (2024)

## 🤝 Contributing

Contributions are welcome! Please feel free to submit issues and pull requests.

Areas where help is needed:
- Completing correctness proofs
- Mathlib integration
- E-graph implementation
- Documentation and examples

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- The Lean 4 community and Mathlib contributors
- The egg project for pioneering equality saturation
- The Fiat-Crypto team for demonstrating verified cryptographic code generation
