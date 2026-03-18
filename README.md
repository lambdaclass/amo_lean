# AMO-Lean: Verified E-Graph Optimizer for Finite Field Arithmetic

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build](https://img.shields.io/badge/Build-3140%20modules-brightgreen.svg)](#build)

## What AMO-Lean Does Today

AMO-Lean uses **equality saturation** (e-graphs) to automatically discover and optimize **modular reduction formulas** for finite fields used in ZK proving systems (Plonky3, SP1, RISC Zero).

Given a prime `p`, AMO-Lean:
1. **Discovers** the optimal reduction formula (Solinas fold) starting from a bare variable
2. **Optimizes** the formula per hardware target (ARM, RISC-V, FPGA) using cost-driven extraction
3. **Generates** C code with the optimized implementation
4. **Proves** the soundness chain formally in Lean 4 (0 sorry in the main chain)

### Live Demo

```lean
-- From a bare witness(0), the e-graph discovers the reduction automatically:
#eval synthesizeViaEGraph babybear_prime arm_cortex_a76
-- Output: uint64_t reduce(uint64_t x) { return ((134217727 * (x >> 31)) + (x & 2147483647)); }

#eval synthesizeViaEGraph babybear_prime riscv_sifive_u74
-- Output: uint64_t reduce(uint64_t x) { return ((((x >> 31) << 27) - (x >> 31)) + (x & 2147483647)); }
-- RISC-V replaces multiplication with shift-sub (saves 2 cycles)
```

### Supported Fields

| Field | Prime | Reduction | Status |
|-------|-------|-----------|--------|
| Mersenne31 | 2³¹ - 1 | `(x >> 31) + (x & mask)` | Verified |
| BabyBear | 2³¹ - 2²⁷ + 1 | `(x >> 31) * c + (x & mask)` | Verified |
| KoalaBear | 2³¹ - 2²⁴ + 1 | `(x >> 31) * c' + (x & mask)` | Verified |
| Goldilocks | 2⁶⁴ - 2³² + 1 | `(x >> 64) * c'' + (x & mask)` | Verified |

### Hardware-Specific Optimization

The e-graph explores multiple equivalent implementations and extracts the cheapest per target:

| BabyBear | ARM (mul=3) | RISC-V (mul=5) | FPGA (mul=1) |
|----------|-------------|----------------|-------------|
| Formula | `c * (x >> 31)` | `((x >> 31) << 27) - (x >> 31)` | `c * (x >> 31)` |
| Optimization | Keeps mul | **Shift-sub** (2 cycles cheaper) | Keeps mul (DSP) |

## Architecture

```
witness(0)                          -- bare input variable
    │
    ▼
Phase 1: Bitwise identities         -- 10 rules (AND/OR/XOR comm, shift compose)
    │
    ▼
Phase 2: Field fold discovery        -- Solinas fold rules per prime
    │   1 class → 70-100 classes
    ▼
Phase 3: Shift-add decomposition     -- x*(2^k-1) → (x<<k)-x
    │   + growth prediction (maxNodesBound)
    ▼
Cost-driven extraction               -- per hardware target
    │   multiCandidateExtract (prefers non-identity)
    ▼
C code emission                      -- uint64_t reduce_mod_p(uint64_t x) { ... }
```

## Formal Verification

### Soundness Chain (0 sorry)

```
StrongWF (ParentsBounded ∧ IsAcyclic)     -- MixedUnionFind.lean
  → union_preserves_strongWF               -- 583 LOC, pigeonhole + rootD induction
  → merge_consistent                       -- MixedSemanticSpec.lean
  → PreservesCV                            -- composable step predicate
  → saturateMixedF_preserves_consistent    -- CAPSTONE (MixedSaturationSpec.lean)
```

The capstone theorem says: after saturating an e-graph with sound rewrite rules, there exists a consistent valuation — any extracted expression is semantically equivalent to the input.

### Additional Verified Components

| Component | Theorems | Sorry | Description |
|-----------|----------|-------|-------------|
| FRI protocol | 189 | 0 | Fold soundness, Merkle integrity, verifier composition |
| Barycentric interpolation | 1 | 0 | First formalization in any proof assistant |
| E-graph extraction | 147 | 0 | Greedy + ILP extraction with completeness proofs |
| UnionFind (StrongWF) | 23 | 0 | Acyclicity via pigeonhole, adapted from OptiSat |
| Pattern soundness | 10 | 0 | All 10 bitwise rules proved at Pattern.eval level |
| Overflow bounds | 7 | 0 | evalMixed_bitwise_bounded by structural induction |

### What Is NOT Verified

- The cost model (hardware cycle counts are unverified metadata)
- Optimality of extraction (greedy, not provably optimal)
- C code compilation (we generate strings, not verified assembly)

## What AMO-Lean Does NOT Do

To be explicit about scope:

- **Does not optimize complete algorithms** (NTT, FRI verifier, Poseidon) — only the modular reduction primitive they use internally
- **Does not generate executable code** — generates C strings that need to be compiled externally
- **Does not replace hand-tuned implementations** — the reductions it discovers are the same ones engineers already use; the value is formal verification + automatic hardware-specific optimization
- **Does not cover large-prime fields** (BN254, BLS12-381) — only small Solinas primes (31-64 bit)

## Build

```bash
git clone https://github.com/manuelpuebla/amo-lean.git
cd amo-lean
lake build    # 3140 modules, ~2 minutes
```

### Run the optimizer

```lean
import AmoLean.EGraph.Verified.Bitwise.MixedRunner
open MixedRunner
open AmoLean.EGraph.Verified.Bitwise (babybear_prime arm_cortex_a76)

#eval synthesizeViaEGraph babybear_prime arm_cortex_a76
```

## Project Structure (Bitwise Module)

| File | LOC | Description |
|------|-----|-------------|
| `MixedNodeOp.lean` | 360 | 14 operations (add, mul, sub, shift, bitwise, constMask) |
| `MixedUnionFind.lean` | 583 | StrongWF with acyclicity, union_root_cases |
| `MixedCoreSpec.lean` | 346 | PostMergeInvariant, merge_preserves_pmi |
| `MixedSemanticSpec.lean` | 172 | merge_consistent, PreservesCV |
| `MixedSaturationSpec.lean` | 113 | saturateMixedF_preserves_consistent |
| `MixedEMatch.lean` | 235 | Fuel-based pattern matching + instantiation |
| `MixedPatternRules.lean` | 195 | 10 bitwise + 9 shift-add pattern rules |
| `PatternSoundInstances.lean` | 191 | All rules proved sound at Pattern.eval level |
| `CostExtraction.lean` | 470 | multiCandidateExtract, cost propagation |
| `GuidedMixedSaturation.lean` | 120 | UCB1 scoring + growth prediction |
| `MixedRunner.lean` | 240 | 3-phase pipeline: build → saturate → extract → C |
| `OverflowBounds.lean` | 128 | Bitwise expression bounds |

## Version History

```
v1.0 - v2.5   (Feb-Mar 2025)   E-graph engine, FRI verification, extraction completeness
v3.0           (Mar 2025)       Zero sorry + end-to-end completeness for CircuitNodeOp
v3.5.1         (Mar 2025)       MixedNodeOp soundness chain, operational pipeline,
                                 hardware-specific optimization (shift-sub on RISC-V)
```

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Plonky3**: Polygon Zero's high-performance STARK library

## License

MIT License — see [LICENSE](LICENSE) for details.
