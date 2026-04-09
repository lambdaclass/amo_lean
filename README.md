# AMO-Lean: Verified Optimizer for Finite Field Arithmetic

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.26.0-purple.svg)](https://leanprover-community.github.io/mathlib4_docs/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build](https://img.shields.io/badge/Build-3140%20modules%20%E2%9C%93-brightgreen.svg)](#build)
[![Sorry](https://img.shields.io/badge/Sorry-0%20(soundness%20chain)-brightgreen.svg)](#formal-verification)

AMO-Lean is a **formally verified optimizer** for finite field arithmetic, implemented natively in Lean 4. It uses **equality saturation** (e-graphs) with verified rewrite rules to automatically optimize modular reduction and NTT butterfly operations for ZK proving systems (Plonky3, SP1, RISC Zero), and emits hardware-specific C code.

Every optimization applied has a corresponding Lean proof. The soundness chain from e-matching through saturation to extraction is proved with **zero sorry and zero custom axioms**.

## What AMO-Lean Can Do

### 1. Optimize Modular Reduction

Given a Solinas prime `p = 2^a - 2^b + 1` and a hardware target, AMO-Lean replaces the expensive `x % p` with shifts, masks, and multiplications by constants:

```lean
-- BabyBear on ARM Cortex-A76 (6 cycles):
#eval synthesizeViaEGraph babybear_prime arm_cortex_a76
-- uint64_t reduce(uint64_t x) { return ((134217727 * (x >> 31)) + (x & 2147483647)); }

-- Same prime on RISC-V (shift-sub replaces mul, saves 2 cycles):
#eval synthesizeViaEGraph babybear_prime riscv_sifive_u74
-- uint64_t reduce(uint64_t x) { return ((((x >> 31) << 27) - (x >> 31)) + (x & 2147483647)); }
```

**Supported fields:**

| Field | Prime | Reduction | ARM cycles |
|-------|-------|-----------|------------|
| Mersenne31 | 2^31 - 1 | `(x >> 31) + (x & mask)` | 3 |
| BabyBear | 2^31 - 2^27 + 1 | `(x >> 31) * c + (x & mask)` | 6 |
| KoalaBear | 2^31 - 2^24 + 1 | `(x >> 31) * c' + (x & mask)` | 6 |
| Goldilocks | 2^64 - 2^32 + 1 | `(x >> 64) * c'' + (x & mask)` | 6 |

**Correctness theorem** (`solinasFold_mod_correct`): For any `x`, `fold(x) % p = x % p`.

### 2. Optimize NTT Butterflies

AMO-Lean generates optimized C code for Cooley-Tukey NTT butterfly operations by inserting Solinas folds at optimal points:

```lean
-- Generate optimized butterfly for BabyBear:
#eval optimizeButterflyDirect babybear_prime
-- Sum:  a' = fold(a + fold(w * b))     -- two Solinas folds, no % p at runtime
-- Diff: b' = fold(p + a - fold(w * b)) -- safe Nat subtraction via p + a
```

Output (BabyBear butterfly sum on ARM):
```c
uint64_t butterfly_sum(uint64_t a, uint64_t w, uint64_t b) {
  uint64_t wb = w * b;
  uint64_t wb_fold = (wb >> 31) * 134217727 + (wb & 0x7FFFFFFF);
  uint64_t sum = a + wb_fold;
  return (sum >> 31) * 134217727 + (sum & 0x7FFFFFFF);
}
```

**Full NTT generation**: `generateOptimizedNTTDirect 8 babybear_prime` produces 3 stages x 4 butterflies = 24 optimized C functions, **instantaneously**.

**Bridge theorem** (`butterfly_nat_eq_field`): The Nat-level butterfly corresponds exactly to the ZMod p field butterfly.

### 3. Hardware-Specific Code Generation

The same algorithm generates different code per hardware target:

| Target | mul cost | Optimization | Example (BabyBear) |
|--------|----------|-------------|-------------------|
| ARM Cortex-A76 | 3 cycles | Keep mul (barrel shifter) | `c * (x >> 31)` |
| RISC-V SiFive U74 | 5 cycles | **Shift-sub** (2 cycles cheaper) | `((x >> 31) << 27) - (x >> 31)` |
| FPGA Xilinx DSP48E2 | 1 cycle | Keep mul (DSP unit) | `c * (x >> 31)` |
| x86 Intel Skylake | 3 cycles | Keep mul | `c * (x >> 31)` |

**Cost comparison theorems** (proved): `mersenneFoldCost hw <= pseudoMersenneFoldCost hw <= montgomeryCost hw` for all targets.

### 4. Kronecker Packing

Pack two 31-bit BabyBear elements into one 64-bit word for parallel processing:

```
kronPack(a, b, 32) = a + b * 2^32

Verified roundtrip:
  unpackLo(pack(a, b)) = a
  unpackHi(pack(a, b)) = b

Verified fusion:
  pack(a1, b1) + pack(a2, b2) = pack(a1 + a2, b1 + b2)
```

Potential: **2x throughput** on BabyBear butterflies using 64-bit SIMD-in-a-register.

### 5. Lazy Reduction with Bound Tracking

AMO-Lean propagates overflow bounds through expression trees and decides when reduction is mandatory:

- BabyBear: **58 butterfly iterations** safe without intermediate reduction (in 64-bit)
- Goldilocks: **57 iterations** safe
- Harvey conditional subtraction: `harveyReduce(x, p) < 2p` (proved) — composable across NTT stages

## Architecture

```
                       Input
                         |
               +---------v---------+
               | SolinasConfig     |    p = 2^a - 2^b + 1
               | (a, b, prime)     |    auto-detected per field
               +---------+---------+
                         |
              +----------v----------+
              | Build E-Graph       |    addMixedExpr: MixedExpr -> EGraph
              | (6-20 e-classes)    |
              +----------+----------+
                         |
    +--------------------v--------------------+
    |        3-Phase Guided Saturation        |
    |                                         |
    |  Phase 1: Bitwise identities (10 rules) |
    |    AND/OR/XOR comm, shift compose,      |
    |    mask = mod 2^n, shift = div/mul 2^n  |
    |                                         |
    |  Phase 2: Field fold rules (1-3 rules)  |
    |    Mersenne fold, Solinas fold,         |
    |    double-reduce elimination            |
    |                                         |
    |  Phase 3: Shift-add decomposition       |
    |    x*(2^k-1) -> (x<<k)-x               |
    |    + UCB1 growth prediction             |
    +--------------------+--------------------+
                         |
              +----------v----------+
              | Cost-Aware Extract  |    per-hardware cycle model
              | multiCandidateExtr  |    prefers non-identity nodes
              +----------+----------+
                         |
              +----------v----------+
              | C Code Emission     |    MixedExpr -> CodegenExpr -> C string
              +---------------------+
```

### Direct Butterfly Pipeline (Instant)

For NTT butterflies, a faster path bypasses the e-graph entirely:

```
butterfly(a, w, b, p)
    |
    v
Insert Solinas fold after each operation:
    wb = w * b
    wb_folded = fold(wb)        -- (wb >> k) * c + (wb & mask)
    sum = a + wb_folded
    result = fold(sum)          -- (sum >> k) * c + (sum & mask)
    |
    v
Emit C code (instantaneous -- no search, no saturation)
```

This works because the optimal butterfly reduction pattern is **deterministic** — there is no search space to explore. The fold insertion points are known: after every multiplication and after every addition.

## Formal Verification

### Soundness Chain (0 sorry, 0 custom axioms)

The complete chain proves that saturating an e-graph with sound rewrite rules preserves `ConsistentValuation`:

```
ematchF_sound                         -- pattern matching produces correct substitutions
    |
    v
instantiateF_sound                    -- RHS instantiation preserves CV + correct value
    |
    v
applyRuleAtF_preserves_cv            -- single rule application preserves CV + VPMI + SHI
    |
    v
applyRulesF_preserves_cv             -- rule list application preserves the triple
    |
    v
saturateMixedF_preserves_consistent  -- full saturation preserves consistency
```

**Key invariants threaded through the chain:**
- `ConsistentValuation (CV)`: every e-class node evaluates to the class representative's value
- `PostMergeInvariant (VPMI)`: union-find well-formedness + children bounded + hashcons entries valid
- `ShapeHashconsInv (SHI)`: every hashcons entry points to a class containing that node

### Verified Rewrite Rules (29+)

| Category | Rules | Examples |
|----------|-------|---------|
| Bitwise | 10 | shift compose, AND/XOR/OR comm, mask-mod bridge |
| Field fold | 4 | Mersenne31, BabyBear, KoalaBear, Goldilocks |
| Mul-reduce | 3 | `(x%p)%p = x%p`, mod distributes over +/* |
| Butterfly | 3 | CT sum decomposition, twiddle decomp, double-reduce elim |
| Kronecker | 3 | pack/unpack roundtrip, lane-fused addition |
| Shift-add | 6 | `x*(2^k-1) -> (x<<k)-x` for k in {24, 27, 32} |

Each rule has a soundness proof: `forall env v, lhsEval env v = rhsEval env v`.

### Bridge Theorems

| Theorem | Statement |
|---------|-----------|
| `solinasFold_mod_correct` | `fold(x) % p = x % p` for Solinas primes |
| `butterfly_nat_eq_field` | `(a + w*b) % p = ZMod.val ((a : ZMod p) + (w : ZMod p) * (b : ZMod p))` |
| `butterflyDiff_nat_eq_field` | Same for butterfly difference |
| `synthesizeReduction_sound` | Synthesized reduction preserves modular arithmetic |

### Additional Verified Components

| Component | Theorems | Description |
|-----------|----------|-------------|
| FRI protocol | 189 | Fold soundness, Merkle integrity, verifier composition |
| Barycentric interpolation | 1 | First formalization in any proof assistant |
| E-graph extraction | 147 | Greedy + ILP extraction with completeness proofs |
| UnionFind (StrongWF) | 27 | Acyclicity via pigeonhole, root preservation through push |
| Field arithmetic | 86 | Mersenne31, BabyBear, Goldilocks with Montgomery |
| Kronecker packing | 8 | Verified roundtrip, lane-fused arithmetic |

### What Is NOT Verified

- **Cost model**: Hardware cycle counts are unverified metadata (correct code, possibly suboptimal)
- **Optimality of extraction**: Greedy extraction, not provably optimal for DAGs with sharing
- **C compilation**: We generate C strings, not verified assembly
- **env uniformity**: `ematchF_sound` requires `witnessVal = constVal` (practical for rewrite rule patterns, not for general expressions)

## Build

```bash
git clone https://github.com/manuelpuebla/amo-lean.git
cd amo-lean
lake build    # 3140 modules, ~2 minutes on Apple Silicon
```

### Quick Start: Optimize a Reduction

```lean
import AmoLean.EGraph.Verified.Bitwise.SynthesisToC
open AmoLean.EGraph.Verified.Bitwise

-- Emit optimized C for all 4 fields:
#eval emitC_mersenne31                           -- Mersenne31
#eval emitC_babybear arm_cortex_a76              -- BabyBear on ARM
#eval emitC_koalabear riscv_sifive_u74           -- KoalaBear on RISC-V
#eval emitC_goldilocks fpga_dsp48e2              -- Goldilocks on FPGA

-- Compare costs across targets:
#eval emitWithCosts babybear_prime               -- ARM, RISC-V, FPGA side by side
```

### Quick Start: Optimize an NTT

```lean
import AmoLean.EGraph.Verified.Bitwise.NTTBridge
open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified.Bitwise.NTTBridge

-- Single butterfly (instant):
#eval optimizeButterflyDirect babybear_prime

-- Full 8-point NTT (instant):
#eval generateOptimizedNTTDirect 8 babybear_prime
```

## Project Structure

### Core Bitwise Engine (~14,700 LOC)

| File | LOC | Description |
|------|-----|-------------|
| `MixedNodeOp.lean` | 430 | 20 operations: algebraic + bitwise + Kronecker |
| `MixedUnionFind.lean` | 681 | StrongWF with acyclicity, union_root_cases |
| `MixedCoreSpec.lean` | 362 | PostMergeInvariant, ShapeHashconsInv, merge properties |
| `MixedSemanticSpec.lean` | 178 | merge_consistent, PreservesCV (with SHI) |
| `MixedEMatch.lean` | 240 | Fuel-based pattern matching + instantiation |
| `MixedEMatchSoundness.lean` | 1200 | ematchF_sound, instantiateF_sound, applyRulesF_preserves_cv |
| `MixedAddNodeTriple.lean` | 360 | add_node_consistent, add/merge_preserves_shi |
| `MixedPatternRules.lean` | 195 | 10 bitwise + 9 shift-add pattern rules |
| `PatternSoundInstances.lean` | 191 | All rules proved sound at Pattern.eval level |
| `ButterflyRules.lean` | 132 | CT sum/diff decomposition, lazy bounds |
| `KroneckerRules.lean` | 86 | Pack/unpack roundtrip, lane fusion |
| `CostExtraction.lean` | 470 | Multi-candidate extract, cost propagation |
| `MixedRunner.lean` | 240 | 3-phase pipeline: build -> saturate -> extract -> C |
| `SynthesisToC.lean` | 250 | Prime -> verified reduction -> C emission |
| `NTTBridge.lean` | 420 | Butterfly -> Solinas fold -> C, ZMod bridge theorems |

### Verified Fields (~1,700 LOC)

| File | Description |
|------|-------------|
| `Field/Mersenne31.lean` | Field instance, ZMod isomorphism, Plonky3 TV |
| `Field/BabyBear.lean` | Montgomery roundtrip, Plonky3 TV |
| `Field/Goldilocks.lean` | Algorithms = Plonky3 (rfl proofs) |
| `Field/Montgomery.lean` | Generic REDC (addition variant, no Nat underflow) |

### FRI Verification (~2,600 LOC)

| File | Description |
|------|-------------|
| `FRI/Verified/FRISemanticSpec.lean` | Evaluation domains, crypto axioms (True placeholders) |
| `FRI/Verified/BarycentricInterpolation.lean` | Novel: first in any proof assistant |
| `FRI/Verified/FoldSoundness.lean` | fold_preserves_consistency |
| `FRI/Verified/FRIPipelineIntegration.lean` | fri_pipeline_soundness (capstone) |

## Relevance to the ZK Ecosystem

### The Problem

Every ZK proving system (Plonky3, SP1, RISC Zero, Halo2) spends a large fraction of prover time on **field arithmetic** — specifically, modular reduction after multiplications. The standard approach is Montgomery reduction (~7-9 cycles), but for Solinas primes (which Plonky3 fields are), faster reductions exist using shifts and masks (~3-6 cycles).

These optimizations are well-known to cryptographic engineers, but:
1. They're implemented **by hand** for each prime and each hardware target
2. They're **not formally verified** — correctness is checked by testing
3. The optimal implementation **varies per hardware** (ARM barrel shifter vs RISC-V shift cost)

### What AMO-Lean Contributes

1. **Automatic discovery**: Given a prime, the e-graph finds the optimal reduction formula. Engineers don't need to derive the shift-mask decomposition manually.

2. **Formal correctness**: Every rule and every composition is proved in Lean 4. The soundness chain from pattern matching to saturation is complete (0 sorry). This is stronger than testing.

3. **Hardware-specific extraction**: The same e-graph produces different code for different targets. The cost model is the only unverified component — but even with an incorrect cost model, the generated code is **correct** (just potentially suboptimal).

4. **NTT butterfly optimization**: The direct pipeline generates C code for NTT butterflies with Solinas fold insertions, producing code that avoids `% p` at runtime entirely.

### Comparison with Related Work

| Project | Domain | Verified? | Codegen? |
|---------|--------|-----------|----------|
| **Fiat-Crypto** (MIT) | Field arithmetic | Yes (Coq) | Yes (C, Rust, Go) |
| **egg** (UW) | Generic e-graphs | No | No |
| **ArkLib** (community) | ZK primitives | Partial (Lean 4) | No |
| **AMO-Lean** | Field arithmetic + NTT | Yes (Lean 4) | Yes (C) |

AMO-Lean is narrower than Fiat-Crypto (4 primes vs dozens) but combines **e-graph optimization** (exploring multiple equivalent implementations automatically) with **formal verification** (Lean 4 kernel) and **hardware-aware extraction** — a combination no other project offers.

## Version History

```
v1.0 - v2.5   (2025)      E-graph engine, FRI verification, extraction completeness
v3.0          (Mar 2026)   Zero sorry, end-to-end completeness for CircuitNodeOp
v3.5          (Mar 2026)   MixedNodeOp soundness chain, 3-phase guided saturation
v4.0          (Mar 2026)   ematchF_sound fully proved, NTT butterfly codegen,
                            Kronecker packing, PreservesCV with ShapeHashconsInv,
                            direct butterfly optimization (instant)
```

## Project Numbers

| Metric | Value |
|--------|-------|
| Total LOC | 74,236 |
| Bitwise engine LOC | 14,696 |
| Theorems + definitions | ~1,600 |
| Sorry (soundness chain) | **0** |
| Custom axioms (active code) | **0** |
| Crypto axioms (FRI, True placeholder) | 3 |
| Supported primes | 4 |
| Hardware targets | 4 |
| Verified rewrite rules | 29+ |
| `lake build` | 3,140 modules, 0 errors |

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic" (S&P 2019)
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity" (ICALP 2018)
4. **Plonky3**: Polygon Zero's high-performance STARK library
5. **Solinas primes**: Solinas, "Generalized Mersenne Numbers" (1999)
6. **Equality Saturation**: Tate et al. "Equality Saturation: A New Approach to Optimization" (POPL 2009)

## License

MIT License — see [LICENSE](LICENSE) for details.

