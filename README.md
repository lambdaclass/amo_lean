# AMO-Lean: Verified Superoptimizer for ZK Field Arithmetic

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.26.0-purple.svg)](https://leanprover-community.github.io/mathlib4_docs/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build](https://img.shields.io/badge/Build-3140%20modules%20%E2%9C%93-brightgreen.svg)](#build)
[![Sorry](https://img.shields.io/badge/Sorry-0%20(soundness%20chain)-brightgreen.svg)](#formal-verification)

AMO-Lean takes a **prime field** and a **hardware target**, and produces **optimized, formally verified C or Rust code** for NTT, polynomial evaluation, FRI folding, and dot products. It uses equality saturation (e-graphs) to explore equivalent implementations of modular arithmetic, then extracts the cheapest one per hardware target -- all with a Lean 4 soundness proof from rewrite rules through saturation to extraction.

## What Problem Does It Solve?

Every ZK proving system (Plonky3, SP1, RISC Zero, Halo2) spends most of its prover time on **field arithmetic** -- modular reduction after multiplications, NTT butterflies, FRI folding. The standard approach:

1. A cryptographic engineer **hand-derives** a reduction formula for each prime (Solinas fold, Montgomery REDC, Barrett, Harvey).
2. They **hand-tune** it for each hardware target (ARM, RISC-V, x86, FPGA).
3. They verify correctness **by testing**.

This is slow, error-prone, and doesn't compose. AMO-Lean replaces all three steps:

| Manual approach | AMO-Lean |
|---|---|
| Derive reduction per prime | Automatic: e-graph explores all algebraic equivalents of `x % p` |
| Tune per hardware | Automatic: cost-aware extraction picks cheapest per target |
| Test correctness | Proved: 0 sorry, 0 custom axioms in the soundness chain |
| One strategy per NTT | Per-stage: bound propagation selects optimal reduction at each butterfly stage |
| Fixed algorithm choice | Discovery: Ruler module finds rewrite rules empirically, e-graph composes them |

**Key guarantee**: even with an incorrect cost model, the generated code is always **semantically correct** (just potentially suboptimal). Correctness and optimization are decoupled by design.

## How It Works

AMO-Lean operates at three levels simultaneously:

```
Level 1 -- Algorithmic (MatExpr)
  Explores NTT factorizations: Cooley-Tukey, radix-2, radix-4, mixed-radix.
  Finds the cheapest butterfly network structure for a given size and hardware.
      |
      | queries per-butterfly cost
      v
Level 2 -- Arithmetic (MixedExpr + bounds)
  Explores modular reduction strategies: Solinas fold, Montgomery REDC,
  Barrett, Harvey, and compositions thereof. Propagates overflow bounds
  through NTT stages. Decides per-stage: reduce now or defer (lazy).
      |
      | emits verified statements
      v
Level 3 -- Code generation (TrustLean.Stmt)
  Lowers the chosen plan to verified C or Rust via TrustLean.Stmt.
  Each reduction strategy has a verified lowering function.
```

### The Two Pipelines

AMO-Lean has two code generation pipelines, selectable at invocation:

**Legacy pipeline** (`--pipeline legacy`, default): Seeds an e-graph with `x % p`, saturates with 30+ verified rewrite rules across 3 phases (bitwise identities, field-specific folds, shift-add decomposition), then extracts the cheapest `MixedExpr` per hardware target via `mixedOpCost(hw, op)`. Produces one uniform reduction strategy for the entire NTT.

**Ultra pipeline** (`--pipeline ultra`): Runs Ruler-based rule discovery, bound-aware multi-relation saturation, per-stage schedule extraction via `costAwareReductionForBound(hw, boundK, p)`, plan-level cost competition across 8+ candidate plans (radix-2, radix-4, mixed-radix, DIT, DIF), and verified codegen via TrustLean.Stmt. Produces **per-stage** reduction choices -- early stages may use lazy reduction, middle stages Solinas, late stages Harvey -- all driven by the hardware cost model and overflow bounds.

### Automatic Rule Discovery

The Ruler module discovers new rewrite rules without human input:

1. Enumerates small expressions (depth <= 3) over the 23-operation vocabulary
2. Evaluates each on field-specific test inputs to produce characteristic vectors (CVecs)
3. Groups expressions by identical CVecs -- these are empirically equivalent
4. Feeds discovered equivalences into the e-graph as new rules

This lets AMO-Lean find field-specific optimizations (e.g., shift-add decomposition of fold constants via CSD encoding) and validate that named algorithms (Solinas, Montgomery, Harvey) all compute `x % p`.

## Inputs and Outputs

### Input: CLI Flags

```
lake env lean --run Bench.lean -- [flags]
```

| Flag | Values | Default | Description |
|------|--------|---------|-------------|
| `--field` | `babybear`, `koalabear`, `mersenne31`, `goldilocks`, `all` | `all` | Prime field(s) to optimize for |
| `--size` | `12,14,16,18,20,22`, `all` | `16,20` | NTT sizes as log2(N), e.g., 16 means N=65536 |
| `--primitive` | `ntt`, `poly`, `fri`, `dot`, `all` | `ntt` | Which operation to benchmark |
| `--lang` | `c`, `rust`, `all` | `c` | Output language |
| `--hardware` | `arm-scalar`, `arm-neon`, `x86-avx2` | `arm-scalar` | Hardware cost model to use |
| `--pipeline` | `legacy`, `ultra` | `legacy` | Which optimization pipeline |
| `--iters` | `auto` or a number | `auto` | Benchmark iterations |
| `--csv PATH` | file path | none | Export results to CSV |
| `--no-explain` | flag | (explain on) | Hide cost model explanation |
| `--help` | flag | | Show help |

### Input: Supported Fields

| Field | Prime p | Form | Word size |
|-------|---------|------|-----------|
| BabyBear | 2013265921 | 2^31 - 2^27 + 1 | 32-bit |
| KoalaBear | 2130706433 | 2^31 - 2^24 + 1 | 32-bit |
| Mersenne31 | 2147483647 | 2^31 - 1 | 32-bit |
| Goldilocks | 18446744069414584321 | 2^64 - 2^32 + 1 | 64-bit |

### Input: Hardware Targets

| Target | Key costs (cycles) | SIMD? | Notes |
|--------|---|---|---|
| `arm-scalar` (ARM Cortex-A76) | mul=3, add=1, shift=1 | No | Barrel shifter, branch penalty=1 |
| `arm-neon` (ARM NEON) | mul=3, add=1, shift=1 | Yes (4 lanes) | Widening penalty=8 for u64 ops |
| `x86-avx2` (x86 AVX2) | mul=3, add=1, shift=1 | Yes (8 lanes) | Widening penalty=8 for u64 ops |

Additional targets available in the Lean API: RISC-V SiFive U74 (mul=5, no barrel shifter), FPGA Xilinx DSP48E2 (mul=1, shift=0).

### Output: Generated Code + Benchmark

AMO-Lean produces two things:

**1. Optimized C or Rust source code** (written to `/tmp/amobench.c` or `/tmp/amobench.rs`):

```c
// Generated for BabyBear, N=65536, ARM Cortex-A76, Ultra pipeline
void ntt_babybear_ultra(int32_t* data, const int32_t* twiddles) {
  // Stage 0: lazy (no reduction -- bound safe)
  // Stage 1: lazy
  // ...
  // Stage 14: harvey (conditional subtract -- tight bound)
  // Stage 15: solinas_fold (final output < 2p)
  ...
}
```

Each stage uses the reduction strategy selected by the cost model + bound analysis. The code includes a self-contained benchmark harness that compares against Plonky3-style implementations.

**2. Benchmark results** (printed to stdout):

```
  AMO-Lean Benchmarker v1.0
  Hardware: ARM Cortex-A76 (scalar)
  Pipeline: ultra

  Field         N      Lang    AMO (us)    P3 (us)   Melem/s     Diff
  ─────────── ────── ───── ─────────── ─────────── ───────── ────────
  BabyBear     2^16   C     142 us      198 us      461       -28%
  BabyBear     2^20   C     2841 us     3892 us     369       -27%
  KoalaBear    2^16   C     139 us      195 us      471       -28%
  Mersenne31   2^16   C     118 us      172 us      555       -31%
```

Columns: AMO-Lean time, Plonky3-equivalent time, throughput in millions of elements/second, relative difference.

**3. Optional CSV export** (`--csv results.csv`):

```csv
hardware,field,log_n,primitive,lang,amo_us,p3_us,melem,diff_pct
arm-scalar,BabyBear,16,ntt,C,142,198,461,-28
```

### Output: Lean API

For programmatic use without the benchmarker:

```lean
import AmoLean.EGraph.Verified.Bitwise.SynthesisToC
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline

-- Synthesize a single reduction (e-graph + cost extraction):
#eval synthesizeViaEGraph babybear_prime arm_cortex_a76
-- "uint64_t reduce(uint64_t x) { return ((134217727 * (x >> 31)) + (x & 2147483647)); }"

-- Generate full NTT with Ultra pipeline:
#eval genOptimizedBenchC_ultra babybearConfig 16 1000 arm_cortex_a76
-- Complete C program: NTT function + benchmark harness + Plonky3 comparison

-- Compare reduction costs across all hardware targets:
#eval costReport babybearConfig
-- "ARM-A76: Solinas=6 Monty=8 Harvey=3 Barrett=10 -> Harvey wins (k<=2)"
-- "ARM-NEON: Solinas=14 Monty=6 Harvey=3 Barrett=18 -> Monty wins (SIMD)"
```

## Build

```bash
git clone https://github.com/manuelpuebla/amo-lean.git
cd amo-lean
lake build    # ~3140 modules, ~2 minutes on Apple Silicon
```

### Run Benchmarks

```bash
# Default: all fields, NTT, C, ARM scalar, legacy pipeline
lake env lean --run Bench.lean

# Ultra pipeline, BabyBear only, all sizes
lake env lean --run Bench.lean -- --pipeline ultra --field babybear --size all

# Multi-target comparison with CSV export
lake env lean --run Bench.lean -- --hardware arm-neon --primitive ntt,fri --csv results.csv
```

## Formal Verification

### Soundness Chain (0 sorry, 0 custom axioms)

```
ematchF_sound                         -- pattern matching: correct substitutions
    |
instantiateF_sound                    -- RHS instantiation: preserves CV
    |
applyRuleAtF_preserves_cv            -- single rule: preserves CV + VPMI + SHI
    |
applyRulesF_preserves_cv             -- rule list: preserves the triple
    |
saturateMixedF_preserves_consistent  -- full saturation: consistency preserved
```

Three invariants threaded through the chain:
- **ConsistentValuation (CV)**: every e-class node evaluates to the class representative's value
- **PostMergeInvariant (VPMI)**: union-find well-formedness + children bounded + hashcons valid
- **ShapeHashconsInv (SHI)**: every hashcons entry points to a class containing that node

### What IS Verified

| Component | Theorems | Coverage |
|---|---|---|
| E-graph soundness chain | 147 | Full: e-match through extraction |
| Rewrite rules (30+) | 30+ | Each rule: `lhsEval = rhsEval` |
| Reduction composition | 5 | `compose(step1, step2)` preserves `x % p` |
| Bridge theorems | 4 | Nat-level butterfly = ZMod p field butterfly |
| FRI protocol | 189 | Fold soundness, Merkle integrity, verifier composition |
| UnionFind | 27 | Acyclicity, root preservation, StrongWF |
| Field arithmetic | 86 | Mersenne31, BabyBear, Goldilocks, Montgomery REDC |
| Cost ordering | 3 | `mersenneCost <= solinasCost <= montgomeryCost` for all HW |

### What Is NOT Verified

- **Cost model**: Hardware cycle counts are unverified metadata (correct code, possibly suboptimal)
- **Extraction optimality**: Greedy extraction, not provably optimal for DAGs with sharing
- **C/Rust compilation**: We generate source strings, not verified assembly
- **Ruler-discovered rules**: Empirically validated on test inputs, not formally proved (intentional trust boundary)

## Comparison with Related Work

| Project | Domain | Verified? | Codegen? | Multi-target? | E-graph? |
|---|---|---|---|---|---|
| **Fiat-Crypto** (MIT) | Field arithmetic | Yes (Coq) | C, Rust, Go | No | No |
| **egg** (UW) | Generic e-graphs | No | No | No | Yes |
| **ArkLib** (community) | ZK primitives | Partial (Lean 4) | No | No | No |
| **SPIRAL** (CMU) | Linear transforms | No | C, CUDA | Yes | No |
| **AMO-Lean** | Field arithmetic + NTT | Yes (Lean 4) | C, Rust | Yes | Yes |

AMO-Lean is narrower than Fiat-Crypto (4 primes vs dozens) but uniquely combines **equality saturation**, **formal verification**, **hardware-aware cost extraction**, and **per-stage bound-driven optimization** in a single system.

## References

1. Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic -- With Proofs" (S&P 2019)
3. Nandi et al. "Ruler: Rewrite Rule Synthesis via Equality Saturation" (OOPSLA 2021)
4. Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity" (ICALP 2018)
5. Solinas, "Generalized Mersenne Numbers" (1999)
6. Franchetti et al. "SPIRAL: Extreme Performance Portability" (Proc. IEEE 2018)

## License

MIT License -- see [LICENSE](LICENSE) for details.
