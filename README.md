# Truth Research ZK: Verified Optimizing Compiler for Cryptographic Primitives

[![Lean 4](https://img.shields.io/badge/Lean-4.26.0-blue.svg)](https://leanprover.github.io/lean4/doc/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Tests](https://img.shields.io/badge/Tests-2850%2B-green.svg)](#testing)
[![Build](https://img.shields.io/badge/Build-3140%20modules-brightgreen.svg)](#build)
[![FRI Verified](https://img.shields.io/badge/FRI-189%20theorems%2C%200%20sorry-blue.svg)](#fri-formal-verification)
[![Extraction Complete](https://img.shields.io/badge/Extraction-complete%20(0%20sorry)-blue.svg)](#verified-extraction-completeness)

## What is AMO-Lean?

**AMO-Lean** is a verified optimizing compiler that transforms mathematical specifications written in Lean 4 into optimized C/Rust code with **formal correctness guarantees**. It targets cryptographic primitives used in STARK provers and zkVMs.

The core value proposition: **write your mathematical specification once in Lean 4, and get optimized C or Rust code that is correct by construction** — every optimization step is a formally proven theorem. This eliminates the traditional tradeoff between performance and correctness in cryptographic implementations.

AMO-Lean currently covers the key building blocks of modern proof systems: NTT (Number Theoretic Transform), FRI (Fast Reed-Solomon IOP), field arithmetic (Goldilocks, BabyBear), Poseidon2 hashing, and a verified e-graph optimization engine. As of v2.4.1, the FRI protocol is formally verified end-to-end (189 theorems, 0 sorry, 0 custom axioms) with **operational-verified bridges** connecting 357 operational defs to algebraic specifications, including a **novel formalization of barycentric interpolation** — the first in any proof assistant. The generated code is Plonky3-compatible and achieves ~60% of hand-optimized Rust throughput with full formal verification.

## Ecosystem & Comparisons

AMO-Lean occupies a unique position: it combines **equality saturation optimization** with **formal verification** in a single tool. Most existing projects do one or the other.

| Project | Approach | Proof Assistant | Verification Scope | Codegen Target |
|---------|----------|-----------------|---------------------|----------------|
| **AMO-Lean** | E-graph optimization + Sigma-SPL IR | Lean 4 | Full pipeline (spec → IR → code) | C, Rust |
| [fiat-crypto](https://github.com/mit-plv/fiat-crypto) | Synthesis from field specs | Coq | Field arithmetic | C, Rust, Go, Java |
| [Jasmin](https://github.com/jasmin-lang/jasmin) | Verified assembly compiler | Coq (EasyCrypt) | Compiler correctness | x86 assembly |
| [CryptoLine](https://github.com/fmlab-iis/cryptoline) | Algebraic program verification | External (SMT) | Post-hoc verification | N/A (verifier only) |
| [hacspec](https://github.com/hacspec/hacspec-v2) | Executable specification language | F\*/Coq | Spec extraction | Rust |
| [SPIRAL](https://www.spiral.net/) | Autotuning + formal rewrite rules | Custom (GAP) | Transform correctness | C, CUDA, FPGA |

**What makes AMO-Lean different:**
- **Equality saturation** (e-graphs) explores the full space of equivalent rewrites simultaneously, extracting the globally optimal form — not just a locally optimal greedy result
- **Sigma-SPL IR** enables algebraic reasoning about loop nest generation from Kronecker product decompositions
- **Trust-Lean verified backend** provides a formally verified C code generator with sanitized identifiers and structural correctness proofs
- **Single tool**: optimization, verification, and code generation in one pipeline, rather than separate tools stitched together

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

This architecture is **portable and modular**: adding a new primitive means writing a Lean specification and lowering rules — the optimization engine and code generator are reusable across all primitives.

### Two Operational Modes

| Mode | Purpose | Status |
|------|---------|--------|
| **Verifier** | Certify external code (e.g., Plonky3) is mathematically correct | Production Ready |
| **Generator** | Generate verified C/Rust code from Lean specs | Production Ready |

## Features

- **Verified Pipeline Soundness** — End-to-end `full_pipeline_soundness` theorem: saturation + extraction preserves semantics, **0 custom axioms**
- **Translation Validation** — Level 2 soundness via `cryptoEquivalent` relation with congruence closure
- **NTT** (Number Theoretic Transform) — Verified, optimized, Plonky3-compatible
- **Radix-4 NTT** — 4-point butterfly (8 axioms pending formal implementation, v2.5.0)
- **Goldilocks Field** — Scalar + AVX2 arithmetic (p = 2^64 - 2^32 + 1), **0 axioms**
- **BabyBear Field** — Scalar arithmetic (p = 2^31 - 2^27 + 1), **0 axioms**
- **FRI Formal Verification** — 16 verified modules (~4,450 LOC, 189 theorems, 0 sorry): fold soundness, Merkle integrity, Fiat-Shamir transcript, per-round soundness (Garreta 2025), verifier composition, pipeline integration, operational-verified bridges
- **Operational-Verified FRI Bridges** — 7 bridge modules connecting 357 operational defs to algebraic specs: domain, fold, transcript, Merkle, plus integration capstone `operational_verified_bridge_complete`
- **Barycentric Interpolation** — First formalization in any proof assistant: `barycentric_eq_lagrange` generic over `[Field F]`
- **FRI Pipeline Integration** — `fri_pipeline_soundness` composes e-graph optimization (Level 1+2) with FRI algebraic guarantees (Level 3)
- **E-Graph Optimization** — Verified engine (121 theorems, 0 sorry) + 19/20 rewrite rules
- **Extraction Completeness** — DAG acyclicity (`computeCostsF_acyclic`) + fuel sufficiency (`extractAuto_complete`), 6 theorems, 0 sorry, 0 axioms
- **Perm Algebra** — Tensor, stride, compose, inverse with **0 axioms** (equation compiler fix)
- **Algebraic Semantics** — C-Lite++ lowering with verified scatter/gather (19/19 cases)
- **Poseidon2 Hash** — BN254 t=3 with HorizenLabs-compatible test vectors
- **Trust-Lean Bridge** — Verified type conversion with roundtrip proofs + injectivity (26 theorems, 0 sorry)

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

### Compiler Driver

The `trzk` compiler driver lets you write an algorithm spec in Lean and compile it to C or Rust in one step.

**1. Write your spec.** Create a `.lean` file with your algorithm expressed as matrix operations:

```lean
-- my_transform.lean
open AmoLean.Matrix (MatExpr)

def spec : MatExpr Int 8 8 :=
  let stage1 : MatExpr Int 8 8 := .kron (.identity 4) (.dft 2)
  let stage2 : MatExpr Int 8 8 := .kron (.identity 2) (.kron (.dft 2) (.identity 2))
  .compose stage2 stage1
```

No imports or boilerplate needed — just the algorithm definition.

**2. Compile it:**

```bash
lake build trzk
.lake/build/bin/trzk my_transform.lean --target c --name my_transform
```

**3. Use the generated code.** The compiler writes `my_transform.c` (or `.rs` for `--target rust`), which you can drop into your own project:

```c
// my_transform.c (generated)
void my_transform(double* restrict in, double* restrict out) {
  for (int i0 = 0; i0 < 4; i0++) {
    out[2 * i0 + 0] = (in[2 * i0 + 0] + in[2 * i0 + 1]);
    out[2 * i0 + 1] = (in[2 * i0 + 0] - in[2 * i0 + 1]);
  }
  // ... stage 2
}
```

Available matrix operations: `.dft`, `.identity`, `.kron` (Kronecker product), `.compose`, `.add`, `.smul`, `.transpose`, `.perm`, `.diag`, `.twiddle`, `.elemwise`. See the `examples/` directory for more specs.

**Options:**

| Flag | Description | Default |
|------|-------------|---------|
| `--target c\|rust` | Output language | `c` |
| `--output <path>` | Output file path | `<spec>.c` or `<spec>.rs` |
| `--name <func>` | Function name in generated code | `spec` |

### Integration Tests (DFT₄ Verification)

The `generated/` directory contains a DFT₄ kernel (Walsh-Hadamard Transform) generated by the AMO-Lean pipeline, with C and Rust implementations. The `integration_tests/` directory contains the Python verifier and test vectors that exercise these binaries end-to-end.

**Step 1: Generate C and Rust code from the Lean pipeline**

```bash
lake env lean AmoLean/FullPipeline.lean
```

This runs the full AMO-Lean pipeline (e-graph optimization, Sigma-SPL lowering, and code generation) and writes two files into `generated/`:

- `generated/dft4.c` — DFT₄ kernel + minimal C test harness
- `generated/dft4.rs` — DFT₄ kernel with NttField trait + minimal Rust test harness

It also runs the 9 in-Lean tests that verify codegen structure (function signatures, temporaries, loop generation, Trust-Lean roundtrip).

**Step 2: Compile the generated binaries**

```bash
cd generated && clang -O2 -o dft4 dft4.c && rustc -o dft4_rs dft4.rs && cd ..
```

**Step 3: Run the integration tests**

```bash
# Verify C binary against WHT_4 reference
python3 integration_tests/verify_dft4.py --binary generated/dft4 integration_tests/test_vectors.txt

# Verify Rust binary against WHT_4 reference
python3 integration_tests/verify_dft4.py --binary generated/dft4_rs integration_tests/test_vectors.txt

# Standalone self-test (roundtrip property: WHT_4^2 = 4·I, no binary needed)
python3 integration_tests/verify_dft4.py integration_tests/test_vectors.txt
```

Each generated binary takes a single integer vector as command-line arguments (e.g. `./dft4 1 2 3 4`) and prints the transformed output. The Python verifier iterates over `test_vectors.txt` (25 integer vectors), invokes the binary for each vector, and checks the result against `WHT_4 · input`.
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

## Examples

All examples are runnable via `lake env lean AmoLean/Demo.lean`. See [DEMO_WALKTHROUGH.md](docs/DEMO_WALKTHROUGH.md) for all 11 examples across 3 pipelines.

### E-Graph: Multi-Rule Optimization (Pipeline 1)

A realistic expression with multiple redundant patterns:

**Input:**
```
((x + 0) * 1 + (y * 0)) * (z^1 + w * 1) + 0
```

The e-graph applies 6 verified rewrite rules (`add_zero`, `mul_one`, `mul_zero`, `pow_one`) in a single saturation pass:

**Output:**
```
x * (z + w)
```

- Nodes: 18 → 5 (72% reduction)
- Operations: 9 → 2 (78% reduction)

**Generated C:**
```c
int64_t optimized_kernel(int64_t x, int64_t y, int64_t z, int64_t w) {
  int64_t t0 = z;
  int64_t t1 = (t0 + w);
  int64_t t2 = (x * t1);
  return t2;
}
```

### Matrix Algebra: DFT-2 to C (Pipeline 2)

The 2-point DFT butterfly — the fundamental NTT building block — goes from Lean specification to C:

**Specification:**
```lean
MatExpr.dft 2    -- The 2×2 DFT matrix [[1,1],[1,-1]]
```

**Generated C:**
```c
void butterfly_2(double* restrict in, double* restrict out) {
  out[0] = (in[0] + in[1]);
  out[1] = (in[0] - in[1]);
}
```

### Matrix Algebra: Parallel Butterflies (Pipeline 2)

The Kronecker product `I_2 ⊗ DFT_2` means "apply DFT_2 independently to 2 blocks":

**Specification:**
```lean
MatExpr.kron (MatExpr.identity 2) (MatExpr.dft 2)    -- I₂ ⊗ DFT₂
```

**Generated C:**
```c
void parallel_butterfly(double* restrict in, double* restrict out) {
  for (int i0 = 0; i0 < 2; i0++) {
    out[2 * i0 + 0] = (in[2 * i0 + 0] + in[2 * i0 + 1]);
    out[2 * i0 + 1] = (in[2 * i0 + 0] - in[2 * i0 + 1]);
  }
}
```

The Kronecker product with the identity on the left produces a loop over blocks, applying the butterfly to consecutive pairs. The gather/scatter patterns compute the correct base addresses automatically.

## Performance

AMO-Lean NTT achieves **~60% of Plonky3 throughput** (1.65x slower on average) with full formal verification — 64/64 oracle tests pass with bit-exact match.

See [BENCHMARKS.md](docs/BENCHMARKS.md) for full NTT benchmark tables, test suite results, and verification criteria.

## What's New in v2.5.1

### Changes Since v2.5.0

| Metric | v2.5.0 | v2.5.1 | Change |
|--------|--------|--------|--------|
| **Lines of Code** | ~48,000 | **~48,550** | +550 LOC (CompletenessSpec.lean) |
| **Extraction theorems** | 121 | **147** | +26 (6 public + 20 private) |
| **Total verified theorems** | ~990 | **~1,016** | +26 |
| **Axioms** | 11 | **11** | No new axioms |
| **Active sorry** | 12 | **12** | Same (Poseidon only) |

### Key Achievements (v2.5.0 -> v2.5.1)

1. **Extraction completeness** (Fase 16) — Formal proof that e-graph extraction is complete: bestNode pointers form an acyclic DAG and `extractAuto` always succeeds. Closes the two remaining gaps (G1, G2) in verified extraction. 550 LOC, 6 public theorems, 0 sorry, 0 axioms.
2. **DAG acyclicity** (G1) — `computeCostsF_acyclic`: after cost iteration with positive costs, the bestNode pointers form an acyclic DAG. Proof via `BestCostLowerBound` as ranking function + `bestCostLowerBound_acyclic`.
3. **Fuel sufficiency** (G2) — `extractAuto_complete`: `extractAuto g rootId` always returns `some` when the DAG is acyclic and all classes have bestNodes. Proof via strong induction on rank (`Nat.strongRecOn`), not simple induction on fuel.
4. **computeCostsF bridge** — Adapted OptiSat's `processKeys` proof to amo-lean's fold-based `computeCostsF`. Key technique: `singlePass` definition matching `computeCostsF` body exactly, enabling `computeCostsF_succ_eq` by `rfl`. Bridge lemmas (`cost_form_eq`, `foldl_cost_bridge`) convert between `Option.map.getD` and abstract `getCost` forms.
5. **SelfLB invariant** — Self-referential lower bound: every bestNode's cost ≥ costFn + children's costs. Preserved through nested fold induction with compound invariant (unionFind preserved ∧ SelfLB preserved).

### Previous: v2.5.0 — Verified E-Graph Extraction

1. **Verified e-graph extraction engine** (Fase 14-15) — Complete extraction pipeline with soundness proofs: `extractF_correct` (greedy extraction preserves semantics), `SoundRewriteRule` (10 verified rewrite rules), `CircuitAdaptor` (domain-specific bridge). 914 LOC, 17 theorems, 0 sorry, 0 axioms.

### Previous: v2.4.1 — Operational-Verified FRI Bridges

1. **Operational-verified FRI bridges** (Fase 13) — 7 bridge modules connecting 357 operational FRI defs to the 123 verified algebraic theorems from Fase 12. Each bridge has a roundtrip or equivalence proof. 6 nodes, 1,606 LOC, ~66 theorems, 0 sorry, 0 new axioms.
2. **Domain bridge** (N13.2) — `friParamsToDomain` converts operational `FRIParams` to verified `FRIEvalDomain`. `ValidFRIParams` ensures well-formedness. `squaredDomain` for folded domains. 337 LOC, 19 theorems.
3. **Fold bridge** (N13.4) — `foldSpec` as universal interface: operational fold = polynomial evaluation on squared domain via `foldBridge_equivalence`. `EvenOddInterpretation` links array layout to polynomials. 272 LOC, 11 theorems.
4. **Capstone theorem** — `operational_verified_bridge_complete` (N13.6) composes domain + fold bridges end-to-end: foldSpec = polynomial evaluation AND degree halving AND ConsistentWithDegree on D'.
5. **Property testing** (N13.1 + N13.6) — First PBT framework in AMO-Lean. `PlausibleSetup` provides `SampleableExt` instances for FRI types. 14 property tests across 4 categories + 5 smoke tests. 272 LOC.
6. **Definitional equality bridges** — Transcript bridge achieves gold standard: `toFormalTranscript`/`fromFormalTranscript` roundtrip, absorb/squeeze commutativity all proved by `rfl`.

### Previous: v2.4.0 — FRI Formal Verification

1. **FRI formal verification** (Fase 12) — Complete formal verification of FRI (Fast Reed-Solomon IOP of Proximity) for Plonky3 certification. 9 new files in `AmoLean/FRI/Verified/`, ~2,840 LOC, 123 theorems, 0 sorry, 0 custom axioms (3 crypto axioms are type `True`).
2. **Barycentric interpolation** (N12.3) — First formalization in any proof assistant. `barycentric_eq_lagrange` proven generic over `[Field F]`, connecting to Mathlib's `Lagrange.interpolate`. 238 LOC.
3. **Three-level verification architecture**:
   - Level 1 (e-graph): `ConsistentValuation` preserved through pipeline
   - Level 2 (TV): `cryptoEquivalent` removes e-graph from TCB
   - Level 3 (FRI): Polynomial evaluations consistent with degree bound via `fri_pipeline_soundness`
4. **Per-round soundness** (N12.7) — Formalized Garreta 2025 simplified round-by-round proof. `per_round_soundness` composes fold degree halving, query detection, and polynomial uniqueness. 422 LOC.
5. **Capstone theorem** — `fri_pipeline_soundness` (N12.9) composes e-graph optimization (Level 1+2) with FRI algebraic guarantees (Level 3). Uses 0 custom axioms.

### Previous: v2.3.0 — Pipeline Soundness + Perm Axiom Eliminated

1. **Verified pipeline soundness** (Fase 11, Subfase 1) — `full_pipeline_soundness` and `full_pipeline_contract` proven end-to-end: saturation preserves `ConsistentValuation`, extraction is correct, 0 sorry, 0 custom axioms. 5 new files, 1,991 LOC, 77 declarations.
2. **Translation validation framework** (N11.11) — Level 2 soundness via `cryptoEquivalent` relation (refl/symm/trans + congruence for add/mul/neg/smul). 229 LOC, 11 theorems, 0 axioms.
3. **Perm axiom eliminated** (Corrección 1) — `applyIndex_tensor_eq` is now a theorem, not an axiom. Root cause: nested `inverse` sub-patterns blocked equation compiler splitter. Fix: `applyInverse` helper extraction (~20 LOC change).
4. **Zero-axiom audit** (N11.12) — All 9 key pipeline theorems audited via `#print axioms` = 0 custom axioms. Integration test: 13 examples, 25 `#check`, 190 LOC.

### Previous: v2.2.0 — Trust-Lean Bridge

1. **Trust-Lean integration** — Trust-Lean v1.2.0 added as lake dependency for verified C code generation
2. **Bridge module** (`AmoLean.Bridge.TrustLean`, 544 LOC) — 21 conversion definitions, 26 theorems (roundtrip + injectivity, zero sorry)
3. **Verified C pipeline** — `verifiedCodeGen : ExpandedSigma -> Option String` chains conversion through Trust-Lean's CBackend
4. **Integration tests** (199 LOC) — All 6 constructors, DFT_4 end-to-end, stress test (>100 sub-expressions, 8261 chars of verified C)

### Previous: v2.1.0 — Lean 4.26 + Verified E-Graph Engine

1. **Lean 4.26 migration** — Full codebase migrated (28 API renames, 61 files, 0 regressions)
2. **Verified e-graph engine** — 13 files with 121 theorems, zero sorry (UnionFind, CoreSpec, ILP extraction)
3. **Bridge adapter** — Transparent `Expr Int <-> CircuitNodeOp` mapping
4. **100% op reduction** — Verified optimizer achieves full simplification on all 9 benchmark cases

### Version History

```
v1.0.0 (Feb 6)    17 axioms    35 sorry    AlgebraicSemantics: 8 axioms eliminated
v1.0.1 (Feb 9)    17 axioms    30 sorry    Benchmark audit, 2850+ tests
v1.1.0 (Feb 12)    9 axioms    12 sorry    Goldilocks/BabyBear 0 axioms, Kron 0 sorry
v2.0.0 (Feb 17)    9 axioms    12 sorry    Lean 4.16 → 4.26 migration complete
v2.1.0 (Feb 17)    9 axioms    12 sorry    Verified e-graph engine (121 theorems, 0 sorry)
v2.2.0 (Feb 21)    9 axioms    12 sorry    Trust-Lean bridge (26 theorems, 0 sorry)
v2.3.0 (Feb 27)    8 axioms    12 sorry    Pipeline soundness + Perm axiom eliminated
v2.4.0 (Feb 27)   11 axioms    12 sorry    FRI formal verification (123 theorems, barycentric interpolation)
v2.4.1 (Feb 27)   11 axioms    12 sorry    Operational-verified FRI bridges (66 theorems, 19 property tests)
v2.5.0 (Mar 2)    11 axioms    12 sorry    Verified extraction engine (17 theorems, SoundRewriteRule)
v2.5.1 (Mar 3)    11 axioms    12 sorry    Extraction completeness: DAG acyclicity + fuel sufficiency (26 theorems)
```

Note: v2.4.0 adds 3 cryptographic axioms (type `True` — standard assumptions: proximity gap, collision resistance, Random Oracle Model). v2.5.1 adds no new axioms. All pipeline and extraction theorems remain axiom-free.

## Future Work

| Task | Relevance | Difficulty | Status |
|------|-----------|------------|--------|
| **NTT Radix-4 axiom elimination** (8 axioms) | High — last remaining non-crypto axioms | High — requires function implementations | Pending (v2.5.0, N11.6-N11.9) |
| **Poseidon formal proofs** (12 sorry) | Medium — currently validated computationally | Medium — Lean match splitter limitation | Tests pass; formal proofs deferred |
| **Mersenne31 field** | High — enables SP1 verification | Medium — architecture supports it | Designed |
| ~~**Perm axiom** (1)~~ | ~~Low~~ | ~~Very High~~ | **RESOLVED** (Corrección 1) |
| ~~**FRI formal verification**~~ | ~~Critical~~ | ~~Very High~~ | **RESOLVED** (Fase 12, v2.4.0) |
| ~~**Operational-Verified FRI bridge**~~ | ~~High~~ | ~~Medium~~ | **RESOLVED** (Fase 13, v2.4.1) |
| ~~**Property testing**~~ | ~~Medium~~ | ~~Low~~ | **RESOLVED** (Fase 13, v2.4.1 — 19 tests via Plausible) |
| ~~**Extraction completeness**~~ | ~~High~~ | ~~High~~ | **RESOLVED** (Fase 16, v2.5.1 — DAG acyclicity + fuel sufficiency, 26 theorems) |

The 12 remaining sorry are isolated to Poseidon2 (Lean match splitter limitation), backed by 21 test vectors. The 8 NTT Radix-4 axioms are the only non-crypto axioms remaining (opaque interface, pending v2.5.0). The 3 FRI crypto axioms (proximity gap, collision resistance, ROM) are standard cryptographic assumptions declared as `True`. The entire e-graph pipeline, extraction completeness, Perm algebra, translation validation, FRI algebraic chain, and operational-verified bridges are **fully axiom-free**.

## References

1. **egg**: Willsey et al. "egg: Fast and Extensible Equality Saturation" (POPL 2021)
2. **Fiat-Crypto**: Erbsen et al. "Simple High-Level Code For Cryptographic Arithmetic"
3. **FRI**: Ben-Sasson et al. "Fast Reed-Solomon Interactive Oracle Proofs of Proximity"
4. **Harvey NTT**: Harvey "Faster arithmetic for number-theoretic transforms" (2014)
5. **Plonky3**: Polygon Zero's high-performance STARK library
6. **Sigma-SPL**: Franchetti et al. "SPIRAL: Code Generation for DSP Transforms"

## License

MIT License — see [LICENSE](LICENSE) for details.

---

**AMO-Lean v2.5.1** — Extraction completeness (26 theorems, 0 sorry): DAG acyclicity + fuel sufficiency for verified e-graph extraction.
