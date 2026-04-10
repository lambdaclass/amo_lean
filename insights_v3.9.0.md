# Insights v3.9.0 — Goldilocks NTT

Collected during planning phase from 5 research agents (bibliografía, lecciones, expertos, QA, benchmark-qa).

## Lecciones Críticas

- **L-731**: Goldilocks (p ~ 1.84e19) exceeds Int64Range — `binOp_agreement` does NOT apply. Use unbounded `evalMicroC` + Solinas two-fold reduction.
- **L-201**: `native_decide` only works for p < 2^32. For Goldilocks, use `zpowMod` + Lucas theorem.
- **L-626**: `evalMicroC_int64` wraps at arithmetic ops (add/mul/sub), not at variable retrieval. Critical for understanding intermediate overflow.
- **L-712**: `WellFormedPat` required for `Pattern.eval` correctness — Nodup on skeleton children IDs. Relevant for ModularRewriteRule (N39.6).
- **L-691**: Reuse UnionFind verification infra from OptiSat/SuperTensor. Grep sibling projects before implementing from scratch.

## Expert Findings (Lean 4)

- **Nat.mul_sub_left_distrib** (Init.Data.Nat.Basic, NO Mathlib needed): closes `hi * (2^32 - 1) = hi * 2^32 - hi` directly. No `omega` needed. Use for N39.5 shift-subtract rule.
- **Nat.div_add_mod**: `n * (m / n) + m % n = m`. Useful for Goldilocks decomposition `x = hi * 2^64 + lo`.
- **ModularRewriteRule strategy**: Stay in `Nat` with `% p` equality. Avoid `ZMod p` (Mathlib dependency, complex API). Soundness proof: `forall x, lhs.eval x % p = rhs.eval x % p`.
- **Adding 7 NeonIntrinsic constructors**: Lean enforces exhaustiveness at compile time. Every `match` breaks — use `lake build` error messages to find incomplete matches. No trick avoids this.

## Bibliografía Relevante

| Paper | Relevance |
|-------|-----------|
| Harvey 2014 (Faster NTT arithmetic) | Redundant representation for word-sized primes |
| van der Hoeven & Lecerf 2024 (Implementing NTTs) | SIMD optimization with NEON support |
| SPIRAL/NTTX (Zhang & Franchetti 2023) | Karatsuba for multi-word multiply, Barrett reduction |
| Fiat-Crypto (Erbsen et al. 2019) | Verified codegen pipeline, Montgomery specialization |
| HACLxN (Polubelova et al. 2020) | Verified ARM NEON + AVX vectorization |
| Skyscraper (Bouvier et al. 2024) | Goldilocks field arithmetic benchmarks |
| E-graph extraction (Goharshady + Sun 2024) | Treewidth-bounded DP extraction, ILP formulations |

## QA Adversarial Findings (Gemini 2 rounds)

### Accepted (incorporated into plan)
1. **Theorem-first for N39.1**: `lowerGoldilocksProductReduce_correct` must be proven BEFORE merge
2. **E-graph bounds for N39.6**: maxNodes:=100000, maxIterations:=10 (prevents Karatsuba blowup)
3. **Statistical thresholds for N39.8**: mean relative error < 5%, P99 < 5 cycles (replaces vague ">2 cycles")
4. **PBT mandate**: SlimCheck or Python hypothesis for N39.1, N39.3, N39.9
5. **Golden vector suite**: version-controlled NTT input/output pairs per field

### Dismissed (with justification)
1. **"Runtime branch in hot loop" (N39.1)**: `if k>32` is evaluated at Lean CODE GENERATION TIME, not in generated C/Rust. The generated code is already specialized per field.
2. **"rfl invariant risk" (N39.8)**: `reductionCostForHW_dynamic` is a SEPARATE function. The `rfl` proof unfolds `reductionCostForHW` (static), which is untouched. The two functions coexist, never interfere.
3. **"Non-determinism in verification" (N39.8)**: The A/B benchmark is for VALIDATING the model against reality. The compiler behavior is deterministic — uses static costs (default) or cached dynamic costs (opt-in). Cache populated from deterministic saturation + extraction.

## Karatsuba Math Clarification (from QA issue)

The identity `phi^2 = phi - 1 (mod p)` is NOT extension-field arithmetic:
- p = 2^64 - 2^32 + 1
- phi = 2^32
- 2^64 = phi^2 ≡ phi - 1 (mod p) because phi^2 - phi + 1 = p ≡ 0 (mod p)
- Therefore: phi^2 ≡ phi - 1 ≡ 2^32 - 1 (mod p)
- This is standard Goldilocks arithmetic used in Plonky2/Plonky3
