# FAQ: Critical Questions About AMO-Lean

**Audience**: Senior Rust developers in ZK/Ethereum with zkVM experience
**Context**: AMO-Lean as a complementary tool for verified cryptographic primitives
**Version**: v1.0.1 (Feb 2026)

---

## Question 1: "If Plonky3 already works and is faster, why do we need this?"

### The question behind the question
Plonky3 has years of development, is battle-tested in production, and AMO-Lean is 1.65x slower. Why invest in something slower?

### Answer

AMO-Lean **does not compete with Plonky3** -- it **complements** it:

**1. Independent verification**
```
Your Plonky3 code --> AMO-Lean oracle tests --> Correctness guarantee
```
When your zkVM processes a $100M transaction, do you trust only tests? AMO-Lean provides a mathematically grounded second opinion. Our 64/64 bit-exact oracle tests confirm Plonky3's NTT produces identical results to our formally verified specification.

**2. Executable specification**
The formally proven theorems in Lean are a **living specification** of what a correct NTT must do. This is documentation that cannot lie and cannot become outdated.

**3. Subtle bug detection**
The 120 pathological vectors (sparse, geometric, boundary, max entropy) are specifically designed to trigger edge cases that standard unit tests miss.

### Performance in context

| Size | AMO-Lean | Plonky3 | Ratio |
|------|----------|---------|-------|
| N=256 | 4.8 us | 3.4 us | 1.39x |
| N=1024 | 23.3 us | 14.6 us | 1.59x |
| N=65536 | 2.50 ms | 1.48 ms | 1.69x |

The 1.65x gap is predominantly due to twiddle factor caching strategy (Plonky3 pre-computes aggressively; AMO-Lean uses a balanced approach to avoid cache thrashing at large sizes).

---

## Question 2: "Why Lean and not Coq, Isabelle, or Rust with Kani/Creusot?"

### The question behind the question
The ZK ecosystem is in Rust. Adding Lean is another dependency, another language, another tool to maintain.

### Answer

**Lean 4 was chosen for specific technical reasons:**

| Criterion | Lean 4 | Coq | Isabelle | Rust+Kani |
|----------|--------|-----|----------|-----------|
| Compiler performance | Fast | Slow | Medium | Fast |
| Metaprogramming | Native | Ltac | ML | Limited |
| Mathematics (Mathlib) | Extensive | Extensive | Extensive | Minimal |
| Code extraction to C | Custom | OCaml | Scala | N/A |

**The key point**: Lean 4 allows writing **executable code** that is also **a proof**. The same code that defines `NTT_recursive` can be executed for testing AND proven equivalent to the specification.

**Rust+Kani** verifies properties of existing code but does not generate code from specifications. They are complementary, not competing tools.

---

## Question 3: "30 sorry statements and 17 axioms -- is that a security hole?"

### The question behind the question
What good is formal verification if it is incomplete? A single `sorry` could hide a critical bug.

### Answer

**Full transparency**. Here is the complete breakdown:

| Classification | Count | Detail |
|----------------|-------|--------|
| **Active** (genuine proof gaps) | **5** | 3 kron bounds in AlgebraicSemantics, 2 Merkle invariants in FRI |
| **Computational** (backed by tests) | **12** | All in Poseidon_Semantics (Lean match splitter limitation) |
| **Deprecated** (superseded code) | **7** | Old Float-based Theorems.lean, replaced by AlgebraicSemantics |
| **Commented out** (inactive) | **6** | Inside `/-...-/` comment blocks |

**What is 100% sorry-free:**
- NTT Core (Butterfly, CooleyTukey, Correctness, LazyButterfly): **0 sorry**
- FRI Folding (FRI_Properties): **0 sorry**
- Matrix/Perm: **0 sorry**
- E-Graph rewrite rules: **0 sorry** (19/20 verified)

**The 5 active sorry** are in the AlgebraicSemantics lowering engine (kron tensor product bounds) and FRI Merkle tree (structural invariants). Neither affects the correctness of generated C code or test results -- they are internal to the verification pipeline.

**Empirical mitigation** for every sorry:
- 64/64 oracle tests vs Plonky3 (bit-exact)
- 120/120 pathological vectors (bit-exact)
- 37/37 Goldilocks field tests with UBSan (0 violations)
- 3M+ FFI calls with 0 errors

**On the 17 axioms**: These are documented facts about number theory (e.g., "p = 2^64 - 2^32 + 1 is prime") and specification axioms for Radix-4. None are in the NTT core proof chain.

See [BENCHMARKS.md](docs/BENCHMARKS.md) for the complete audit.

---

## Question 4: "How do we integrate this with our Rust zkVM without rewriting everything?"

### The question behind the question
We have 100K+ lines of Rust. We are not throwing that away for C code.

### Answer

**Minimally invasive integration at 3 levels:**

**Level 1: External verification (zero code changes)**
```bash
# In CI/CD -- verify your NTT output against AMO-Lean reference
clang -DFIELD_NATIVE -O2 -o oracle_test generated/oracle_test.c
./oracle_test  # 64/64 tests in <1 second
```

**Level 2: Oracle testing (minimal changes)**
```rust
#[cfg(test)]
mod amolean_verification {
    use amolean_ffi::verify_ntt_output;

    #[test]
    fn ntt_matches_amolean() {
        let input = random_goldilocks_vec(1024);
        let our_result = our_ntt(&input);
        assert!(verify_ntt_output(&input, &our_result));
    }
}
```

**Level 3: Drop-in component (for critical modules)**
```rust
use amolean::NttContext;

impl<F: GoldilocksField> CommitmentScheme<F> {
    fn commit(&self, data: &mut [F]) {
        let ctx = NttContext::new(data.len().ilog2() as usize);
        ctx.forward(data);  // FFI overhead: 0.03%
    }
}
```

The FFI overhead is 0.03% (measured: 1.08 ns per call vs 3316 ns for NTT N=256). For context, this means using AMO-Lean's verified NTT adds negligible latency even as a drop-in.

---

## Question 5: "What about other fields? Our zkVM uses BabyBear, not Goldilocks."

### Answer

**Current**: Goldilocks only (p = 2^64 - 2^32 + 1)

**Architecture supports extension** -- the NTT is parametrized over a field typeclass:

```lean
class NTTField (F : Type*) extends Add F, Sub F, Mul F where
  inv : F -> F
  pow : F -> Nat -> F
  -- ...

instance : NTTField Goldilocks := { ... }    -- Implemented
instance : NTTField BabyBear := { ... }      -- Planned
```

| Field | Difficulty | Priority | Notes |
|-------|-----------|----------|-------|
| BabyBear (p = 2^31 - 2^27 + 1) | Medium | High | Used in Risc0, SP1 |
| Mersenne31 (p = 2^31 - 1) | Low | Medium | Trivial reduction |
| BN254 scalar field | High | Low | 256-bit, structurally different |

---

## Question 6: "Who maintains this? What if the project is abandoned?"

### Answer

**Honest risks**: The bus factor is low and there is no large company backing the project.

**Mitigations**:

1. **Self-contained code**: `libamolean/` is header-only C with zero external dependencies. Works without Lean installed.
2. **Exhaustive documentation**: 32K+ lines of progress logs, 24 design decisions, 85+ QA lessons.
3. **Fork-friendly**: MIT License, comprehensive CI pipeline, 2850+ automated tests.

**Worst case**: The project is abandoned, but you keep:
- Working C code you can maintain independently
- Lean specifications as formal documentation
- Full test suite you can continue running

---

## Question 7: "Generated C code, not Rust. How do we know it is memory-safe?"

### Answer

**Multi-layer safety:**

| Layer | Protection | Evidence |
|-------|-----------|---------|
| Compilation | `-Wall -Wextra -Werror` | CI enforced |
| Runtime | UndefinedBehaviorSanitizer | 37 Goldilocks + 4 NTT tests, 0 violations |
| Bounds | Formal verification of ranges | Lean theorems |
| Overflow | `__uint128_t` for intermediates | Edge case tests |
| FFI | Panic safety (catch_unwind + panic=abort) | 3M+ stress calls |

**The generated code is intentionally simple:**
```c
// The entire NTT is ~300 lines of C
// No dynamic malloc in hot path (pre-allocated buffers)
// No function pointers
// No recursion (iterative loop)
```

---

## Question 8: "60% of Plonky3 throughput is not enough for production."

### The question behind the question
In a STARK prover, NTT can be 30-50% of total time. Losing 40% there is significant.

### Answer

**Current performance data** (Feb 2026 benchmark):

| Size | AMO-Lean | Plonky3 | AMO Throughput |
|------|----------|---------|----------------|
| N=256 | 4.8 us | 3.4 us | 53.7 Melem/s |
| N=1024 | 23.3 us | 14.6 us | 44.0 Melem/s |
| N=65536 | 2.50 ms | 1.48 ms | 26.2 Melem/s |

**The gap comes from**:
1. Twiddle caching strategy (Plonky3 pre-computes more aggressively)
2. Radix-2 vs Plonky3's more aggressive optimizations
3. No SIMD for multiplication (validated as slower for Goldilocks on both x86 and ARM)

**Path to better performance:**

| Optimization | Expected Impact | Status |
|-------------|-----------------|--------|
| Radix-4 codegen | +20-30% | Butterfly verified, codegen pending |
| Improved memory scheduling | +5-10% | Research |
| Montgomery form | +10-15% | Requires representation change |
| **Potential total** | **85-95%** | |

**The tradeoff question**: For the full zkVM pipeline, if NTT is 40% of time, the formal verification overhead is ~24% total. If that verification prevents ONE bug in production, what is that worth?

---

## Question 9: "How do 64 oracle tests prove equivalence? An NTT has 2^64 possible inputs."

### Answer

**Multi-layer testing strategy:**

**Layer 1: Structured tests (64 tests)**
For each N in {8, 16, 32, 64, 128, 256, 512, 1024}: sequential, zeros, ones, impulse, max values, random. All bit-exact vs Plonky3.

**Layer 2: Pathological vectors (120 tests)**
Sparse ([p-1, 0, ..., 0, 1]), geometric ([1, w, w^2, ...]), max entropy ([p-1, p-2, ...]), boundary ([0, 1, p-1, p-2, ...]), alternating ([0, p-1, 0, p-1, ...]). All bit-exact.

**Layer 3: Algebraic properties**
Roundtrip (INTT(NTT(x)) = x), butterfly sum (a'+b' = 2a mod p), reduction idempotence. Verified with 1000 random inputs each.

**Layer 4: Stress testing**
1,000,000 FFI iterations, 0 errors, 0 memory leaks, 0 UB.

**Layer 5: Formal verification**
71+ theorems proven in Lean, including butterfly correctness, orthogonality sums, and Cooley-Tukey equivalence. These cover ALL inputs by construction.

---

## Question 10: "Why AMO-Lean vs established tools (Fiat-Crypto, Hacspec, Jasmin)?"

### Answer

**Honest comparison:**

| Tool | Strength | Weakness for zkVMs |
|------|----------|---------------------|
| **Fiat-Crypto** | Proven in production (Chrome/BoringSSL) | Only field arithmetic, not NTT/FRI |
| **Hacspec** | Readable specifications | Does not generate optimized code |
| **Jasmin** | Verified assembly | Very low level, hard to use |
| **AMO-Lean** | Full STARK pipeline (field -> NTT -> FRI -> optimized C) | Newer, less battle-tested |

**AMO-Lean's niche:**

```
Fiat-Crypto: "Verified field arithmetic"
Hacspec:     "Protocol specifications"
Jasmin:      "Verified cryptographic assembly"
AMO-Lean:    "Complete verified pipeline for STARK primitives"
             (field -> NTT -> FRI -> E-Graph optimization -> C code)
```

The proposal is **complementary**, not replacement:

```
Your zkVM (Rust + Plonky3)
       |
       +-- Use Plonky3 for performance
       |
       +-- Use AMO-Lean for:
           +-- Verifying Plonky3 output is correct (64/64 oracle tests)
           +-- Generating regression tests (120 pathological vectors)
           +-- Formal specification (documentation that cannot lie)
           +-- Security audits (2850+ tests, UBSan, FFI stress)
```

---

## Summary: What can you expect from AMO-Lean?

### Today (v1.0.1)

| Capability | For your team |
|-----------|---------------|
| Verified NTT (Goldilocks) | Verify your implementation (64/64 bit-exact) |
| 2850+ tests | Add to your CI pipeline |
| 120 pathological vectors | Find edge cases in any NTT |
| Formal specification | Auditable documentation |
| Poseidon2 BN254 | Hash verification (134K H/s, HorizenLabs-compatible) |
| FRI fold verified | Folding correctness (0 sorry) |

### Next steps

| Improvement | Impact |
|------------|--------|
| BabyBear field | Verify Risc0/SP1 implementations |
| Radix-4 codegen | Close performance gap to ~85% |
| Rust bindings | Native integration without FFI |

---

*Questions? Open an issue on GitHub or contact the team.*
