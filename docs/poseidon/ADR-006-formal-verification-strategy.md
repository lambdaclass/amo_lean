# ADR-006: Formal Verification Strategy for Poseidon2

**Status**: Accepted
**Date**: 2026-01-27
**Context**: Step 4d - Formal Proof of Equivalence

---

## Problem Statement

We need to prove that the MatExpr representation of Poseidon2 is semantically equivalent to the pure Lean specification:

```lean
theorem poseidon2_correct :
  ∀ input, eval(poseidon2_matexpr input) = poseidon2_spec input
```

### Why This Is Hard

1. **Scale**: 64 rounds × MDS matrices × S-box operations = potential term explosion
2. **Non-linearity**: S-box (x^5) breaks linear algebra simplifications
3. **Modular arithmetic**: SMT solvers handle non-linear mod arithmetic poorly
4. **Dependent types**: Vector indexing creates proof obligations about bounds

---

## Rejected Approaches

### 1. Native Decide / Computational Reflection

**Proposal**: Use `native_decide` to check equality for concrete inputs.

**Why Rejected**:
- Only works for `Decidable` propositions on concrete values
- Cannot prove universal statements (∀ input...)
- BN254 field has ~2^254 elements - cannot enumerate
- Makes Lean compiler part of trusted code base (+30k LOC)

**Source**: [Lean 4 Core documentation](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean)

### 2. Full Proof by Reflection (CPDT-style)

**Proposal**: Write a verified decision procedure that computes proofs.

**Why Rejected**:
- Overkill for this problem
- Requires implementing a verified interpreter
- Simpler compositional approach is sufficient

**Source**: Adam Chlipala, "Certified Programming with Dependent Types", Ch. 15

### 3. Brute-Force Unfolding

**Proposal**: Unfold all definitions and let `simp` solve.

**Why Rejected**:
- 64 rounds unfolded = billions of terms
- Lean kernel will run out of memory
- `simp` will timeout

---

## Chosen Approach: Compositional Verification

### Inspiration Sources

1. **Software Foundations Vol. 2** - Program Equivalence chapter
   - Congruence lemmas: if subterms are equivalent, larger terms are equivalent
   - URL: https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html

2. **CompCert** - Xavier Leroy
   - Simulation diagrams for compiler pass correctness
   - Compositional proofs across 20+ compilation passes
   - URL: https://xavierleroy.org/publi/compcert-CACM.pdf

3. **LeanSSR** - Small Scale Reflection for Lean 4
   - Reflect predicate for computational proofs
   - Integration with Decidable
   - URL: https://arxiv.org/pdf/2403.12733

### Core Principles

1. **Structural Correspondence, Not Computation**
   - Don't ask Lean to compute x^5 mod p
   - Prove that if Spec applies sbox5 and MatExpr applies sbox5, outputs match
   - Reduce "number theory" to "function composition"

2. **Opaque Operations**
   - Treat `sbox5`, `mdsExternal`, `mdsInternal` as black boxes
   - Prove properties about their composition, not their internals
   - Internal correctness was validated in Phase 4b (10,035 test vectors)

3. **Induction Over Structure, Not Size**
   - Don't inductively prove for n=1,2,...,64
   - Prove: "if one round preserves equivalence, fold of rounds preserves equivalence"
   - This gives O(1) proof complexity, not O(64)

---

## Implementation Plan

### Phase A: Semantic Foundations

**Goal**: Define evaluation semantics for MatExpr over `Array Nat`.

**Gap Identified**: Current codebase has no `eval : MatExpr → Array Nat → Array Nat`.
- `Semantics.lean` evaluates `SigmaExpr` (lower IR) with `Float`
- `Spec.lean` is pure functions on `Array Nat`
- `MatExpr.lean` only generates C code

**Deliverable**: `AmoLean/Verification/Poseidon_Semantics.lean`

```lean
structure EvalCtx where
  prime : Nat
  roundConstants : Array (Array Nat)

def evalMatExpr (ctx : EvalCtx) : MatExpr α t 1 → Array Nat → Array Nat
```

**Estimated effort**: ~100 lines
**Risk**: Low

### Phase B: Congruence Lemmas

**Goal**: Prove that each MatExpr constructor evaluates to the corresponding Spec operation.

**Key Lemmas**:
```lean
lemma elemwise_pow5_correct :
  evalMatExpr ctx (.elemwise (.pow 5) e) input =
  (evalMatExpr ctx e input).map (Spec.sbox5 ctx.prime)

lemma mdsApply_external_correct :
  evalMatExpr ctx (.mdsApply "MDS_EXT" t e) input =
  Spec.mdsExternal ctx.prime (evalMatExpr ctx e input)

lemma addRoundConst_correct :
  evalMatExpr ctx (.addRoundConst r t e) input =
  Spec.addRoundConstants ctx.prime (ctx.roundConstants.get! r) (evalMatExpr ctx e input)

lemma partialElemwise_correct :
  evalMatExpr ctx (.partialElemwise 0 (.pow 5) e) input =
  Spec.sboxPartial ctx.prime 5 (evalMatExpr ctx e input)
```

**Estimated effort**: ~200 lines
**Risk**: Medium (Array indexing may require auxiliary lemmas)

### Phase C: Round Equivalence

**Goal**: Prove that MatExpr round functions equal Spec round functions.

**Key Theorems**:
```lean
theorem fullRound_equiv (ctx : EvalCtx) (round : Nat) (input : Array Nat) :
  evalMatExpr ctx (mkFullRound config round inputExpr) input =
  Spec.fullRound params round input

theorem partialRound_equiv (ctx : EvalCtx) (round : Nat) (input : Array Nat) :
  evalMatExpr ctx (mkPartialRound config round inputExpr) input =
  Spec.partialRound params round input
```

**Approach**: Compose Phase B lemmas with `simp`.

**Estimated effort**: ~50 lines
**Risk**: Low (follows from Phase B)

### Phase D: Main Theorem

**Goal**: Prove complete permutation equivalence.

**Key Theorem**:
```lean
theorem poseidon2_correct (ctx : EvalCtx) (config : PoseidonConfig) (input : Array Nat) :
  evalMatExpr ctx (buildPermutation config) input =
  Spec.poseidon2Permutation params input
```

**Approach**:
1. Express permutation as `foldl` over rounds
2. Use `foldl_equiv` lemma: if `f ≡ g` then `foldl f ≡ foldl g`
3. Apply Phase C theorems for each round type

**Estimated effort**: ~30 lines
**Risk**: Very low (if Phases B and C complete)

---

## Risk Analysis

### Known Risks

| Risk | Mitigation |
|------|------------|
| Array indexing proofs | Define helper lemmas for `get!`/`set!` |
| Modular arithmetic identities | Use `omega` where applicable, manual proofs otherwise |
| Term size in `simp` | Configure `simp only [...]` to prevent expansion |
| Heterogeneous equality | Avoid by keeping types simple (Array Nat) |

### Potential `sorry` Locations

1. **Array bounds**: `arr.get! i` when `i < arr.size` needs proof
2. **Modular arithmetic**: `((a + b) % p + c) % p = (a + b + c) % p`
3. **MDS linearity**: Properties of matrix-vector multiplication

### Exit Criteria Per Phase

| Phase | Criteria |
|-------|----------|
| A | `evalMatExpr` compiles, basic `#eval` tests pass |
| B | All congruence lemmas compile (with or without sorry) |
| C | Round equivalence compiles, example inputs verified |
| D | Main theorem compiles, overall sorry count documented |

---

## Verification Checklist

After each phase:

- [ ] Code compiles without errors
- [ ] `#check` on main definitions is instantaneous (<100ms)
- [ ] No excessive memory usage during elaboration
- [ ] `sorry` count documented
- [ ] Example computations match Spec.lean output

---

## References

1. Pierce et al., "Software Foundations Vol. 2: Programming Language Foundations"
   - Chapter: Equiv (Program Equivalence)
   - https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html

2. Xavier Leroy, "Formal verification of a realistic compiler"
   - Communications of the ACM, 2009
   - https://xavierleroy.org/publi/compcert-CACM.pdf

3. Adam Chlipala, "Certified Programming with Dependent Types"
   - MIT Press, 2013
   - http://adam.chlipala.net/cpdt/

4. Gladshtein et al., "Small Scale Reflection for the Working Lean User"
   - arXiv:2403.12733, 2024
   - https://arxiv.org/pdf/2403.12733

5. Seul Baek, "Reflected Decision Procedures in Lean"
   - CMU MS Thesis, 2019
   - https://www.andrew.cmu.edu/user/avigad/Students/baek_ms_thesis.pdf

---

*Last updated: 2026-01-27*
