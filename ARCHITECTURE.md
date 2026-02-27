# AMO-Lean: Architecture

## Current Version: v2.3.0


### Fase 11: Verified Pipeline + Axiom Elimination

**Goal**: Close 5 high-severity gaps from v2.2.0 autopsy. Adapt proven theorems from internal libraries (OptiSat, SuperTensor, ProofKit). Target: **0 custom axioms**, end-to-end pipeline soundness.

| Gap | Severity | Target |
|-----|----------|--------|
| G4 Pipeline E2E soundness | ALTA | `full_pipeline_soundness` with 0 external hypotheses |
| G5 Extraction correctness | ALTA | `extractF_correct` + `extractILP_correct` proven |
| G2 NTT Radix-4 axioms | ALTA | 8 axioms eliminated, constructive proofs |
| G3 Perm axiom | BAJA | 1 axiom eliminated |
| G6 Translation validation | MEDIA | `CryptoEquivalent` framework with congruence |

**Out of scope**: G1 (Poseidon 12 sorry), G7 (1220 uncovered defs).

**Soundness Architecture** (two-level, per QA):
- **Level 1** (N11.1-N11.5): Internal e-graph consistency — saturation + extraction preserve `ConsistentValuation`
- **Level 2** (N11.11): External bridge — `CryptoEquivalent` connects e-graph output to user-facing expression
- **Composition** (N11.12): Level 1 + Level 2 = `verified_optimization_pipeline`

**New files** (7):
- `AmoLean/EGraph/Verified/SemanticSpec.lean` — NodeSemantics + ConsistentValuation
- `AmoLean/EGraph/Verified/SoundRule.lean` — SoundRewriteRule framework
- `AmoLean/EGraph/Verified/SaturationSpec.lean` — Saturation soundness
- `AmoLean/EGraph/Verified/ExtractSpec.lean` — Extraction correctness (greedy)
- `AmoLean/EGraph/Verified/ILPSpec.lean` — ILP extraction + certificate validation
- `AmoLean/EGraph/Verified/PipelineSoundness.lean` — End-to-end composition
- `AmoLean/EGraph/Verified/TranslationValidation.lean` — CryptoEquivalent framework

**Modified files** (4):
- `AmoLean/NTT/Radix4/Butterfly4.lean` — Replace axiom with constructive proof
- `AmoLean/NTT/Radix4/Algorithm.lean` — Replace 5 axioms with proofs
- `AmoLean/NTT/Radix4/Equivalence.lean` — Replace 2 axioms with proofs
- `AmoLean/Matrix/Perm.lean` — Replace axiom with constructive proof

**Test file** (1): `Tests/PipelineSoundnessTest.lean`

**Library adaptation map**:
- OptiSat → N11.1-N11.5 (SemanticSpec, SoundRule, SaturationSpec, ExtractSpec, ILPSpec, PipelineSoundness)
- SuperTensor → N11.6-N11.9 (tiling lemmas, index arithmetic), N11.11 (TranslationValidation)
- ProofKit → N11.2 (foldl patterns), N11.4 (HashMap utilities)

**Lessons applied**: L-457 (pipeline TCB), L-310 (generic typeclasses), L-311 (three-part contract), L-250 (extraction correctness), L-318 (structural homomorphism), L-201 (BabyBear decidable), L-128 (IsWellFormedNTT), L-082 (axiom audit), L-405 (HashMap.fold), L-390 (foldl induction), L-312 (zero sorry gate)

#### DAG (v2.3.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N11.1 CryptoSemanticSpec | FUND | — | done |
| N11.2 ConsistentValuation + Invariant Triple | FUND | N11.1 | done |
| N11.3 SoundRewriteRule + Saturation Soundness | CRIT | N11.2 | done |
| N11.4 Extraction Correctness | CRIT | N11.2 | done |
| N11.5 full_pipeline_soundness | CRIT | N11.3, N11.4 | done |
| N11.6 Butterfly4 Foundation | FUND | — | pending |
| N11.7 NTT_radix4 + Spec Equivalence | CRIT | N11.6 | pending |
| N11.8 INTT_radix4 + Roundtrip Identity | CRIT | N11.6, N11.7 | pending |
| N11.9 Equivalence Proofs | PAR | N11.7, N11.8 | pending |
| N11.10 Perm Axiom Elimination | PAR | — | pending |
| N11.11 Translation Validation Framework | CRIT | — | pending |
| N11.12 Integration + Zero-Axiom Audit | HOJA | N11.5, N11.9, N11.10, N11.11 | pending |

#### Formal Properties (v2.3.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N11.1 | evalOp covers ALL CircuitNodeOp constructors | COMPLETENESS | P0 |
| N11.1 | evalOp_ext: evaluation depends only on children values | SOUNDNESS | P0 |
| N11.1 | evalOp_mapChildren: commutes with child remapping | PRESERVATION | P0 |
| N11.2 | empty_consistent: empty e-graph is vacuously consistent | INVARIANT | P0 |
| N11.2 | add_preserves_cv: adding nodes preserves consistency | PRESERVATION | P0 |
| N11.2 | merge_preserves_cv: merging equivalent classes preserves consistency | PRESERVATION | P0 |
| N11.3 | saturateF_preserves_consistent: saturation with sound rules preserves CV | SOUNDNESS | P0 |
| N11.3 | All 19 rules pass SoundRewriteRule audit (semantic entailment) | SOUNDNESS | P0 |
| N11.4 | extractF_correct: greedy extraction yields correct expressions | SOUNDNESS | P0 |
| N11.4 | extractILP_correct: ILP extraction yields correct expressions | SOUNDNESS | P0 |
| N11.5 | full_pipeline_soundness: zero external hypotheses | SOUNDNESS | P0 |
| N11.6 | butterfly4_orthogonality: DFT-4 invertible (constructive) | EQUIVALENCE | P0 |
| N11.7 | NTT_radix4 matches O(N^2) spec | EQUIVALENCE | P0 |
| N11.8 | INTT_radix4 . NTT_radix4 = identity | EQUIVALENCE | P0 |
| N11.9 | ntt_spec_roundtrip: spec-level roundtrip | EQUIVALENCE | P0 |
| N11.10 | applyIndex_tensor_eq: tensor distributes over pointwise | EQUIVALENCE | P0 |
| N11.11 | CryptoEquivalent is equivalence relation + congruence for all ops | SOUNDNESS | P0 |
| N11.12 | #print axioms shows 0 custom axioms on key theorems | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Detailed Node Specifications

**Subfase 1: Semantic Pipeline Soundness (G4+G5)**

**N11.1 FUNDACIONAL — CryptoSemanticSpec** (~300-500 LOC)
- Define `NodeSemantics` instance for `CircuitNodeOp`
- `evalOp` for all constructors: mkConst, mkAdd, mkMul, mkPow (constant exponent only), mkNeg, mkVar
- Prove `evalOp_ext`: evaluation depends only on children values
- Prove `evalOp_mapChildren`: commutes with child remapping
- **mkPow restriction**: constant integer exponents only (`mkPow (e : EClassId) (n : Nat)`). Variable exponents deferred.
- Adapt from: OptiSat/SemanticSpec + SuperTensor/SemanticSpec
- De-risk: sketch evalOp definition, verify type alignment with existing CircuitNodeOp

**N11.2 FUNDACIONAL — ConsistentValuation + Invariant Triple** (~500-800 LOC)
- Define `ConsistentValuation g env v`: for all reachable nodes, evalOp = valuation at root
- Define `PostMergeInvariant g`: parent pointers valid after merge
- Define `SemanticHashconsInv g env v`: hashcons = semantic node equality
- Prove: `empty_consistent`, `add_preserves_cv`, `merge_preserves_cv`, `find_preserves_cv`, `rebuild_preserves_cv`
- Uses ProofKit foldl patterns (L-390) + HashMap.fold decomposition (L-405)
- Adapt from: OptiSat/SemanticSpec (30 theorems)
- De-risk: verify AMO EGraph field layout matches OptiSat pattern (HashMap Nat EClass, UnionFind)

**N11.3 CRITICO — SoundRewriteRule + Saturation Soundness** (~400-600 LOC)
- Define `SoundRewriteRule` for AMO domain (algebraic + field rules)
- **Precondition audit** (per QA): audit all 19 existing rules for implicit domain conditions (division by zero, field characteristic). Formally prove semantic entailment including side-conditions.
- Wire 19 rules as `SoundRewriteRule` instances
- Prove `saturateF_preserves_consistent` (fuel-based induction, L-311 contract)
- Adapt from: OptiSat/SoundRule + SaturationSpec

**N11.4 CRITICO — Extraction Correctness** (~500-700 LOC)
- Prove `extractF_correct` (greedy: BestNodeInv + fuel induction)
- Prove `extractILP_correct` (ILP: certificate validation via HashMap.fold)
- 4 decomposition theorems: `checkRootActive_sound`, `checkExactlyOne_sound`, `checkChildDeps_sound`, `checkAcyclicity_sound` (DFS with node coloring)
- `validSolution_decompose`: ValidSolution ↔ all 4 checks pass
- L-250: ValidSolution only for termination, not correctness
- Adapt from: OptiSat/ExtractSpec + ILPSpec (13 theorems)

**N11.5 CRITICO — full_pipeline_soundness** (~200-400 LOC)
- Level 1 soundness: compose saturation (N11.3) + extraction (N11.4)
- **Zero external hypotheses** — only structural assumptions on initial e-graph state:
  - `ConsistentValuation g env v`
  - `PostMergeInvariant g`
  - `SemanticHashconsInv g env v`
- Three-part contract (L-311): fuel availability + result semantics + frame preservation
- Adapt from: OptiSat/TranslationValidation + SuperTensor/PipelineSoundness

**Subfase 2: NTT Radix-4 Axiom Elimination (G2)**

**N11.6 FUNDACIONAL — Butterfly4 Foundation** (~400-700 LOC)
- Replace `axiom butterfly4_orthogonality` with constructive proof
- Implement `butterfly4`/`ibutterfly4` as computable functions over field elements
- Prove invertibility using roots of unity properties
- **De-risk strategy**: time-box algebraic approach. If intractable for generic field, use `native_decide` for BabyBear (L-201, 31-bit) + `zpowMod` for Goldilocks as interim, with tech debt ticket.
- Uses: Mathlib ring/field theory, SuperTensor tiling lemmas for index arithmetic

**N11.7 CRITICO — NTT_radix4 + Spec Equivalence** (~500-800 LOC)
- Replace axioms: `NTT_radix4`, `NTT_radix4_eq_spec`, `NTT_radix4_nil_axiom`
- Recursive proof: split into stride-4 sublists, apply butterfly4, combine
- L-128: add `IsWellFormedNTT` preconditions for degenerate cases
- Uses: SuperTensor `tileSplit_sum` for index arithmetic

**N11.8 CRITICO — INTT_radix4 + Roundtrip Identity** (~400-600 LOC)
- Replace axioms: `INTT_radix4`, `INTT_radix4_NTT_radix4_identity`
- Inverse butterfly + normalization factor (1/N in field)
- Uses: butterfly4_orthogonality (N11.6) + NTT structure (N11.7)

**N11.9 PARALELO — Equivalence Proofs** (~200-300 LOC)
- Replace axioms: `ntt_spec_roundtrip`, `intt_radix4_eq_spec_axiom`
- Composition of N11.7 + N11.8 correctness proofs

**Subfase 3: Perm + Translation Validation (G3+G6)**

**N11.10 PARALELO — Perm Axiom Elimination** (~200-400 LOC)
- Replace `axiom applyIndex_tensor_eq` with constructive proof
- Tensor product distributes over pointwise index application
- Induction on list structure + stride decomposition

**N11.11 CRITICO — Translation Validation Framework** (~400-600 LOC)
- Level 2 soundness: connect e-graph output to external representation
- Define `CryptoEquivalent` relation (refl, symm, trans)
- Congruence lemmas for ALL AMO operations (add, mul, neg, pow, ntt, butterfly, kron, perm)
- `ValidatedOptResult` struct connecting e-graph output to expression semantics
- Adapt from: SuperTensor/TranslationValidation (21 congruence theorems)

**N11.12 HOJA — Integration + Zero-Axiom Audit** (~100-200 LOC)
- Composite proof: `verified_optimization_pipeline` = Level 1 (N11.5) + Level 2 (N11.11)
- Integration tests for full pipeline: spec → optimize → extract → validate
- `#print axioms` on all key theorems = 0 custom axioms
- Verify: 9 axioms eliminated (8 Radix-4 + 1 Perm)
- Remaining: only 12 Poseidon sorry (out of scope, documented)
- L-312: zero sorry audit as final gate

#### Bloques

- [x] **B31 Semantic Foundation**: N11.1 (SECUENCIAL) ✓
- [x] **B32 ConsistentValuation**: N11.2 (SECUENCIAL) ✓
- [x] **B33 Saturation + Extraction**: N11.3, N11.4 (PARALELO) ✓
- [x] **B34 Pipeline Composition**: N11.5 (SECUENCIAL) ✓
- [ ] **B35 Butterfly4 Foundation**: N11.6 (SECUENCIAL, de-risk sketch)
- [ ] **B36 NTT Radix-4**: N11.7 (SECUENCIAL)
- [ ] **B37 INTT + Equivalence**: N11.8, N11.9 (SECUENCIAL)
- [ ] **B38 Perm + Translation Validation**: N11.10, N11.11 (PARALELO)
- [ ] **B39 Integration + Audit**: N11.12 (SECUENCIAL)

#### Execution Order

```
Branch A (Pipeline, G4+G5):
  B31 (N11.1 FUND) → B32 (N11.2 FUND) → B33 (N11.3+N11.4 PAR) → B34 (N11.5 CRIT)

Branch B (NTT Radix-4, G2):                    ← independent, parallelizable
  B35 (N11.6 FUND) → B36 (N11.7 CRIT) → B37 (N11.8+N11.9 CRIT+PAR)

Branch C (Perm+TV, G3+G6):                     ← independent, parallelizable
  B38 (N11.10+N11.11 PAR)

Final:
  B39 (N11.12 HOJA) ← depends on B34, B37, B38
```

**Note**: Branches A, B, C are fully independent and can execute in parallel with 2+ workers.

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N11.6 | VERY HIGH | Time-box algebraic proof; fallback to field-specific native_decide |
| N11.7 | VERY HIGH | SuperTensor tiling lemmas for index arithmetic |
| N11.2 | HIGH | Verify EGraph type alignment with OptiSat before starting |
| N11.4 | HIGH | OptiSat HashMap.fold decomposition pattern proven |
| N11.8 | HIGH | Builds on N11.6+N11.7 foundations |
| N11.3 | MEDIUM-HIGH | Precondition audit per QA recommendation |
| N11.11 | MEDIUM-HIGH | SuperTensor TV framework directly adaptable |
| N11.1 | MEDIUM | Clear pattern from OptiSat/SuperTensor |
| N11.5 | MEDIUM | Composition, main work in N11.3+N11.4 |
| N11.10 | MEDIUM | Standalone proof, well-defined target |
| N11.9 | MEDIUM | Follows from N11.7+N11.8 |
| N11.12 | LOW | Mechanical verification |

#### Estimated Metrics

| Metric | Estimate |
|--------|----------|
| New LOC | 4,200-6,600 |
| New files | 7 + 1 test |
| Modified files | 4 |
| New theorems | 80-120 |
| Axioms eliminated | 9 (8 Radix-4 + 1 Perm) |
| Target axioms | 0 custom |

---

## Previous Versions

### v2.2.0

## Project Structure (v2.2.0)

```
amo-lean/
├── AmoLean/                    # Lean source (~41,700 LOC, 97 files)
│   ├── NTT/                    # NTT specification + proofs
│   │   ├── Spec.lean           # O(N^2) reference specification
│   │   ├── CooleyTukey.lean    # O(N log N) verified algorithm
│   │   ├── Butterfly.lean      # Butterfly operation proofs
│   │   ├── LazyButterfly.lean  # Harvey optimization (lazy reduction)
│   │   ├── Correctness.lean    # Main equivalence theorems + INTT roundtrip
│   │   ├── ListFinsetBridge.lean # List<->Finset bridge (0 axioms)
│   │   ├── BabyBear.lean       # BabyBear NTT (0 sorry)
│   │   └── Radix4/             # Verified radix-4 implementation
│   ├── Field/                  # Field implementations (0 axioms, 0 sorry)
│   │   ├── Goldilocks.lean     # Goldilocks (p = 2^64 - 2^32 + 1)
│   │   └── BabyBear.lean       # BabyBear (p = 2^31 - 2^27 + 1)
│   ├── EGraph/                 # E-Graph optimization engine
│   │   ├── Optimize.lean       # Equality saturation (unverified, deprecated)
│   │   ├── VerifiedRules.lean  # 19/20 rules with formal proofs
│   │   └── Verified/           # Verified e-graph engine (121 theorems, 0 sorry)
│   │       ├── UnionFind.lean  # Verified union-find (43 theorems)
│   │       ├── CoreSpec.lean   # Hashcons + merge invariants (78 theorems)
│   │       ├── Bridge.lean     # Expr Int <-> CircuitNodeOp adapter
│   │       ├── Rules.lean      # 10 verified rules wired to Bridge
│   │       └── Optimize.lean   # Verified optimization pipeline
│   ├── FRI/                    # FRI protocol components (0 sorry)
│   ├── Bridge/                 # Trust-Lean bridge (26 theorems, 0 sorry)
│   │   └── TrustLean.lean      # Verified type conversion + roundtrip + pipeline
│   ├── Sigma/                  # Sigma-SPL IR definitions
│   ├── Matrix/                 # Matrix algebra + permutations
│   ├── Verification/           # Correctness proofs
│   │   ├── AlgebraicSemantics.lean  # Lowering correctness (~5,700 LOC, 0 sorry)
│   │   ├── FRI_Properties.lean      # FRI folding proofs (0 sorry)
│   │   └── Poseidon_Semantics.lean  # Poseidon2 verification (12 sorry, test-backed)
│   └── Backends/               # Code generation (C, Rust)
│
├── generated/                  # Generated C code
│   ├── field_goldilocks.h      # Goldilocks arithmetic (scalar)
│   ├── field_goldilocks_avx2.h # Goldilocks arithmetic (AVX2)
│   ├── ntt_kernel.h            # Lazy butterfly kernel
│   ├── ntt_context.h           # NTT context with caching
│   └── poseidon2_bn254_t3.h    # Poseidon2 hash
│
├── libamolean/                 # Distributable header-only C library
├── verification/plonky3/       # Plonky3 verification suite (Rust FFI)
├── Tests/                      # Test suites (2850+ tests)
└── docs/                       # Documentation
    ├── BENCHMARKS.md            # Full benchmark report
    └── project/                 # Design decisions, progress logs
```

---

## Fase 10: Trust-Lean Wiring

**Goal**: Integrar Trust-Lean v1.2.0 como lake dependency de amo-lean. Crear módulo Bridge con conversión de tipos verificada (roundtrip + injectivity) y pipeline end-to-end MatExpr -> ExpandedSigma -> TrustLean.Stmt -> código C via CBackend industrial. Incluye QA follow-ups para cerrar con FULL PASS.

**Files**:
- `lakefile.lean` — Add Trust-Lean dependency
- `AmoLean/Bridge/TrustLean.lean` — Conversion functions + proofs + pipeline (~544 LOC)
- `AmoLean/Tests/TrustLeanIntegration.lean` — Integration test suite + stress test

### DAG (v2.2.0)

| Nodo | Tipo | Deps | Gate | Status |
|------|------|------|------|--------|
| N10.1 Lake Dependency Setup | FUND | — | `lake build` succeeds with `import TrustLean.Bridge`, 0 warnings | done |
| N10.2 Type Conversion + Roundtrip | CRIT | N10.1 | Roundtrip proven, convertScalarVar Option totality, 0 sorry | done |
| N10.3 Integration Tests + Pipeline | PAR | N10.2 | 6 constructors tested, pipeline e2e generates C, semantic equiv | done |
| N10.4 Zero Sorry Audit | HOJA | N10.3 | 0 sorry/admit/axiom in Bridge, full build clean | done |
| N10.5 Forward Roundtrips Intermedios | CRIT | N10.2 | 5 forward theorems proven, 0 sorry | done |
| N10.6 Forward Sigma + Injectivity | CRIT | N10.5 | roundtrip_expandedSigma_forward + convert_injective proven, 0 sorry | done |
| N10.7 Stress Test + Docs | PAR | — | Stress test >100 exprs with roundtrip verification | done |

> Nodes N10.5-N10.7 are QA follow-ups (Corrección 1: CONDITIONAL PASS -> FULL PASS).

### Detailed Node Specifications

**N10.1 FUNDACIONAL — Lake Dependency Setup** (~20 LOC)
- Add `require "trust-lean" from git "../Trust-Lean" @ "v1.2.0"` to lakefile.lean
- Update version to v2.2.0
- Create `AmoLean/Bridge/TrustLean.lean` stub with `import TrustLean.Bridge`
- Verify `lake build` succeeds with 0 errors, 0 warnings
- lean-toolchain compatibility: both projects already at v4.26.0 (verified)

**N10.2 CRITICO — Type Conversion + Roundtrip** (~200 LOC)
- `convertScalarVar : String -> Nat -> Option TrustLean.Bridge.ScalarVar`
  - Maps: "x" -> some (.input, n), "y" -> some (.output, n), "t" -> some (.temp, n)
  - All others -> none
- `convertScalarExpr : AmoLean.ScalarExpr -> Option TrustLean.Bridge.ScalarExpr`
- `convertIdxExpr : AmoLean.IdxExpr -> TrustLean.Bridge.IdxExpr` (direct, no Option needed)
- `convertGather / convertScatter` (direct mapping)
- `convertExpandedKernel : AmoLean.ExpandedKernel -> Option TrustLean.Bridge.ExpandedKernel`
- `convertExpandedSigma : AmoLean.ExpandedSigma -> Option TrustLean.Bridge.ExpandedSigma`
- `convertBack*` for roundtrip (reverse direction, total)
- **Theorems**: roundtrip_correctness, convert_injective, scalarVar_totality_wellformed
- **De-risk**: ScalarVar mapping verified safe — only {"x","y","t"} flow through ExpandedSigma smart constructors

**N10.3 PARALELO — Integration Tests + Pipeline** (~100-150 LOC)
- Test each of 6 ExpandedSigma constructors: nop, scalar, seq, par, loop, temp
- Pipeline function: `verifiedCodeGen : AmoLean.ExpandedSigma -> Option String`
  - Chains: convertExpandedSigma -> expandedSigmaToStmt -> stmtToC
- `#eval` tests generating actual C code
- Semantic equivalence: output of verified pipeline matches expected C structure

**N10.4 HOJA — Zero Sorry Audit**
- `grep -r "sorry\|admit\|axiom" AmoLean/Bridge/` returns empty
- Full `lake build` clean (0 errors, 0 warnings)
- No `native_decide` or `simp [*]` in proofs

**N10.5 CRITICO — Forward Roundtrips Intermedios** (~80 LOC, Corrección 1)
- `roundtrip_scalarExpr_forward`: inducción sobre 6 constructores (var, const, neg, add, sub, mul). Cada binary op requiere `simp only [Option.bind_eq_some]` para extraer sub-hipótesis.
- `roundtrip_scalarAssign_forward`: usa ScalarExpr + ScalarVar forward roundtrips.
- `roundtrip_scalarVarList_forward`: inducción sobre lista.
- `roundtrip_scalarAssignList_forward`: inducción sobre lista.
- `roundtrip_expandedKernel_forward`: compuesto de listas + escalares.

**N10.6 CRITICO — Forward Roundtrip ExpandedSigma + Injectivity** (~50 LOC, Corrección 1)
- `roundtrip_expandedSigma_forward`: inducción sobre 6 constructores (nop, scalar, seq, par, loop, temp).
- `convert_injective`: derivado del forward roundtrip — si `convertExpandedSigma a = convertExpandedSigma b = some x`, entonces `a = convertBack x = b`.

**N10.7 PARALELO — Stress Test + Docs** (~40 LOC, Corrección 1)
- Generador programático: `buildLargeSigma : Nat -> ExpandedSigma` usando `.seq` y `.loop` anidados.
- Verificación: `#eval` confirma `(convertExpandedSigma (buildLargeSigma 120)).isSome = true` + roundtrip check.
- **Note**: The `require TrustLean from "../Trust-Lean"` path dependency is intentional for co-development within the `claudio/` monorepo. For external distribution, convert to git dependency with pinned hash.

### Formal Properties (v2.2.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N10.2 | Roundtrip correctness: convertBack . convertExpandedSigma = id | EQUIVALENCE | P0 |
| N10.2 | Injectivity: conversion preserves distinctness | SOUNDNESS | P0 |
| N10.2 | ScalarVar totality for well-formed names {"x","y","t"} | INVARIANT | P0 |
| N10.3 | Pipeline semantic equivalence: C output matches for converted inputs | PRESERVATION | P1 |
| N10.5 | Forward roundtrip ScalarExpr: convertScalarExpr e = some e' -> convertBackScalarExpr e' = e | EQUIVALENCE | P0 |
| N10.5 | Forward roundtrip ExpandedKernel: same pattern | EQUIVALENCE | P0 |
| N10.6 | Forward roundtrip ExpandedSigma: convertExpandedSigma s = some s' -> convertBackExpandedSigma s' = s | EQUIVALENCE | P0 |
| N10.6 | Injectivity: convertExpandedSigma a = convertExpandedSigma b -> a = b | SOUNDNESS | P0 |
| N10.7 | Stress test: (convertExpandedSigma (buildLargeSigma 120)).isSome = true | INVARIANT | P1 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

### Bloques

- [x] **B24 Lake + Stub**: N10.1 (SECUENCIAL) ✓
- [x] **B25 Conversion Core**: N10.2 (SECUENCIAL) ✓
- [x] **B26 Integration + Pipeline**: N10.3 (SECUENCIAL) ✓
- [x] **B27 Final Audit**: N10.4 (SECUENCIAL) ✓
- [x] **B28 Forward Intermedios**: N10.5 (SECUENCIAL) ✓
- [x] **B29 Forward Sigma + Injectivity**: N10.6 (SECUENCIAL) ✓
- [x] **B30 Stress + Docs**: N10.7 (SECUENCIAL) ✓

### Execution Order

```
B24 (N10.1 FUND) -> B25 (N10.2 CRIT) -> B26 (N10.3 PAR) -> B27 (N10.4 HOJA)
                                       -> B28 (N10.5 CRIT) -> B29 (N10.6 CRIT)
                                          B30 (N10.7 PAR) — paralelo, sin deps
```

---

## Key Design Decisions (v2.3.0)

12. **Two-level soundness architecture**: Level 1 (pipeline soundness) proves internal e-graph consistency. Level 2 (translation validation) bridges e-graph semantics to user expressions. Composition in N11.12 yields `verified_optimization_pipeline`. This separation allows independent development and testing.
13. **Constant-exponent mkPow only**: `mkPow (e : EClassId) (n : Nat)` — variable exponents require non-linear integer arithmetic. Deferred to future version.
14. **Copy/adapt from internal libraries**: OptiSat, SuperTensor, ProofKit theorems copied and adapted (never imported as lake dependency). Each project compiles autonomously.
15. **Butterfly4 de-risk**: Time-boxed algebraic proof with native_decide fallback. BabyBear (31-bit) is natively decidable (L-201). Goldilocks requires zpowMod + Lucas.
16. **Precondition audit for rewrite rules**: All 19 rules explicitly audited for domain conditions (QA recommendation). Division, characteristic, zero handling documented per rule.

## Key Design Decisions (v2.2.0)

1. **Equality Saturation (E-Graphs)**: Optimization via verified rewrite rules rather than ad-hoc transformations. Every optimization is a theorem.
2. **Sigma-SPL Algebraic IR**: Matrix expressions lowered through scatter/gather semantics. 19/19 operations formally verified.
3. **Lazy Reduction (Harvey 2014)**: Defer modular reduction in butterfly operations for reduced modular arithmetic overhead.
4. **Skeleton + Kernel Architecture**: Manual C loop structure (skeleton) with Lean-verified butterfly (kernel). Combines performance control with formal guarantees.
5. **Twiddle Factor Caching**: Pre-computed twiddle factors for all NTT layers, stored in NttContext.
6. **Nat in Lean Proofs**: Use arbitrary-precision naturals to avoid overflow reasoning during proofs. C code uses fixed-width integers with verified bounds.
7. **Goldilocks Specialization**: Exploit p = 2^64 - 2^32 + 1 structure for efficient reduction without Barrett/Montgomery.
8. **Option type for convertScalarVar** (v2.2.0): Since `String` is infinite domain but only {"x","y","t"} are valid ExpandedSigma variable names, `convertScalarVar` returns `Option TrustLean.Bridge.ScalarVar`. Totality proven for well-formed inputs.
9. **Unidirectional Coe only** (v2.2.0): `AmoLean -> TrustLean` coercion only. No bidirectional Coe (causes elaborator loops).
10. **Module isolation** (v2.2.0): Only `AmoLean.Bridge.TrustLean` imports Trust-Lean. Rest of amo-lean never touches Trust-Lean types directly.
11. **Coexistence with legacy codegen** (v2.2.0): `AmoLean/Sigma/CodeGen.lean` (unverified) stays untouched. New verified pipeline is additive.

For detailed rationale on decisions 1-7, see [docs/project/DESIGN_DECISIONS.md](docs/project/DESIGN_DECISIONS.md).

## Verification Status (v2.2.0)

| Component | Status | Sorry | Axioms | Detail |
|-----------|--------|-------|--------|--------|
| NTT Radix-2 (CooleyTukey + INTT roundtrip) | **100%** | 0 | 0 | Fully proven incl. bridge |
| NTT Radix-4 | Interface | 0 | 8 | Opaque functions + properties |
| FRI (Folding + Merkle) | **100%** | 0 | 0 | Fully proven |
| Matrix/Perm | **100%** | 0 | 1 | Match splitter limitation |
| E-Graph Rewrite Rules | **95%** | 0 | 0 | 19/20 rules verified |
| **E-Graph Verified Engine** | **100%** | **0** | **0** | **121 theorems, 4,594 LOC** |
| **Trust-Lean Bridge** | **100%** | **0** | **0** | **26 theorems, 544 LOC, roundtrip + injectivity** |
| Goldilocks Field | **100%** | 0 | 0 | All 5 axioms eliminated |
| BabyBear Field | **100%** | 0 | 0 | All 4 axioms eliminated |
| AlgebraicSemantics | **100%** | 0 | 0 | 19/19 cases proven |
| Poseidon2 | Computational | 12 | 0 | All backed by 21 test vectors |

**Codebase**: ~41,700 LOC | **9 axioms** (8 Radix-4 + 1 Perm) | **12 active sorry** (all Poseidon, match splitter limitation) | **147 verified theorems** (121 e-graph + 26 bridge)

---

## Version History

| Version | Date | Highlights |
|---------|------|------------|
| **v2.3.0** | Feb 2026 | **PLANNED**: Pipeline soundness + axiom elimination (0 custom axioms target) |
| **v2.2.0** | Feb 2026 | Trust-Lean bridge (26 theorems, 0 sorry, roundtrip + injectivity) |
| **v2.1.0** | Feb 2026 | Verified e-graph engine (121 theorems, 0 sorry) |
| **v2.0.0** | Feb 2026 | Lean 4.16 -> 4.26 migration |
| **v1.1.0** | Feb 2026 | FRI verified, Goldilocks/BabyBear 0 axioms |
| **v1.0.0** | Feb 2026 | Initial release: AlgebraicSemantics, 2850+ tests |


- v2.1.0: Lean 4.26 + verified e-graph engine
- v2.0.0: Major restructuring
- v1.1.0: FRI verified
- v1.0.0: Initial release
