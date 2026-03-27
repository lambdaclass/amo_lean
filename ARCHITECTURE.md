# AMO-Lean: Architecture

## Current Version: v2.5.1


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
| N11.10 Perm Axiom Elimination | PAR | — | done ✓ |
| N11.11 Translation Validation Framework | CRIT | — | done ✓ |
| N11.12 Integration + Zero-Axiom Audit | HOJA | N11.5, N11.9, N11.10, N11.11 | done ✓ |

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

**N11.10 PARALELO — Perm Axiom Elimination** (828 LOC) ✓
- `applyIndex_tensor_eq` axiom eliminated via Fase 11 Corrección 1
- Root cause: nested `inverse` sub-patterns blocked equation compiler splitter
- Fix: `applyInverse` helper extraction → flat patterns → 9 equation lemmas generated
- `lean_verify`: 0 axioms on `applyIndex_tensor_eq` and `tensor_compose_pointwise`

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
- [x] **B38 Perm + Translation Validation**: N11.10, N11.11 (PARALELO) ✓
- [x] **B39 Integration + Audit**: N11.12 (SECUENCIAL) ✓

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

### Fase 12: FRI Formal Verification + Barycentric Interpolation (v2.4.0)

**Goal**: Formalize FRI soundness in Lean 4 to certify Plonky3 end-to-end. Novel contribution: first formalization of barycentric interpolation in any proof assistant.

| Gap | Severity | Target |
|-----|----------|--------|
| G8 FRI soundness (prove → verify) | CRITICA | `fri_verifier_soundness` with round-by-round analysis |
| G9 Merkle tree integrity | CRITICA | `merkle_verify_correct` with collision resistance axiom |
| G10 Fold-polynomial equivalence | CRITICA | `fold_degree_halving` via barycentric interpolation |
| G11 Pipeline integration | ALTA | `fri_pipeline_soundness` composing e-graph + FRI |
| G12 Barycentric interpolation | ALTA | `barycentric_eq_lagrange` — **novel contribution** |
| G13 Transcript/Fiat-Shamir | MEDIA | `challenge_binding` under Random Oracle Model |

**Out of scope**: G1 (Poseidon 12 sorry), G2 (NTT Radix-4 8 axioms, deferred to v2.5.0).

**Soundness Architecture** (two-level, same as e-graph pipeline):
- **Level 1** (N12.1-N12.8): Internal FRI soundness — fold correctness, Merkle integrity, verifier rejects invalid proofs
- **Level 2** (N12.9): External bridge — compose FRI with e-graph pipeline via `CryptoEquivalent`
- **Composition**: Level 1 + Level 2 + N11.5 = `fri_pipeline_soundness`

**Documented axioms** (3, all standard cryptographic assumptions):
1. `proximity_gap_rs` — Proximity gap for RS codes (BCIKS20, JACM 2023). Published theorem.
2. `collision_resistant_hash` — Hash function collision resistance. Standard crypto assumption.
3. `random_oracle_model` — Fiat-Shamir in Random Oracle Model. Standard assumption.

**Axiom budget**: max 3 crypto + max 2 engineering (with elimination plan) = 5 total.

**New files** (9, in `AmoLean/FRI/Verified/`):
- `FRISemanticSpec.lean` — Formal types, evaluation domains, round state, invariants
- `FieldBridge.lean` — AMO-Lean FieldConfig ↔ Mathlib Polynomial via ZMod
- `BarycentricInterpolation.lean` — **Novel**: barycentric interpolation formalization
- `FoldSoundness.lean` — Fold degree preservation via barycentric evaluation
- `MerkleSpec.lean` — Merkle tree integrity, proof validity
- `TranscriptSpec.lean` — Transcript determinism, Fiat-Shamir binding
- `PerRoundSoundness.lean` — Garreta 2025 state function, per-round error bound
- `VerifierComposition.lean` — Multi-round composition, main soundness theorem
- `FRIPipelineIntegration.lean` — Connect FRI to e-graph pipeline

**Reference projects** (study architecture, write own code — no imports, no copies):
- ZkLinalg (Math Inc.) — FRI soundness theorem patterns
- ArkLib/ArkLibFri (Nethermind) — SplitFold, RoundConsistency architecture
- VCVio (Verified-zkEVM) — Fiat-Shamir formalization patterns
- risc0-lean4 (RISC Zero) — Merkle tree operations reference

**Reference papers**:
- Garreta, Mohnblatt, Wagner (2025) — "Simplified Round-by-round Soundness Proof of FRI" (ePrint 2025/1993)
- Ben-Sasson, Carmon, Ishai, Kopparty, Saraf (2020) — "Proximity Gaps for RS Codes" (BCIKS20, JACM 2023)
- Attema, Fehr, Klooss (2023) — "Fiat-Shamir Security of FRI" (ePrint 2023/1071)

**Lessons applied**: L-311 (three-part contract), L-390 (foldl induction), L-222 (PostFoldInvariant), L-329 (bridge decomposition), L-359 (roundtrip), L-351 (no example-based verification), L-457 (TCB hypotheses), L-401 (invariant strengthening), L-478 (equation compiler), L-312 (zero sorry gate)

#### DAG (v2.4.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N12.1 FRISemanticSpec | FUND | — | ✓ (447 LOC, 7T 11D 3ax, 0 sorry) |
| N12.2 FieldBridge | FUND | N12.1 | ✓ (266 LOC, 11T 4D 0ax, 0 sorry) |
| N12.3 BarycentricInterpolation | CRIT | N12.2 | ✓ (238 LOC, 11T 2D 0ax, 0 sorry) |
| N12.4 FoldSoundness | FUND | N12.2, N12.3 | ✓ (364 LOC, 21T 0D 0ax, 0 sorry) |
| N12.5 MerkleSpec | PAR | N12.1 | ✓ (258 LOC, 13T 9D 0ax, 0 sorry) |
| N12.6 TranscriptSpec | PAR | N12.1 | ✓ (279 LOC, 17T 6D 0ax, 0 sorry) |
| N12.7 PerRoundSoundness | CRIT | N12.4, N12.5, N12.6 | ✓ (422 LOC, 25T 2D 0ax, 0 sorry) |
| N12.8 VerifierComposition | CRIT | N12.7 | ✓ (317 LOC, 10T 1D 0ax, 0 sorry) |
| N12.9 FRIPipelineIntegration | HOJA | N12.8, N11.5 | ✓ (249 LOC, 8T 1D 0ax, 0 sorry) |

#### Formal Properties (v2.4.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N12.1 | FRIEvalDomain has correct size and generator | INVARIANT | P0 |
| N12.1 | FRIRoundInvariant is decidable for concrete instances | COMPLETENESS | P1 |
| N12.2 | evaluation at domain points equals Polynomial.eval | EQUIVALENCE | P0 |
| N12.2 | degree bound via root counting matches natDegree | EQUIVALENCE | P0 |
| N12.3 | barycentric_eq_lagrange: barycentric = Lagrange (all fields) | EQUIVALENCE | P0 |
| N12.3 | barycentric_eval_correct: correct evaluation at all points | SOUNDNESS | P0 |
| N12.3 | barycentric_degree_bound: result has correct degree | INVARIANT | P0 |
| N12.4 | fold_degree_halving: fold reduces natDegree by half | SOUNDNESS | P0 |
| N12.4 | fold_eval_correct: fold evaluation matches specification | SOUNDNESS | P0 |
| N12.4 | fold_composition_sound: n-fold preserves soundness | PRESERVATION | P0 |
| N12.5 | merkle_verify_correct: valid proof ↔ correct leaf | SOUNDNESS | P0 |
| N12.5 | merkle_root_deterministic: same leaves → same root | INVARIANT | P0 |
| N12.6 | transcript_deterministic: same inputs → same challenges | INVARIANT | P0 |
| N12.6 | challenge_binding: committed data determines challenges | SOUNDNESS | P0 |
| N12.7 | round_error_bound: per-round error ≤ ε (Garreta) | SOUNDNESS | P0 |
| N12.7 | query_soundness: queries catch cheating (card_roots_le_degree) | SOUNDNESS | P0 |
| N12.8 | fri_algebraic_guarantees: degree halving + root counting + uniqueness | SOUNDNESS | P0 |
| N12.8 | fri_single_round_correct: completeness + soundness + uniqueness | SOUNDNESS | P1 |
| N12.9 | fri_pipeline_soundness: e-graph + FRI = verified pipeline | SOUNDNESS | P0 |
| N12.9 | #print axioms = exactly 3 documented crypto axioms | SOUNDNESS | P0 |

#### Detailed Node Specifications

**Subfase 1: Foundation + Bridge**

**N12.1 FUNDACIONAL — FRISemanticSpec** (~300-400 LOC)
- Define `FRIEvalDomain F n`: evaluation domain as subgroup generated by primitive 2^n-th root of unity
- Define `FRIRoundState F`: (polynomial representation, domain, commitment, challenge)
- Define `FRIRoundInvariant`: degree bound + domain consistency + commitment validity
- Define `FRIFoldSpec F`: abstract fold operation specification
- Define `FRIConfig`: blowup factor, query count, round count, security parameter
- Properties: `domain_size_correct`, `domain_squaring` (omega^2 generates next domain)
- Mathlib: `IsPrimitiveRoot`, `rootsOfUnity`, `Polynomial`
- Generic over `[Field F]` where mathematically sound
- De-risk: verify IsPrimitiveRoot API covers domain squaring property

**N12.2 FUNDACIONAL — FieldBridge** (~400-600 LOC)
- Bridge `FieldConfig`/`FRIField` (UInt64-based) to Mathlib `Field` + `Polynomial` via `ZMod p`
- `evaluation_coefficient_duality`: evaluation at domain points ↔ polynomial coefficients
- `degree_bound_via_roots`: degree connects to root counting
- `field_char_correct`: characteristic matches field spec
- Risk (L-015): `ring` timeout on large `ZMod`. Mitigation: custom `@[simp]` lemmas, `calc` steps
- Test both BabyBear (p = 2^31 - 2^27 + 1) and Goldilocks (p = 2^64 - 2^32 + 1)
- If bridge too complex: axiomatize `eval_coeff_duality` as engineering axiom (with elimination plan)
- De-risk: MANDATORY sketch before N12.3/N12.4 begin

**Subfase 2: Barycentric Interpolation (Novel Contribution)**

**N12.3 CRITICO — BarycentricInterpolation** (~350-500 LOC) ⭐ NOVEL
- **First formalization of barycentric interpolation in any proof assistant**
- Define `barycentricWeights`: weights for arbitrary distinct points
- Define `barycentricInterp`: first and second barycentric form
- Prove `barycentric_eq_lagrange`: equivalence with Mathlib's `Lagrange.interpolate`
- Prove `barycentric_eval_correct`: correct evaluation at all points
- Prove `barycentric_degree_bound`: result polynomial has correct natDegree
- Prove `barycentric_unique`: uniqueness of interpolating polynomial
- ALL theorems generic over `[Field F]` — no field-specific assumptions
- Mathlib-PR-ready: naming conventions, module docstring, reusable API
- Reference: Berrut & Trefethen (2004) "Barycentric Lagrange Interpolation"
- Firewall: develop in `_aux` first, migrate when complete

**Subfase 3: Fold Soundness**

**N12.4 FUNDACIONAL — FoldSoundness** (~500-700 LOC)
- `fold_degree_halving`: fold reduces natDegree by half (key theorem)
- `fold_eval_correct`: fold evaluation matches specification via barycentric (N12.3)
- `fold_composition_sound`: n-fold composition preserves proximity
- `fold_preserves_invariant`: FRIRoundInvariant preserved through fold
- Uses N12.2 (FieldBridge) for polynomial reasoning
- Uses N12.3 (barycentric) for evaluation correctness
- Fuel-based totality for recursive fold composition (L-311)
- Reference: Garreta 2025 fold analysis, ArkLib SplitFold architecture
- De-risk: time-box fold_degree_halving (3 sessions max). Fallback: axiomatize `fold_preserves_proximity`

**Subfase 4: Commitment + Transcript (parallel)**

**N12.5 PARALELO — MerkleSpec** (~300-400 LOC)
- `MerkleTree` inductive type (Leaf | Node)
- `merkle_root_deterministic`: same leaves → same root
- `merkle_verify_correct`: valid proof ↔ correct leaf value at index
- `merkle_verify_complete`: honest tree passes verification
- `merkle_binding`: collision resistance implies commitment binding
- `axiom collision_resistant_hash` (documented crypto axiom #1)
- Minimal approach: axiomatize collision resistance, prove structural properties
- Reference: risc0-lean4 Merkle operations

**N12.6 PARALELO — TranscriptSpec** (~200-300 LOC)
- Extend existing `TranscriptState` (590 LOC in Transcript.lean)
- `transcript_deterministic`: same inputs → same challenges
- `challenge_binding`: committed data determines challenges
- `challenge_independence`: challenges independent under ROM
- `axiom random_oracle_model` (documented crypto axiom #2)
- Builds on existing `absorb_order_matters` (only real theorem in FRI module)

**Subfase 5: Verifier Soundness**

**N12.7 CRITICO — PerRoundSoundness** (~400-550 LOC)
- `FRIStateFunction`: Garreta 2025 state function per round
- `round_error_bound`: Pr[S(r+1) bad | S(r) good] ≤ ε
- `query_soundness`: queries catch cheating via `Polynomial.card_roots_le_degree`
- `round_soundness`: combines fold + query + proximity gap for single round
- `axiom proximity_gap_rs` (documented crypto axiom #3, BCIKS20 JACM 2023)
- Reference: Garreta 2025 Theorem 3.2
- Firewall: `_aux` approach mandatory

**N12.8 CRITICO — VerifierComposition** (~300-400 LOC)
- `fri_error_composition`: multi-round error via union bound
- `fri_verifier_soundness`: main theorem — far from RS → reject w.h.p.
- `fri_completeness`: close to RS → accept
- Explicit statement of all assumptions (field size, proximity parameter, round count)
- Compose N12.7 iterated over all rounds
- Firewall: `_aux` approach mandatory

**Subfase 6: Integration**

**N12.9 HOJA — FRIPipelineIntegration** (~250-350 LOC)
- `FRIVerifiedResult` struct connecting FRI output to pipeline
- Extend `CryptoEquivalent` for FRI operations
- `fri_pipeline_soundness`: compose e-graph (N11.5) + FRI (N12.8)
- Final axiom audit: `#print axioms` on ALL key theorems = exactly 3 crypto axioms
- Integration tests: compose with `full_pipeline_soundness`
- `lake build` full project: 0 errors

#### Bloques

- [x] **B40 FRI Foundation**: N12.1 ✓ (447 LOC, 7T 11D 3ax, 0 sorry)
- [x] **B41 Field Bridge**: N12.2 ✓ (266 LOC, 11T 4D 0ax, 0 sorry)
- [x] **B42 Barycentric Interpolation**: N12.3 ✓ (238 LOC, 11T 2D 0ax, 0 sorry — NOVEL)
- [x] **B43 Fold Soundness**: N12.4 ✓ (364 LOC, 21T 0D 0ax, 0 sorry)
- [x] **B44 Merkle + Transcript**: N12.5 ✓ (258 LOC), N12.6 ✓ (279 LOC), 0 sorry, 0 axioms
- [x] **B45 Per-Round Soundness**: N12.7 ✓ (422 LOC, 25T 2D 0ax, 0 sorry)
- [x] **B46 Verifier Composition**: N12.8 ✓ (317 LOC, 10T 1D 0ax, 0 sorry)
- [x] **B47 Pipeline Integration + Audit**: N12.9 ✓ (249 LOC, 8T 1D 0ax, 0 sorry)

#### Execution Order

```
Branch A (Core Polynomial — critical path):
  B40 (N12.1 FUND) → B41 (N12.2 FUND) → B42 (N12.3 CRIT) → B43 (N12.4 FUND)

Branch B (Commitment + Transcript — after B40, parallel with B41-B43):
  B44 (N12.5 + N12.6 PAR)

Convergence:
  B45 (N12.7 CRIT) ← B43, B44

Composition:
  B46 (N12.8 CRIT) ← B45

Final:
  B47 (N12.9 HOJA) ← B46
```

**Note**: Branch B can execute in parallel with Branch A blocks B41-B43, since it only depends on B40.

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N12.2 | MUY ALTA | L-015: ring timeout on large ZMod. Custom simp lemmas, calc steps. Fallback: engineering axiom |
| N12.4 | ALTA | fold_degree_halving time-boxed (3 sessions). Fallback: axiomatize fold_preserves_proximity |
| N12.7 | ALTA | Proximity gap as axiom (standard). Garreta simplified proof. card_roots_le_degree in Mathlib |
| N12.3 | MEDIA-ALTA | Novel work, no reference formalization. Lagrange in Mathlib as sanity check |
| N12.8 | MEDIA | Composition of proven pieces. Union bound is standard |
| N12.1 | MEDIA | IsPrimitiveRoot API well-tested. Domain squaring straightforward |
| N12.5 | MEDIA | Collision resistance as standard axiom. Structural proofs are clean |
| N12.9 | MEDIA | Existing pipeline composition patterns from Fase 11 |
| N12.6 | BAJA-MEDIA | Extends existing TranscriptState. ROM is standard |

#### Estimated Metrics

| Metric | Estimate |
|--------|----------|
| New LOC | 3,000-4,200 |
| New files | 9 (in AmoLean/FRI/Verified/) |
| Modified files | 0 |
| New theorems | 97-125 |
| Crypto axioms | 3 (standard, documented) |
| Engineering axioms | 0-2 (with elimination plan) |
| Target sorry | 0 |

---

### Fase 13: Operational-Verified FRI Bridges + Property Testing

**Goal**: Bridge the operational FRI code (4,916 LOC, ~357 defs) with the verified specification (2,844 LOC, 123 theorems) through 5 critical type isomorphisms and function equivalence proofs. Add property-based testing infrastructure via Plausible. First project in the Lean 4 ZK ecosystem to formally bridge operational and verified FRI code.

**Strategy**: Three-layer bridge (proven in Trust-Lean v1.2.0, L-336, L-368):
- Layer 1: Type isomorphisms (roundtrip proofs between operational ↔ verified types)
- Layer 2: Function equivalence (operational function = spec function under bridge)
- Layer 3: Property preservation (invariants transfer across bridge)

**Scope**: 5 critical bridges (NOT all 357 defs — L-275 scope control):
1. Domain: `FRIParams` ↔ `FRIEvalDomain`
2. Transcript: `TranscriptState` ↔ `FormalTranscript`
3. Fold: `friFold` ↔ `foldPolynomial` (HIGHEST VALUE)
4. Merkle: `FlatMerkle` ↔ `MerkleTree` (HIGHEST RISK)
5. Query: in integration node (compose fold + merkle bridges)

**New files** (7):
- `AmoLean/Testing/PlausibleSetup.lean` — Plausible instances + smoke tests
- `AmoLean/FRI/Verified/DomainBridge.lean` — Domain bridge
- `AmoLean/FRI/Verified/TranscriptBridge.lean` — Transcript bridge
- `AmoLean/FRI/Verified/FoldBridge.lean` — Fold bridge
- `AmoLean/FRI/Verified/MerkleBridge.lean` — Merkle bridge
- `AmoLean/FRI/Verified/PropertyTests.lean` — Plausible property tests
- `AmoLean/FRI/Verified/BridgeIntegration.lean` — Integration theorem

**Modified files** (1):
- `lakefile.lean` — Add Plausible dependency

**Lessons applied**: L-336 (bridge architecture type-first), L-368 (roundtrip properties), L-359 (injectivity via forward roundtrip), L-352 (spec connects to impl), L-146 (bridge lemma), L-311 (three-part contract), L-351 (examples ≠ proof), L-138 (never defer foundational), L-339 (rfl not runtime), L-403 (boundary testing), L-415 (proof-carrying data), L-209 (beq_iff_eq bridge)

#### DAG (v2.4.1)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N13.1 Plausible Infrastructure | PAR | — | ✓ done |
| N13.2 Domain Bridge | FUND | — | ✓ done |
| N13.3 Transcript Bridge | PAR | — | ✓ done |
| N13.4 Fold Bridge | CRIT | N13.2 | ✓ done |
| N13.5 Merkle Bridge | CRIT | — | ✓ done |
| N13.6 Property Tests + Integration | HOJA | N13.1, N13.2, N13.3, N13.4, N13.5 | ✓ done |

#### Formal Properties (v2.4.1)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N13.1 | SampleableExt generates values in [0, p) for Goldilocks/BabyBear | INVARIANT | P0 |
| N13.1 | Plausible smoke tests pass (field associativity, commutativity) | SOUNDNESS | P1 |
| N13.2 | friParamsToDomain roundtrip: domainToParams ∘ friParamsToDomain = id | EQUIVALENCE | P0 |
| N13.2 | domainBridge_size: domain size matches FRIParams.domainSize | PRESERVATION | P0 |
| N13.2 | domainBridge_elements_distinct: domain elements are distinct | INVARIANT | P0 |
| N13.3 | transcriptBridge_absorb: absorb commutes with bridge | PRESERVATION | P0 |
| N13.3 | transcriptBridge_squeeze: squeeze commutes with bridge (under ROM) | PRESERVATION | P0 |
| N13.3 | transcriptBridge_deterministic: bridge preserves determinism | SOUNDNESS | P0 |
| N13.4 | foldBridgeEquivalence: evalOnDomain (foldPolynomial pE pO α) D' = friFold evals α | EQUIVALENCE | P0 |
| N13.4 | foldBridge_preserves_degree: operational fold consistent with degree bound | PRESERVATION | P0 |
| N13.4 | foldBridge_composition: bridge commutes with multi-round folding | SOUNDNESS | P1 |
| N13.5 | flatToInductive roundtrip: flatToInductive ∘ inductiveToFlat = id | EQUIVALENCE | P0 |
| N13.5 | merkleBridge_hashPreserving: bridge preserves hash well-formedness | PRESERVATION | P0 |
| N13.5 | merkleBridge_verifyPath: verification path translates correctly | SOUNDNESS | P0 |
| N13.6 | operational_verified_bridge_complete: integration theorem composes all 5 bridges | SOUNDNESS | P0 |
| N13.6 | All ~30 Plausible property tests pass | INVARIANT | P1 |
| N13.6 | Axiom audit: only existing crypto axioms (proximity_gap_rs, collision_resistant_hash, random_oracle_model) | SOUNDNESS | P0 |

> **Nota**: Propiedades en lenguaje natural (intención de diseño).
> Los stubs ejecutables están en BENCHMARKS.md § Formal Properties.

#### Detailed Node Specifications

**N13.1 PAR — Plausible Infrastructure** (~80-120 LOC)
- Add `require plausible from git "https://github.com/leanprover-community/plausible" @ "v0.1.0"` to lakefile.lean
- Create `AmoLean/Testing/PlausibleSetup.lean`:
  - `SampleableExt` instance for `GoldilocksField` (modular reduction in [0, p))
  - `SampleableExt` instance for `BabyBearField` (modular reduction in [0, p))
  - `Arbitrary` instances for simple ADTs: `FRIParams`, `FieldConfig`
  - 3-5 `plausible` tactic smoke tests (field associativity, commutativity)
- Gate: `lake build` succeeds with 0 errors
- Fallback: If Plausible incompatible with Lean 4.26.0, use Mathlib `slim_check` directly

**N13.2 FUND — Domain Bridge** (~150-250 LOC)
- File: `AmoLean/FRI/Verified/DomainBridge.lean`
- `friParamsToDomain`: Converts `FRIParams` + primitive root → `FRIEvalDomain F`
- `domainToParams`: Reverse direction (for roundtrip)
- `domainBridgeWellFormed`: Resulting domain has correct size and injectivity
- `domainBridge_size`: `(friParamsToDomain params ω).size = params.domainSize`
- `domainBridge_elements_distinct`: Elements are distinct powers of ω
- Roundtrip: `domainToParams ∘ friParamsToDomain = id` (when parameters are valid)
- Connects: `FRI/Basic.lean:FRIParams` ↔ `FRI/Verified/FRISemanticSpec.lean:FRIEvalDomain`
- Gate: 0 sorry, `lake build` clean
- De-risk: IsPrimitiveRoot API well-tested from Fase 12

**N13.3 PAR — Transcript Bridge** (~100-200 LOC)
- File: `AmoLean/FRI/Verified/TranscriptBridge.lean`
- `toFormalTranscript : TranscriptState F → FormalTranscript F`
- `fromFormalTranscript : FormalTranscript F → TranscriptState F` (if fields align)
- `transcriptBridge_absorb`: absorbing data commutes with bridge
- `transcriptBridge_squeeze`: squeezing challenges commutes with bridge (under ROM axiom)
- `transcriptBridge_deterministic`: bridge preserves transcript determinism
- Connects: `FRI/Transcript.lean:TranscriptState` ↔ `FRI/Verified/TranscriptSpec.lean:FormalTranscript`
- Gate: 0 sorry, 0 new axioms (uses existing `random_oracle_model`)

**N13.4 CRIT — Fold Bridge** (~200-350 LOC) — HIGHEST VALUE
- File: `AmoLean/FRI/Verified/FoldBridge.lean`
- `foldBridgeEquivalence`: `evalOnDomain (foldPolynomial pE pO α) D' = friFold evals α` (under domain bridge)
- `foldBridge_preserves_degree`: operational fold output is consistent with degree bound
- `foldBridge_composition`: bridge commutes with multi-round folding
- Uses `FieldBridge.evalOnDomain` as intermediate representation
- Connects: `FRI/Fold.lean:friFold` ↔ `FRI/Verified/FoldSoundness.lean:foldPolynomial`
- Firewall: `foldBridgeEquivalence_aux` approach mandatory
- Gate: 0 sorry, 0 new axioms
- Risk: ALTA — Vec ↔ Polynomial type mismatch requires careful evalOnDomain threading

**N13.5 CRIT — Merkle Bridge** (~300-450 LOC) — HIGHEST RISK
- File: `AmoLean/FRI/Verified/MerkleBridge.lean`
- Staged proof strategy (per QA):
  1. Define `pathToFlatIndex` and `flatIndexToPath` helper functions
  2. Prove inversion: `pathToFlatIndex ∘ flatIndexToPath = id` and vice-versa
  3. Prove semantic correctness: parent/sibling index preservation
  4. Build `flatToInductive` / `inductiveToFlat` on proven helpers
- `merkleBridge_hashPreserving`: bridge preserves hash well-formedness
- `merkleBridge_verifyPath`: verification path translates correctly
- Connects: `FRI/Merkle.lean:FlatMerkle` ↔ `FRI/Verified/MerkleSpec.lean:MerkleTree`
- Firewall: `flatToInductive_aux` approach mandatory
- Gate: 0 sorry, 0 new axioms. If index arithmetic intractable after 3 sessions, confine axiom to index mapping ONLY (not hash or tree logic)
- Risk: MUY ALTA — flat array index arithmetic is complex

**N13.6 HOJA — Property Tests + Integration** (~200-300 LOC)
- Files: `AmoLean/FRI/Verified/PropertyTests.lean` + `AmoLean/FRI/Verified/BridgeIntegration.lean`
- ~30 Plausible property tests across 3 categories:
  - Field arithmetic (5): roundtrip, associativity, commutativity for Goldilocks/BabyBear
  - FRI operational (15): fold size halving, Merkle path length, transcript determinism, domain size
  - Bridge roundtrips (10): domain↔, transcript↔, fold↔, merkle↔
- Integration theorem: `operational_verified_bridge_complete`
  - Chains all 5 bridges: operational FRI code + valid parameters → verified guarantees hold
  - Connects `fri_pipeline_soundness` (Fase 12) with operational code via bridges
- Query verification bridge: compose fold bridge + merkle bridge to show `verifyFoldQuery` matches spec
- Final axiom audit: `#print axioms` on all bridge theorems
- Gate: all properties pass, 0 sorry, `lake build` clean
- Each Plausible property must correspond to or be derivable from a formal theorem

#### Bloques

- [x] **B48 Domain Bridge**: N13.2 (FUND, SEQUENTIAL) ✓
- [x] **B49 Plausible + Transcript**: N13.1 + N13.3 (PAR, AGENT_TEAM) ✓
- [x] **B50 Fold Bridge**: N13.4 (CRIT, SEQUENTIAL + FIREWALL) ✓
- [x] **B51 Merkle Bridge**: N13.5 (CRIT, SEQUENTIAL + FIREWALL) ✓
- [x] **B52 Properties + Integration**: N13.6 (HOJA, SEQUENTIAL) ✓

#### Execution Order

```
Branch A (Critical Path):
  B48 (N13.2 FUND) → B50 (N13.4 CRIT) → B52 (N13.6 HOJA)

Branch B (Parallel, independent):
  B49 (N13.1 + N13.3 PAR) → B52

Branch C (Independent, highest risk):
  B51 (N13.5 CRIT) → B52
```

Recommended order: B48 → B50 → B49 → B51 → B52
- B48 first: unblocks B50 (fold bridge needs domain bridge)
- B50 second: highest value bridge, on critical path
- B49 third: parallel block, independent of B48/B50
- B51 fourth: highest risk, time-boxed with staged strategy
- B52 last: integrates all bridges + properties

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N13.5 | MUY ALTA | Staged proof strategy (index helpers → inversion → bridge). Time-box 3 sessions. Axiom confined to index mapping if needed. |
| N13.4 | ALTA | evalOnDomain as intermediate. FieldBridge (N12.2) provides infrastructure. Firewall `_aux`. |
| N13.1 | MEDIA | Plausible v0.1.0 on Lean 4.26.0. Fallback: Mathlib slim_check. |
| N13.2 | MEDIA | IsPrimitiveRoot API proven in Fase 12. FRIEvalDomain structure well-understood. |
| N13.3 | BAJA-MEDIA | TranscriptState fields should map to FormalTranscript. ROM axiom covers hash semantics. |
| N13.6 | BAJA | Composition of proven pieces. Standard integration pattern from Fase 12 capstone. |

#### Estimated Metrics

| Metric | Estimate |
|--------|----------|
| New LOC | 1,000-1,500 |
| New files | 7 |
| Modified files | 1 (lakefile.lean) |
| New theorems | 40-60 |
| New axioms | 0 (target), 0-1 (Merkle fallback, confined) |
| Target sorry | 0 |
| Plausible properties | ~30 |

### Fase 14: Bridge Correctness — Expr Int ↔ CircuitNodeOp Soundness (v2.4.2)

**Goal**: Formalize that the translation from `Expr Int` patterns to `CircuitNodeOp` `RewriteRule`s (via `Bridge.mkRule`) preserves semantics. Create `SoundRewriteRule` instances for the 10 bridgeable rules (excluding 4 power rules — `CircuitNodeOp` has no `powGate`). Connect the 20 algebraic theorems in `VerifiedRules.lean` to the verified e-graph engine's `SoundRewriteRule` framework.

**Strategy**: 4-level bridge (from insights investigation):
1. **Level 0** (EXISTS): 20 algebraic theorems in `VerifiedRules.lean` (all proven, 0 sorry)
2. **Level 1** (NEW): `exprCircuitEval` — bridge evaluator mapping `VerifiedRules.eval` to `CircuitEnv`-based evaluation
3. **Level 2** (NEW): 10 `SoundRewriteRule (Expr Int) Int` instances with 1-line soundness proofs
4. **Level 3** (NEW): Master theorem connecting all sound rules to the pipeline's `PreservesCV` framework

**Scope**: 10 of 20 rules bridgeable (the 10 in `Rules.lean`). 4 power rules excluded by design (`CircuitNodeOp` has no `powGate` — circuits use repeated multiplication). 6 structural rules (assoc/comm/const-fold) excluded by design (not in `Rules.lean`).

#### DAG

```
N14.1 (FUND) ─→ N14.2 (CRIT) ─→ N14.3 (HOJA)
```

**N14.1 FUNDACIONAL — ExprCircuitEval Bridge Evaluator** (~60 LOC)
- `exprCircuitEval : Expr Int → CircuitEnv Int → Int` = `VerifiedRules.eval (fun v => env.witnessVal v) e`
- Unfolding lemmas: `exprCircuitEval_const`, `exprCircuitEval_var`, `exprCircuitEval_add`, `exprCircuitEval_mul`
- Key insight: `witnessVal` maps variable indices to field values, bridging `VarId → Int` and `CircuitEnv Int`
- File: `AmoLean/EGraph/Verified/BridgeCorrectness.lean`

**N14.2 CRÍTICO — SoundRewriteRule Instances** (~120 LOC)
- 10 instances: `addZeroRight_sound`, `addZeroLeft_sound`, `mulOneRight_sound`, `mulOneLeft_sound`, `mulZeroRight_sound`, `mulZeroLeft_sound`, `distribLeft_sound`, `distribRight_sound`, `factorRight_sound`, `factorLeft_sound`
- Each soundness proof is a 1-line application of existing `*_correct` theorem from `VerifiedRules.lean`
- Pattern: `fun env vars => theorem_correct (fun v => env.witnessVal v) (vars 0) ...`
- Reuses `exprCircuitEval` as the `eval` field and `mkRule` patterns as the `rule` field

**N14.3 HOJA — Pipeline Integration + Master Theorem** (~70 LOC)
- `allSoundRules : List (SoundRewriteRule (Expr Int) Int)` — collection of all 10 sound rules
- `allSoundRules_sound`: every rule in the collection satisfies `soundness`
- 10 individual `*_rule_eq` theorems: each `sound.rule = Rules.namedRule` (7 by `rfl`, 3 by `unfold+rfl`)
- `bridge_complete`: `Rules.allRules.length = allSoundRules.length := rfl`
- Axiom census: 0 custom axioms in entire module
- Note: single `bridge_rules_match` theorem replaced by decomposed individual proofs (simpler, kernel reduction limits on complex patterns)

#### Formal Properties (v2.4.2)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N14.1 | exprCircuitEval preserves evaluation: `exprCircuitEval e env = VerifiedRules.eval (fun v => env.witnessVal v) e` | EQUIVALENCE | P0 |
| N14.1 | Unfolding for add: `exprCircuitEval (.add a b) env = exprCircuitEval a env + exprCircuitEval b env` | PRESERVATION | P0 |
| N14.2 | Each SoundRewriteRule has eval = exprCircuitEval | INVARIANT | P0 |
| N14.2 | Each soundness proof follows from *_correct theorem | SOUNDNESS | P0 |
| N14.3 | allSoundRules.length = 10 | INVARIANT | P1 |
| N14.3 | allSoundRules rules = Rules.allRules | EQUIVALENCE | P0 |
| N14.3 | Zero custom axioms in BridgeCorrectness.lean | SOUNDNESS | P0 |

#### Bloques

- [x] **B53 ExprCircuitEval**: N14.1 (SECUENCIAL, FUNDACIONAL) ✓
- [x] **B54 SoundRewriteRule Instances**: N14.2 (SECUENCIAL, CRÍTICO) ✓
- [x] **B55 Integration + Master**: N14.3 (SECUENCIAL, HOJA) ✓

#### Execution Order

```
B53 (N14.1 FUND) → B54 (N14.2 CRIT) → B55 (N14.3 HOJA)
```

All sequential: N14.2 depends on `exprCircuitEval`, N14.3 depends on all instances.

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N14.1 | BAJA | Thin wrapper over existing `VerifiedRules.eval`. Definitional equality. |
| N14.2 | MEDIA | Each proof is 1 line, but 10 instances need consistent pattern. Template from SuperTensor `TranslationValidation.lean`. |
| N14.3 | BAJA | Composition of proven pieces. Standard collection + list operations. |

#### Estimated Metrics

| Metric | Estimate |
|--------|----------|
| New LOC | 200-300 |
| New files | 1 |
| Modified files | 0 |
| New theorems | ~25 |
| New axioms | 0 |
| Target sorry | 0 |

### Fase 15: VerifiedExtraction Integration — Generic Greedy Extraction (v2.5.0)

**Goal**: Integrate VerifiedExtraction's generic greedy extraction framework into AMO-Lean. Replace the circuit-specific extraction typeclasses with a parametric framework where `CircuitNodeOp` is an adaptor instance. This gives: (1) generic `extractF_correct` theorem for free, (2) typeclass-based API for future Op types, (3) pathway to ILP/Treewidth DP extraction in future versions.

**Source**: `~/Documents/claudio/VerifiedExtraction/` — 11 files, ~2,756 LOC, 0 sorry, 0 axioms. Core framework: `Core.lean` (352 LOC, NodeOps/NodeSemantics/EGraph/ConsistentValuation) + `Greedy.lean` (213 LOC, Extractable/EvalExpr/ExtractableSound/extractF/extractF_correct).

**Strategy** (5 levels from user spec):
1. **Copy foundation**: Core.lean + Greedy.lean as `AmoLean/EGraph/VerifiedExtraction/{Core,Greedy}.lean`
2. **NodeOps instance**: `children`, `mapChildren`, `replaceChildren` (NEW), `localCost` + 4 laws for `CircuitNodeOp`
3. **NodeSemantics instance**: Reuse existing `evalOp` from `SemanticSpec.lean`
4. **CircuitExpr + Extractable + EvalExpr**: Expression type matching all 7 `CircuitNodeOp` constructors
5. **ExtractableSound proof**: 7-case proof following `arith_extractable_sound` pattern from `Integration.lean`

**Adaptor template**: `VerifiedExtraction/Integration.lean` — `ArithOp` adaptor (3 constructors, ~150 LOC). `CircuitNodeOp` has 7 constructors, so ~2.3x the proof surface.

**Key insight**: AMO-Lean's `ENode.children`, `ENode.mapChildren`, `ENode.localCost` already implement the operations — just need to unwrap from `ENode` to `CircuitNodeOp`. Only `replaceChildren` is truly new.

#### DAG

```
N15.1 (FUND) → N15.2 (CRIT) → N15.3 (CRIT) → N15.4 (HOJA)
```

**N15.1 FUNDACIONAL — Library Foundation** (~550 LOC, 2 new files)
- Copy + namespace-adapt VerifiedExtraction `Core.lean` → `AmoLean/EGraph/VerifiedExtraction/Core.lean`
- Copy + namespace-adapt VerifiedExtraction `Greedy.lean` → `AmoLean/EGraph/VerifiedExtraction/Greedy.lean`
- Namespace: `VerifiedExtraction` → `AmoLean.EGraph.VerifiedExtraction`
- Import adjustments: `VerifiedExtraction.Core` → `AmoLean.EGraph.VerifiedExtraction.Core`
- Generic framework: `NodeOps`, `NodeSemantics`, `EGraph Op`, `ConsistentValuation`, `BestNodeInv`, `Extractable`, `EvalExpr`, `ExtractableSound`, `extractF`, `extractF_correct`
- Must compile: `lake build AmoLean.EGraph.VerifiedExtraction.Greedy`

**N15.2 CRÍTICO — NodeOps + NodeSemantics for CircuitNodeOp** (~250 LOC)
- Define `circuitReplaceChildren : CircuitNodeOp → List EClassId → CircuitNodeOp` (7-case match)
- Instance `NodeOps CircuitNodeOp` with:
  - `children` (from existing `ENode.children` unwrapped)
  - `mapChildren` (from existing `ENode.mapChildren` unwrapped)
  - `replaceChildren` = `circuitReplaceChildren`
  - `localCost` (from existing `ENode.localCost` unwrapped)
  - 4 laws: `mapChildren_children` (7 cases by `cases op <;> simp`), `mapChildren_id` (7 cases), `replaceChildren_children` (7 cases, needs `list_length_N` helpers), `replaceChildren_sameShape` (7 cases)
- Instance `NodeSemantics CircuitNodeOp (CircuitEnv Val) Val` with:
  - `evalOp` = existing `SemanticSpec.evalOp`
  - `evalOp_ext` = adapt from existing `evalOp_ext` (change from `ENode` to `CircuitNodeOp`)
- Helper lemmas: `list_length_one`, `list_length_two`
- File: `AmoLean/EGraph/VerifiedExtraction/CircuitAdaptor.lean`

**N15.3 CRÍTICO — CircuitExpr + Extractable + ExtractableSound** (~250 LOC)
- Define `CircuitExpr` inductive:
  - `const (n : Nat)` | `witness (n : Nat)` | `pubInput (n : Nat)` | `add (a b : CircuitExpr)` | `mul (a b : CircuitExpr)` | `neg (a : CircuitExpr)` | `smul (c : Nat) (a : CircuitExpr)`
- Define `CircuitExpr.eval : CircuitExpr → CircuitEnv Val → Val`
- Instance `Extractable CircuitNodeOp CircuitExpr` (7-case `reconstruct`)
- Instance `EvalExpr CircuitExpr (CircuitEnv Val) Val`
- Prove `circuit_extractable_sound : ExtractableSound CircuitNodeOp CircuitExpr (CircuitEnv Val) Val`
  - 7 cases following `arith_extractable_sound` pattern:
    - `constGate`: 0 children, reconstruct to `CircuitExpr.const`, eval = `env.constVal`
    - `witness`: 0 children, reconstruct to `CircuitExpr.witness`, eval = `env.witnessVal`
    - `pubInput`: 0 children, reconstruct to `CircuitExpr.pubInput`, eval = `env.pubInputVal`
    - `addGate`: 2 children, `list_length_two`, eval = `v a + v b`
    - `mulGate`: 2 children, `list_length_two`, eval = `v a * v b`
    - `negGate`: 1 child, `list_length_one`, eval = `-(v a)`
    - `smulGate`: 1 child, `list_length_one`, eval = `env.constVal c * v a`
- File: `AmoLean/EGraph/VerifiedExtraction/CircuitAdaptor.lean` (same file as N15.2)

**N15.4 HOJA — Integration + End-to-End** (~200 LOC)
- Instantiate `extractF_correct` for `CircuitNodeOp` / `CircuitExpr` / `CircuitEnv Val` / `Val`
- Structured test suite:
  1. **Unit**: smoke test per constructor (empty graph, single-node per op type)
  2. **Edge cases**: `smulGate` with scalar 0/1, `addGate` with `constGate 0`, `negGate` chain
  3. **DAG sharing**: 2 nodes sharing a child → extraction handles deduplication
  4. **Evaluation equivalence**: `CircuitExpr.eval` matches `evalOp` for constructed examples
- `#print axioms` audit on `circuit_extractable_sound` and `extractF_correct` instantiation
- Namespace safety: verify `open AmoLean.EGraph.VerifiedExtraction` and `open AmoLean.EGraph.Verified` coexist without collision
- File: `AmoLean/EGraph/VerifiedExtraction/Integration.lean`

#### Formal Properties (v2.5.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N15.1 | Core.lean + Greedy.lean compile with 0 errors, 0 sorry | INVARIANT | P0 |
| N15.1 | extractF_correct theorem available for any Op satisfying typeclasses | SOUNDNESS | P0 |
| N15.2 | NodeOps CircuitNodeOp satisfies all 4 laws | SOUNDNESS | P0 |
| N15.2 | NodeSemantics.evalOp = existing SemanticSpec.evalOp | EQUIVALENCE | P0 |
| N15.2 | evalOp_ext proven for CircuitNodeOp (7 constructors) | PRESERVATION | P0 |
| N15.3 | CircuitExpr.eval covers all 7 constructors | COMPLETENESS | P0 |
| N15.3 | ExtractableSound for CircuitNodeOp proven (7 cases, 0 sorry) | SOUNDNESS | P0 |
| N15.4 | extractF_correct instantiates for CircuitNodeOp with 0 axioms | SOUNDNESS | P0 |
| N15.4 | Generic extraction compatible with existing pipeline | EQUIVALENCE | P1 |

#### Bloques

- [x] **B56 Library Foundation**: N15.1 (SECUENCIAL, FUNDACIONAL) ✓
- [x] **B57 NodeOps + NodeSemantics**: N15.2 (SECUENCIAL, CRÍTICO) ✓
- [x] **B58 CircuitExpr + ExtractableSound**: N15.3 (SECUENCIAL, CRÍTICO) ✓
- [x] **B59 Integration**: N15.4 (SECUENCIAL, HOJA) ✓

#### Execution Order

```
B56 (N15.1 FUND) → B57 (N15.2 CRIT) → B58 (N15.3 CRIT) → B59 (N15.4 HOJA)
```

All sequential: each block depends on the previous.

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N15.1 | BAJA | Mechanical copy + namespace rename. Source compiles in VerifiedExtraction. |
| N15.2 | MEDIA | 7 constructors × 4 laws = 28 proof obligations. Follow ArithOp pattern. Use `cases op <;> simp` cascade. |
| N15.3 | MEDIA | `smulGate` mixes scalar constant + child value (unique among constructors). Test this case first. |
| N15.4 | BAJA | Composition of proven pieces. Standard instantiation. |

#### Actual Metrics

| Metric | Result |
|--------|--------|
| New LOC | 914 |
| New files | 4 |
| Modified files | 0 |
| Theorems | 17 |
| Definitions | 33 |
| Instances | 6 |
| Axioms | 0 |
| Sorry | 0 |
| Warnings (new files) | 0 |

---

### Fase 16: Extraction Completeness — DAG Acyclicity + Fuel Sufficiency (v2.5.1) ✅ COMPLETE

**Status**: All 4 blocks completed 2026-03-03. 550 LOC, 6 public theorems, 0 sorry, 0 axioms. G1 (DAG acyclicity) and G2 (fuel sufficiency) both closed.

**Goal**: Close two critical completeness gaps in the VerifiedExtraction pipeline: (G1) prove that `computeCostsF` with positive cost functions produces an acyclic bestNode DAG, and (G2) prove that `extractAuto` always succeeds when the DAG is acyclic. Port from OptiSat v1.5.1 CompletenessSpec.lean (425 LOC, 9 declarations, 0 sorry), adapted to amo-lean's fold-based `computeCostsF`.

**Source**: `~/Documents/claudio/optisat/LambdaSat/CompletenessSpec.lean` — proven strategy with 0 sorry, 0 axioms.

**Key adaptation**: amo-lean's `computeCostsF` (Core.lean:241-260) uses `HashMap.fold` + `EClass.updateBest` inline, while OptiSat uses `processKeys` + `computeCostsLoop`. The bridge theorem (N16.2) must be adapted to the fold-based implementation. Extraction theorems (N16.3) are implementation-independent.

**Reference**: L-519 (HashMap nodup bridge), L-520 (omega + struct with-update), L-521 (parasitic rewrite in foldl).

**Files** (new):
- `AmoLean/EGraph/VerifiedExtraction/CompletenessSpec.lean` — all completeness definitions + theorems

**Files** (modified):
- `AmoLean.lean` — +import CompletenessSpec
- `ARCHITECTURE.md` — Fase 16 + v2.5.1
- `BENCHMARKS.md` — Fase 16 results

#### DAG

```
N16.1 (FUND) → N16.2 (CRIT) ─┐
                               ├→ N16.4 (HOJA)
             N16.3 (CRIT) ────┘
```

**N16.1 FUNDACIONAL — Definitions + Pure Acyclicity Theorem** (~120 LOC)
- Define `bestCostOf`, `BestNodeChild`, `AcyclicBestNodeDAG`, `BestCostLowerBound`
- Prove helper lemmas: `foldl_ge_init`, `foldl_sum_ge_mem`
- Prove `bestCostLowerBound_acyclic`: BestCostLowerBound + positive costs → AcyclicBestNodeDAG
- Pure definitions — independent of `computeCostsF` implementation
- File: `AmoLean/EGraph/VerifiedExtraction/CompletenessSpec.lean`

**N16.2 CRÍTICO — computeCostsF Bridge** (~200 LOC)
- Define `SelfLB` invariant adapted to amo-lean's fold-based computeCostsF
- Prove `computeCostsF_bestCost_lower_bound`: fresh graph → BestCostLowerBound after computeCostsF
- Prove `computeCostsF_acyclic`: composition with positive costs
- Adaptation: HashMap.fold + EClass.updateBest (instead of processKeys + updateClassBest)
- Key lemmas: `get?_insert_self_cls`, `get?_insert_ne_cls`, `keys_nodup_cls`, `foldl_sum_le_pointwise`
- File: same CompletenessSpec.lean

**N16.3 CRÍTICO — Fuel Sufficiency** (~70 LOC)
- Prove `mapOption_some_of_forall`: mapOption succeeds when f succeeds on all elements
- Prove `extractF_of_rank`: fuel > rank(id) → extractF returns some (strong induction)
- Prove `extractAuto_complete`: extractAuto succeeds when rank < numClasses
- Independent of computeCostsF — depends only on extractF/extractAuto definitions (identical to OptiSat)
- File: same CompletenessSpec.lean

**N16.4 HOJA — Integration + Tests + Documentation** (~50 LOC)
- Add `import AmoLean.EGraph.VerifiedExtraction.CompletenessSpec` to AmoLean.lean
- Smoke tests: small DAG acyclicity + fuel sufficiency examples
- Update README.md, ARCHITECTURE.md, BENCHMARKS.md for v2.5.1

#### Formal Properties (v2.5.1)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N16.1 | `bestCostLowerBound_acyclic`: BestCostLowerBound + positive costs → AcyclicBestNodeDAG | SOUNDNESS | P0 |
| N16.1 | All definitions compile with 0 sorry, 0 axioms | INVARIANT | P0 |
| N16.2 | `computeCostsF_acyclic`: computeCostsF with positive costs → AcyclicBestNodeDAG | SOUNDNESS | P0 |
| N16.2 | `computeCostsF_bestCost_lower_bound`: fresh graph → BestCostLowerBound | PRESERVATION | P0 |
| N16.3 | `extractF_of_rank`: fuel > rank → extractF succeeds | COMPLETENESS | P0 |
| N16.3 | `extractAuto_complete`: extractAuto always succeeds given acyclic DAG | COMPLETENESS | P0 |
| N16.4 | `lake build` passes with 0 new sorry, 0 new axioms | INVARIANT | P0 |

#### Bloques

- [x] **B60**: N16.1 (SECUENCIAL, FUNDACIONAL) ✓ 2026-03-03
- [x] **B61**: N16.2 (SECUENCIAL, CRÍTICO) ✓ 2026-03-03
- [x] **B62**: N16.3 (SECUENCIAL, CRÍTICO) ✓ 2026-03-03
- [x] **B63**: N16.4 (SECUENCIAL, HOJA) ✓ 2026-03-03

#### Execution Order

```
B60 (N16.1 FUND) → B61 (N16.2 CRIT) → B62 (N16.3 CRIT) → B63 (N16.4 HOJA)
```

Note: N16.3 is independent of N16.2 (depends only on N16.1 definitions), but executed after for clarity. Could be parallelized.

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N16.1 | BAJA | Direct copy from OptiSat + namespace rename. Pure definitions. |
| N16.2 | ALTA | amo-lean's fold-based computeCostsF differs from OptiSat's processKeys. Requires adapted SelfLB proof over HashMap.fold. De-risk with sketch. |
| N16.3 | BAJA | Direct copy from OptiSat. extractF is identical. Strong induction pattern proven. |
| N16.4 | BAJA | Mechanical: imports + smoke tests + docs. |

---

### Fase 17: Plonky3 Translation Validation (Camino 2) — v2.6.0

**Goal**: Per-function refinement bridge proving Plonky3's field arithmetic implementations are correct. For each Plonky3 field operation: `plonky3_impl(machine_ints) = field_spec(ZMod p)`. End-to-end: Plonky3 prover computation → FRI algebraic guarantees.

**Novel contributions**:
- First formalization of Mersenne31 field in Lean 4 (or any proof assistant)
- First formal Montgomery reduction in Lean 4
- First per-function translation validation of a STARK prover library

**Architecture**:
```
Plonky3 Rust (untrusted)           [verification/plonky3/plonky3_source/]
    | [manual formalization — mirrors exact Rust algorithms]
Plonky3.*Ops (Lean on UInt32/UInt64)     [NEW: AmoLean/Field/Plonky3/]
    | [per-function refinement theorems with explicit overflow preconditions]
AMO-Lean Field.* (Mersenne31, BabyBear, Goldilocks)   [NEW + EXISTING]
    | [toZMod_* homomorphism theorems]
ZMod p (Mathlib)                   [abstract field algebra]
    | [existing fri_pipeline_soundness]
FRI Algebraic Guarantees           [3 crypto axioms]
```

**Trust boundary**: Manual per-function Lean formalization of Plonky3 Rust (verified by inspection against `verification/plonky3/plonky3_source/`). Follows CertiPlonk/Jasmin methodology. Direct Lean refinement (not MicroC) because Trust-Lean's MicroC only has Int64 evaluator.

**Strategy**: Vertical Slice First — complete Mersenne31 end-to-end before expanding.

**Reference projects** (study, not import): CertiPlonk (Nethermind), Jasmin/Kyber Episode IV (Almeida et al. TCHES 2023), Affeldt et al. Montgomery Verified (ITP 2018), Trieu NTT Verified (2025 Rocq), Fiat-Crypto (Erbsen et al. S&P 2019).

**Lessons applied**: L-019 (Injective.commRing/field), L-016 (two-level proof: Nat then ZMod), L-201 (native_decide for 31-bit), L-202 (80% mechanical replication), L-512 (three-tier bridge), L-573 (ZMod Mathlib patterns), L-566 (Bool-to-Prop bridge), L-567 (native_decide limit), L-311 (three-part contract), L-478 (equation compiler), L-532 (trust boundary = hypothesis).

**New files** (7-9, in `AmoLean/Field/` and `AmoLean/Field/Plonky3/`):
- `AmoLean/Field/Mersenne31.lean` — Mersenne31 field type + ops + toZMod + Field instance
- `AmoLean/Field/Montgomery.lean` — Generic Montgomery reduction (R=2^32)
- `AmoLean/Field/Plonky3Field.lean` — PlonkyField typeclass + instances
- `AmoLean/Field/Plonky3/Mersenne31TV.lean` — Mersenne31 Plonky3 refinement
- `AmoLean/Field/Plonky3/BabyBearTV.lean` — BabyBear Montgomery refinement
- `AmoLean/Field/Plonky3/GoldilocksTV.lean` — Goldilocks verification
- `AmoLean/NTT/Plonky3/ButterflyTV.lean` — NTT butterfly TV
- `AmoLean/FRI/Plonky3/FoldTV.lean` — FRI fold TV
- `AmoLean/Plonky3/TVPipeline.lean` — End-to-end pipeline

#### DAG (v2.6.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N17.1 Mersenne31Field | FUND | — | ✓ (889 LOC, 0 sorry) |
| N17.2 Mersenne31 Refinement | CRIT | N17.1 | ✓ (286 LOC, 0 sorry) |
| N17.3 Montgomery Reduction | FUND | — | ✓ (337 LOC, 0 sorry) |
| N17.4 BabyBear Monty Refinement | CRIT | N17.3 | ✓ (353 LOC, 0 sorry) |
| N17.5 Goldilocks Plonky3 Verification | PAR | — | ✓ (219 LOC, 0 sorry) |
| N17.6 Plonky3Field Typeclass | FUND | N17.1, N17.4, N17.5 | ✓ (180 LOC, 0 sorry) |
| N17.7 NTT Butterfly TV | PAR | N17.6 | ✓ (215 LOC, 0 sorry) |
| N17.8 FRI Fold TV | PAR | N17.6 | ✓ (174 LOC, 0 sorry) |
| N17.9 Plonky3 TV Pipeline | HOJA | N17.7, N17.8 | ✓ (213 LOC, 0 sorry) |

#### Formal Properties (v2.6.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N17.1 | mersenne31_prime_is_prime : Nat.Prime (2^31 - 1) | INVARIANT | P0 |
| N17.1 | from_u62_correct : from_u62 x % p = x % p for x < 2^62 | SOUNDNESS | P0 |
| N17.1 | toZMod is ring homomorphism (add, mul, neg, sub) | PRESERVATION | P0 |
| N17.1 | Field Mersenne31Field instance | SOUNDNESS | P0 |
| N17.2 | mersenne31_add_refines : toZMod (add a b) = toZMod a + toZMod b | EQUIVALENCE | P0 |
| N17.2 | Non-vacuity: concrete values satisfy all hypotheses | INVARIANT | P0 |
| N17.3 | monty_reduce_correct : monty_reduce x % p = x * R_inv % p | SOUNDNESS | P0 |
| N17.3 | monty_reduce_range : x < R*p → monty_reduce x < p | INVARIANT | P0 |
| N17.3 | monty_mul_correct : from_monty(a_M * b_M) = from_monty(a_M) * from_monty(b_M) mod p | SOUNDNESS | P0 |
| N17.4 | babybear_mu_correct : MU * p % 2^32 = 1 | INVARIANT | P0 |
| N17.4 | babybear_plonky3_mul_zmod : Plonky3 monty mul = ZMod mul | EQUIVALENCE | P0 |
| N17.5 | goldilocks_plonky3_eq : Plonky3 reduce128 = AMO-Lean reduce128 | EQUIVALENCE | P0 |
| N17.6 | All 3 fields instantiate Plonky3Field | COMPLETENESS | P0 |
| N17.7 | dit_butterfly_correct : butterfly preserves ZMod semantics | SOUNDNESS | P0 |
| N17.7 | butterfly_invertible : DIT o DIF = id over ZMod p | EQUIVALENCE | P1 |
| N17.8 | fri_fold_tv : fold_impl = foldPolynomial over ZMod p | EQUIVALENCE | P0 |
| N17.9 | plonky3_tv_pipeline_soundness : end-to-end composition | SOUNDNESS | P0 |
| N17.9 | #print axioms = exactly 3 existing crypto axioms | SOUNDNESS | P0 |

#### Detailed Node Specifications

**Subfase 1: Mersenne31 Vertical Slice**

**N17.1 FUNDACIONAL — Mersenne31Field** (~600 LOC)
- `Mersenne31Field` structure: `val : UInt32`, `val_lt : val.toNat < ORDER_NAT`
- p = 2^31 - 1 (Mersenne prime), `mersenne31_prime_is_prime` via `native_decide` (31-bit, L-201)
- Operations matching Plonky3's exact algorithms from `mersenne_31.rs`:
  - `add`: i32 overflow detection → conditional correction (Plonky3 lines 467-481)
  - `sub`: wrapping sub → `sub &= P` bitmask (Plonky3 lines 488-496)
  - `mul`: u64 intermediate → `from_u62` split 31-bit halves (2^31 ≡ 1 mod p) (Plonky3 lines 514-517, 540-545)
  - `neg`: `P - value` (Plonky3 lines 503-506)
  - `halve`: `shr + conditional HALF_P_PLUS_1` (utils.rs lines 92-97)
  - `inv`: Fermat `a^{p-2}`
- `toZMod` homomorphisms, `CommRing` + `Field` via `Function.Injective.commRing/field` (L-019)
- Proof strategy (L-016): prove at Nat level first (split_ifs, omega), lift via val_cast_of_lt
- Explicit overflow preconditions: `val.toNat < 2^31` maintained through all ops
- De-risk: primality proof + from_u62_correct sketch BEFORE full file
- Pattern: ~80% mechanical from BabyBear.lean (L-202)
- File: `AmoLean/Field/Mersenne31.lean`

**N17.2 CRITICO — Mersenne31 Plonky3 Refinement** (~200 LOC)
- Per-function refinement theorems: `toZMod (op a b) = toZMod a ⊕ toZMod b` for all ops
- Non-vacuity example: concrete values (a=1000000, b=1500000000)
- Smoke tests: `#eval` for 10+ test vectors from Plonky3 test suite
- Firewall `_aux` pattern
- File: `AmoLean/Field/Plonky3/Mersenne31TV.lean`

**Subfase 2: Montgomery + BabyBear**

**N17.3 FUNDACIONAL — Montgomery Reduction** (~400 LOC)
- Generic Montgomery theory (R = 2^32):
  - `MontgomeryConfig`: p, p_prime, p_lt_2_31, MONTY_BITS=32, MONTY_MU, mu_correct
  - `monty_reduce`: mirrors `monty-31/src/utils.rs` lines 105-125
  - Core theorems: `monty_reduce_correct`, `monty_reduce_range`, `to_monty_from_monty`, `monty_mul_correct`, `monty_add_preserves`
- Overflow preconditions explicit and proven
- **Proof spike mandatory** before full file (~50 LOC sketch for `monty_reduce_correct`)
- File: `AmoLean/Field/Montgomery.lean`

**N17.4 CRITICO — BabyBear Montgomery Refinement** (~250 LOC)
- Instantiate MontgomeryConfig: p=2013265921, MONTY_BITS=32, MONTY_MU=2281701377
- `mu_babybear_correct` via `native_decide`
- Mirror Plonky3 MontyField31 operations, refinement theorems composing with existing `toZMod_mul`
- Non-vacuity example with concrete BabyBear values
- File: `AmoLean/Field/Plonky3/BabyBearTV.lean`

**Subfase 3: Goldilocks + Unified Interface**

**N17.5 PAR — Goldilocks Plonky3 Verification** (~120 LOC)
- Verify Plonky3's Goldilocks algorithms match AMO-Lean's existing `Goldilocks.lean`
- Expected near-identity (same reduce128 algorithm per insights analysis)
- File: `AmoLean/Field/Plonky3/GoldilocksTV.lean`

**N17.6 FUND — Plonky3Field Typeclass** (~200 LOC)
- Typeclass parameterized over repr type (UInt32/UInt64), extension-field-ready:
  ```
  class Plonky3Field (F : Type) extends Field F where
    char : Nat; char_prime : Nat.Prime char
    toZMod : F → ZMod char; toZMod_injective; toZMod_ringHom
    toNat : F → Nat; toNat_lt : ∀ a, toNat a < char
  ```
- Instances: Mersenne31Field, BabyBearField, GoldilocksField
- File: `AmoLean/Field/Plonky3Field.lean`

**Subfase 4: Higher-Level Operations**

**N17.7 PAR — NTT Butterfly TV** (~200 LOC)
- DIT/DIF butterfly over `[Plonky3Field F]`
- Prove: butterfly preserves ZMod semantics, invertibility
- File: `AmoLean/NTT/Plonky3/ButterflyTV.lean`

**N17.8 PAR — FRI Fold TV** (~250 LOC)
- FRI fold over PlonkyField, compose with existing FoldBridge
- Three-layer bridge: Plonky3 array-fold → AMO-Lean friFold → foldPolynomial
- File: `AmoLean/FRI/Plonky3/FoldTV.lean`

**Subfase 5: End-to-End**

**N17.9 HOJA — Plonky3 TV Pipeline** (~200 LOC)
- Master theorem composing all, non-vacuity example, axiom audit (= 3 crypto only)
- File: `AmoLean/Plonky3/TVPipeline.lean`

#### Bloques

- [x] **B64 Mersenne31 Foundation**: N17.1 (SECUENCIAL, FUNDACIONAL) ✓
- [x] **B65 Mersenne31 Refinement**: N17.2 (SECUENCIAL, CRITICO) ✓
- [x] **B66 Montgomery Foundation**: N17.3 (SECUENCIAL, FUNDACIONAL) ✓
- [x] **B67 BabyBear Monty Refinement**: N17.4 (SECUENCIAL, CRITICO) ✓
- [x] **B68 Goldilocks + PlonkyField**: N17.5 + N17.6 (AGENT_TEAM) ✓
- [x] **B69 NTT Butterfly + FRI Fold TV**: N17.7 + N17.8 (AGENT_TEAM) ✓
- [x] **B70 Pipeline Integration**: N17.9 (SECUENCIAL, HOJA) ✓

#### Execution Order

```
VERTICAL SLICE (Mersenne31):
  B64 (N17.1 FUND) → B65 (N17.2 CRIT)

MONTGOMERY EXPANSION:
  B66 (N17.3 FUND) → B67 (N17.4 CRIT)

PARALLEL (after B65, independent of B66-B67):
  B68 (N17.5 + N17.6)

CONVERGENCE (after B67 + B68):
  B69 (N17.7 + N17.8)

FINAL:
  B70 (N17.9 HOJA) ← B69
```

Critical path: B64 → B65 → B66 → B67 → B69 → B70
Parallel: B68 alongside B66-B67

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N17.1 | MEDIA | 31-bit native_decide OK (L-201). ~80% mechanical from BabyBear (L-202). De-risk: from_u62 + primality sketch. |
| N17.2 | MEDIA | Simple ops (no Montgomery). UInt32 overflow bounded (val < 2^31). |
| N17.3 | ALTA | ~96 lemmas in literature. Proof spike mandatory. Time-box 3 sessions. Fallback: axiomatize monty_reduce_correct. |
| N17.4 | ALTA | Concrete MU via native_decide. Depends on N17.3 solidity. |
| N17.5 | BAJA | Near-identity with existing Goldilocks.lean. May be mostly rfl. |
| N17.6 | MEDIA | Typeclass design. De-risk with sketch. Extension-field-ready. |
| N17.7 | MEDIA | 2 add + 1 mul, generic over PlonkyField. |
| N17.8 | MEDIA | Composes with existing FoldBridge. Array ↔ polynomial bridge. |
| N17.9 | BAJA | Mechanical composition. Standard capstone. |

#### Estimated Metrics

| Metric | Estimate |
|--------|----------|
| New LOC | 2,400-3,000 |
| New files | 7-9 |
| Modified files | 0-1 |
| New theorems | 65-95 |
| New axioms | 0 |
| Target sorry | 0 |
| Non-vacuity examples | 3+ |

---

## Key Design Decisions (v2.6.0)

27. **Direct Lean refinement, not MicroC path**: Trust-Lean's MicroC only has Int64 evaluator (no UInt32/UInt64). Direct Lean refinement gives same mathematical guarantee. MicroC path deferred to v2.7.0.
28. **Plonky3 source as reference, not import**: Plonky3 Rust in `verification/plonky3/plonky3_source/` as reference. Lean functions mirror exact algorithms (line-by-line correspondence).
29. **Montgomery as separate generic module**: Reusable for any 31-bit field with Montgomery form (BabyBear, KoalaBear). Not coupled to BabyBear.
30. **Plonky3Field typeclass over repr type**: Per QA — parameterized, extension-field-ready. No assumption on char < 2^32.
31. **Overflow preconditions explicit**: Every refinement theorem carries explicit bounds on inputs, proven maintained by Plonky3 algorithms.

## Key Design Decisions (v2.5.1)

26. **Completeness as separate file, not modifying Core/Greedy**: CompletenessSpec.lean is additive — no changes to existing Core.lean or Greedy.lean. This preserves the zero-regression property and keeps the completeness proofs isolated. The bridge theorem (N16.2) reasons about the existing computeCostsF implementation without requiring refactoring.

## Key Design Decisions (v2.5.0)

25. **Generic + Adaptor pattern**: Instead of replacing AMO-Lean's existing circuit-specific extraction (ExtractSpec.lean), add the generic VerifiedExtraction framework alongside it. The `CircuitAdaptor` instantiates the generic typeclasses for `CircuitNodeOp`, getting `extractF_correct` for free. Existing code untouched — zero regression risk.
26. **Copy, don't import**: Following project convention (L-134), VerifiedExtraction files are copied and adapted, not added as a `require` dependency. This keeps AMO-Lean self-contained and allows namespace-specific modifications.
27. **CircuitExpr vs Expr Int**: New `CircuitExpr` type with 7 constructors matching ALL `CircuitNodeOp` variants (including `witness`, `pubInput`, `smulGate` which are absent from `Expr Int`). This ensures complete extraction coverage.

## Key Design Decisions (v2.4.2)

22. **Witness-variable bridge**: `exprCircuitEval` maps `Expr Int` evaluation to `CircuitEnv` by routing variable lookups through `witnessVal`. This is sound because in the e-graph engine, pattern variables bind to witness nodes (user-supplied values), not constants or public inputs.
23. **1-line soundness proofs**: Each `SoundRewriteRule` soundness proof is a single application of the existing `*_correct` theorem composed with the witness-variable bridge. This is possible because `exprCircuitEval` is definitionally equal to `VerifiedRules.eval` with the appropriate environment substitution.
24. **10 of 20 rules bridgeable**: Power rules (4) excluded because `CircuitNodeOp` has no `powGate`; structural rules (assoc/comm, 4) and constant folding (2) excluded because they are not wired in `Rules.lean`. This is by design, not a gap.

17. **Three-layer bridge architecture**: Type isomorphisms (Layer 1) → function equivalence (Layer 2) → property preservation (Layer 3). Proven effective in Trust-Lean v1.2.0 (26 theorems, 0 sorry). Avoids monolithic bridge that tries to verify all 357 defs at once.
18. **Plausible over SlimCheck**: Plausible (leanprover-community/plausible) is standalone, compatible with Lean 4.26.0, and supports `deriving Arbitrary`. Replaces the Mathlib-internal `slim_check` tactic with modern `plausible` tactic.
19. **Formal proofs P0, Plausible P1**: Following Trust-Lean pattern — `decide`/`rfl`/`omega` are strictly stronger than random testing. Bridge correctness proven formally; Plausible supplements with exploration testing.
20. **Staged Merkle proof strategy**: Instead of axiomatizing flatToInductive directly, decompose into (a) index mapping helpers, (b) inversion proofs, (c) semantic correctness, (d) bridge on proven helpers. Confine axiom to index arithmetic only if intractable.
21. **Scope control: 5 bridges not 357**: Only bridge the 5 critical type mismatches (Domain, Transcript, Fold, Merkle, Query). The integration theorem composes them to cover the verification chain without touching every operational def.

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
- **Trust-Lean v3.0 integration**: Added `verifiedCodeGenMicroC` pipeline (ExpandedSigma → MicroCStmt → C text) with formal evaluation semantics, full inductive roundtrip (`master_roundtrip`), Int64 overflow model, and call semantics. Both CBackend (`verifiedCodeGen`) and MicroC (`verifiedCodeGenMicroC`) paths coexist.

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
| E-Graph Rewrite Rules | **100%** | 0 | 0 | 20/20 rules verified, 10 SoundRewriteRule instances |
| **E-Graph Verified Engine** | **100%** | **0** | **0** | **121 theorems, 4,594 LOC** |
| **Trust-Lean Bridge** | **100%** | **0** | **0** | **26 theorems + v3.0 MicroC pipeline, roundtrip + injectivity** |
| Goldilocks Field | **100%** | 0 | 0 | All 5 axioms eliminated |
| BabyBear Field | **100%** | 0 | 0 | All 4 axioms eliminated |
| AlgebraicSemantics | **100%** | 0 | 0 | 19/19 cases proven |
| Poseidon2 | Computational | 12 | 0 | All backed by 21 test vectors |

**Codebase**: ~41,700 LOC | **9 axioms** (8 Radix-4 + 1 Perm) | **12 active sorry** (all Poseidon, match splitter limitation) | **147 verified theorems** (121 e-graph + 26 bridge)

---

### Fase 21: Bitwise Verification of Field Arithmetic via E-graphs — v3.1.0

**Goal**: Extend the verified E-graph engine to verify that bitwise implementations (shifts, AND, masks) of modular reduction are semantically equivalent to algebraic specifications for Mersenne31, BabyBear, and Goldilocks.

**Approach**: "E-graph as verifier" (Alternativa A from bitwise analysis). NO optimization discovery — verification of KNOWN implementations.

**Key Architectural Decisions**:
1. **MixedNodeOp** as SEPARATE inductive from CircuitNodeOp → preserves all 121 existing theorems
2. **evalMixedOp on Nat** (concrete, no typeclass for bitwise) → field bridge via toZMod AFTER extraction
3. **ConditionalSoundRewriteRule** for field-specific rules → sideCond carries explicit Nat bounds
4. **Bounded saturation** (fuel=10) → Herbie research: 3 iterations sufficient
5. **BitwiseLean library** (~/Documents/claudio/bitwiselean/) copied/adapted, never imported

**New files** (8):
- `AmoLean/EGraph/Verified/Bitwise/MixedNodeOp.lean` — MixedNodeOp inductive + evalMixedOp + NodeOps/NodeSemantics
- `AmoLean/EGraph/Verified/Bitwise/BitwiseBridge.lean` — Bridge theorems + ConsistentValuation preservation
- `AmoLean/EGraph/Verified/Bitwise/BitwiseRules.lean` — Generic bitwise SoundRewriteRule instances
- `AmoLean/EGraph/Verified/Bitwise/FieldFoldRules.lean` — Mersenne31/BabyBear/Goldilocks fold rules
- `AmoLean/EGraph/Verified/Bitwise/MixedExtract.lean` — MixedExpr + extractF_correct for MixedNodeOp
- `AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean` — Pipeline soundness + TV extension
- `AmoLean/EGraph/Verified/Bitwise/Tests.lean` — Smoke tests
- `Tests/NonVacuity/Bitwise.lean` — Non-vacuity examples

**Source adaptations**: BitwiseLean (40 thms) → Bridge, MersenneFold, PseudoMersenneFold, Montgomery

**Lessons applied**: L-458 (concrete evalOp), L-516 (mirror inductive), L-016 (two-level Nat+ZMod), L-019 (injective bootstrap), L-546 (ConditionalRewriteRule extension), L-478 (flat patterns), L-311 (three-part contract)

#### DAG (v3.1.0)

```
N21.1 MixedNodeOp (FUND) ──→ N21.2 BitwiseBridge (FUND) ──→ N21.3 BitwiseRules (CRIT)
                                                           ──→ N21.4 FieldFoldRules (CRIT)
                                                           ──→ N21.5 MixedExtract (PAR)
N21.3 + N21.4 + N21.5 ──→ N21.6 MixedPipeline (HOJA)
N21.6 ──→ N21.7 IntegrationTests (HOJA)
```

| Node | Name | Type | Files | LOC | Theorems | Deps |
|------|------|------|-------|-----|----------|------|
| N21.1 | MixedNodeOp | FUND | Bitwise/MixedNodeOp.lean | ~350 | 15 | — |
| N21.2 | BitwiseBridge | FUND | Bitwise/BitwiseBridge.lean | ~300 | 10 | N21.1 |
| N21.3 | BitwiseRules | CRIT | Bitwise/BitwiseRules.lean | ~250 | 12 | N21.2 |
| N21.4 | FieldFoldRules | CRIT | Bitwise/FieldFoldRules.lean | ~350 | 8 | N21.2 |
| N21.5 | MixedExtract | PAR | Bitwise/MixedExtract.lean | ~300 | 10 | N21.2 |
| N21.6 | MixedPipeline | HOJA | Bitwise/MixedPipeline.lean | ~250 | 5 | N21.3, N21.4, N21.5 |
| N21.7 | IntegrationTests | HOJA | Tests + NonVacuity | ~200 | 3 | N21.6 |
| **Total** | | | **8 files** | **~2,000** | **~63** | |

#### Blocks (topological order)

| Block | Nodes | Type | Execution |
|-------|-------|------|-----------|
| B71 | N21.1 | FUND | Sequential (de-risk sketch first) |
| B72 | N21.2 | FUND | Sequential (de-risk bridge theorem first) |
| B73 | N21.3, N21.4, N21.5 | CRIT+PAR | Agent Team (3 parallel after B72) |
| B74 | N21.6 | HOJA | Sequential |
| B75 | N21.7 | HOJA | Sequential |

#### Node Details

**N21.1 MixedNodeOp** (FUND, ~350 LOC)
- `inductive MixedNodeOp` with 13 constructors:
  - 7 algebraic (mirror CircuitNodeOp): constGate, witness, pubInput, addGate, mulGate, negGate, smulGate
  - 6 bitwise: shiftLeft(EClassId, Nat), shiftRight(EClassId, Nat), bitAnd(EClassId, EClassId), bitXor(EClassId, EClassId), bitOr(EClassId, EClassId), constMask(Nat)
- `evalMixedOp : MixedNodeOp → (Nat → Nat) → (Nat → Nat) → (EClassId → Nat) → Nat` (on Nat, concrete)
- `children`, `mapChildren`, `replaceChildren`, `localCost` (shift/and/or/xor = 0, mul = 1)
- `NodeOps MixedNodeOp` instance with 4 law proofs
- `NodeSemantics MixedNodeOp` instance with evalOp_ext
- `toMixed : CircuitNodeOp → MixedNodeOp` (embedding)
- `toMixed_children_eq` : children preservation theorem

**N21.2 BitwiseBridge** (FUND, ~300 LOC)
- Bridge theorems adapted from BitwiseLean: mask_eq_mod, shiftRight_eq_div_pow, mod_from_split
- `evalMixed_toMixed_eq` : evalMixedOp (toMixed op) = evalOp op (key bridge)
- `MixedConsistentValuation` + preservation: merge, find, canonicalize, processClass
- QA-mandated: formal proof that each new rewrite rule preserves ConsistentValuation

**N21.3 BitwiseRules** (CRIT, ~250 LOC)
- ~10 SoundRewriteRule instances for generic bitwise identities
- shift_shift_compose, and_mask_idem, and_comm, and_assoc, or_comm, or_assoc, xor_comm, xor_self_zero
- mask_mod_bridge, shift_mul_bridge (as rewrite rules)
- `allBitwiseRules` collection + `allBitwiseRules_sound` master theorem

**N21.4 FieldFoldRules** (CRIT, ~350 LOC)
- ~4 ConditionalSoundRewriteRule instances:
  - mersenne31_fold_rule (sideCond: input < 2^62)
  - babybear_fold_rule (sideCond: input < 2^62)
  - goldilocks_fold_rule (sideCond: input < 2^128)
  - monty_reduce_rule (sideCond: x < R*p, prime p, valid mu_neg)
- Adapts BitwiseLean: MersenneFold, PseudoMersenneFold, Montgomery
- `allFieldFoldRules` collection

**N21.5 MixedExtract** (PAR, ~300 LOC)
- `inductive MixedExpr` (13 constructors mirroring MixedNodeOp)
- `MixedExpr.eval : MixedExpr → (Nat → Nat) → Nat`
- `Extractable MixedNodeOp MixedExpr`, `EvalExpr MixedExpr Nat Nat`
- `mixed_extractable_sound : ExtractableSound MixedNodeOp MixedExpr Nat Nat`
- `mixed_extractF_correct` : extractF produces semantically correct expressions

**N21.6 MixedPipeline** (HOJA, ~250 LOC)
- `mixed_pipeline_soundness` : saturateF + extractF → correct for bitwise+field rules
- `mixed_tv_extension` : cryptoEquivalent extended for MixedExpr
- Composition: allBitwiseRules ++ allFieldFoldRules → verified optimization

**N21.7 IntegrationTests** (HOJA, ~200 LOC)
- #eval smoke tests: monty_reduce via E-graph = direct, mersenne31 fold via E-graph = direct
- Non-vacuity examples: concrete inputs for mixed_pipeline_soundness (all hypotheses satisfiable)
- Property tests (Plausible): fold equivalence for random field elements

#### Progress Tree

- [x] B71: N21.1 MixedNodeOp (343 LOC, 6T 12D 4I, 0 sorry)
- [x] B72: N21.2 BitwiseBridge (163 LOC, 10 bridge thms + 12 simp, 0 sorry)
- [x] B73: N21.3 BitwiseRules (237 LOC) | N21.4 FieldFoldRules (274 LOC) | N21.5 MixedExtract (220 LOC) — all 0 sorry
- [x] B74: N21.6 MixedPipeline (238 LOC, 17 thms + 3 examples, 0 sorry)
- [x] B75: N21.7 IntegrationTests (269 LOC, 37 #eval + 29 examples, 0 sorry)

---

### Fase 22: Cost-Model-Driven Synthesis of Verified Modular Reduction — v3.2.0

**Goal**: Given a prime `p` and a hardware target (ARM/RISC-V/FPGA), synthesize the optimal verified modular reduction via E-graph equality saturation with parametric cost model.

**Approach**: Alternativa B — E-graph as SYNTHESIZER (not just verifier). Extends Fase 21 infrastructure.

**Key Architectural Decisions**:
1. **HardwareCost as structure** (not typeclass) — only 3 targets, per L-418
2. **SolinasConfig** unifies 4 ZK primes (Mersenne31, BabyBear, KoalaBear, Goldilocks) via ONE parametric fold rule
3. **PhasedSaturation wraps** saturateF (no modification to existing verified code) — heuristic, not confluent
4. **CostExtraction** reuses encodeEGraph by passing `costFn = mixedOpCost hw`
5. **synthesis_egraph_optimal** — cost minimal among extractions of the final E-graph (not globally optimal)
6. **detectSolinasForm** returns `Except String SolinasConfig` with `configOverride` escape hatch

**New files** (7):
- `AmoLean/EGraph/Verified/Bitwise/CostModelDef.lean` — HardwareCost + ARM/RISC-V/FPGA + parametric cost
- `AmoLean/EGraph/Verified/Bitwise/SolinasRuleGen.lean` — SolinasConfig → FieldFoldRule generator
- `AmoLean/EGraph/Verified/Bitwise/PhasedSaturation.lean` — Two-phase wrapper (algebraic→bitwise)
- `AmoLean/EGraph/Verified/Bitwise/CostExtraction.lean` — ILP extraction with HardwareCost objective
- `AmoLean/EGraph/Verified/Bitwise/ReductionComposition.lean` — Compose reduction steps
- `AmoLean/EGraph/Verified/Bitwise/SynthesisPipeline.lean` — End-to-end synthesis
- `AmoLean/EGraph/Verified/Bitwise/SynthesisTests.lean` + `Tests/NonVacuity/Synthesis.lean`

**Source adaptations**: BitwiseLean (CostModel, SolinasFold, KoalaBearFold)

**Lessons applied**: L-513 (compositional pipelines), L-527 (non-recursive ILP), L-311 (three-part contract), L-517 (unified dispatch), L-418 (concrete defs before typeclasses), L-478 (flat patterns)

#### DAG (v3.2.0)

```
N22.1 CostModelDef (FUND) ──→ N22.3 PhasedSaturation (CRIT) ──→ N22.6 SynthesisPipeline (HOJA)
                           ──→ N22.4 CostExtraction (CRIT) ────→
N22.2 SolinasRuleGen (FUND) ──→ N22.3
                             ──→ N22.5 ReductionComposition (PAR) → N22.6
N22.6 ──→ N22.7 IntegrationTests (HOJA)
```

| Node | Name | Type | Files | LOC | Theorems | Deps |
|------|------|------|-------|-----|----------|------|
| N22.1 | CostModelDef | FUND | Bitwise/CostModelDef.lean | ~250 | 8 | — |
| N22.2 | SolinasRuleGen | FUND | Bitwise/SolinasRuleGen.lean | ~300 | 10 | — |
| N22.3 | PhasedSaturation | CRIT | Bitwise/PhasedSaturation.lean | ~300 | 6 | N22.1, N22.2 |
| N22.4 | CostExtraction | CRIT | Bitwise/CostExtraction.lean | ~440 | 8 | N22.1 |
| N22.5 | ReductionComposition | PAR | Bitwise/ReductionComposition.lean | ~200 | 5 | N22.2 |
| N22.6 | SynthesisPipeline | HOJA | Bitwise/SynthesisPipeline.lean | ~300 | 6 | N22.3, N22.4, N22.5 |
| N22.7 | IntegrationTests | HOJA | SynthesisTests + NonVacuity | ~200 | 3 | N22.6 |
| **Total** | | | **8 files** | **~2,000** | **~46** | |

#### Blocks (topological order)

| Block | Nodes | Type | Execution |
|-------|-------|------|-----------|
| B76 | N22.1 | FUND | Sequential (de-risk sketch) |
| B77 | N22.2 | FUND | Sequential (de-risk sketch) |
| B78 | N22.3 | CRIT | Sequential (after B76+B77) |
| B79 | N22.4 | CRIT | Sequential (after B76) |
| B80 | N22.5 | PAR | Sequential (after B77, parallel with B79) |
| B81 | N22.6 | HOJA | Sequential (after B78+B79+B80) |
| B82 | N22.7 | HOJA | Sequential |

#### Progress Tree

- [x] B76: N22.1 CostModelDef (188 LOC, 7 thms, 0 sorry)
- [x] B77: N22.2 SolinasRuleGen (344 LOC, 25 decls, 0 sorry)
- [x] B78: N22.3 PhasedSaturation (379 LOC, 15 thms, 0 sorry)
- [x] B79: N22.4 CostExtraction (425 LOC, 17 thms, 0 sorry)
- [x] B80: N22.5 ReductionComposition (254 LOC, 12 thms, 0 sorry)
- [x] B81: N22.6 SynthesisPipeline (333 LOC, 13 thms, 0 sorry)
- [x] B82: N22.7 IntegrationTests (184 LOC, 13 examples, 0 sorry)

---

### Fase 23: Verified C Codegen Pipeline + Enhanced Cost Model — v3.2.4

**Goal**: Complete end-to-end pipeline from prime specification to verified C code via Trust-Lean MicroC, with register-pressure-aware cost model and BitVec dual representation.

**Pipeline**: `synthesizeReduction(p, hw)` → `toTrustLeanExpr` → `stmtToMicroC` → `microCToString` → verified C code

**Key Decisions** (from QA):
1. negE → `binOp .sub (litInt 0) expr` (unsigned wrapping, NOT unaryOp.neg)
2. constE → `litInt (env.constVal n)` (inline at translation time)
3. tempCount via max-live-variables (post-order traversal)
4. Master theorem: `∀ e env, MixedExpr.eval e env = wrapUInt w (evalExpr trustEnv (toTrustLeanExpr e))`
5. Trust-Lean bridges (N23.4/N23.5) in Trust-Lean project

#### DAG (v3.2.4)

```
N23.1 EnhancedCostModel (FUND) ──→ N23.3 MixedExprToStmt (CRIT) ──→ N23.6 SynthesisToC (CRIT)
N23.2 BitVecBridge (FUND)                                        ──→
N23.4 KoalaBearBridge (PAR)  ──→ N23.6
N23.5 GoldilocksBridge (PAR) ──→ N23.6
N23.6 ──→ N23.7 BenchmarkTests (HOJA)
N23.6 ──→ N23.8 CostIntegration (HOJA)
```

| Node | Name | Type | LOC | Deps |
|------|------|------|-----|------|
| N23.1 | EnhancedCostModel | FUND | ~200 | — |
| N23.2 | BitVecBridge | FUND | ~500 | — |
| N23.3 | MixedExprToStmt | CRIT | ~350 | N23.1 |
| N23.4 | KoalaBearBridge | PAR | ~150 | — (Trust-Lean) |
| N23.5 | GoldilocksBridge | PAR | ~200 | — (Trust-Lean) |
| N23.6 | SynthesisToC | CRIT | ~300 | N23.3, N23.4, N23.5 |
| N23.7 | BenchmarkTests | HOJA | ~200 | N23.6 |
| N23.8 | CostIntegration | HOJA | ~150 | N23.1, N23.6 |

#### Progress Tree

- [x] B83: N23.1 EnhancedCostModel (238 LOC, 4 thms, 0 sorry)
- [x] B84: N23.2 BitVecBridge (592 LOC, 33 thms, 0 sorry)
- [x] B85: N23.3 MixedExprToStmt (316 LOC, 7 thms + soundness, 0 sorry)
- [x] B86: N23.4 KoalaBearBridge (230 LOC) | N23.5 GoldilocksBridge (208 LOC) — Trust-Lean, 0 sorry
- [x] B87: N23.6 SynthesisToC (255 LOC, 6 thms, 0 sorry)
- [x] B88: N23.7 CostIntegration (207 LOC) | N23.8 CodegenTests (244 LOC) — 0 sorry

---

### Fase 24: E-Graph Discovery Engine — v3.3.0

**Goal**: Enable the E-graph to DISCOVER optimal bitwise reductions by generating 80+ rules programmatically, controlling explosion via guided saturation + shadow graph, and extracting with polynomial-time DP when possible.

**Key Innovation**: Guided Saturation (single unified E-graph with phased rule activation) replaces Cascade E-graph. Later-phase rules see earlier equivalences.

**Anti-Explosion Architecture** (4 layers, from QA):
1. **PREDICT**: Growth bound prediction (VR1CS maxNodesBound) → decide fuel/budget
2. **GENERATE**: Shift-Add (CSD), Congruence, Lazy Reduction rules → 80+ rules automatically
3. **SATURATE**: Guided Saturation + Shadow Graph + Rule Scoring (UCB1-lite)
4. **EXTRACT**: Treewidth DP (tw≤15) → ILP → Greedy fallback

**Synthesis-by-Verification**: Rule generator proposes candidates → Lean tactic proves LHS=RHS → only verified rules enter ruleset.

**Key Decisions** (from QA):
1. Guided Saturation (NOT Cascade): single E-graph, phased rule activation (fuel 0-10 algebraic, 10-40 bitwise, 40-50 scheduling)
2. CSD decomposition for shift-add (optimal non-zero bits)
3. Congruence bounded: k ∈ [bitWidth-2..2*bitWidth+2] (~10 rules, not 128)
4. Lazy Reduction with verified `maxAbsValue` interval analysis
5. Shadow Graph operational (outside TCB) — extraction still verified via extractF_correct

#### Architectural Gap: MatEGraph ↔ MixedEGraph Two-Layer Connection

**Problem identified** (2026-03-27): The project has two optimization levels that should feed each other but are currently disconnected:

- **Level 1 (algorithmic)**: `NTTFactorizationRules.lean` defines 5 strategies (`radix2DIT`, `radix2DIF`, `radix4DIT`, `splitRadix`, `kroneckerPacked`) as `MatRewriteRule` over `MatENodeOp`. These rules describe how to decompose NTT into stages with different factorizations.
- **Level 2 (arithmetic)**: `MixedEGraph` + `MultiRelMixed` + `BoundPropagation` fully optimize each butterfly's modular reduction (Solinas/Montgomery/Harvey/lazy) with bound tracking.

**What's missing**: Level 1 has rule definitions but **no saturation loop** (no `MatEGraph` executor). Plan generation in `NTTPlanSelection.generateCandidates` is hardcoded to 5 candidates (all radix-2). Consequence: `Butterfly4Bridge` (200 LOC, proven cost savings) is never used in practice. The two-layer feedback loop — where Level 2 cost information guides Level 1 factorization choices — does not exist.

**Evidence**:
- `NTTFactorizationRules.lean:allNTTFactorizationRules` → 4 rules defined, never executed
- `NTTPlanSelection.lean:generateCandidates` → 5 hardcoded candidates, 0 radix-4
- `Butterfly4Bridge.lean` → complete, proven, zero consumers
- `MatENodeOp` (in Vector.lean) → 12-constructor inductive type, no e-graph operations

**Solution**: Extend Fase 24 with two new nodes (N24.11, N24.12) that implement the MatEGraph saturation loop and extraction to NTTPlan. GuidedSaturation's `threePhaseSaturateF` pattern is reusable (parametric in step functions and fuel), but requires new step functions over `MatENodeOp` and a cost oracle that queries Level 2.

**Quick win (independent, ~100 LOC)**: Extend `generateCandidates` to include radix-4 and mixed-radix plans. This activates `Butterfly4Bridge` and captures ~80% of the value without the full MatEGraph machinery. Can be done at any time without waiting for Fase 24 integration.

**Dependency**: The correctness bridge `nttPlan_semantic_preservation` depends on the butterfly foldl lemmas being proven in `StageSimulation.lean` (`dit_bottomUp_eq_ntt_generic`, `dit_bottomUp_eq_ntt_spec`).

#### DAG (v3.3.0)

```
N24.1 ShiftAddGen (FUND) ──→ N24.5 GuidedSaturation (CRIT)
N24.2 CongruenceGen (FUND) ──→
N24.3 LazyReduction (PAR) ──→
N24.4 ShadowGraph (FUND) ──→ N24.5
N24.6 RuleScoring (PAR) ──→ N24.5
N24.7 GrowthPrediction (PAR) ──→ N24.5
N24.8 TreewidthDP (CRIT) ──→ N24.9 DiscoveryPipeline (HOJA)
N24.5 ──→ N24.11 MatEGraphStep (FUND)
N24.11 ──→ N24.12 MatPlanExtraction (CRIT)
N24.12 ──→ N24.9
N24.8 ──→ N24.9
N24.9 ──→ N24.10 DiscoveryTests (HOJA)
```

| Node | Name | Type | LOC | Deps |
|------|------|------|-----|------|
| N24.1 | ShiftAddGen | FUND | ~300 | — |
| N24.2 | CongruenceGen | FUND | ~250 | — |
| N24.3 | LazyReduction | PAR | ~250 | — |
| N24.4 | ShadowGraph | FUND | ~250 | — |
| N24.5 | GuidedSaturation | CRIT | ~400 | N24.1-N24.4, N24.6, N24.7 |
| N24.6 | RuleScoring | PAR | ~200 | — |
| N24.7 | GrowthPrediction | PAR | ~200 | — |
| N24.8 | TreewidthDP | CRIT | ~500 | — |
| N24.9 | DiscoveryPipeline | HOJA | ~300 | N24.8, N24.12 |
| N24.10 | DiscoveryTests | HOJA | ~250 | N24.9 |
| N24.11 | MatEGraphStep | FUND | ~300 | N24.5 |
| N24.12 | MatPlanExtraction | CRIT | ~200 | N24.11 |
| **Total** | | | **~3,400** | |

#### Blocks

| Block | Nodes | Execution |
|-------|-------|-----------|
| B89 | N24.1 | FUND sequential |
| B90 | N24.2 | FUND sequential |
| B91 | N24.3, N24.6, N24.7 | PAR parallel |
| B92 | N24.4 | FUND sequential |
| B93 | N24.5 | CRIT sequential (after all B89-B92) |
| B94 | N24.8 | CRIT sequential (independent) |
| B97 | N24.11 | FUND sequential (after B93) |
| B98 | N24.12 | CRIT sequential (after B97) |
| B95 | N24.9 | HOJA sequential (after B94+B98) |
| B96 | N24.10 | HOJA sequential |

#### Progress Tree

- [x] B89: N24.1 ShiftAddGen (229 LOC, 17 decls, 0 sorry — wiring PASS)
- [x] B90: N24.2 CongruenceGen (210 LOC, 12 decls, 0 sorry — wired to GuidedSaturation.phase2CongruenceRules)
- [x] B91: N24.3 LazyReduction (290 LOC) | N24.6 RuleScoring (199 LOC) | N24.7 GrowthPrediction (213 LOC) — all 0 sorry, wiring PASS
- [x] B92: N24.4 ShadowGraph (241 LOC, 25 decls, 0 sorry — W2 advisory: 2 dead fields, W4: infinityCost redefined)
- [x] B93: N24.5 GuidedSaturation (281 LOC, 21 decls, 0 sorry — W2 advisory: 6 GuidedResult fields unread, W4: phase1Rules/phaseSafeFuel redefined)
- [x] B94: N24.8 TreewidthDP (195 LOC, 18 decls, 0 sorry — W2 advisory: DPEntry.bestChild unread)
- [x] B97: N24.11 MatEGraphStep (250 LOC, 0 sorry — CostOracle + radix assignment exploration + Fibonacci growth bound)
- [x] B98: N24.12 MatPlanExtraction (175 LOC, 3 sorry de-risk — assignmentToPlan + selectBestPlanExplored + refinePlanBounds)
- [x] B95: N24.9 DiscoveryPipeline (192 LOC, 0 sorry — imports MatPlanExtraction, totalRuleCount fixed for phase2CongruenceRules)
- [x] B96: N24.10 DiscoveryTests (178 LOC) + ReductionDecomp (214 LOC) wired to Pipeline — 959 jobs, 0 errors

#### Detailed Node Specifications — N24.11, N24.12 (Two-Layer Connection)

**N24.11 FUNDACIONAL — MatEGraphStep** (~300 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/MatEGraphStep.lean`
- Purpose: Saturation loop for `MatRewriteRule` over `MatENodeOp`, connecting algorithmic-level NTT factorization exploration to the arithmetic-level MixedEGraph.
- **What exists already** (reuse, not rewrite):
  - `MatENodeOp` inductive type (12 constructors: identity, dft, ntt, twiddle, perm, kron, compose, add, smul, transpose, conjTranspose, elemwise) — in `Vector.lean`
  - `MatRewriteRule` structure (name, canApply, description) — in `NTTFactorizationRules.lean`
  - `allNTTFactorizationRules` (4 rules: radix2DIT, radix2DIF, radix4DIT, kroneckerPack) — in `NTTFactorizationRules.lean`
  - `threePhaseSaturateF` pattern (parametric in step functions) — in `GuidedSaturation.lean`
  - `GrowthPrediction.maxNodesBound` (reusable for any rule set) — in `GrowthPrediction.lean`
- **What needs to be built**:
  1. `MatEGraph` type: lightweight hashcons over `MatENodeOp` e-classes (NOT the full MixedEGraph — matrix operations are coarser-grained, ~50-200 nodes max for a single NTT)
  2. `matApplyRule : MatEGraph → MatRewriteRule → MatEGraph` — single rule application (match + rewrite)
  3. `matSaturateStep : MatEGraph → MatEGraph` — apply all matching rules, rebuild
  4. `matSaturateF : MatEGraph → Nat → MatEGraph` — fuel-bounded loop using `threePhaseSaturateF` pattern
  5. Cost oracle: `matNodeCost : MatENodeOp → Level2CostQuery → Nat` — queries Level 2 (MixedEGraph + BoundPropagation) for the arithmetic cost of implementing a specific factorization
- **Key design decision**: The cost oracle is the feedback channel. When the MatEGraph evaluates "radix-4 DIT for stage 3", it asks Level 2: "what's the cheapest reduction strategy for a radix-4 butterfly with input bound k=3 on ARM NEON?" Level 2 answers using `selectReductionForBound` + `reductionCost`. This makes algorithmic choices cost-aware without duplicating the arithmetic cost model.
- **Growth control**: MatEGraph is small (NTT of size 2^20 has ~20 stages, each stage has ~5 factorization options → ~100 nodes max). Explosion risk is LOW compared to MixedEGraph. Still use `maxNodesBound` as safety check.
- **De-risk**: Implement `matSaturateF` with a single phase first (no three-phase structure). Three-phase only if rule interactions require phasing (unlikely at this granularity).
- Theorems: `matSaturateF_terminates`, `matSaturateF_preserves_valid` (valid = all e-classes represent semantically equivalent NTT factorizations)

**N24.12 CRITICO — MatPlanExtraction** (~200 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/MatPlanExtraction.lean`
- Purpose: Extract optimal `NTTPlan` from a saturated `MatEGraph`, replacing the 5 hardcoded candidates in `generateCandidates`.
- **What exists already** (reuse):
  - `NTTPlan.Plan` structure with per-stage `NTTStage` (radix, reduction, direction, bounds) — in `NTTPlan.lean`
  - `mkBoundAwarePlan` (constructs plan with per-stage bound tracking) — in `NTTPlan.lean`
  - `extractF_correct` / `extractILP_correct` (extraction correctness for MixedEGraph) — pattern reusable
  - `TreewidthDP` (polynomial extraction for tw≤15) — in `Discovery/TreewidthDP.lean`
- **What needs to be built**:
  1. `matExtract : MatEGraph → (MatENodeOp → Nat) → NTTPlan.Plan` — greedy extraction with cost function
  2. `matExtractDP : MatEGraph → NiceTree → NTTPlan.Plan` — DP extraction via TreewidthDP (optional, for large NTTs)
  3. `refinePlanWithBounds : NTTPlan.Plan → BoundRuleFactory → NTTPlan.Plan` — post-extraction bound refinement: for each stage in the extracted plan, query BoundPropagation for optimal reduction choice
  4. `matExtract_correct` theorem: extracted plan is semantically equivalent to the original NTT specification
- **Integration with existing pipeline**: Replace `generateCandidates` call in `NTTPlanSelection.selectBestPlan` with: (1) build MatEGraph from NTT spec, (2) saturate with `matSaturateF`, (3) extract with `matExtract`, (4) refine with `refinePlanWithBounds`. Backward compat: `generateCandidates` becomes a fallback when MatEGraph is not available or fuel=0.
- **Correctness bridge**: `nttPlan_semantic_preservation` — the master theorem connecting algorithmic plan to NTT spec. Depends on `StageSimulation.dit_bottomUp_eq_ntt_generic` (proven) and butterfly foldl lemmas (in progress by another agent). This is the HIGH-risk deliverable; if intractable, fallback to `native_decide` for BabyBear N≤16 + documented sorry.
- De-risk: `matExtract` greedy first, DP only if extraction quality is poor.

**Quick Win (independent of N24.11/N24.12, ~100 LOC)**:
- File: `NTTPlanSelection.lean` (modify `generateCandidates`)
- Add radix-4 and mixed-radix candidates:
  ```lean
  mkUniformPlan p n .r4 .solinasFold,        -- radix-4 + Solinas
  mkUniformPlan p n .r4 .montgomery,          -- radix-4 + Montgomery
  mkMixedRadixPlan p n hwIsSimd arrayIsLarge, -- radix-4 early, radix-2 late
  ```
- This activates `Butterfly4Bridge` (currently orphaned) and captures ~80% of the radix-4 value
- Can be done ANY time, does not depend on Fase 24 integration
- Does NOT replace N24.11/N24.12 — enumeration is not exploration, but is sufficient for 3-4 prime fields

---

### Known Limitations & Design Decisions (Autopsy 2026-03-27)

**F1. E-matching evaluates on constant-collapsed environments (DESIGN)**
`applyRulesF_preserves_cv` requires `env.witnessVal = env.constVal ∧ env.pubInputVal = env.constVal`. This is intentional: e-matching soundness is proven for a simplified evaluation model where all input sources collapse to constants (see `MixedEMatchSoundness.lean:712-716`, syntheticEnv construction). This enables pattern matching to use a single evaluation function. For full circuit evaluation with distinct witnesses/pubInputs, the e-graph results are trusted via `pipeline_mixed_equivalent` which operates at the UF root level.

**F2. VerifiedCodeGen has two lowering paths (21/21 constructors covered)**
The autopsy flagged 7 "uncovered" MixedNodeOp constructors in `lowerMixedExprToLLE`. This is a measurement artifact: the 3 reduction constructors (montyReduceE, barrettReduceE, harveyReduceE) require conditionals (`Stmt.ite`) which LowLevelExpr cannot express. They are covered by `lowerMixedExprFull` (VerifiedCodeGen.lean:96-123) which delegates to TrustLeanBridge's `lowerHarveyReduce`, `lowerMontyReduce`, `lowerBarrettReduce` — all producing verified Stmt with Stmt.ite. Total coverage: 21/21 constructors across both paths.

**F3. ConsistentValuation constructible incrementally (non-vacuity validated)**
`full_pipeline_soundness` assumes initial ConsistentValuation. This CAN be constructed via `empty_consistent` + `merge_consistent` chain (SemanticSpec.lean:110-115, MixedSemanticSpec.lean:46-123). Non-vacuity example in `Tests/NonVacuity/PipelineCV.lean`.

**F4. roundtrip_succeeds sorry (BLOCKED, dead code)**
`RoundtripSoundness.lean:154` has `sorry`. Blocker: `MatUnionFind.find` is `partial` (no equation lemmas). The theorem is used by nobody — superseded by 8 concrete `native_decide` examples in the same file (lines 163-206). Resolving requires either: (a) making `find` total with fuel, or (b) proving equation lemmas for the partial function.

**F5. NTT field invertibility (LOW, covered by [Field F])**
`dit_bottomUp_eq_ntt_spec` requires `[Field F]` (top-level variable), which includes multiplicative inversion. `IsPrimitiveRoot` is a lightweight monoid property that does NOT require field structure, but the field constraint is inherited from the file-level variable declaration. Non-vacuity example in `Tests/NonVacuity/NTTDIT.lean`.

**F6. pipeline_mixed_equivalent name clarification**
This theorem proves: "if two e-classes have the same UF root AND extraction succeeds for both, the results are semantically equivalent." It does NOT prove that saturation produces the UF equivalence — that is the job of `saturateMixedF_preserves_consistent`. The name reflects post-saturation extraction correctness.

**F7. full_pipeline_soundness outputs existential (soundness, not optimality)**
The conclusion `∃ v_sat, ConsistentValuation ... ∧ evalExpr expr env = v_sat root` proves soundness: the extracted expression evaluates correctly. It does NOT prove optimality (that the extraction is cost-minimal). Optimality is a property of the cost model, not the soundness chain.

---

### Fase 25: FRI Fold + Poseidon Bound-Aware Optimization — v3.3.1

**Goal**: Connect Level 1↔Level 2 optimization feedback to FRI fold and Poseidon S-box primitives. The existing infrastructure (CostOracle, selectReductionForBound, BoundPropagation, stageBoundFactor) is already generalized — only instantiation for new primitives is needed.

**Key insight**: CostOracle and selectReductionForBound take bounds and return reductions — they don't know they're working with NTT. FRI fold (bound ~2p after mul+add) and Poseidon S-box (bound ~p^d after exponentiation) simply provide different bound inputs.

**New files** (3):
- `AmoLean/EGraph/Verified/Bitwise/FRIFoldPlan.lean` — FRI fold reduction selection
- `AmoLean/EGraph/Verified/Bitwise/PoseidonStagePlan.lean` — Poseidon per-round reduction
- `AmoLean/EGraph/Verified/Bitwise/PrimitivesIntegration.lean` — Unified primitive dispatch

#### DAG (v3.3.1)

```
N25.1 FRIFoldPlan (FUND) ──→ N25.3 PrimitivesIntegration (HOJA)
N25.2 PoseidonStagePlan (PAR) ──→ N25.3
```

| Node | Name | Type | LOC | Deps | File |
|------|------|------|-----|------|------|
| N25.1 | FRIFoldPlan | FUND | ~80 | — | Bitwise/FRIFoldPlan.lean |
| N25.2 | PoseidonStagePlan | PAR | ~100 | — | Bitwise/PoseidonStagePlan.lean |
| N25.3 | PrimitivesIntegration | HOJA | ~70 | N25.1, N25.2 | Bitwise/PrimitivesIntegration.lean |
| **Total** | | | **~250** | | |

#### Blocks

| Block | Nodes | Execution |
|-------|-------|-----------|
| B99 | N25.1 | FUND sequential |
| B100 | N25.2 | PAR (parallel with B99) |
| B101 | N25.3 | HOJA (after B99 + B100) |

#### Progress Tree

- [ ] B99: N25.1 FRIFoldPlan
- [ ] B100: N25.2 PoseidonStagePlan
- [ ] B101: N25.3 PrimitivesIntegration

#### Detailed Node Specifications

**N25.1 FUNDACIONAL — FRIFoldPlan** (~80 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/FRIFoldPlan.lean`
- FRI fold = `alpha * f_odd[i] + f_even[i]` — bound after mul+add is ~2p
- `FRIFoldConfig` structure: field prime, alpha bound factor, hardware target
- `selectFRIReduction` := direct reuse of `selectReductionForBound 2 hwIsSimd arrayIsLarge`
- `friFoldCost` using existing CostOracle (butterflyCost pattern for mul+add)
- Smoke tests: BabyBear + Goldilocks FRI fold cost comparisons

**N25.2 PARALELO — PoseidonStagePlan** (~100 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/PoseidonStagePlan.lean`
- Poseidon S-box = x^d (d=7 BabyBear, d=5 BN254) — bound after exponentiation explodes (~p^d)
- `PoseidonStageConfig`: field prime, exponent d, number of full/partial rounds
- `selectPoseidonReduction`: per-round reduction selection
  - Full rounds: aggressive reduction mandatory (Montgomery, bound too large for Harvey/lazy)
  - Partial rounds: only 1 S-box per round, bounds smaller → lazy possible?
- Bound tracking: `poseidonBoundAfterSbox(inputK, d) := inputK * d` (multiplicative growth)
- `poseidonStageCost` using existing CostOracle
- Smoke tests: BabyBear Poseidon t=8, full vs partial round cost difference

**N25.3 HOJA — PrimitivesIntegration** (~70 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/PrimitivesIntegration.lean`
- Unified `selectPrimitiveReduction(primitive, boundK, hw)` dispatching to NTT/FRI/Poseidon
- Integration smoke test: same prime (BabyBear), different primitives → different reduction choices:
  - NTT butterfly (bound ~2p) → Harvey
  - FRI fold (bound ~2p) → Harvey (same as NTT)
  - Poseidon S-box (bound ~p^7) → Montgomery
- Wire into UltraPipeline: extend report to include FRI + Poseidon costs

#### Formal Properties (v3.3.1)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N25.1 | selectFRIReduction produces valid ReductionChoice for all fields | SOUNDNESS | P0 |
| N25.1 | FRI fold cost ≤ NTT butterfly cost (same field, same hw) | OPTIMIZATION | P1 |
| N25.2 | Poseidon full-round always selects aggressive reduction (not lazy) | INVARIANT | P0 |
| N25.2 | poseidonBoundAfterSbox monotone in exponent d | PRESERVATION | P1 |
| N25.3 | Same prime + different primitives → can produce different reductions | COMPLETENESS | P0 |

---

### Fase 26: Pipeline Soundness + Benchmarks — v3.4.0

**Goal**: Compose `ultra_pipeline_soundness` (Fases 22-24), bridge backward compat to v1 pipeline, generate + benchmark optimized NTT code with radix-4/mixed plans vs Plonky3.

**Lessons applied**: L-513 (compositional proofs ~30 LOC), L-311 (three-part contract), L-338 (fuel via max not sum), L-572 (three-tier bridge), codegen emission gap (match type widths, no silent defaults)

**Key infrastructure reused**: UltraPipeline.lean (237 LOC), MixedPipeline.lean (`pipeline_mixed_equivalent`, `compose_sound`), ReductionComposition.lean (`compose_sound`), MixedExprToRust.lean, StageSimulation.lean (`dit_bottomUp_eq_ntt_spec`, 0 sorry), benchmark.sh, 15+ existing bench files

**New files** (4):
- `AmoLean/EGraph/Verified/Bitwise/UltraSoundness.lean` — Master composition theorem
- `AmoLean/EGraph/Verified/Bitwise/UltraBridge.lean` — v2 → v1 backward compat bridge
- `AmoLean/EGraph/Verified/Bitwise/UltraBenchGen.lean` — Rust NTT code generation with radix-4/mixed plans
- `Tests/NonVacuity/UltraPipeline.lean` — Non-vacuity + mixed-radix integration tests

**Modified files** (1): `scripts/benchmark.sh` (add hyperfine + radix-4 profiles)

#### DAG (v3.3.1)

```
N26.1 UltraSoundness (FUND) ──→ N26.2 v2Bridge (CRIT) ──→ N26.5 IntegrationTests (HOJA)
N26.3 BenchCodeGen (PAR, independent) ──→ N26.4 BenchRunner (HOJA)
```

| Node | Name | Type | LOC | Deps | File |
|------|------|------|-----|------|------|
| N26.1 | UltraSoundness | FUND | ~300 | Fases 22-24 | Bitwise/UltraSoundness.lean |
| N26.2 | v2BridgeTheorem | CRIT | ~200 | N26.1 | Bitwise/UltraBridge.lean |
| N26.3 | BenchCodeGen | PAR | ~150 | — | Bitwise/UltraBenchGen.lean |
| N26.4 | BenchRunner | HOJA | ~100 | N26.3 | scripts/ + Tests/interop/ |
| N26.5 | IntegrationTests | HOJA | ~100 | N26.1, N26.2 | Tests/NonVacuity/UltraPipeline.lean |
| **Total** | | | **~850** | | |

#### Blocks

| Block | Nodes | Execution |
|-------|-------|-----------|
| B103 | N26.1 | FUND sequential (de-risk sketch first) |
| B104 | N26.2 | CRIT sequential (after B103) |
| B105 | N26.3 | PAR (independent, parallel with B103-B104) |
| B106 | N26.4, N26.5 | HOJA (after B104 + B105) |

#### Progress Tree

- [ ] B103: N26.1 UltraSoundness
- [ ] B104: N26.2 v2BridgeTheorem
- [ ] B105: N26.3 BenchCodeGen
- [ ] B106: N26.4 BenchRunner | N26.5 IntegrationTests

#### Detailed Node Specifications

**N26.1 FUNDACIONAL — UltraSoundness** (~300 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/UltraSoundness.lean`
- Purpose: Master composition theorem `ultra_pipeline_soundness` threading Fases 22-24.
- **Intermediate state formalization** (QA amendment):
  - `Post_F22_Valid` : MRCV preserved after multi-relation colored saturation
  - `Post_F23_Valid` : NTT plan semantically equivalent to DFT spec (via `dit_bottomUp_eq_ntt_spec`)
  - `Post_F24_Valid` : Discovery engine preserves CCV (via `threePhaseSaturateF_preserves_consistent`)
- **Composition pattern**: Dependent threading (L-513), NOT flat conjunction. Each state feeds the next:
  ```
  initial_state → saturate(MRCV) → Post_F22_Valid
  Post_F22_Valid → extractPlan(semantic) → Post_F23_Valid
  Post_F23_Valid → discover(CCV) → Post_F24_Valid
  Post_F24_Valid → output_correct
  ```
- Fuel: compose via `max` (L-338), not sum
- Three-part contract (L-311): fuel availability + result semantics + frame preservation
- De-risk: sketch as chain of implications between intermediate states BEFORE full proof. If composition is intractable (>3 sessions), fallback to `native_decide` for BabyBear N=16 + documented sorry
- Theorems: `ultra_pipeline_soundness`, `ultra_pipeline_fuel_bound`

**N26.2 CRITICO — v2BridgeTheorem** (~200 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/UltraBridge.lean`
- Purpose: Prove backward compatibility — Ultra pipeline (v2: bounds+colors+discovery) implies existing `pipeline_mixed_equivalent` (v1).
- `v2_implies_v1_soundness`: any expression optimized by Ultra pipeline is also valid under the base pipeline
- Pattern: projection — v2 state contains v1 state as sub-structure. The extra fields (bounds, colors, discovery rules) are refinements that don't invalidate base equivalences
- Consumes: `pipeline_mixed_equivalent` from MixedPipeline.lean, `ultra_pipeline_soundness` from N26.1
- De-risk: if projection is not clean (v2 modifies base state), may need adapter theorem. Check that `MultiRelMixed.saturate` with `nullFactory` produces same result as base `saturateF`

**N26.3 PARALELO — BenchCodeGen (Verified C + Rust FFI)** (~200 LOC)
- Files: `AmoLean/EGraph/Verified/Bitwise/UltraBenchGen.lean` + `Tests/interop/ultra_ffi/`
- Purpose: Generate **verified C code** via Path A (VerifiedCodeGen → TrustLeanBridge → Trust-Lean backend), then wrap in Rust FFI for benchmarking.
- **Architecture** (decision 2026-03-27: avoid unverified string emission):
  ```
  Path A (VERIFIED):
  selectBestPlanExplored → NTTPlan → MixedExpr
    → lowerMixedExprToLLE [theorem: lowerOp_correct]
    → Trust-Lean Stmt [theorem: evalStmt_correct]
    → Trust-Lean C backend → verified .c files

  Rust FFI wrapper (trivial, ~30 LOC per field):
  extern "C" { fn reduce_babybear(x: u64) -> u64; }
  // Benchmark harness calls verified C kernel via FFI
  ```
- **Why NOT MixedExprToRust (Path B)**: String emission layer is NOT verified. Prior incident: 11/12 Rust + 9 C files defective despite correct proofs. Unacceptable for industry presentation.
- **Why C + FFI**: Trust-Lean C backend is the only verified code emitter. Rust FFI wrapper is trivial (`extern "C"`) and auditable. The benchmark measures exactly the verified kernel.
- 4 fields: BabyBear, Mersenne31, Goldilocks, KoalaBear
- **Test vectors**: generate input/output pairs from Lean spec, validate C output matches before benchmarking
- **Future**: Trust-Lean Rust backend (separate project) will eliminate the FFI layer

**N26.4 HOJA — BenchRunner** (~100 LOC)
- Extends: `scripts/benchmark.sh` + `Tests/interop/`
- **Statistical methodology** (QA amendment): `hyperfine --warmup 3 --min-runs 10` for all comparisons, report mean/stddev/min/max
- Targets: BabyBear NTT +25-30% vs Plonky3, Goldilocks +15-20%, KoalaBear +20-25%
- N = 2^20 for all benchmarks (production-relevant size)
- Compare against: Plonky3 `Radix2Bowers::dft_batch` (the fastest known Plonky3 NTT)
- Output: CSV results + summary in BENCHMARKS.md

**N26.5 HOJA — IntegrationTests** (~100 LOC)
- File: `Tests/NonVacuity/UltraPipeline.lean`
- Non-vacuity example: BabyBear N=1024 (pure radix-4 path, covers `ultra_pipeline_soundness` hypotheses)
- **Mixed-radix test** (QA amendment): N=512 (radix-4 + radix-2 mixed path) to exercise `mkMixedRadixPlan` logic
- `#print axioms ultra_pipeline_soundness` = 0 custom axioms
- `#print axioms v2_implies_v1_soundness` = 0 custom axioms

#### Formal Properties (v3.4.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N26.1 | ultra_pipeline_soundness threads all three invariants (MRCV, semantic, CCV) | SOUNDNESS | P0 |
| N26.1 | ultra_pipeline_fuel_bound ≤ max of phase fuels | INVARIANT | P1 |
| N26.2 | v2_implies_v1_soundness: Ultra result → base pipeline_mixed_equivalent | PRESERVATION | P0 |
| N26.2 | v2_null_factory_eq_v1: Ultra with null factory = base saturation | EQUIVALENCE | P1 |
| N26.3 | Generated C is formally verified (Path A: lowerOp_correct + evalStmt_correct chain) | SOUNDNESS | P0 |
| N26.3 | Rust FFI wrapper matches C output on Lean spec test vectors | PRESERVATION | P0 |
| N26.4 | BabyBear NTT ≥ 1.25× Plonky3 (mean, N=2^20) | OPTIMIZATION | P0 |
| N26.5 | Non-vacuity: all hypotheses of ultra_pipeline_soundness jointly satisfiable | INVARIANT | P0 |
| N26.5 | #print axioms ultra_pipeline_soundness = 0 custom axioms | SOUNDNESS | P0 |

---

## Version History

| Version | Date | Highlights |
|---------|------|------------|
| **v2.5.1** | Mar 2026 | Extraction completeness: bestNode DAG acyclicity (bestCostLowerBound_acyclic), fuel sufficiency (extractF_of_rank, extractAuto_complete). Ported from OptiSat v1.5.1. 1 new file, 0 sorry, 0 axioms. |
| **v2.5.0** | Mar 2026 | VerifiedExtraction Integration: generic greedy extraction framework (Core + Greedy + CircuitAdaptor), 4 new files, 914 LOC, 17 theorems, 0 sorry, 0 axioms |
| **v2.4.2** | Feb 2026 | Bridge Correctness — 10 SoundRewriteRule instances, 0 sorry, 0 axioms |
| **v2.4.1** | Feb 2026 | Operational-verified FRI bridges + Plausible property testing |
| **v2.4.0** | Feb 2026 | FRI formal verification (9 files, 2,844 LOC, 123 theorems, 0 sorry, 0 axioms) + barycentric interpolation |
| **v2.3.0** | Feb 2026 | Pipeline soundness + axiom elimination (0 custom axioms, 77 declarations) |
| **v2.2.0** | Feb 2026 | Trust-Lean bridge (26 theorems, 0 sorry, roundtrip + injectivity) |
| **v2.1.0** | Feb 2026 | Verified e-graph engine (121 theorems, 0 sorry) |
| **v2.0.0** | Feb 2026 | Lean 4.16 -> 4.26 migration |
| **v1.1.0** | Feb 2026 | FRI verified, Goldilocks/BabyBear 0 axioms |
| **v1.0.0** | Feb 2026 | Initial release: AlgebraicSemantics, 2850+ tests |


- v2.1.0: Lean 4.26 + verified e-graph engine
- v2.0.0: Major restructuring
- v1.1.0: FRI verified
- v1.0.0: Initial release
