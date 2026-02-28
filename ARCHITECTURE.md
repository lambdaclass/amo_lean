# AMO-Lean: Architecture

## Current Version: v2.4.1 (planning)


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

---

## Key Design Decisions (v2.4.1)

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
| **v2.4.1** | Feb 2026 | **PLANNED**: Operational-verified FRI bridges + Plausible property testing |
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
