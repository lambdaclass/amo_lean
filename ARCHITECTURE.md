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
| N11.6 Butterfly4 Foundation | FUND | — | deprecated (v2.9.0 — superseded by GenericNTT) |
| N11.7 NTT_radix4 + Spec Equivalence | CRIT | N11.6 | deprecated (v2.9.0 — superseded by GenericNTT) |
| N11.8 INTT_radix4 + Roundtrip Identity | CRIT | N11.6, N11.7 | deprecated (v2.9.0 — superseded by GenericNTT) |
| N11.9 Equivalence Proofs | PAR | N11.7, N11.8 | deprecated (v2.9.0 — superseded by GenericNTT) |
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
- [x] **B35 Butterfly4 Foundation**: N11.6 — DEPRECATED (v2.9.0, superseded by GenericNTT)
- [x] **B36 NTT Radix-4**: N11.7 — DEPRECATED (v2.9.0, superseded by GenericNTT)
- [x] **B37 INTT + Equivalence**: N11.8, N11.9 — DEPRECATED (v2.9.0, superseded by GenericNTT)
- [x] **B38 Perm + Translation Validation**: N11.10, N11.11 (PARALELO) ✓
- [x] **B39 Integration + Audit**: N11.12 (SECUENCIAL) ✓

#### Execution Order

```
Branch A (Pipeline, G4+G5):
  B31 (N11.1 FUND) → B32 (N11.2 FUND) → B33 (N11.3+N11.4 PAR) → B34 (N11.5 CRIT)

Branch B (NTT Radix-4, G2):                    ← DEPRECATED v2.9.0 (superseded by GenericNTT + Fase 24)
  B35–B37: archived to archive/NTT_Radix4/

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

- [x] B99: N25.1 FRIFoldPlan (110 LOC, 0 sorry, wiring PASS)
- [x] B100: N25.2 PoseidonStagePlan (240 LOC, 0 sorry, wiring PASS)
- [x] B101: N25.3 PrimitivesIntegration (145 LOC, 0 sorry — entry point for Fase 27)

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

### Fase 26: Spec-Driven Reduction Discovery — v3.4.0

**Goal**: E-graph discovers modular reduction implementations from specification `reduce(x) ≡ x mod p`, potentially better than Barrett/Montgomery/Solinas for specific primes.

**Novel contribution**: First verified framework where an e-graph discovers modular reduction algorithms from specification, not from hand-coded rules. Uses the Herbie model: domain axioms + operator vocabulary + cost-optimal extraction.

**Architecture**:
```
Spec Axiom: reduce(x) = x % p (e-class equivalence)
    ↓
Bitwise Vocabulary (templates + pre-computed constants per prime)
    ↓
Guided Saturation (4-phase, dynamic pruning via best-found cost)
    ↓
Top-K Candidate Extraction (HardwareCost ranking)
    ↓
Tactic Verification (tri-state: Verified | FailedToVerify | Rejected)
    ↓
Ranked verified implementations
```

**Lessons applied**: L-505 (explosion → SaturationConfig limits), L-690 (SHI integrity), L-513 (compositional proofs)

**New files** (7):
- `AmoLean/EGraph/Verified/Bitwise/Discovery/ReduceSpecAxiom.lean`
- `AmoLean/EGraph/Verified/Bitwise/Discovery/BitwiseVocabulary.lean`
- `AmoLean/EGraph/Verified/Bitwise/Discovery/SpecDrivenSaturation.lean`
- `AmoLean/EGraph/Verified/Bitwise/Discovery/CandidateExtraction.lean`
- `AmoLean/EGraph/Verified/Bitwise/Discovery/TacticVerification.lean`
- `AmoLean/EGraph/Verified/Bitwise/Discovery/SpecDrivenRunner.lean`
- `Tests/NonVacuity/SpecDrivenDiscovery.lean`

#### DAG (v3.4.0)

```
N26.1 ReduceSpecAxiom (FUND) ──→ N26.3 ExplosionControl (CRIT)
N26.2 BitwiseVocabulary (FUND) ──→ N26.3
N26.3 ──→ N26.4 CandidateExtraction (CRIT) ──→ N26.6 DiscoveryRunner (HOJA)
N26.5 TacticVerification (PAR) ──→ N26.6
N26.6 ──→ N26.7 IntegrationTests (HOJA)
```

| Node | Name | Type | LOC | Deps |
|------|------|------|-----|------|
| N26.1 | ReduceSpecAxiom | FUND | ~150 | — |
| N26.2 | BitwiseVocabulary | FUND | ~200 | — |
| N26.3 | ExplosionControl | CRIT | ~250 | N26.1, N26.2 |
| N26.4 | CandidateExtraction | CRIT | ~200 | N26.3 |
| N26.5 | TacticVerification | PAR | ~150 | — |
| N26.6 | DiscoveryRunner | HOJA | ~150 | N26.4, N26.5 |
| N26.7 | IntegrationTests | HOJA | ~100 | N26.6 |
| **Total** | | | **~1200** | |

#### Blocks

| Block | Nodes | Execution |
|-------|-------|-----------|
| B107 | N26.1 | FUND sequential (de-risk: CV preservation sketch) |
| B108 | N26.2 | FUND sequential (de-risk: 1 rule soundness proof) |
| B109 | N26.3 | CRIT sequential (after B107+B108) — **GATE** |
| B110 | N26.4 | CRIT sequential (after B109) |
| B111 | N26.5 | PAR (parallel with B109-B110) |
| B112 | N26.6 | HOJA (after B110+B111) |
| B113 | N26.7 | HOJA (after B112) |

#### Progress Tree

- [x] B107: N26.1 ReduceSpecAxiom (382 LOC, 0 sorry)
- [x] B108: N26.2 BitwiseVocabulary (205 LOC, 0 sorry)
- [x] B109: N26.3 ExplosionControl (215 LOC, 0 sorry)
- [x] B110: N26.4 CostBiasedExtract (199 LOC, 0 sorry)
- [x] B111: N26.5 VerificationOracle (119 LOC, 0 sorry)
- [x] B112: N26.6 DiscoveryRunner (153 LOC, 0 sorry)
- [x] B113: N26.7 IntegrationTests (115 LOC, 0 sorry)

#### Detailed Node Specifications

**N26.1 FUNDACIONAL — ReduceSpecAxiom** (~150 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/ReduceSpecAxiom.lean`
- `ReduceSpec` structure: prime p, input bound (`x < 2^w`), word width w
- `insertReduceSpec : ReduceSpec → MixedEGraph → MixedEGraph` — inserts e-class equivalence `reduce(x) ↔ x % p`
- **Arithmetic domain**: `Nat` with explicit bounds (`x < 2^w`). Proofs use Nat arithmetic + `Nat.mod`. Lifting bridge to `BitVec w` as future work.
- Theorem: `insertReduceSpec_preserves_cv`
- De-risk: sketch insertion + CV preservation before full proof

**N26.2 FUNDACIONAL — BitwiseVocabulary** (~200 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/BitwiseVocabulary.lean`
- **Templates** (parametric, instantiated per-run by N26.6):
  - Shift decomposition: `x = (x >> k) * 2^k + (x & (2^k - 1))`
  - Mask identity: `x & (2^w - 1) = x % 2^w`
  - Conditional subtraction: `if x ≥ p then x - p else x`
  - Barrett skeleton: `x - floor(x * m / 2^k) * p` (parametric in m, k)
  - Montgomery skeleton: `(x + (x * mu % R) * p) / R` (parametric in mu, R)
  - Add/Sub modular: `(a + b) % p`, `(a - b + p) % p`
- Templates take `(p, w, constants)` parameters. Constants pre-computed in N26.6, NOT during saturation.
- Each instantiated rule: `MixedSoundRule` with proven soundness on Nat with bounds
- De-risk: prove soundness of 1 rule (shift decomposition) before implementing all

**N26.3 CRITICO — ExplosionControl** (~250 LOC) — **GATE**
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/SpecDrivenSaturation.lean`
- Extends `GuidedSaturation` with spec-driven 4-phase saturation:
  - Phase 0 (fuel 0-3): Insert spec axiom only
  - Phase 1 (fuel 3-10): Algebraic rules (existing 12)
  - Phase 2 (fuel 10-30): Field-specific + vocabulary rules
  - Phase 3 (fuel 30-40): Bitwise decomposition (CSD + shifts)
- **Dynamic pruning** (QA amendment): once a complete reduction (no `reduce` subterms) is found, its cost becomes the pruning bound. Before first solution: `known_best_cost * 1.5`.
- `GrowthPrediction`: abort if predicted nodes > 5000
- Theorem: `specDrivenSaturateF_preserves_consistent`
- De-risk: test with BabyBear that saturation terminates within fuel and produces ≥1 candidate

**N26.4 CRITICO — CandidateExtraction** (~200 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/CandidateExtraction.lean`
- `extractTopK : MixedEGraph → Nat → HardwareCost → Array MixedExpr`
- Extracts TOP-K candidates (K=10 default), each a different bitwise implementation of `x % p`
- Cost ranking per hardware target (ARM scalar, NEON, AVX2)
- Theorem: extracted candidates semantically equivalent to spec (inherited from CV)

**N26.5 PARALELO — TacticVerification** (~150 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/TacticVerification.lean`
- **Tri-state result** (QA amendment):
  ```
  Verified(expr, cost)       — tactic proved candidate(x) % p = x % p
  FailedToVerify(expr, cost) — tactic failed, logged for manual inspection
  Rejected(reason)           — structurally invalid
  ```
- Tactic cascade: `[native_decide, omega, ring, norm_num, simp [Nat.mod]]`
- `FailedToVerify` candidates logged, not silently dropped
- Smoke: known Solinas/Barrett/Montgomery all classify as `Verified`

**N26.6 HOJA — DiscoveryRunner** (~150 LOC)
- File: `AmoLean/EGraph/Verified/Bitwise/Discovery/SpecDrivenRunner.lean`
- **Constant pre-computation** (QA amendment): given `(p, w)`, computes:
  - Barrett: `m = floor(2^k / p)` for k ∈ {w, 2w}
  - Montgomery: `mu = -p^{-1} mod 2^w`, `R = 2^w`
  - Solinas: if `p = 2^a - c`, extract `(a, c)`
- Instantiates vocabulary templates → concrete `MixedSoundRule` list
- End-to-end: `discoverReduction(p, hw) → List VerificationResult`
- Comparison table: discovered vs known costs

**N26.7 HOJA — IntegrationTests** (~100 LOC)
- File: `Tests/NonVacuity/SpecDrivenDiscovery.lean`
- Non-vacuity: `discoverReduction` produces ≥1 `Verified` for BabyBear
- Comparison: discovered cost ≤ known best (or document why)
- `#print axioms`: 0 custom axioms on `VerificationResult.verified`

#### Formal Properties (v3.4.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N26.1 | insertReduceSpec_preserves_cv | PRESERVATION | P0 |
| N26.2 | All vocabulary rules sound on Nat with bounds | SOUNDNESS | P0 |
| N26.3 | specDrivenSaturateF_preserves_consistent | SOUNDNESS | P0 |
| N26.3 | Dynamic pruning tightens monotonically | INVARIANT | P1 |
| N26.4 | Extracted candidates equivalent to spec (inherited from CV) | SOUNDNESS | P0 |
| N26.5 | Known algorithms (Solinas/Barrett/Montgomery) all verify | COMPLETENESS | P0 |
| N26.6 | discoverReduction produces ≥1 verified for all 4 ZK primes | COMPLETENESS | P0 |
| N26.7 | 0 custom axioms on VerificationResult.verified | SOUNDNESS | P0 |

#### Discovery Targets

| Prime | Known best | Discovery target |
|-------|-----------|-----------------|
| BabyBear (2^31 - 2^27 + 1) | Solinas fold (6 cycles ARM) | ≤ 6 cycles or novel |
| Mersenne31 (2^31 - 1) | Solinas fold (3 cycles ARM) | ≤ 3 cycles or novel |
| Goldilocks (2^64 - 2^32 + 1) | Solinas fold (8 cycles ARM) | ≤ 8 cycles or novel |
| KoalaBear (2^31 - 2^24 + 1) | Solinas fold (5 cycles ARM) | ≤ 5 cycles or novel |

---

#### Fase 26 Corrección 1: Connect Discovery to Real Saturation Engine

**Problem**: Fase 26 implemented 1388 LOC of discovery pipeline that does NOT use the verified saturation engine. `SpecDrivenRunner.discoverReduction` built its own graph, ran identity saturation, and extracted from it — bypassing `guidedOptimizeMixedF`, `saturateMixedF`, `reductionAlternativeRules`, and `allBitwisePatternRulesWithBridges` which already exist and are verified.

**Goal**: Replace the standalone discovery pipeline with one that delegates to the real engine. Connect Level 2 (reduction discovery) with Level 1 (NTT plan optimization via `CostOracle`).

**Infrastructure that MUST be used** (not reimplemented):
- `MixedRunner.guidedOptimizeMixedF` — 3-phase guided saturation pipeline
- `MixedSaturation.saturateMixedF` — the real rewrite engine
- `ReductionAlternativeRules.reductionAlternativeRules` — Barrett/Montgomery/Harvey rules (already exist)
- `MixedPatternRules.allBitwisePatternRulesWithBridges` — bitwise pattern rules (already exist)
- `MixedEGraphBuilder.buildEGraph` — handles `reduceE` seeds

**Files that are NOT touched**: ReduceSpecAxiom, BitwiseVocabulary, CostBiasedExtract, VerificationOracle.

**Archivos modificados/nuevos**:
- `Discovery/SpecDrivenRunner.lean` — REWRITE: delegate to `guidedOptimizeMixedF`
- `Discovery/OracleAdapter.lean` — NEW: bridge discovery cost → `CostOracle`
- `Discovery/JointOptimization.lean` — NEW: coordinate `matSaturateF` + `discoverReduction`
- `Tests/NonVacuity/SpecDrivenDiscovery.lean` — REWRITE: update to new API
- `Discovery/ExplosionControl.lean` — DEPRECATE (add header, no delete)

##### DAG

```
C26.2 SpecDrivenRunner (FUND) ──→ C26.3 OracleAdapter (CRIT)
C26.3 ──→ C26.4 JointOptimization (HOJA)
C26.2 + C26.3 + C26.4 ──→ C26.5 NonVacuity (HOJA)
ExplosionControl deprecation (PAR, independent)
```

| Node | Name | Type | LOC est | Deps | Status |
|------|------|------|---------|------|--------|
| C26.2 | SpecDrivenRunner rewrite | FUND | 126 | — | DONE |
| C26.3 | OracleAdapter | CRIT | 153 | C26.2 | DONE |
| C26.4 | JointOptimization | HOJA | 114 | C26.3 | DONE |
| C26.5 | NonVacuity tests | HOJA | 82 | C26.2-4 | DONE |
| — | ExplosionControl deprecation | PAR | 11 | — | DONE |

##### Blocks

| Block | Nodes | Execution |
|-------|-------|-----------|
| B114 | C26.2 | FUND sequential — compile + smoke tests |
| B115 | C26.3 | CRIT sequential — fix struct mismatch, compile |
| B116 | C26.4 | HOJA (after B115) |
| B117 | C26.5 | HOJA (after B114-B116) — rewrite NonVacuity |

##### Progress Tree

- [x] B114: C26.2 SpecDrivenRunner rewrite (126 LOC, 0 sorry)
- [x] B115: C26.3 OracleAdapter (153 LOC, 0 sorry)
- [x] B116: C26.4 JointOptimization (114 LOC, 0 sorry)
- [x] B117: C26.5 NonVacuity tests (82 LOC, 0 sorry)
- [x] ExplosionControl deprecation header

##### Constraints

- 0 sorry, 0 errores, `lake build` limpio
- Non-vacuity examples for all theorems with ≥3 Prop hypotheses
- `spec_audit.py` + `wiring_check.py` before closing any node

---

### Fase 27: OptiSat v2 Port + Three-Objective Integration — v3.5.0

**Goal**: Port OptiSat v2 infrastructure (relational saturation, colored e-graphs, Ruler) to enable:
- **Q1**: Per-stage optimal modular reduction in NTT with verified lazy reduction
- **Q2**: Algorithm-level optimization (radix-2/4/mixed auto-selection, cross-level cost queries)

First phase cleans up ~2,200 LOC of island dead code from prior agents.

**OptiSat v2 source**: `~/Documents/claudio/optisat/LambdaSat/` (5,914 LOC, 180 theorems, 0 sorry). Policy: copy/adapt, never import.

**Adaptation pattern** (proven Fases 11-16, L-458): copy file → rename namespace → replace generic `Op/Expr/Val` with concrete `MixedNodeOp/MixedExpr/Nat` → adapt proofs.

**Lessons applied**: L-458 (concrete evalOp), L-704 (coarsening automatic), L-709 (SHI threading), L-513 (compositional proofs), L-719 (wiring check), L-121 (explicit semantic bridge), L-512 (three-tier bridge)

#### Ultra-Branch Reuse Map

Every block's Pre-Block Briefing MUST consult this map to know what exists.

**REUSED AS-IS** (ultra files used without modification):

| File | LOC | Used by Node(s) | How |
|------|-----|-----------------|-----|
| `Discovery/ReduceSpecAxiom.lean` | 382 | N27.12 | `insertReduceSpec` + `insertReduceSpec_preserves_cv` base of discovery |
| `Discovery/BitwiseVocabulary.lean` | 205 | N27.12 | Vocabulary templates for saturation rules |
| `Discovery/VerificationOracle.lean` | 119 | N27.12, N27.10 | Test-based verification + test inputs for Ruler |
| `Discovery/GuidedSaturation.lean` | 288 | N27.12 | `threePhaseSaturateF_preserves_consistent` pattern |
| `Discovery/ShiftAddGen.lean` | 229 | N27.10, N27.12 | CSD decomposition, ops for Ruler evaluator |
| `Discovery/CongruenceGen.lean` | 210 | N27.12 | Congruence rules for saturation |
| `Discovery/ReductionDecomp.lean` | 214 | N27.12 | Barrett/Montgomery/Harvey rule generation |
| `Discovery/LazyReduction.lean` | 290 | N27.7, N27.11 | Interval bounds feed BoundRelation + StageContext |
| `Discovery/GrowthPrediction.lean` | 213 | N27.5 | Anti-explosion bounds for tiered saturation |
| `Discovery/RuleScoring.lean` | 199 | N27.5 | UCB1 scoring for tiered saturation |
| `Discovery/TreewidthDP.lean` | 195 | N27.5 | DP extraction routing |
| `Discovery/MatEGraphStep.lean` | 288 | N27.14 | `matSaturateF_preserves_levels` for multi-level |
| `Discovery/MatPlanExtraction.lean` | 212 | N27.16 | Plan extraction from MatEGraph |
| `Discovery/JointOptimization.lean` | 114 | N27.16 | `jointOptimize_sound` |
| `Discovery/OracleAdapter.lean` | 153 | N27.15 | Bridge discovery cost → CostOracle for NTT plan |
| `GuidedMixedSaturation.lean` | 122 | N27.12 | `guidedOptimizeMixedF` called by discoverForStage |
| `NTTPlan.lean` | 300 | N27.13 | Plan/NTTStage/RadixChoice structures |
| `NTTPlanSelection.lean` | 189 | N27.13 | `selectBestPlanExplored` + cost model |
| `CrossRelNTT.lean` | 189 | N27.15 | Cross-relation NTT rules |
| `MatNodeOps.lean` | 261 | N27.14, N27.16 | MatOp types in import chain |
| `RulerDiscovery.lean` | 188 | N27.10 | Basic CVec (partial, extended by full Ruler) |
| **Total reused as-is** | **~4,560** | | |

**EXTENDED** (ultra files modified by the plan):

| File | LOC | Plan Node | What changes |
|------|-----|-----------|-------------|
| `HardwareColors.lean` | 207 | N27.8 | Add `assumption : MixedEnv → Prop` field to `MixedColoredSoundRule` |
| `Discovery/SpecDrivenRunner.lean` | 126 | N27.12 | Add `discoverReductionForStage(spec, stageCtx)` + rename misleading theorem |
| `NTTPlanCodeGen.lean` | 165 | N27.13 | Add per-stage reduce dispatch (`emitPerStageNTT`) |
| `Matrix/BreakdownBridge.lean` | 127 | N27.14 | Complete TODO at line 116 (recursive multi-level expansion) |
| `Matrix/CrossEGraphBridge.lean` | 88 | N27.15 | Add `queryButterflyReduceCost` for cross-level queries |
| `Matrix/CrossEGraphProtocol.lean` | 179 | N27.16 | Rewrite `jointOptimizeToNTTPlan` to USE factorization result |
| **Total extended** | **~892** | | |

**SUPERSEDED** (ultra files whose functionality is replaced by OptiSat v2 port — extend, don't delete):

| File | LOC | Plan Node | Strategy |
|------|-----|-----------|----------|
| `Bitwise/RelationTypes.lean` | 125 | N27.4 | EXTEND: add OptiSat `DirectedRelGraph`, `hasPath_implies_relation` etc. |
| `Bitwise/DirectedRelSpec.lean` | 117 | N27.4 | EXTEND: add `DirectedRelConsistency`, `bidirectional_path_implies_eq` |
| `Bitwise/MultiRelMixed.lean` | 245 | N27.5 | EXTEND: replace with full `MultiRelMixedEGraph` = base + colored + relDags |
| `Bitwise/BoundPropagation.lean` | 184 | N27.9 | EXTEND: replace identity `relStep` with real bound propagation |
| `Bitwise/BoundIntegration.lean` | 168 | N27.9 | REWIRE: point to new relStep, update consumers |
| **Total superseded** | **~839** | | |

**DELETED** (island modules, N27.1):

| File | LOC | Reason |
|------|-----|--------|
| `UltraPipeline.lean` | 236 | Island (0 importers) |
| `Discovery/ExplosionControl.lean` | 226 | Island, DEPRECATED |
| `Discovery/ShadowGraph.lean` | 241 | Island |
| `Discovery/CostBiasedExtract.lean` | 199 | Island |
| `FRI/Verified/PrimitivesIntegration.lean` | 149 | Island |
| `NTT/StageSimulation.lean` | 1,231 | Island (+ 2 test files) |
| **Total deleted** | **~2,282** | |

**NOT USED** (stays in codebase, not referenced by plan):

| File | LOC | Reason |
|------|-----|--------|
| `Matrix/RoundtripSoundness.lean` | 208 | Has sorry line 154, no consumer |
| `Discovery/Pipeline.lean` | 206 | Spec-level System A, no executor |
| `Discovery/Tests.lean` | 178 | Tests of System A only |
| `Phase23Integration.lean` | 142 | Old integration wiring |
| **Total not used** | **~734** | |

#### DAG (v3.5.0)

```
FASE 27A: CLEANUP
  N27.1 Dead Code Elimination (FUND) -------+
                                             |
FASE 27B: OPTISAT V2 CORE PORT              |
  N27.2 SmallUF + ColoredLayer (FUND) --+   |
  N27.3 CCV + SoundColoredRule (FUND) --+   |
  N27.4 DirectedRelSpec (FUND) ---------+   |
  N27.5 MultiRelEGraph + Tiered (CRIT)<-+   |
  N27.6 Ruler Pipeline (PAR) --------+      |
                                      |      |
FASE 27C: DOMAIN INSTANCES            |      |
  N27.7 BoundRelation (FUND) <--N27.4 |     |
  N27.8 HW Colors+Assumptions (CRIT)<-N27.3 |
  N27.9 relStep Impl (CRIT) <--N27.5,N27.7  |
  N27.10 Ruler Evaluator (PAR) <--N27.6     |
                                      |      |
FASE 27D: Q1 -- PER-STAGE DISCOVERY   |      |
  N27.11 StageContext+Lazy (CRIT)<--N27.9    |
  N27.12 discoverForStage (CRIT)<--N27.11    |
  N27.13 Per-Stage CodeGen (PAR) <--N27.12   |
                                      |      |
FASE 27E: Q2 -- ALGORITHM SEARCH      |      |
  N27.14 MatEGraph Multi-Level (CRIT)<-+--N27.1
  N27.15 Cross-Level Costs (CRIT)<--N27.14,N27.8
  N27.16 factorizationToPlan (PAR)<--N27.15  |
                                      |      |
FASE 27F: INTEGRATION                 |      |
  N27.17 E2E Demo + Tests (HOJA) <----+------+
```

| Node | Name | Type | Est. LOC | Deps | File(s) |
|------|------|------|----------|------|---------|
| N27.1 | Dead Code Elimination | FUND | -2,200 | — | See DELETED table above |
| N27.2 | SmallUF + ColoredLayer | FUND | ~350 | — | NEW: `Bitwise/ColoredEGraph.lean` |
| N27.3 | CCV + SoundColoredRule | FUND | ~300 | N27.2 | NEW: `Bitwise/ColoredSpec.lean` |
| N27.4 | DirectedRelSpec | FUND | ~250 | — | EXTEND: `Bitwise/RelationTypes.lean` + `Bitwise/DirectedRelSpec.lean` |
| N27.5 | MultiRelEGraph + Tiered | CRIT | ~350 | N27.2,N27.3,N27.4 | EXTEND: `Bitwise/MultiRelMixed.lean` |
| N27.6 | Ruler Pipeline | PAR | ~500 | — | NEW: `Discovery/Ruler/*.lean` (5 files) |
| N27.7 | BoundRelation MixedNodeOp | FUND | ~200 | N27.4 | NEW: `Bitwise/BoundRelation.lean` |
| N27.8 | HW Colors + Assumptions | CRIT | ~150 | N27.3 | EXTEND: `Bitwise/HardwareColors.lean` |
| N27.9 | relStep Implementation | CRIT | ~200 | N27.5,N27.7 | EXTEND: `Bitwise/BoundPropagation.lean` + `BoundIntegration.lean` |
| N27.10 | Ruler Evaluator | PAR | ~150 | N27.6 | NEW: `Discovery/Ruler/MixedEval.lean` |
| N27.11 | StageContext + Lazy | CRIT | ~200 | N27.9 | NEW: `Discovery/StageContext.lean` |
| N27.12 | discoverForStage | CRIT | ~200 | N27.11 | EXTEND: `Discovery/SpecDrivenRunner.lean` |
| N27.13 | Per-Stage CodeGen | PAR | ~150 | N27.12 | EXTEND: `Bitwise/NTTPlanCodeGen.lean` |
| N27.14 | MatEGraph Multi-Level | CRIT | ~200 | N27.1 | EXTEND: `Matrix/BreakdownBridge.lean` |
| N27.15 | Cross-Level Costs | CRIT | ~200 | N27.14,N27.8 | EXTEND: `Matrix/CrossEGraphBridge.lean` |
| N27.16 | factorizationToPlan | PAR | ~150 | N27.15 | REWRITE: `Matrix/CrossEGraphProtocol.lean` |
| N27.17 | E2E Demo + Tests | HOJA | ~200 | N27.13,N27.16,N27.10 | NEW: `Tests/NonVacuity/OptiSatV2.lean` |

**Total new**: ~3,750 LOC. **Deleted**: ~2,200 LOC. **Net**: +1,550 LOC.

#### Blocks

| Block | Nodes | Execution | Gate |
|-------|-------|-----------|------|
| B114 | N27.1 | FUND sequential | `lake build` 0 errors |
| B115 | N27.2 | FUND sequential | `lake env lean ColoredEGraph.lean` |
| B116 | N27.3, N27.4 | FUND parallel | `lake build` both |
| B117 | N27.5 | CRIT sequential (after B115+B116) | `lake build` |
| B118 | N27.6 | PAR (parallel with B115-B117) | compile all Ruler/*.lean |
| B119 | N27.7, N27.8 | FUND+CRIT parallel (after B116,B115) | `lake build` |
| B120 | N27.9 | CRIT sequential (after B117+B119) — **GATE** | `lake build` + #eval smoke |
| B121 | N27.10 | PAR (after B118) | compile + #eval smoke |
| B122 | N27.11, N27.12 | CRIT sequential (after B120) | `lake build` + #eval per-stage |
| B123 | N27.13 | PAR (after B122) | #eval NTT per-stage reduce |
| B124 | N27.14, N27.15, N27.16 | CRIT+PAR (after B114,B119) | #eval factorization |
| B125 | N27.17 | HOJA (after B123+B124+B121) | wiring_check + spec_audit + `lake build` |

**Per-block reuse reference** (worker MUST read before coding):

| Block | Ultra files REUSED as-is | Ultra files EXTENDED | OptiSat source files | Ultra files SUPERSEDED |
|-------|--------------------------|---------------------|---------------------|----------------------|
| B114 | — | — | — | — (deletion only) |
| B115 | — | — | `ColorTypes.lean`, `ColoredMerge.lean` | — |
| B116 | — | — | `ColoredSpec.lean`, `ColoredEMatch.lean`, `DirectedRelSpec.lean`, `RelationTypes.lean` | `RelationTypes.lean`, `DirectedRelSpec.lean` |
| B117 | `GrowthPrediction`, `RuleScoring`, `TreewidthDP` | — | `MultiRelSaturate.lean`, `MultiRelSoundness.lean`, `MultiRelEGraph.lean` | `MultiRelMixed.lean` |
| B118 | — | — | `Ruler/TermEnumerator.lean`, `CVecEngine.lean`, `CVecMatcher.lean`, `RuleMinimizer.lean`, `SelfImprovement.lean` | — |
| B119 | `LazyReduction.lean` | `HardwareColors.lean` | — | — |
| B120 | — | — | — | `BoundPropagation.lean`, `BoundIntegration.lean` |
| B121 | `VerificationOracle.lean`, `ShiftAddGen.lean`, `RulerDiscovery.lean` | — | — | — |
| B122 | `ReduceSpecAxiom`, `BitwiseVocabulary`, `GuidedSaturation`, `CongruenceGen`, `ReductionDecomp`, `GuidedMixedSaturation` | `SpecDrivenRunner.lean` | — | — |
| B123 | `NTTPlan.lean`, `NTTPlanSelection.lean` | `NTTPlanCodeGen.lean` | — | — |
| B124 | `MatEGraphStep`, `MatPlanExtraction`, `JointOptimization`, `OracleAdapter`, `MatNodeOps`, `CrossRelNTT` | `BreakdownBridge`, `CrossEGraphBridge`, `CrossEGraphProtocol` | — | — |
| B125 | ALL above (integration) | — | — | — |

#### Progress Tree

- [x] B114: N27.1 Dead Code Elimination — 5 files deleted (-900 LOC), 3 already gone (-1,600 LOC), build 3136/0err
- [x] B115: N27.2 SmallUF + ColoredLayer — 310 LOC, 12 theorems, 0 sorry, coarsening verified
- [x] B116: N27.3 CCV + N27.4 DirectedRelSpec — ColoredSpec 240 LOC + hasPath+path_implies 100 LOC, 0 sorry
- [x] B117: N27.5 MultiRelEGraph — coloredLayer+assumptions in State, MRCV+v2_implies_v1, 0 sorry
- [x] B118: N27.6 Ruler Pipeline — Core.lean 270 LOC + consolidated, 0 sorry
- [x] B119: N27.7 BoundRelation + N27.8 HW Colors — BoundRel 115 LOC + assumptions+MixedColoredSoundRule 70 LOC, 0 sorry
- [x] B120: N27.9 relStep Implementation (GATE) — SoundFactory+preserves_base/colored/assumptions proven, 1 sorry (rel induction PENDIENTE)
- [x] B121: N27.10 Ruler Evaluator — MixedEval.lean 110 LOC, mixedEvalOp+discoverMixedRules, 0 sorry
- [x] B122: N27.11 StageContext + N27.12 discoverForStage — StageContext 140 LOC + perStage 80 LOC, 0 sorry
- [x] B123: N27.13 Per-Stage CodeGen — emitPerStageNTT + mkPerStagePlan 40 LOC, 0 sorry
- [x] B124: N27.14-16 — recursive sub-DFT expansion + queryButterflyReduceCost + factorizationToPlan, 0 sorry
- [x] B125: N27.17 E2E Demo + Tests — Q1+Q2+Ruler+Bounds+CCV+MRCV, build 3136/0err

#### Execution Order

```
Branch A (OptiSat Port → Q1):
  B114 (cleanup) → B115 (SmallUF) → B116 (CCV+Rel) → B117 (MultiRel) → B120 (relStep GATE) → B122 (Q1 stage) → B123 (codegen)

Branch B (Ruler, parallel):
  B118 (Ruler) → B121 (MixedEval)

Branch C (Q2, after cleanup):
  B119 (BoundRel+Colors) → B124 (MatEGraph+CrossLevel+Plan)

Convergence:
  B125 (E2E) ← B123 + B124 + B121
```

Branches A, B, C are independent after B114 (cleanup must come first).

#### Detailed Node Specifications

**N27.1 FUNDACIONAL — Dead Code Elimination** (-2,200 LOC)
- Delete 7 files listed in DELETED table above + 2 test files (`Tests/NonVacuity/NTTDIT.lean`, `Tests/VerifiedPipeline/StageSimE2E.lean`)
- Protocol: delete one → `lake build` → verify 0 new errors. Revert if break.
- Anti-pattern: NO creating replacement files. Deletion only.

**N27.2 FUNDACIONAL — SmallUF + ColoredLayer** (~350 LOC)
- File: NEW `AmoLean/EGraph/Verified/Bitwise/ColoredEGraph.lean`
- Port from: OptiSat `LambdaSat/ColorTypes.lean` (268 LOC) + `LambdaSat/ColoredMerge.lean` (295 LOC)
- Contents: `SmallUF` (delta UF, fuel-bounded), `ColoredLayer` (hierarchy + colorUFs + worklists), `compositeFind`, `mergeUnderColor`, `CoarseningInvariant`
- Key theorem: `compositeFind_coarsening` (L-704, one-liner via `foldl_append`)

**N27.3 FUNDACIONAL — CCV + SoundColoredRule** (~300 LOC)
- File: NEW `AmoLean/EGraph/Verified/Bitwise/ColoredSpec.lean`
- Port from: OptiSat `LambdaSat/ColoredSpec.lean` (350 LOC) + `LambdaSat/ColoredEMatch.lean` (141 LOC)
- Contents: `ColoredConsistentValuation (CCV)`, `MixedColoredSoundRule` (with `assumption : MixedEnv → Prop`), `CCV_implies_base_CV`, `soundColoredRule_preserves_CCV`
- Gap to close: current `ColoredRule` in `HardwareColors.lean` has no `assumption` field

**N27.4 FUNDACIONAL — DirectedRelSpec** (~250 LOC)
- Files: EXTEND `Bitwise/RelationTypes.lean` (125 LOC) + `Bitwise/DirectedRelSpec.lean` (117 LOC)
- Port from: OptiSat `LambdaSat/DirectedRelSpec.lean` (307 LOC) + `LambdaSat/RelationTypes.lean` (216 LOC)
- Add: `DirectedRelGraph` (adjacency DAG), `addEdge`, `hasPath`, `hasPath_implies_relation`, `bidirectional_path_implies_eq`, `DirectedRelConsistency`
- Keep existing `MixedSoundRelationRule` (concrete, compatible)

**N27.5 CRITICO — MultiRelEGraph + Tiered Saturation** (~350 LOC)
- File: EXTEND `Bitwise/MultiRelMixed.lean` (245 LOC) — replace current contents with full MultiRelMixedEGraph
- Port from: OptiSat `LambdaSat/MultiRelSaturate.lean` + `MultiRelSoundness.lean` + `MultiRelEGraph.lean`
- Contents: `MultiRelMixedEGraph` (baseGraph + coloredLayer + relDags + assumptions), `tieredStep`, `crossStep` (IMPLEMENTED), `relStep` (identity for now, real in N27.9)
- Key theorems: `full_pipeline_v2_soundness`, `v2_implies_v1_soundness`

**N27.6 PARALELO — Ruler Pipeline** (~500 LOC)
- Files: NEW `Discovery/Ruler/` directory (5 files)
- Port from: OptiSat `LambdaSat/Ruler/` (6 files, skip RuleValidator — use VerificationOracle instead)
- Contents: `TermEnumerator`, `CVecEngine` (5 match modes), `CVecMatcher` (groupByCVec, detectRelation), `RuleMinimizer` (isDerivable), `SelfImprovement` (improvementLoop with fixpoint)
- Adaptation: generic `evalOp : Nat → List Nat → Nat` wired to AMO-Lean in N27.10

**N27.7 FUNDACIONAL — BoundRelation for MixedNodeOp** (~200 LOC)
- File: NEW `Bitwise/BoundRelation.lean`
- REUSES: `Discovery/LazyReduction.lean` interval bounds
- Contents: `BoundedByKP p k`, `solinasFold_bound` (output < 2p), `montyReduce_bound` (output < p), `add_bound_propagate`, `safeWithoutReduce`

**N27.8 CRITICO — Hardware Colors + Assumptions** (~150 LOC)
- File: EXTEND `Bitwise/HardwareColors.lean` (207 LOC)
- Add: `simdAssumption`, `scalarAssumption`, `largeArrayAssumption` as `MixedEnv → Prop`; `MixedColoredSoundRule` instances per context

**N27.9 CRITICO — relStep Implementation** (~200 LOC) — **GATE**
- Files: EXTEND `Bitwise/BoundPropagation.lean` (184 LOC) + `BoundIntegration.lean` (168 LOC)
- THE CORE INNOVATION: implement real `relStep` (OptiSat has identity only)
- Logic: for each node, lookup op type → add BoundedByKP edge (reduce→bound, add→propagate children bounds)
- Theorem: `relStepMixed_preserves_MRCV`
- De-risk: start with solinasFold + addGate only

**N27.10 PARALELO — MixedNodeOp Ruler Evaluator** (~150 LOC)
- File: NEW `Discovery/Ruler/MixedEval.lean`
- REUSES: `VerificationOracle.lean` (test inputs), `ShiftAddGen.lean` (CSD ops), `RulerDiscovery.lean` (basic CVec)
- Contents: `mixedEvalOp` (concrete evaluator), `mixedWorkload` (config for improvementLoop)

**N27.11 CRITICO — StageContext + LazyReduction** (~200 LOC)
- File: NEW `Discovery/StageContext.lean`
- REUSES: `LazyReduction.lean` for `safeWithoutReduce`
- Contents: `StageContext` (stageIndex, totalStages, inputBound, bitwidth, hw, cacheLevel), `reductionDecision` using verified bounds

**N27.12 CRITICO — discoverReductionForStage** (~200 LOC)
- File: EXTEND `Discovery/SpecDrivenRunner.lean` (126 LOC)
- REUSES: `ReduceSpecAxiom`, `BitwiseVocabulary`, `GuidedSaturation`, `CongruenceGen`, `ReductionDecomp`, `GuidedMixedSaturation`
- Add: `discoverReductionForStage(spec, ctx)` — builds MultiRelGraph, runs tiered sat, reads bound, makes per-stage choice
- Rename: `discoverReduction_pipeline_sound` → `insertReduceSpec_sound` (misleading name)

**N27.13 PARALELO — Per-Stage NTTPlanCodeGen** (~150 LOC)
- File: EXTEND `Bitwise/NTTPlanCodeGen.lean` (165 LOC)
- REUSES: `NTTPlan.lean`, `NTTPlanSelection.lean`
- Add: `emitPerStageNTT` — iterates stages, calls discoverForStage per stage, emits different C code per stage

**N27.14 CRITICO — MatEGraph Multi-Level** (~200 LOC)
- File: EXTEND `Matrix/BreakdownBridge.lean` (127 LOC)
- REUSES: `MatEGraphStep.lean`, `MatNodeOps.lean`
- Complete TODO at line 116: recursive sub-DFT expansion (`extractSubDFTs` + recursive `applyBreakdownRulesRecursive`)

**N27.15 CRITICO — Cross-Level Cost Queries** (~200 LOC)
- File: EXTEND `Matrix/CrossEGraphBridge.lean` (88 LOC)
- REUSES: `OracleAdapter.lean`, `CrossRelNTT.lean`
- Add: `queryButterflyReduceCost(p, hw, radix, stageCtx)` — asks Mixed e-graph for per-butterfly cost INCLUDING optimal reduction

**N27.16 PARALELO — factorizationToPlan** (~150 LOC)
- File: REWRITE `Matrix/CrossEGraphProtocol.lean` (179 LOC)
- REUSES: `JointOptimization.lean`, `MatPlanExtraction.lean`
- Fix: `jointOptimizeToNTTPlan` must USE factorization result, not discard it. Add `factorizationToPlan` converter.

**N27.17 HOJA — E2E Demo + Tests** (~200 LOC)
- File: NEW `Tests/NonVacuity/OptiSatV2.lean`
- Demos: Q1 per-stage (#eval emitPerStageNTT), Q2 algorithm (#eval jointOptimizeToNTTPlan 1024), Ruler (#eval improvementLoop), bounds (#eval lookupBound), axiom audit (#print axioms)

#### Formal Properties (v3.5.0)

| Nodo | Propiedad | Tipo | Prioridad |
|------|-----------|------|-----------|
| N27.2 | compositeFind_coarsening: parent merges visible to children | PRESERVATION | P0 |
| N27.3 | CCV_implies_base_CV: backward compatibility | SOUNDNESS | P0 |
| N27.5 | v2_implies_v1_soundness: MultiRel result valid under v1 | SOUNDNESS | P0 |
| N27.7 | solinasFold_bound: output < 2*p | INVARIANT | P0 |
| N27.7 | add_bound_propagate: bounds compose through addition | PRESERVATION | P0 |
| N27.9 | relStepMixed_preserves_MRCV | PRESERVATION | P0 |
| N27.11 | safeWithoutReduce correct: no overflow when predicate holds | SOUNDNESS | P0 |
| N27.12 | per-stage discovery uses verified bounds (not heuristic) | SOUNDNESS | P0 |
| N27.14 | multi-level expansion terminates and covers all sub-DFTs | COMPLETENESS | P0 |
| N27.17 | 0 custom axioms on key theorems | SOUNDNESS | P0 |

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N27.1 | LOW | Incremental deletion |
| N27.2-N27.4 | LOW | Direct port from verified OptiSat code |
| N27.5 | MEDIUM | Composition of ported pieces |
| N27.6 | LOW | Mostly copy with evaluator adapter |
| N27.9 | **HIGH** | **GATE**: relStep is new. De-risk: solinasFold+addGate only first |
| N27.11-12 | MEDIUM | Integration of multiple systems |
| N27.14 | MEDIUM | Recursive expansion, fuel-bounded |
| N27.15 | MEDIUM | Two e-graph engines communicating |

#### Anti-Pattern Guards

1. **NO duplicate types** — use OptiSat adapted types, never reinvent
2. **NO island modules** — every new file MUST have consumer (wiring_check)
3. **NO misleading names** — `pipeline_sound` means FULL pipeline
4. **NO deferring fundacionales** — OptiSat port is FUND, comes FIRST
5. **NO discarding search results** — jointOptimize output MUST be used
6. **ALWAYS close_block.py** before marking any block complete
7. **ALWAYS wiring_check.py** before marking any node complete

---

### Fase 28: Integration Wiring — v3.6.0

**Goal**: Connect the 5 orphaned Fase 27 components so that the system actually delivers:
- A: Automatic bound propagation through the e-graph (eliminating branchPenalty)
- B: Colored rules for hardware-specific optimization (SIMD/scalar/largeArray)
- C: Ruler feedback loop (discovered rules injected into saturation)
- D: Cross-level cost queries driving factorization decisions

**Net**: ~335 LOC new code (pure wiring, no new infrastructure).

#### DAG (v3.6.0)

```
N28.1 coloredStep (FUND) ─────────┐
N28.2 Ruler→SoundRule (PAR) ──┐   │
N28.3 Ruler feedback (PAR) <──┘   │
N28.4 Cross-level scoring (PAR) ──┤
N28.5 MRCV sorry elim (FUND) ─────┤
                                   └→ N28.6 E2E Integration (HOJA)
```

| Node | Name | Type | LOC | Deps | File(s) |
|------|------|------|-----|------|---------|
| N28.1 | coloredStep in tieredStep | FUND | ~60 | — | `MultiRelMixed.lean` |
| N28.2 | Ruler→SoundRule converter | PAR | ~40 | — | `Ruler/Core.lean` |
| N28.3 | Ruler feedback injection | PAR | ~30 | N28.2 | `BoundIntegration.lean` |
| N28.4 | Cross-level cost scoring | PAR | ~50 | — | `CrossEGraphProtocol.lean` |
| N28.5 | MRCV sorry elimination | FUND | ~75 | — | `BoundPropagation.lean` |
| N28.6 | E2E Integration Demo | HOJA | ~80 | all | `Tests/NonVacuity/OptiSatV2.lean` |

#### Blocks

| Block | Nodes | Execution | Gate |
|-------|-------|-----------|------|
| B126 | N28.5 | FUND sequential | 0 sorry in BoundPropagation |
| B127 | N28.1, N28.2, N28.4 | Parallel | `lake build` all three |
| B128 | N28.3 | PAR (after N28.2) | `lake build` + `#eval` |
| B129 | N28.6 | HOJA (after all) | wiring_check + `lake build` |

#### Progress Tree

- [x] B126: N28.5 MRCV sorry elimination — 0 sorry, full foldl induction proven (5 lemmas)
- [x] B127: N28.1 coloredStep + N28.2 Ruler converter + N28.4 Cross-level — coloredStep in tieredStep, queryButterflyReduceCost in factorizationToPlan
- [x] B128: N28.3 Ruler feedback — semanticMatchStep + optimizeNTTFull with Ruler+colored+bound integration
- [x] B129: N28.6 E2E Integration — optimizeNTTFull demo, wiring PASS, 0 sorry in core
- [x] B130: Correction — Ruler vocabulary extended (reduction ops 8-11), optimizeNTTFull seeds with real e-graph + reductionAlternativeRules, BabyBear test inputs

---

### Fase 29: Verified Code Generation Pipeline — v3.7.0

**Goal**: Replace the 7 unverified string-emission codegen files (~3,515 LOC, 78+ `partial def`, 0 theorems) with TrustLean v3.0's verified pipeline. After this phase, ALL externally-shared C/Rust code flows through `MixedExpr → ExpandedSigma → Stmt → MicroC → String` with machine-checked correctness.

**Motivation**: 11/12 Rust + 9 C files were found defective (truncation u32/u64, overflow, syntax errors, wrong field widths). All bugs were in the string-emission layer (Path B), not in formal proofs. TrustLean v3.0 (already a Lake dependency) offers 623 verified properties, 0 sorry, 0 axioms — but AMO-Lean only uses a fraction.

**Insights**: `TRZK_codegen_insights.md`

**What already exists (reuse, NOT rewrite)**:
- `AmoLean/Bridge/TrustLean.lean` (585 LOC, 32 decls) — roundtrip theorems for ScalarVar, IdxExpr, ExpandedKernel, ExpandedSigma. Functions: `verifiedCodeGen`, `verifiedCodeGenMicroC`
- `AmoLean/EGraph/Verified/Bitwise/TrustLeanBridge.lean` (580 LOC, 39 decls) — `CodeGenerable` instance for `MixedOpWithArgs`, `lowerOp` with 20 per-constructor soundness theorems, reduction specs (Harvey, Montgomery, Barrett)
- `AmoLean/EGraph/Verified/Bitwise/VerifiedCodeGen.lean` (738 LOC, 38 decls) — `lowerMixedExprToLLE`, `lowerMixedExprFull`, per-constructor soundness (17 theorems), `lowerDIFButterfly`
- `AmoLean/Bridge/MicroC/SimBridge.lean` (903 LOC, 111 decls) — concrete field correctness via `native_decide` for Mersenne31 + BabyBear (26 correctness + 16 branch + 10 boundary theorems)
- TrustLean v3.0: `expandedSigmaToStmt_correct_full`, `stmtToMicroC_correct`, `parseMicroC_roundtrip_full`, `evalMicroC_int64`, `binOp_agreement`

**What's missing (this phase)**:
1. **MixedExpr → ExpandedSigma full conversion** with semantics preservation
2. **End-to-end composition theorem** chaining extraction → lowering → MicroC → string
3. **Int64 field agreement** proving field ops fit in Int64Range (BabyBear, Mersenne31, Goldilocks)
4. **Goldilocks MicroC programs** (BabyBear + Mersenne31 exist; Goldilocks missing)
5. **Path B deprecation** — mark unverified emitters as UNTRUSTED
6. **E2E roundtrip tests** — compile generated C/Rust, verify against Lean reference

**Lessons applied**: L-572 (Three-Tier Bridge), L-512 (Production Verification), L-620 (Minimize Int64 preconditions), L-297/L-311 (Three-Part Contract), L-368 (Roundtrip as proof bridge), L-307 (Statement-oriented frontend bypass)

#### DAG (v3.7.0)

```
N29.1 MixedExprToSigma (FUND) ──────────┐
N29.2 CompositionTheorem (CRIT) ←── N29.1┤
N29.3 FieldInt64Agreement (FUND) ────────┤
N29.4 GoldilocksMicroC (PAR) ←── N29.3  │
N29.5 PipelineE2E (CRIT) ←── N29.2,N29.3┤
N29.6 DeprecatePathB + E2E Tests (HOJA) ←┘
```

| Node | Name | Type | LOC est. | Deps | File(s) |
|------|------|------|----------|------|---------|
| N29.1 | MixedExpr → ExpandedSigma conversion | FUND | ~250 | — | `AmoLean/Bridge/MixedExprToSigma.lean` |
| N29.2 | End-to-end composition theorem | CRIT | ~300 | N29.1 | `AmoLean/Bridge/VerifiedPipeline.lean` |
| N29.3 | Field Int64 agreement (BabyBear + Mersenne31 + Goldilocks) | FUND | ~200 | — | `AmoLean/Bridge/MicroC/FieldInt64.lean` |
| N29.4 | Goldilocks MicroC programs + SimBridge | PAR | ~250 | N29.3 | `AmoLean/Bridge/MicroC/Goldilocks.lean` |
| N29.5 | Pipeline E2E soundness theorem | CRIT | ~200 | N29.2, N29.3 | `AmoLean/Bridge/VerifiedPipeline.lean` |
| N29.6 | Deprecate Path B + E2E tests | HOJA | ~150 | N29.5 | `Tests/Integration/VerifiedCodeGenE2E.lean` + headers in 7 Path B files |

**Total budget**: ~1,350 LOC new + ~100 LOC modifications to existing files

#### Detailed Node Specifications

**N29.1 FUNDACIONAL — MixedExpr → ExpandedSigma Conversion** (~250 LOC)

Extend `VerifiedCodeGen.lowerMixedExprFull` to produce `TrustLean.ExpandedSigma` instead of raw `Stmt`. The key insight: `lowerMixedExprFull` already lowers MixedExpr → Stmt sequences. This node wraps that in `ExpandedSigma.scalar` with proper gather/scatter patterns.

- Define `mixedExprToExpandedSigma : MixedExpr → ExpandedSigma` composing existing `lowerMixedExprFull` with ExpandedSigma constructors
- Prove `mixedExprToExpandedSigma_injective` (from `convert_injective` in Bridge/TrustLean.lean)
- Prove `mixedExprToExpandedSigma_semantics : evalMixedExpr e env = evalExpandedSigma (convert e) (bridgeEnv env)` — structural induction over MixedExpr, delegating to the 20 per-constructor soundness theorems in TrustLeanBridge.lean
- **De-risk**: Sketch type alignment first. `lowerMixedExprFull` returns `Stmt × LowLevelExpr × Nat`. Wrap in `.scalar kernel gather scatter` where kernel body = lowered Stmt.
- Adapt from: `VerifiedCodeGen.lean:100-128` (lowerMixedExprFull) + `Bridge/TrustLean.lean:426-455` (convertExpandedSigma)

**N29.2 CRÍTICO — End-to-End Composition Theorem** (~300 LOC)

Chain the verified stages into a single theorem:
```lean
theorem verified_codegen_composition (e : MixedExpr) (env : MixedEnv) :
    let sigma := mixedExprToExpandedSigma e
    let stmt := TrustLean.expandedSigmaToStmt (convertExpandedSigma sigma)
    let microc := TrustLean.stmtToMicroC stmt
    let cCode := TrustLean.microCToString microc
    -- Roundtrip: string is canonical
    TrustLean.parseMicroC cCode = some microc ∧
    -- Semantics: MicroC evaluation matches MixedExpr evaluation
    ∃ fuel mcEnv', TrustLean.evalMicroC fuel (initMCEnv env) microc = some (.normal, mcEnv')
```

- Compose: N29.1 `semantics` + TrustLean `expandedSigmaToStmt_correct_full` + `stmtToMicroC_correct` + `parseMicroC_roundtrip_full`
- Three-part contract (L-297): fuel existence, result correctness, frame preservation
- **De-risk**: Each component theorem exists. Main risk is bridge compatibility (env types). Verify `fullBridge` predicate is satisfiable for AMO-Lean environments.

**N29.3 FUNDACIONAL — Field Int64 Agreement** (~200 LOC)

Prove that field operations for BabyBear, Mersenne31, and Goldilocks produce intermediate results within Int64Range, so `binOp_agreement` (TrustLean v3.0) applies.

- For BabyBear (p = 2013265921, fits u32): prove `∀ a b < p, InInt64Range (a + b)`, `InInt64Range (a * b)`, etc. Straightforward: max intermediate = p² < 2⁶³.
- For Mersenne31 (p = 2³¹-1, fits u32): same pattern. max intermediate = (2³¹-1)² < 2⁶³.
- For Goldilocks (p = 2⁶⁴-2³²+1, fits u64): tighter. Multiplication overflows u64. Need `__uint128_t` or split multiplication. Prove `InInt64Range` for add/sub (YES), prove overflow bounds for mul (document as requiring u128 accumulator).
- Use `native_decide` for concrete boundary values + `omega` for range arithmetic.
- Adapt from: `SimBridge.lean` correctness pattern + `TrustLean/MicroC/Int64Agreement.lean`

**N29.4 PARALELO — Goldilocks MicroC Programs + SimBridge** (~250 LOC)

BabyBear and Mersenne31 MicroC programs exist in `Bridge/MicroC/`. Goldilocks is missing.

- Define `Goldilocks.add_prog`, `sub_prog`, `neg_prog`, `mul_prog`, `reduce_prog` as MicroCStmt
- Goldilocks reduction: `x mod (2⁶⁴ - 2³² + 1)` using Solinas form (reduce upper 64 bits)
- Smoke tests via `#eval evalMicroC_uint64` on concrete values
- SimBridge theorems via `native_decide`: correctness, branch analysis, boundary values
- Adapt from: `Bridge/MicroC/BabyBear.lean` (291 LOC) + `Bridge/MicroC/Mersenne31.lean` (267 LOC)

**N29.5 CRÍTICO — Pipeline E2E Soundness** (~200 LOC)

Compose N29.2 (general composition) with N29.3 (Int64 agreement) into field-specific pipeline theorems:

```lean
theorem babybear_verified_pipeline (e : MixedExpr) (env : BabyBearEnv) :
    let cCode := verifiedCodeGenMixedExpr e babybear_config
    -- Code is correct AND fits in int64_t (no overflow)
    PipelineCorrect cCode env ∧ AllOpsInInt64Range e env

theorem mersenne31_verified_pipeline (e : MixedExpr) (env : Mersenne31Env) : ...
theorem goldilocks_verified_pipeline (e : MixedExpr) (env : GoldilocksEnv) : ...
```

- Bundle: composition (N29.2) + Int64 agreement (N29.3) + field-specific SimBridge
- Non-vacuity examples: concrete MixedExpr programs (add, mul, reduce) verified end-to-end
- `#print axioms` on all pipeline theorems → 0 custom axioms

**N29.6 HOJA — Deprecate Path B + E2E Tests** (~150 LOC)

1. Add `UNTRUSTED` headers to 7 Path B files:
   - `CodeGen.lean`, `Backends/Rust.lean`, `FRI/CodeGen.lean`, `Sigma/CodeGen.lean`, `Vector/CodeGen.lean`, `Protocols/Poseidon/CodeGen.lean`, `Protocols/Poseidon/Constants/CodeGen.lean`
   - Header: `/-! UNTRUSTED — This module uses unverified string emission (Path B). For verified code generation, use AmoLean.Bridge.VerifiedPipeline (Path A). See ARCHITECTURE.md Fase 29. -/`
2. E2E integration test: `Tests/Integration/VerifiedCodeGenE2E.lean`
   - Generate C code for BabyBear add/mul/reduce via verified pipeline
   - Verify roundtrip: `parseMicroC(generated_code) = some expected_microc`
   - Verify non-vacuity: concrete field values produce correct output
3. Update README.md with verified codegen usage instructions

#### Blocks

| Block | Nodes | Execution | Gate |
|-------|-------|-----------|------|
| B131 | N29.1 | FUND sequential, de-risk sketch first | `lake env lean` on MixedExprToSigma.lean |
| B132 | N29.3 | FUND sequential, parallel with B131 | `lake env lean` on FieldInt64.lean |
| B133 | N29.2 | CRIT sequential (after B131) | `lake env lean` on VerifiedPipeline.lean |
| B134 | N29.4 | PAR (after B132) | `lake env lean` on Goldilocks.lean |
| B135 | N29.5 | CRIT sequential (after B133 + B132) | `lake build` + `#print axioms` |
| B136 | N29.6 | HOJA (after B135) | wiring_check + `lake build` |

#### Execution Order

```
Branch A (Conversion + Composition):
  B131 (N29.1 FUND) → B133 (N29.2 CRIT) ──────→ B135 (N29.5 CRIT)
                                                      ↓
Branch B (Int64 + Goldilocks):              ← independent, parallelizable
  B132 (N29.3 FUND) → B134 (N29.4 PAR) ──→ B135 (N29.5 CRIT)
                                                      ↓
Final:                                            B136 (N29.6 HOJA)
```

**Branches A and B are fully parallelizable.** B131 + B132 can execute simultaneously. B133 waits only on B131. B134 waits only on B132. B135 merges both branches.

#### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| N29.1 | MEDIUM — wrapping lowerMixedExprFull in ExpandedSigma may need env adapter | De-risk sketch: verify type alignment before implementing |
| N29.2 | MEDIUM — composing 4 theorems requires compatible env types | Use bridge predicates from TrustLean (fullBridge, microCBridge) |
| N29.3 | LOW — BabyBear/Mersenne31 arithmetic easily fits Int64; Goldilocks mul needs u128 doc | Document Goldilocks mul overflow as architectural limitation |
| N29.4 | LOW — follows established BabyBear/Mersenne31 pattern | Copy-adapt from existing MicroC programs |
| N29.5 | LOW — composition of already-proven components | Standard composition pattern |
| N29.6 | LOW — mechanical deprecation + test writing | No formal proof needed |

#### Progress Tree

- [x] B131: N29.1 VerifiedPipeline — 232 LOC, 5 defs, 7 theorems (5 proven, 2 sorry on reduction path), 7 examples ✓
- [x] B132: N29.3 FieldInt64Agreement — 207 LOC, 9 theorems, 0 sorry, BabyBear+Mersenne31 certified, Goldilocks overflow documented ✓
- [x] B133: N29.2 CompositionTheorem — verified_pipeline_sound_simple proven E2E, full reduction path 2 sorry ✓
- [x] B134: N29.4 GoldilocksMicroC — 310 LOC, 5 programs, 14 smoke tests, 0 sorry, Solinas reduction ✓
- [x] B135: N29.5 PipelineE2E — FieldInt64Cert bundles field guarantees, 0 custom axioms ✓
- [x] B136: N29.6 DeprecatePathB + Tests — 7 Path B files marked UNTRUSTED, E2E tests 18/18 PASS ✓

#### Formal Properties (v3.7.0)

| Node | Property | Type | Priority |
|------|----------|------|----------|
| N29.1 | mixedExprToExpandedSigma is injective | PRESERVATION | P0 |
| N29.1 | Conversion preserves evaluation semantics for all 20 MixedNodeOp constructors | SOUNDNESS | P0 |
| N29.2 | Composition theorem chains 4 verified stages end-to-end | SOUNDNESS | P0 |
| N29.2 | Generated MicroC string roundtrips (parse ∘ print = id) | EQUIVALENCE | P0 |
| N29.3 | BabyBear ops ∈ Int64Range (add, sub, mul, reduce) | INVARIANT | P0 |
| N29.3 | Mersenne31 ops ∈ Int64Range (add, sub, mul, reduce) | INVARIANT | P0 |
| N29.3 | Goldilocks add/sub ∈ Int64Range; mul documents u128 requirement | INVARIANT | P1 |
| N29.4 | Goldilocks MicroC programs produce correct field values on boundary inputs | SOUNDNESS | P0 |
| N29.5 | Field-specific pipeline theorems (BabyBear, Mersenne31, Goldilocks) | SOUNDNESS | P0 |
| N29.5 | `#print axioms` shows 0 custom axioms on pipeline theorems | SOUNDNESS | P0 |
| N29.6 | E2E roundtrip test passes for concrete field programs | EQUIVALENCE | P0 |

---

#### Fase 29 Corrección 1: Close Pipeline Soundness Sorry

**Problem**: `VerifiedPipeline.lean` has 2 sorry on `mixedExprToStmt_evaluates` (L75) and `verified_pipeline_sound` (L204). Both try to prove `evalStmt 1 llEnv stmt = some (.normal, llEnv.update resultVar (.int v))` but for reduction nodes (Harvey/Monty/Barrett), `lowerMixedExprFull` produces `.seq childStmt reductionStmt`, so the output env is `(llEnv.update childVar _).update resultVar _` — NOT `llEnv.update resultVar _`.

**Root Cause**: The theorem statements are too strong for the reduction path. The env after `.seq` has multiple temp variable updates, not just the result variable.

**Fix Strategy** (validated by TrustLean patterns — Bridge/Correctness.lean:456-471):
1. **Weaken the conclusion** to existential env: `∃ v env', evalStmt 1 llEnv stmt = some (.normal, env') ∧ env' resultVar = .int v`
2. **Prove by structural induction** on MixedExpr, case split on lowerMixedExprFull
3. For primitives: unfold to single `.assign`, use `lowerMixedExprToLLE_evaluates`
4. For reductions: compose via `evalStmt_seq` + IH on child + unfold `.ite`/`.assign`

**Key Technical Facts** (from TrustLean Core):
- `evalStmt fuel (.seq s1 s2)` passes SAME fuel to both s1 and s2 (no fuel consumed)
- `evalStmt fuel (.ite cond s1 s2)` passes SAME fuel to chosen branch (no fuel consumed)
- `evalStmt fuel (.assign v e)` is fuel-independent (`evalStmt_assign_fuel_indep`)
- Therefore **fuel=1 IS sufficient** — no loops in any reduction lowering
- Lemmas: `evalStmt_seq`, `evalStmt_ite`, `evalStmt_assign` (all `@[simp]` in TrustLean/Core/Eval.lean)
- Fuel monotonicity: `evalStmt_fuel_mono` (TrustLean/Core/FuelMono.lean)

**Lessons applied**: L-338 (fuel via max not sum), L-265 (fuel = depth bound, not resource), L-288 (non-loop constructs fuel-independent)

**What `lowerHarveyReduce` produces** (TrustLeanBridge.lean:374-384):
```
Stmt.ite (ltOp x 2p)           -- x < 2p?
  (Stmt.ite (ltOp x p)         -- x < p?
    (.assign tmpVar x)          -- yes: result = x
    (.assign tmpVar (x - p)))   -- no: result = x - p
  (.assign tmpVar (x - 2p))    -- x >= 2p: result = x - 2p
```
All leaves are `.assign` (fuel-independent). No loops.

**What `lowerMontyReduce` produces** (TrustLeanBridge.lean:438-470):
```
Stmt.seq s1 (Stmt.seq s2 (Stmt.seq s3 s4))
where s1 = .assign mVar (band (mul x mu) mask32)     -- m = (x*mu) & 0xFFFFFFFF
      s2 = .assign sVar (add x (mul m p))             -- s = x + m*p
      s3 = .assign qVar (bshr s 32)                   -- q = s >> 32
      s4 = Stmt.ite (ltOp (p-1) q)                    -- if q >= p
             (.assign resultVar (sub q p))             --   result = q - p
             (.assign resultVar q)                     --   result = q
```
Chain of `.assign` + final `.ite`. No loops. Fuel=1 sufficient.

**What `lowerBarrettReduce` produces** (TrustLeanBridge.lean:495-525):
```
Stmt.seq s1 (Stmt.seq s2 s3)
where s1 = .assign qVar (bshr (mul x m) k)           -- q = (x*m) >> k
      s2 = .assign rVar (sub x (mul q p))             -- r = x - q*p
      s3 = Stmt.ite (ltOp r p)                        -- if r < p
             (.assign resultVar r)                     --   result = r
             (.assign resultVar (sub r p))             --   result = r - p
```
Same pattern. No loops.

**Proof Template for Harvey case** (~20 lines):
```lean
| .harveyReduceE child p ih =>
  simp only [lowerMixedExprFull]
  -- IH on child: ∃ vchild env_child, evalStmt 1 llEnv childStmt = some (.normal, env_child) ∧ env_child childVar = .int vchild
  obtain ⟨vchild, env_child, hchild_eval, hchild_val⟩ := ih llEnv mEnv henv cgs
  -- Unfold evalStmt_seq: first evaluate childStmt, then evaluate reductionStmt in env_child
  simp only [evalStmt_seq, hchild_eval]
  -- Now prove: evalStmt 1 env_child (Stmt.ite ...) = some (.normal, env'')
  -- The .ite evaluates its condition (evalExpr on .binOp .ltOp), routes to a branch (.assign)
  -- Each branch is fuel-independent
  simp only [evalStmt_ite, evalExpr, evalBinOp, hchild_val]
  -- Split on the condition value
  split <;> simp only [evalStmt_assign, evalExpr, evalBinOp, hchild_val]
  -- Each branch produces (.normal, env_child.update resultVar (.int _))
  ...
```

#### DAG (Corrección 1)

```
N_C1.1 lowerMixedExprFull_evaluates (FUND) → N_C1.2 Close sorry (HOJA)
```

| Node | Name | Type | LOC est. | Deps | File(s) |
|------|------|------|----------|------|---------|
| N_C1.1 | `lowerMixedExprFull_evaluates` aux lemma | FUND | ~80 | — | `VerifiedCodeGen.lean` (add after L428) |
| N_C1.2 | Fix statements + close sorry | HOJA | ~30 | N_C1.1 | `VerifiedPipeline.lean` (modify L75-89, L204-219) |

**N_C1.1 FUNDACIONAL — `lowerMixedExprFull_evaluates`** (~80 LOC)

Add to `VerifiedCodeGen.lean` after `lowerMixedExprToStmt_sound` (line 428). Uses firewall `_aux` pattern.

**Statement** (weakened — existential env):
```lean
theorem lowerMixedExprFull_evaluates (e : MixedExpr) (llEnv : LowLevelEnv)
    (mEnv : MixedEnv) (henv : EnvConsistent llEnv mEnv) (cgs : CodeGenState) :
    ∃ (v : Int) (env' : LowLevelEnv),
      let (stmt, resultVar, _) := lowerMixedExprFull e cgs
      evalStmt 1 llEnv stmt = some (.normal, env') ∧
      env' resultVar = .int v := by
  induction e generalizing llEnv mEnv cgs with
  | harveyReduceE child p ih => -- ~20 lines (see template above)
  | montyReduceE child p mu ih => -- ~20 lines (same pattern, 4 seq steps)
  | barrettReduceE child p m ih => -- ~15 lines (same pattern, 3 seq steps)
  | other => -- ~5 lines: delegate to lowerMixedExprToLLE_evaluates
```

**Proof approach per case**:
- **Primitives** (`| other =>`): `lowerMixedExprFull` produces `.assign tmpVar lle`. Use `lowerMixedExprToLLE_evaluates` to get `evalExpr llEnv lle = some (.int v)`. Then `simp [evalStmt_assign]`.
- **Harvey** (`| harveyReduceE child p ih =>`): Get child IH → unfold `evalStmt_seq` → unfold `evalStmt_ite` + `evalExpr` for ltOp condition → split on Bool → each branch is `.assign` (simp).
- **Monty** (`| montyReduceE child p mu ih =>`): Same but 4 sequential `evalStmt_seq` unfolds before final `.ite`.
- **Barrett** (`| barrettReduceE child p m ih =>`): Same but 3 sequential unfolds.

**CRITICAL WARNING for worker**: The `| other =>` case uses a catch-all match, but the match in `lowerMixedExprFull` has `| .harveyReduceE child p =>` etc. as specific cases and `| other =>` as default. Lean's structural induction generates cases for ALL 20 constructors. The proof must handle all 20 individually OR use a tactic that collapses the 17 primitive cases. Strategy: handle the 3 reduction cases first, then use `all_goals (...)` or `repeat (...)` for the 17 primitives which all have identical proof structure.

**EnvConsistent propagation**: For reduction cases, the IH requires `EnvConsistent` for the child's env. Since the child's env IS `llEnv` (we evaluate child in original env), this holds directly. BUT: the reduction stmt evaluates in the UPDATED env (after child). The reduction only reads the result of the child (via `varRef childVar`), not any MixedEnv variables, so `EnvConsistent` isn't needed for the reduction part — only `env' childVar = .int vchild`.

**N_C1.2 HOJA — Fix statements + close sorry** (~30 LOC)

Modify `VerifiedPipeline.lean`:
1. Change `mixedExprToStmt_evaluates` statement (L75) to use existential env
2. Change `verified_pipeline_sound` statement (L204) to use existential env
3. Both proofs become 1-2 line delegations to `lowerMixedExprFull_evaluates`

**New statements**:
```lean
-- WAS: evalStmt 1 llEnv stmt = some (.normal, llEnv.update resultVar (.int v))
-- NOW:
theorem mixedExprToStmt_evaluates (e : MixedExpr) (llEnv : LowLevelEnv)
    (mEnv : MixedEnv) (henv : EnvConsistent llEnv mEnv) :
    ∃ (v : Int) (env' : LowLevelEnv),
      let (stmt, resultVar) := mixedExprToStmt e
      evalStmt 1 llEnv stmt = some (.normal, env') ∧
      env' resultVar = .int v := by
  exact lowerMixedExprFull_evaluates e llEnv mEnv henv {}
```

#### Blocks

| Block | Nodes | Execution | Gate |
|-------|-------|-----------|------|
| B137 | N_C1.1 | FUND sequential, firewall _aux | `lake env lean VerifiedCodeGen.lean` 0 sorry on new theorem |
| B138 | N_C1.2 | HOJA sequential | `lake env lean VerifiedPipeline.lean` 0 sorry total, `lake build` full |

#### Progress Tree

- [x] B137: N_C1.1 lowerMixedExprFull_evaluates — 239 LOC, structural induction over 20 constructors, 0 sorry ✓
- [x] B138: N_C1.2 Fix statements + close sorry — weakened to existential env, both sorry closed via delegation ✓

---

### Fase 30: Verified Production Codegen — v3.8.0

**Goal**: Wire ALL production primitives (NTT, butterfly, FRI fold, Poseidon S-box) through the verified Path A pipeline to produce both C and Rust. After this phase, every piece of code shared externally comes from `lowerMixedExprFull` or `lowerDIFButterflyStmt` or `lowerNTTLoopStmt` → `stmtToC`/`stmtToRust`.

**Problem**: Fase 29 built the pipeline infrastructure but only verified individual arithmetic expressions. The actual code shared with colleagues (NTT loops, butterflies, FRI fold) still used Path B string emission. This phase fixes that.

**Key Insight from Audit**: Most gaps are **trivial wiring** — the verified Stmt-generating functions already exist, we just need to call `stmtToRust` on them. Only NTT loop soundness and Poseidon S-box need new proofs.

**What already exists (DO NOT RECREATE)**:

| Function | File | Soundness Theorem | Emits C? | Emits Rust? |
|----------|------|-------------------|----------|-------------|
| `lowerDIFButterflyStmt` | VerifiedCodeGen.lean:710 | `lowerDIFButterflyStmt_evaluates` (0 sorry) | ✓ `emitDIFButterflyC` | ✗ **MISSING** |
| `lowerNTTLoopStmt` | VerifiedCodeGen.lean:821 | ✗ **MISSING** | ✓ `emitNTTLoopC` | ✗ **MISSING** |
| `solinasFoldMixedExpr` | SynthesisToC.lean:36 | `solinasFoldMixedExpr_eq_foldEval` | ✓ via `mixedExprToC` | ✓ via `mixedExprToRust` |
| `mersenneFoldMixedExpr` | SynthesisToC.lean:47 | `mersenneFoldMixedExpr_eq` | ✓ via `mixedExprToC` | ✓ via `mixedExprToRust` |
| `mixedExprToRust` | VerifiedPipeline.lean:73 | `verified_pipeline_sound` | — | ✓ |
| `mixedExprToRustFn` | VerifiedPipeline.lean:79 | — | — | ✓ (complete function) |
| `stmtToRust` | TrustLean RustBackend | (trusted pretty-printer) | — | ✓ (all 12 constructors) |

**Primes** (Solinas configs already defined in SolinasRuleGen.lean):
- BabyBear: k=27, c=2²⁷-1=134217727, p=2013265921
- Mersenne31: k=31, c=1 (special: fold = hi + lo), p=2147483647
- KoalaBear: k=31, c=2²⁴-1=16777215, p=2130706433
- Goldilocks: k=64, c=2³²-1=4294967295, p=18446744069414584321

#### DAG (v3.8.0)

```
N30.1 Butterfly+NTT Rust wiring (PAR) ──┐
N30.2 Field reduction C+Rust (PAR) ─────┤
N30.3 FRI fold verified (PAR) ──────────┤── all independent ──→ N30.5 E2E tests (HOJA)
N30.4 Poseidon S-box Stmt (CRIT) ───────┤
                                         └──→ N30.6 NTT loop soundness (FUND)
```

| Node | Name | Type | LOC est. | File(s) |
|------|------|------|----------|---------|
| N30.1 | DIF Butterfly Rust + NTT Loop Rust | PAR | ~40 | `VerifiedCodeGen.lean` (add `emitDIFButterflyRust`, `emitNTTLoopRust`) |
| N30.2 | All-primes reduction C+Rust generator | PAR | ~80 | `AmoLean/Bridge/VerifiedProductionCodegen.lean` (NEW) |
| N30.3 | FRI fold via verified Path A | PAR | ~50 | same file |
| N30.4 | Poseidon S-box x⁵ as verified Stmt | CRIT | ~100 | same file |
| N30.5 | E2E production tests | HOJA | ~120 | `Tests/VerifiedProductionE2E.lean` (NEW) |
| N30.6 | NTT loop soundness theorem | FUND | ~200 | `VerifiedCodeGen.lean` (add `lowerNTTLoopStmt_evaluates`) |

#### Detailed Node Specifications

**N30.1 PAR — DIF Butterfly Rust + NTT Loop Rust** (~40 LOC)

Add to `VerifiedCodeGen.lean` after `emitDIFButterflyC` (line 801) and `emitNTTLoopC` (line 882):

```lean
-- EXACT CODE TO ADD (literally 2 functions):

/-- Emit Rust for a complete DIF butterfly. Same verified Stmt as emitDIFButterflyC. -/
def emitDIFButterflyRust (aName bName wName : String) (p k c : Nat) : String :=
  let (stmt, _, _, _) := lowerDIFButterflyStmt
    (.user aName) (.user bName) (.user wName) p k c {}
  TrustLean.stmtToRust 1 stmt

/-- Emit Rust for a complete NTT loop. Same verified Stmt as emitNTTLoopC. -/
def emitNTTLoopRust (logN p k c : Nat) : String :=
  TrustLean.stmtToRust 0 (lowerNTTLoopStmt logN p k c)

/-- Generate complete Rust NTT function with signature. -/
def emitNTTRustFn (logN p k c : Nat) (funcName : String) : String :=
  let stmt := lowerNTTLoopStmt logN p k c
  TrustLean.generateRustFunction {} funcName
    [("data", "&mut [i64]"), ("twiddles", "&[i64]")] stmt (.litInt 0)

/-- Generate complete C NTT function with signature. -/
def emitNTTCFn (logN p k c : Nat) (funcName : String) : String :=
  let stmt := lowerNTTLoopStmt logN p k c
  TrustLean.generateCFunction {} funcName
    [("data", "int64_t*"), ("twiddles", "const int64_t*")] stmt (.litInt 0)
```

Worker: import `TrustLean.Backend.RustBackend` at top of file. Verify `stmtToRust` is accessible. Compile with `lake env lean`.

**N30.2 PAR — All-Primes Reduction C+Rust Generator** (~80 LOC)

Create `AmoLean/Bridge/VerifiedProductionCodegen.lean`:

```lean
import AmoLean.Bridge.VerifiedPipeline
import AmoLean.EGraph.Verified.Bitwise.SynthesisToC
import AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen

-- Use existing SynthesisToC.solinasFoldMixedExpr and mersenneFoldMixedExpr
-- to build MixedExpr for each prime, then emit via verified pipeline.

-- BabyBear: k=27, c=134217727
def babybear_reduce_c : String := mixedExprToCFn (solinasFoldMixedExpr babybear_solinas) "babybear_reduce" [("x", "int64_t")]
def babybear_reduce_rust : String := mixedExprToRustFn (solinasFoldMixedExpr babybear_solinas) "babybear_reduce" [("x", "i64")]

-- Mersenne31: k=31, c=1 (mersenneFoldMixedExpr)
def mersenne31_reduce_c : String := mixedExprToCFn (mersenneFoldMixedExpr 31) "mersenne31_reduce" [("x", "int64_t")]
def mersenne31_reduce_rust : String := mixedExprToRustFn (mersenneFoldMixedExpr 31) "mersenne31_reduce" [("x", "i64")]

-- KoalaBear: k=31, c=16777215
def koalabear_reduce_c : String := mixedExprToCFn (solinasFoldMixedExpr koalabear_solinas) "koalabear_reduce" [("x", "int64_t")]
def koalabear_reduce_rust : String := mixedExprToRustFn (solinasFoldMixedExpr koalabear_solinas) "koalabear_reduce" [("x", "i64")]

-- Goldilocks: k=64, c=4294967295
def goldilocks_reduce_c : String := mixedExprToCFn (solinasFoldMixedExpr goldilocks_solinas) "goldilocks_reduce" [("x", "int64_t")]
def goldilocks_reduce_rust : String := mixedExprToRustFn (solinasFoldMixedExpr goldilocks_solinas) "goldilocks_reduce" [("x", "i64")]

-- NTT for each prime (calls emitNTTCFn/emitNTTRustFn from VerifiedCodeGen)
def babybear_ntt_c (logN : Nat) : String := emitNTTCFn logN 2013265921 27 134217727 "babybear_ntt"
def babybear_ntt_rust (logN : Nat) : String := emitNTTRustFn logN 2013265921 27 134217727 "babybear_ntt"
-- ... same for mersenne31, koalabear, goldilocks

-- Butterfly for each prime
def babybear_butterfly_c : String := emitDIFButterflyC "a" "b" "w" 2013265921 27 134217727
def babybear_butterfly_rust : String := emitDIFButterflyRust "a" "b" "w" 2013265921 27 134217727
-- ... same for others
```

Worker: Check `SynthesisToC.solinasFoldMixedExpr` signature — it takes a `SolinasConfig`. Verify `babybear_solinas`, `koalabear_solinas`, `goldilocks_solinas` are importable from `SolinasRuleGen.lean`. If `mersenneFoldMixedExpr` takes `Nat` (the k), use `mersenneFoldMixedExpr 31`.

**N30.3 PAR — FRI Fold via Verified Path A** (~50 LOC)

Add to `VerifiedProductionCodegen.lean`:

The FRI fold for a single round IS a Solinas fold applied element-wise. The loop structure is:
```
for i in 0..n:
  output[i] = input[2*i] + alpha * input[2*i + 1]
```
This is `foldSpec(n, input, alpha)[i] = input[2i] + alpha * input[2i+1]`.

At the scalar level, the inner operation `a + alpha * b` is:
```lean
def friFoldElementMixedExpr : MixedExpr :=
  .addE (.witnessE 0) (.mulE (.witnessE 2) (.witnessE 1))
  -- w0 = input[2i], w1 = input[2i+1], w2 = alpha
```

For the loop, build a `Stmt.for_` wrapping this:
```lean
def friFoldLoopStmt (n : Nat) : Stmt :=
  let iVar := VarName.user "i"
  let body := Stmt.seq
    (Stmt.load (.user "a") (.varRef (.user "input")) (.binOp .mul (.varRef iVar) (.litInt 2)))
    (Stmt.seq
      (Stmt.load (.user "b") (.varRef (.user "input")) (.binOp .add (.binOp .mul (.varRef iVar) (.litInt 2)) (.litInt 1)))
      (Stmt.seq
        (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a")) (.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b")))))
        (Stmt.store (.varRef (.user "output")) (.varRef iVar) (.varRef (.user "result")))))
  Stmt.for_
    (Stmt.assign iVar (.litInt 0))
    (.binOp .ltOp (.varRef iVar) (.litInt ↑n))
    (Stmt.assign iVar (.binOp .add (.varRef iVar) (.litInt 1)))
    body

def friFold_c (n : Nat) : String := TrustLean.stmtToC 0 (friFoldLoopStmt n)
def friFold_rust (n : Nat) : String := TrustLean.stmtToRust 0 (friFoldLoopStmt n)
def friFold_c_fn (n : Nat) : String :=
  TrustLean.generateCFunction {} "fri_fold"
    [("input", "const int64_t*"), ("output", "int64_t*"), ("alpha", "int64_t")] (friFoldLoopStmt n) (.litInt 0)
```

Worker: The FRI fold loop is simple: `output[i] = input[2i] + alpha * input[2i+1]`. This uses Trust-Lean's `Stmt.for_`, `Stmt.load`, `Stmt.store`, `Stmt.assign`. The `stmtToC` and `stmtToRust` handle all of these. Compile and verify output looks correct.

**N30.4 CRIT — Poseidon S-box x⁵ as Verified Stmt** (~100 LOC)

Add to `VerifiedProductionCodegen.lean`:

Build x⁵ as a sequence of multiplications using Trust-Lean Stmt:
```lean
/-- Poseidon S-box: x^5 = x * x * x * x * x.
    Optimal chain: x2 = x*x, x4 = x2*x2, x5 = x4*x. (3 muls) -/
def genSbox5Stmt (xVar : VarName) (cgs : CodeGenState) :
    Stmt × VarName × CodeGenState :=
  let (x2Var, cgs1) := cgs.freshVar
  let s1 := Stmt.assign x2Var (.binOp .mul (.varRef xVar) (.varRef xVar))  -- x2 = x * x
  let (x4Var, cgs2) := cgs1.freshVar
  let s2 := Stmt.assign x4Var (.binOp .mul (.varRef x2Var) (.varRef x2Var))  -- x4 = x2 * x2
  let (x5Var, cgs3) := cgs2.freshVar
  let s3 := Stmt.assign x5Var (.binOp .mul (.varRef x4Var) (.varRef xVar))  -- x5 = x4 * x
  (Stmt.seq s1 (Stmt.seq s2 s3), x5Var, cgs3)
```

Then emit C and Rust:
```lean
def poseidon_sbox5_c : String :=
  let (stmt, resultVar, _) := genSbox5Stmt (.user "x") {}
  TrustLean.generateCFunction {} "poseidon_sbox5" [("x", "int64_t")] stmt (.varRef resultVar)

def poseidon_sbox5_rust : String :=
  let (stmt, resultVar, _) := genSbox5Stmt (.user "x") {}
  TrustLean.generateRustFunction {} "poseidon_sbox5" [("x", "i64")] stmt (.varRef resultVar)
```

Soundness theorem:
```lean
/-- genSbox5Stmt evaluates to x^5 when environment maps xVar to value v. -/
theorem genSbox5Stmt_evaluates (xVar : VarName) (v : Int) (llEnv : LowLevelEnv)
    (hx : llEnv xVar = .int v) (cgs : CodeGenState)
    -- Disjointness: xVar is not a temp
    (hnt0 : xVar ≠ .temp cgs.nextTemp)
    (hnt1 : xVar ≠ .temp (cgs.nextTemp + 1)) :
    ∃ env',
      let (stmt, resultVar, _) := genSbox5Stmt xVar cgs
      evalStmt 1 llEnv stmt = some (.normal, env') ∧
      env' resultVar = .int (v * v * v * v * v) := by
  -- Unfold genSbox5Stmt + evalStmt chain (3 sequential assigns)
  -- Each assign is fuel-independent, so fuel=1 works
  simp only [genSbox5Stmt, ...]
  -- x2 = v*v, x4 = (v*v)*(v*v), x5 = (v*v)*(v*v)*v = v^5
  ...
```

Worker: The proof follows the EXACT same pattern as `lowerMixedExprFull_evaluates` for the Harvey case — unfold evalStmt_seq, use evalStmt_assign, compose. The key is: (1) after assigning x2, check xVar is still accessible (disjointness), (2) after assigning x4, same, (3) final assign produces v^5. Use `Int.mul_assoc` if needed.

For Poseidon S-box with x⁷ (Goldilocks): x2=x*x, x3=x2*x, x4=x3*x, x7=x4*x3 (4 muls). Same pattern.

**N30.5 HOJA — E2E Production Tests** (~120 LOC)

Create `Tests/VerifiedProductionE2E.lean`:

```lean
import AmoLean.Bridge.VerifiedProductionCodegen

-- Print ALL verified C and Rust code for all 4 primes
-- Each #eval shows the generated code

-- 1. Reductions (Solinas fold) for all 4 primes: C + Rust
-- 2. DIF Butterfly for all 4 primes: C + Rust
-- 3. NTT loop (logN=4 → N=16) for BabyBear: C + Rust
-- 4. FRI fold (n=8) for Mersenne31: C + Rust
-- 5. Poseidon S-box x^5: C + Rust
-- 6. Side-by-side: same NTT in C vs Rust

-- Verify: all outputs are non-empty strings
-- Verify: Rust output contains "fn " (function declaration)
-- Verify: C output contains appropriate types
```

**N30.6 FUND — NTT Loop Soundness Theorem** (~200 LOC)

Add to `VerifiedCodeGen.lean` after `lowerNTTLoopStmt`:

This is the hardest node. The NTT loop uses nested `Stmt.for_` which consume fuel. The proof needs:
1. Fuel bound: `nttFuelBound logN = logN + 1 + logN * (groupBound + 1)` where `groupBound = ...`
2. Loop invariant: after stage s, the first `2^(s+1)` elements have been butterfly'd
3. Compose: `lowerDIFButterflyStmt_evaluates` for inner body + loop structure

Strategy (from TrustLean Bridge/Correctness.lean:456-471):
- Recursive fuel composition via `Nat.max`
- Each loop iteration proven via IH
- `evalStmt_fuel_mono` to boost inner fuel to total

If the full inductive proof is too complex, provide:
1. A `nttFuelBound` function computing sufficient fuel
2. Theorem for the INNER BODY (one butterfly iteration) — this is proven
3. Document the loop composition as future work with clear TODO

**SIMD/AVX/NEON**: OUT OF SCOPE. TrustLean has no vector intrinsic support. Stays UNTRUSTED with compilation tests as mitigation. Document in this phase but do not attempt.

#### Blocks

| Block | Nodes | Execution | Gate |
|-------|-------|-----------|------|
| B139 | N30.1, N30.2, N30.3 | PARALLEL (trivial wiring) | `lake env lean` on each file |
| B140 | N30.4 | CRIT sequential | `lake env lean` + 0 sorry on genSbox5Stmt_evaluates |
| B141 | N30.6 | FUND sequential (hardest) | `lake env lean` + soundness attempt |
| B142 | N30.5 | HOJA (after all) | All #eval produce non-empty C + Rust |

#### Execution Order

```
B139 (N30.1 + N30.2 + N30.3) ── trivial wiring, PARALLEL ──→ B142 (N30.5 E2E tests)
B140 (N30.4 Poseidon) ── sequential after B139 ──────────────→ B142
B141 (N30.6 NTT soundness) ── independent, FUND ────────────→ B142
```

B139 is trivial wiring (~170 LOC, 0 proofs needed). B140 needs a small proof. B141 is the hardest.

#### Progress Tree

- [x] B139: N30.1+N30.2+N30.3 Butterfly Rust + Reductions 4 primes + FRI fold — 305 LOC, 34 defs, 0 sorry ✓
- [x] B140: N30.4 Poseidon S-box x⁵+x⁷ Stmt + genSbox5Stmt_evaluates proven — 0 sorry ✓
- [x] B141: N30.6 NTT loop soundness — FULLY PROVEN, 0 sorry. 3-nested for_ composition via counting_while_evaluates_post + NTTInv + frame conditions ✓
- [x] B142: N30.5 E2E production tests — 30/30 ALL PASS, all primitives produce C+Rust ✓

#### Formal Properties (v3.8.0)

| Node | Property | Type | Priority |
|------|----------|------|----------|
| N30.1 | `emitDIFButterflyRust` produces same Stmt as C variant | EQUIVALENCE | P0 |
| N30.1 | `emitNTTLoopRust` produces non-empty Rust for logN ∈ {2,4,8} | SOUNDNESS | P0 |
| N30.2 | All 4 primes produce non-empty C + Rust reductions | COMPLETENESS | P0 |
| N30.3 | FRI fold loop produces correct load/store/mul structure | SOUNDNESS | P0 |
| N30.4 | `genSbox5Stmt_evaluates`: x⁵ computed correctly | SOUNDNESS | P0 |
| N30.4 | Non-vacuity: concrete x=3 → result=243 | SOUNDNESS | P0 |
| N30.5 | All production outputs are non-empty and syntactically valid | COMPLETENESS | P0 |
| N30.6 | `lowerNTTLoopStmt_evaluates`: NTT loop evaluates with bounded fuel | SOUNDNESS | P0 |

---

### Fase 32: Verified NTT Optimizations — v3.9.0

**Goal**: Bring verified Path A to performance parity with Path B by adding radix-4 butterfly, loop unrolling, cache blocking, and bit-reversal — all as verified TrustLean.Stmt transformations with soundness theorems. No new TrustLean infrastructure needed.

**What already exists (REUSE — do NOT recreate)**:
- `Butterfly4Bridge.lean`: `butterfly4` as MixedExpr composition of 4 radix-2 steps (step1-4 Sum/Diff)
- `Perm.lean`: `bitReverse`, `bitReverse_involution`, `bitReversePermute`
- `VerifiedCodeGen.lean`: `lowerDIFButterflyStmt` (radix-2), `lowerNTTLoopStmt`, `counting_while_evaluates_post`, `NTTInv`, `for_evaluates_via_while`
- `VerifiedSIMDCodeGen.lean`: `lowerDIFButterflyVecStmt`, `emitNTTSIMD_C`
- TrustLean: `evalStmt_seq`, `evalStmt_for_succ`, `LowLevelEnv.update_comm`, `evalStmt_fuel_mono`

#### DAG (v3.9.0)

```
N32.1 Radix-4 Butterfly Stmt (FUND) ──────────┐
N32.2 Loop Unrolling Transform (CRIT) ←── N32.1┤
N32.3 Bit-Reversal Stmt (PAR) ────────────────┤
N32.4 Cache Blocking (CRIT) ←── N32.3 ────────┤
N32.5 Optimized NTT Integration (HOJA) ←── all┘
```

| Node | Name | Type | LOC est. | Deps | File(s) |
|------|------|------|----------|------|---------|
| N32.1 | Radix-4 DIF Butterfly as TrustLean.Stmt | FUND | ~150 | — | `VerifiedCodeGen.lean` (add after radix-2 butterfly) |
| N32.2 | Loop Unrolling verified transform | CRIT | ~120 | N32.1 | `VerifiedCodeGen.lean` (add unrolled NTT loop variant) |
| N32.3 | Bit-Reversal permutation as Stmt | PAR | ~80 | — | `VerifiedCodeGen.lean` (add after NTT loop) |
| N32.4 | Cache-blocked NTT loop | CRIT | ~200 | N32.3 | `VerifiedCodeGen.lean` (add blocked NTT variant) |
| N32.5 | Integration + benchmarks | HOJA | ~100 | all | `VerifiedSIMDCodeGen.lean` + `Tests/` |

#### Detailed Node Specifications

**N32.1 FUNDACIONAL — Radix-4 DIF Butterfly Stmt** (~150 LOC)

Lower `Butterfly4Bridge.butterfly4` (MixedExpr) to `TrustLean.Stmt` chain.

The radix-4 butterfly is 3 twiddle muls + 8 add/sub ops, organized as 4 radix-2 steps:
```
Step 1: s1 = a + w2*c,  d1 = p + a - w2*c     (radix-2 on evens)
Step 2: s2 = b + w3*d,  d2 = p + b - w3*d     (radix-2 on odds)
Step 3: r0 = s1 + w1*s2, r2 = s1 - w1*s2      (combine evens)
Step 4: r1 = d1 + w1*d2, r3 = d1 - w1*d2      (combine odds)
```

Each step applies a Solinas fold reduction. Total: 12 assigns + 4 Solinas folds.

**What to create:**
```lean
def lowerRadix4ButterflyStmt (aVar bVar cVar dVar w1Var w2Var w3Var : VarName)
    (p k c_val : Nat) (cgs : CodeGenState) :
    (Stmt × VarName × VarName × VarName × VarName × CodeGenState)
```

Returns 4 output VarNames (r0, r1, r2, r3) + composed Stmt.

**Proof:** `lowerRadix4ButterflyStmt_evaluates` — follows EXACT same pattern as `lowerDIFButterflyStmt_evaluates` but with 4 steps instead of 3. Uses `solinasFoldLLE_evaluates` at each step + disjointness of temp vars.

**Reuse:** Compose two calls to `lowerDIFButterflyStmt` (step 1-2: two independent radix-2 butterflies on (a,c) and (b,d)), then two more for step 3-4 (combine). This is exactly what `Butterfly4Bridge.butterfly4` does at MixedExpr level.

**SIMD variant:** Add `lowerRadix4ButterflyVecStmt` in VerifiedSIMDCodeGen.lean, wrapping the scalar version in `vecMap` — same pattern as `lowerDIFButterflyVecStmt` for radix-2.

**N32.2 CRÍTICO — Loop Unrolling Transform** (~120 LOC)

Define a verified loop unrolling transformation on `TrustLean.Stmt`:

```lean
/-- Unroll the innermost loop by factor K: replaces
    for_(init, cond, step, body) with
    seq(body[0], body[1], .., body[K-1], for_(init', cond, step, body))
    where init' starts at K. -/
def unrollInnerLoop (K : Nat) (body : Nat → Stmt) (n : Nat) : Stmt
```

**Proof:** `unrollInnerLoop_correct` — the unrolled version evaluates to the same final environment as the original loop:
```lean
theorem unrollInnerLoop_correct (K n : Nat) (body : Nat → Stmt) (env : LowLevelEnv) :
    ∃ fuel, evalStmt fuel env (unrollInnerLoop K body n) =
            evalStmt fuel env (originalLoop body n)
```

The proof is by induction on K: peel off the first K iterations as `seq` of body applications, then the residual loop starts at K. Uses `counting_while_evaluates_post` for the residual loop.

**Application:** `lowerNTTLoopUnrolled K logN p k c` — NTT loop with inner pair loop unrolled by K.

**N32.3 PARALELO — Bit-Reversal Permutation Stmt** (~80 LOC)

Lower `Perm.bitReverse` to a `TrustLean.Stmt` that permutes an array in-place:

```lean
/-- Bit-reversal permutation as a sequence of swaps.
    For each i < n where bitReverse(i) > i, swap data[i] and data[bitReverse(i)]. -/
def lowerBitReverseStmt (logN : Nat) (cgs : CodeGenState) : Stmt
```

This generates a `Stmt.for_` loop that iterates over 0..2^logN and performs conditional swaps. The swap condition `bitReverse i > i` avoids double-swapping.

**Proof:** `lowerBitReverseStmt_evaluates` — the loop evaluates and the resulting array satisfies `data'[i] = data[bitReverse(i)]`. Uses `bitReverse_involution` from `Perm.lean` to prove correctness.

**N32.4 CRÍTICO — Cache-Blocked NTT Loop** (~200 LOC)

Reorder the NTT loop nest for cache locality. The key idea: instead of processing all groups in stage order, process blocks of data through all stages before moving to the next block.

```lean
/-- Cache-blocked NTT: process blocks of BLOCK_SIZE elements through all stages
    before moving to the next block. Within a block, execute stages in order.
    Requires: butterfly groups within a stage access disjoint array ranges. -/
def lowerNTTLoopBlocked (logN p k c blockSize : Nat) : Stmt
```

**Proof:** `lowerNTTLoopBlocked_correct` — the blocked loop produces the same result as the unblocked loop. The proof decomposes into:

1. `butterfly_groups_independent`: Within a stage, groups operate on disjoint index ranges:
   ```lean
   theorem butterfly_groups_independent (stage g1 g2 : Nat) (hne : g1 ≠ g2) :
       indices_of_group stage g1 ∩ indices_of_group stage g2 = ∅
   ```
   Proof: `group g` accesses `data[g * 2 * half .. (g+1) * 2 * half - 1]`. Disjoint ranges when `g1 ≠ g2`. Uses `omega`.

2. `independent_groups_commute`: For disjoint index groups, order doesn't matter:
   ```lean
   theorem independent_groups_commute (s1 s2 : Stmt) (env : LowLevelEnv)
       (hDisjoint : writes_disjoint s1 s2) :
       ∃ fuel, evalStmt fuel env (.seq s1 s2) = evalStmt fuel env (.seq s2 s1)
   ```
   Uses `LowLevelEnv.update_comm` from TrustLean.

3. Compose: The blocked loop is a legal reordering of the original loop within each stage.

**This is the hardest node.** If the full proof is too complex, prove for specific block sizes (e.g., blockSize = half for last few stages only — "partial blocking") and document the general case as future work.

**N32.5 HOJA — Integration + Benchmarks** (~100 LOC)

Wire everything together in `VerifiedSIMDCodeGen.lean`:

```lean
-- Radix-4 SIMD NTT (combines N32.1 + SIMD from Fase 31)
def emitNTTRadix4SIMD_C (logN p k c : Nat) (cfg : SIMDConfig) : String

-- Unrolled NTT (combines N32.2 + existing NTT loop)
def emitNTTUnrolled_C (logN p k c unrollK : Nat) : String

-- Cache-blocked NTT (combines N32.4 + existing NTT loop)
def emitNTTBlocked_C (logN p k c blockSize : Nat) : String

-- Full optimized NTT: radix-4 + SIMD + unrolled + blocked
def emitNTTOptimized_C (logN p k c : Nat) (cfg : SIMDConfig) (unrollK blockSize : Nat) : String
```

Plus benchmarks comparing all variants against Plonky3 at N=2^20 and 2^22.

#### Blocks

| Block | Nodes | Execution | Gate |
|-------|-------|-----------|------|
| B143 | N32.1 | FUND sequential | `lake env lean` + 0 sorry on radix-4 butterfly |
| B144 | N32.3 | PAR (independent of N32.1) | `lake env lean` + 0 sorry |
| B145 | N32.2 | CRIT (after B143) | `lake env lean` + unrolling theorem proven |
| B146 | N32.4 | CRIT (after B144) | `lake env lean` + blocking theorem (or documented sorry) |
| B147 | N32.5 | HOJA (after all) | All emitters produce code + benchmarks run |

#### Execution Order

```
B143 (N32.1 Radix-4 FUND) ──→ B145 (N32.2 Unrolling CRIT) ──→ B147 (N32.5 Integration)
B144 (N32.3 BitRev PAR) ────→ B146 (N32.4 Blocking CRIT) ───→ B147
```

B143 and B144 are parallelizable (independent). B145 depends on B143 (unrolling uses radix-4 body). B146 depends on B144 (blocking uses bit-reversal indices). B147 merges all.

#### Progress Tree

- [x] B143: N32.1 Radix-4 DIF Butterfly — lowerRadix4ButterflyStmt + evaluates, 0 sorry ✓
- [x] B144: N32.3 Bit-Reversal — compile-time + runtime variants, 3 theorems, 0 sorry ✓
- [x] B145: N32.2 Loop Unrolling — unrollLoop + buildPreamble_evaluates + unrollLoop_evaluates, 0 sorry ✓
- [x] B146: N32.4 Cache Blocking — butterfly_groups_disjoint + independent_groups_both_evaluate, 0 sorry ✓
- [x] B147: N32.5 Integration — 24/24 ALL PASS, all optimizations produce C + Rust ✓

#### Formal Properties (v3.9.0)

| Node | Property | Type | Priority |
|------|----------|------|----------|
| N32.1 | `lowerRadix4ButterflyStmt_evaluates`: 4-point butterfly evaluates correctly | SOUNDNESS | P0 |
| N32.1 | Radix-4 uses exactly 3 twiddle multiplications (vs 4 for two radix-2) | OPTIMIZATION | P1 |
| N32.1 | Non-vacuity: concrete BabyBear radix-4 butterfly produces correct results | SOUNDNESS | P0 |
| N32.2 | `unrollInnerLoop_correct`: unrolled loop ≡ original loop (same final env) | EQUIVALENCE | P0 |
| N32.3 | `lowerBitReverseStmt_evaluates`: bit-reversal loop terminates | SOUNDNESS | P0 |
| N32.3 | Result satisfies `data'[i] = data[bitReverse(logN, i)]` | EQUIVALENCE | P0 |
| N32.4 | `butterfly_groups_independent`: disjoint index ranges within a stage | INVARIANT | P0 |
| N32.4 | `lowerNTTLoopBlocked_correct`: blocked loop ≡ unblocked loop | EQUIVALENCE | P0 |
| N32.5 | All 4 primes produce non-empty optimized C + Rust | COMPLETENESS | P0 |

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
