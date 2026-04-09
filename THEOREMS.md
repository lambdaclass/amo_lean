═══ Specification Audit: amo-lean ═══
Theorems: 1553  Lemmas: 61  Pipeline: 360
Clean: 1359  T1(vacuity): 0  T1.5(identity): 0  T2(weak): 23  T3(structural): 44  T4(no-witness): 188

── TIER 2 — WEAK SPECS (23 issues) ──
  theorem threePhaseSaturateF_preserves_consistent
    AmoLean/EGraph/Verified/Bitwise/Discovery/GuidedSaturation.lean:253
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation

  theorem phasedSaturateF_phase1_consistent
    AmoLean/EGraph/Verified/Bitwise/PhasedSaturation.lean:179
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation

  theorem phasedSaturateF_phase2_consistent
    AmoLean/EGraph/Verified/Bitwise/PhasedSaturation.lean:196
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation

  theorem saturateF_preserves_triple
    AmoLean/EGraph/Verified/Bitwise/PhasedSaturation.lean:213
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation

  theorem phasedSaturateF_preserves_consistent
    AmoLean/EGraph/Verified/Bitwise/PhasedSaturation.lean:244
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation

  theorem single_pass_from_composed_step
    AmoLean/EGraph/Verified/Bitwise/PhasedSaturation.lean:269
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation

  theorem compareCosts_solinas_le_montgomery
    AmoLean/EGraph/Verified/Bitwise/SynthesisPipeline.lean:225
    ⚠ T2-UNUSED-PARTIAL: 1/2 params are _-prefixed: ['_name']

  theorem saturateF_preserves_consistent
    AmoLean/EGraph/Verified/SaturationSpec.lean:359
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation

  theorem mul_comm_correct [PIPELINE] [SORRY]
    AmoLean/EGraph/VerifiedRules.lean:241
    ⚠ T2-PIPELINE-SORRY: pipeline theorem contains sorry — top-level result is unverified

  theorem foldStep_eq_abstract_fold
    AmoLean/FRI/Plonky3/FoldTV.lean:139
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_h2']

  theorem foldStep_matches_foldPolynomial
    AmoLean/FRI/Plonky3/FoldTV.lean:162
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_h2']

  theorem fri_multi_round_terminates
    AmoLean/FRI/Verified/FRIMultiRound.lean:185
    ⚠ T2-UNUSED-PARTIAL: 1/2 params are _-prefixed: ['_hd']

  theorem final_degree_bound [PIPELINE]
    AmoLean/FRI/Verified/FRISemanticSpec.lean:403
    ⚠ T2-UNUSED-PARTIAL: 1/2 params are _-prefixed: ['_h']

  theorem fri_operational_sound [PIPELINE]
    AmoLean/FRI/Verified/FRIVerifierOperational.lean:132
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_hwf']

  theorem fri_operational_loop_connection
    AmoLean/FRI/Verified/FRIVerifierOperational.lean:226
    ⚠ T2-UNUSED-PARTIAL: 1/2 params are _-prefixed: ['_hd']

  theorem fold_from_pair_evals
    AmoLean/FRI/Verified/FoldSoundness.lean:198
    ⚠ T2-UNUSED-PARTIAL: 3/7 params are _-prefixed: ['_k', '_hk', '_hi']

  theorem bitReverse_lt
    AmoLean/Matrix/Perm.lean:63
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_h']

  theorem lazy_sub_equiv
    AmoLean/NTT/Bounds.lean:236
    ⚠ T2-UNUSED-PARTIAL: 1/2 params are _-prefixed: ['_ha']

  lemma inv_root_exp_zero
    AmoLean/NTT/Correctness.lean:461
    ⚠ T2-UNUSED-PARTIAL: 2/3 params are _-prefixed: ['_hn', '_hω']

  theorem ntt_coeff_generic_split
    AmoLean/NTT/GenericCorrectness.lean:170
    ⚠ T2-UNUSED-PARTIAL: 1/5 params are _-prefixed: ['_hk']

  theorem ntt_coeff_generic_split_upper
    AmoLean/NTT/GenericCorrectness.lean:188
    ⚠ T2-UNUSED-PARTIAL: 1/9 params are _-prefixed: ['_hk']

  theorem compose_correct [PIPELINE] [SORRY]
    AmoLean/Verification/Poseidon_Semantics.lean:543
    ⚠ T2-PIPELINE-SORRY: pipeline theorem contains sorry — top-level result is unverified

  theorem evalAddRC_eq_spec [PIPELINE] [SORRY]
    AmoLean/Verification/Poseidon_Semantics.lean:567
    ⚠ T2-PIPELINE-SORRY: pipeline theorem contains sorry — top-level result is unverified

── TIER 3 — STRUCTURAL (44 issues) ──
  theorem costAwareExtractF_zero_fuel_correct [PIPELINE]
    AmoLean/EGraph/Verified/Bitwise/CostExtraction.lean:279
    ⚠ T3-MANY-HYPOTHESES: 11 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem costAwareExtract_hw_mixed_equivalent
    AmoLean/EGraph/Verified/Bitwise/CostExtraction.lean:322
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem canDeferReduction_sound [PIPELINE]
    AmoLean/EGraph/Verified/Bitwise/Discovery/LazyReduction.lean:103
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem mixed_extractable_sound [PIPELINE]
    AmoLean/EGraph/Verified/Bitwise/MixedExtract.lean:103
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem mixed_extractF_correct [PIPELINE]
    AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean:63
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem mixed_extractAuto_correct [PIPELINE]
    AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean:74
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem mixedEquivalent_refl
    AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean:167
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem mixedEquivalent_symm
    AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean:172
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem mixedEquivalent_trans
    AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean:178
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem extract_same_class_equivalent
    AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean:185
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem pipeline_mixed_equivalent [PIPELINE]
    AmoLean/EGraph/Verified/Bitwise/MixedPipeline.lean:204
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem extractF_correct [PIPELINE]
    AmoLean/EGraph/Verified/ExtractSpec.lean:170
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem concrete_pipeline_soundness [PIPELINE]
    AmoLean/EGraph/Verified/MasterChain.lean:60
    ⚠ T3-MANY-HYPOTHESES: 15 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem concrete_pipeline_contract [PIPELINE]
    AmoLean/EGraph/Verified/MasterChain.lean:99
    ⚠ T3-MANY-HYPOTHESES: 20 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem soundRuleMatch_pipeline_soundness [PIPELINE]
    AmoLean/EGraph/Verified/MasterChain.lean:206
    ⚠ T3-MANY-HYPOTHESES: 18 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem soundMergeStep_preserves_cv [PIPELINE]
    AmoLean/EGraph/Verified/PreservesCVInstances.lean:100
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem soundRuleMatchMerges_preserves_cv [PIPELINE]
    AmoLean/EGraph/Verified/PreservesCVInstances.lean:202
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem soundMergeStep_pipeline_cv [PIPELINE]
    AmoLean/EGraph/Verified/PreservesCVInstances.lean:296
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem ConditionalSoundRewriteRule.isSound [PIPELINE]
    AmoLean/EGraph/Verified/SoundRewriteRule.lean:92
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem cryptoEquivalent_symm
    AmoLean/EGraph/Verified/TranslationValidation.lean:51
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem cryptoEquivalent_trans
    AmoLean/EGraph/Verified/TranslationValidation.lean:56
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem cryptoEquivalent_add
    AmoLean/EGraph/Verified/TranslationValidation.lean:75
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem cryptoEquivalent_mul
    AmoLean/EGraph/Verified/TranslationValidation.lean:87
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem cryptoEquivalent_neg
    AmoLean/EGraph/Verified/TranslationValidation.lean:99
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem cryptoEquivalent_smul
    AmoLean/EGraph/Verified/TranslationValidation.lean:109
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem circuit_extractable_sound [PIPELINE]
    AmoLean/EGraph/VerifiedExtraction/CircuitAdaptor.lean:194
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem extractF_correct [PIPELINE]
    AmoLean/EGraph/VerifiedExtraction/Greedy.lean:156
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem smoke_circuit_sound [PIPELINE]
    AmoLean/EGraph/VerifiedExtraction/Integration.lean:41
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem circuit_extractF_correct [PIPELINE]
    AmoLean/EGraph/VerifiedExtraction/Integration.lean:91
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem circuit_extractAuto_correct [PIPELINE]
    AmoLean/EGraph/VerifiedExtraction/Integration.lean:103
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem friEquivalent_refl
    AmoLean/FRI/Verified/FRIPipelineIntegration.lean:46
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem friEquivalent_symm
    AmoLean/FRI/Verified/FRIPipelineIntegration.lean:50
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem friEquivalent_trans
    AmoLean/FRI/Verified/FRIPipelineIntegration.lean:54
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem fri_pipeline_soundness [PIPELINE]
    AmoLean/FRI/Verified/FRIPipelineIntegration.lean:123
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem fri_verifier_sound [PIPELINE]
    AmoLean/FRI/Verified/FullVerifier.lean:106
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem fri_full_correctness [PIPELINE]
    AmoLean/FRI/Verified/FullVerifier.lean:178
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem merkleBridge_empty_proof [PIPELINE]
    AmoLean/FRI/Verified/MerkleBridge.lean:223
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem merkleBridge_single_step [PIPELINE]
    AmoLean/FRI/Verified/MerkleBridge.lean:231
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem query_phase_sound [PIPELINE]
    AmoLean/FRI/Verified/QueryVerification.lean:212
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem bridge_init_agreement [PIPELINE]
    AmoLean/FRI/Verified/TranscriptBridge.lean:163
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem circuit_equiv_implies_constraint_equiv
    AmoLean/Plonky3/ConstraintEGraph.lean:123
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem checkConstraint_sound [PIPELINE]
    AmoLean/Plonky3/ConstraintVerification.lean:27
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem checkSystem_sound [PIPELINE]
    AmoLean/Plonky3/ConstraintVerification.lean:34
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem full_stack_correct [PIPELINE]
    AmoLean/Plonky3/EndToEnd.lean:75
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary

── TIER 4 — NO WITNESS (188 issues) ──
  lemma applyFirst_sound [PIPELINE]
    AmoLean/Correctness.lean:239
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem saturateF_preserves_triple'
    AmoLean/EGraph/Verified/Bitwise/Discovery/GuidedSaturation.lean:231
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem IsRootAt_of_rootD_self
    AmoLean/EGraph/Verified/CoreSpec.lean:218
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem IsRootAt_backward_find
    AmoLean/EGraph/Verified/CoreSpec.lean:226
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem add_preserves_children_bounded
    AmoLean/EGraph/Verified/CoreSpec.lean:1238
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem mapOption_get
    AmoLean/EGraph/Verified/ExtractSpec.lean:65
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem checkExactlyOne_sound [PIPELINE]
    AmoLean/EGraph/Verified/ExtractSpec.lean:303
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem checkChildDeps_sound [PIPELINE]
    AmoLean/EGraph/Verified/ExtractSpec.lean:342
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem checkAcyclicity_sound [PIPELINE]
    AmoLean/EGraph/Verified/ExtractSpec.lean:375
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractILP_correct [PIPELINE]
    AmoLean/EGraph/Verified/ExtractSpec.lean:458
    ⚠ T2-UNUSED-PARTIAL: 1/12 params are _-prefixed: ['_hvalid']
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ilp_extraction_soundness [PIPELINE]
    AmoLean/EGraph/Verified/ExtractSpec.lean:505
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem congruence_extract
    AmoLean/EGraph/Verified/PipelineSoundness.lean:64
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem optimization_soundness_greedy [PIPELINE]
    AmoLean/EGraph/Verified/PipelineSoundness.lean:88
    ⚠ T3-MANY-HYPOTHESES: 15 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem optimization_soundness_ilp [PIPELINE]
    AmoLean/EGraph/Verified/PipelineSoundness.lean:114
    ⚠ T3-MANY-HYPOTHESES: 16 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem greedy_ilp_equivalent
    AmoLean/EGraph/Verified/PipelineSoundness.lean:141
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem full_pipeline_soundness [PIPELINE]
    AmoLean/EGraph/Verified/PipelineSoundness.lean:178
    ⚠ T3-MANY-HYPOTHESES: 15 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem full_pipeline_soundness_ilp [PIPELINE]
    AmoLean/EGraph/Verified/PipelineSoundness.lean:201
    ⚠ T3-MANY-HYPOTHESES: 16 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem full_pipeline_contract [PIPELINE]
    AmoLean/EGraph/Verified/PipelineSoundness.lean:234
    ⚠ T3-MANY-HYPOTHESES: 20 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem processClass_shi_combined
    AmoLean/EGraph/Verified/SaturationSpec.lean:31
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rebuildStep_preserves_triple_aux
    AmoLean/EGraph/Verified/SaturationSpec.lean:250
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rebuildStepBody_preserves_triple
    AmoLean/EGraph/Verified/SaturationSpec.lean:310
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem consistent_root_eq
    AmoLean/EGraph/Verified/SemanticSpec.lean:118
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem class_nodes_same_value
    AmoLean/EGraph/Verified/SemanticSpec.lean:134
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem nodeEval_canonical
    AmoLean/EGraph/Verified/SemanticSpec.lean:154
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem go_preserves_v_eq
    AmoLean/EGraph/Verified/SemanticSpec.lean:171
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem nodeEval_canonicalize
    AmoLean/EGraph/Verified/SemanticSpec.lean:218
    ⚠ T2-UNUSED-PARTIAL: 1/7 params are _-prefixed: ['_hbnd']
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem cv_hca_implies_shi
    AmoLean/EGraph/Verified/SemanticSpec.lean:246
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem processClass_merges_valid
    AmoLean/EGraph/Verified/SemanticSpec.lean:439
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merge_preserves_shi
    AmoLean/EGraph/Verified/SemanticSpec.lean:599
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem sound_rule_preserves_consistency [PIPELINE]
    AmoLean/EGraph/Verified/SoundRewriteRule.lean:106
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication
    ⚠ T3-MANY-HYPOTHESES: 11 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem conditional_sound_rule_preserves_consistency [PIPELINE]
    AmoLean/EGraph/Verified/SoundRewriteRule.lean:120
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_push
    AmoLean/EGraph/Verified/UnionFind.lean:204
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_fuel_extra
    AmoLean/EGraph/Verified/UnionFind.lean:223
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_fuel_add
    AmoLean/EGraph/Verified/UnionFind.lean:277
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_bounded
    AmoLean/EGraph/Verified/UnionFind.lean:293
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem IsRootAt_set_ne
    AmoLean/EGraph/Verified/UnionFind.lean:307
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_parent_step
    AmoLean/EGraph/Verified/UnionFind.lean:319
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_not_in_class
    AmoLean/EGraph/Verified/UnionFind.lean:334
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_other_class
    AmoLean/EGraph/Verified/UnionFind.lean:362
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_same_class
    AmoLean/EGraph/Verified/UnionFind.lean:389
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_to_root
    AmoLean/EGraph/Verified/UnionFind.lean:451
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem compressPath_preserves_rootD
    AmoLean/EGraph/Verified/UnionFind.lean:467
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem compressPath_bounded
    AmoLean/EGraph/Verified/UnionFind.lean:558
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem root_setIfInBounds_target
    AmoLean/EGraph/Verified/UnionFind.lean:673
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_avoids_root
    AmoLean/EGraph/Verified/UnionFind.lean:705
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_compose
    AmoLean/EGraph/Verified/UnionFind.lean:734
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_union_step
    AmoLean/EGraph/Verified/UnionFind.lean:753
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem cycle_contradicts_wf
    AmoLean/EGraph/Verified/UnionFind.lean:849
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_depth_bound
    AmoLean/EGraph/Verified/UnionFind.lean:868
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_root_to_root
    AmoLean/EGraph/Verified/UnionFind.lean:901
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_root_to_oob
    AmoLean/EGraph/Verified/UnionFind.lean:916
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem union_creates_equiv
    AmoLean/EGraph/Verified/UnionFind.lean:931
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem union_root_cases
    AmoLean/EGraph/Verified/UnionFind.lean:1169
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractF_of_rank
    AmoLean/EGraph/VerifiedExtraction/CompletenessSpec.lean:495
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractAuto_complete
    AmoLean/EGraph/VerifiedExtraction/CompletenessSpec.lean:534
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem consistent_root_eq
    AmoLean/EGraph/VerifiedExtraction/Core.lean:324
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem mapOption_get
    AmoLean/EGraph/VerifiedExtraction/Greedy.lean:66
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractAuto_correct [PIPELINE]
    AmoLean/EGraph/VerifiedExtraction/Greedy.lean:203
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem barycentric_unique
    AmoLean/FRI/Verified/BarycentricInterpolation.lean:118
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domain_fold_composition [PIPELINE]
    AmoLean/FRI/Verified/BridgeIntegration.lean:55
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domain_fold_degree_lt_size [PIPELINE]
    AmoLean/FRI/Verified/BridgeIntegration.lean:70
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fold_bridge_consistent_output [PIPELINE]
    AmoLean/FRI/Verified/BridgeIntegration.lean:93
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem operational_verified_bridge_complete [PIPELINE] [SORRY]
    AmoLean/FRI/Verified/BridgeIntegration.lean:148
    ⚠ T2-PIPELINE-SORRY: pipeline theorem contains sorry — top-level result is unverified
    ⚠ T3-MANY-HYPOTHESES: 14 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_size [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:90
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_generator [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:98
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_elements_distinct [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:106
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_generator_pow_size [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:114
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_roundtrip [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:153
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_roundtrip_size [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:162
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_supports_folding [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:176
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_folded_generator [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:186
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_initial_round [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:201
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_initial_domain [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:210
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_initial_degreeBound [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:220
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_initial_consistent [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:229
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_size_eq_mul [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:244
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_size_eq_domainSize_zero [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:253
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_degree_lt_size [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:262
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domainBridge_degreeBound_le_half [PIPELINE]
    AmoLean/FRI/Verified/DomainBridge.lean:273
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem invariant_preserved
    AmoLean/FRI/Verified/FRISemanticSpec.lean:180
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem disagreement_bound
    AmoLean/FRI/Verified/FieldBridge.lean:105
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_hp']
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem agreement_implies_equality
    AmoLean/FRI/Verified/FieldBridge.lean:202
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem eval_determines_poly [SORRY]
    AmoLean/FRI/Verified/FieldBridge.lean:246
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem foldBridge_preserves_degree [PIPELINE]
    AmoLean/FRI/Verified/FoldBridge.lean:130
    ⚠ T2-UNUSED-PARTIAL: 1/9 params are _-prefixed: ['_input']
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem foldBridge_consistent [PIPELINE]
    AmoLean/FRI/Verified/FoldBridge.lean:145
    ⚠ T2-UNUSED-PARTIAL: 1/9 params are _-prefixed: ['_input']
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem FoldBridgeResult.domain_size [PIPELINE]
    AmoLean/FRI/Verified/FoldBridge.lean:186
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem foldBridge_composes_with_domain [PIPELINE]
    AmoLean/FRI/Verified/FoldBridge.lean:200
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem half_pow_eq_neg_one
    AmoLean/FRI/Verified/FoldSoundness.lean:46
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domain_element_neg [PIPELINE]
    AmoLean/FRI/Verified/FoldSoundness.lean:85
    ⚠ T2-UNUSED-PARTIAL: 1/5 params are _-prefixed: ['_hi']
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem squared_domain_element [PIPELINE]
    AmoLean/FRI/Verified/FoldSoundness.lean:97
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fold_preserves_consistency
    AmoLean/FRI/Verified/FoldSoundness.lean:244
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fold_consistent_on_squared_domain [PIPELINE]
    AmoLean/FRI/Verified/FoldSoundness.lean:262
    ⚠ T2-UNUSED-PARTIAL: 1/10 params are _-prefixed: ['_hd_le_k']
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem single_round_soundness [PIPELINE]
    AmoLean/FRI/Verified/FoldSoundness.lean:317
    ⚠ T3-MANY-HYPOTHESES: 9 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fold_determines_unique
    AmoLean/FRI/Verified/FoldSoundness.lean:336
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkleBridge_verify_equiv [PIPELINE]
    AmoLean/FRI/Verified/MerkleBridge.lean:91
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkleBridge_verify_converse [PIPELINE]
    AmoLean/FRI/Verified/MerkleBridge.lean:107
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkleBridge_verify_iff [PIPELINE]
    AmoLean/FRI/Verified/MerkleBridge.lean:122
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkleBridge_with_hash [PIPELINE]
    AmoLean/FRI/Verified/MerkleBridge.lean:147
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkleTree_build_wf
    AmoLean/FRI/Verified/MerkleBridge.lean:179
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkle_binding_step
    AmoLean/FRI/Verified/MerkleSpec.lean:182
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkle_wf_root_eq
    AmoLean/FRI/Verified/MerkleSpec.lean:198
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkle_wf_children
    AmoLean/FRI/Verified/MerkleSpec.lean:205
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merkle_wf_build
    AmoLean/FRI/Verified/MerkleSpec.lean:212
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem honest_fold_consistent
    AmoLean/FRI/Verified/PerRoundSoundness.lean:79
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem honest_fold_complete
    AmoLean/FRI/Verified/PerRoundSoundness.lean:97
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem commitment_binding_witness
    AmoLean/FRI/Verified/PerRoundSoundness.lean:138
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem commitment_composable
    AmoLean/FRI/Verified/PerRoundSoundness.lean:147
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fold_output_unique
    AmoLean/FRI/Verified/PerRoundSoundness.lean:200
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fold_output_unique_from_honest
    AmoLean/FRI/Verified/PerRoundSoundness.lean:211
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem query_disagreement_bounded
    AmoLean/FRI/Verified/PerRoundSoundness.lean:230
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem query_catches_cheating
    AmoLean/FRI/Verified/PerRoundSoundness.lean:241
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem round_invariant_preserved
    AmoLean/FRI/Verified/PerRoundSoundness.lean:255
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem per_round_soundness [PIPELINE]
    AmoLean/FRI/Verified/PerRoundSoundness.lean:337
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem state_good_transition
    AmoLean/FRI/Verified/PerRoundSoundness.lean:369
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem agreement_set_bounded
    AmoLean/FRI/Verified/VerifierComposition.lean:52
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem disagreement_count_lower_bound
    AmoLean/FRI/Verified/VerifierComposition.lean:83
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fri_completeness [PIPELINE]
    AmoLean/FRI/Verified/VerifierComposition.lean:128
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem detection_per_round
    AmoLean/FRI/Verified/VerifierComposition.lean:184
    ⚠ T2-UNUSED-PARTIAL: 1/13 params are _-prefixed: ['_hd_le_k']
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem fri_single_round_correct [PIPELINE] [SORRY]
    AmoLean/FRI/Verified/VerifierComposition.lean:259
    ⚠ T2-PIPELINE-SORRY: pipeline theorem contains sorry — top-level result is unverified
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  lemma prime_dvd_eq
    AmoLean/Field/Goldilocks.lean:77
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem NTT_recursive_getElem_lower
    AmoLean/NTT/CooleyTukey.lean:190
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem intt_recursive_eq_spec' [PIPELINE]
    AmoLean/NTT/Correctness.lean:482
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lazy_butterfly_fst_bound
    AmoLean/NTT/LazyButterfly.lean:102
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lazy_butterfly_snd_bound
    AmoLean/NTT/LazyButterfly.lean:111
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lazy_butterfly_fst_simulates
    AmoLean/NTT/LazyButterfly.lean:137
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lazy_butterfly_snd_simulates
    AmoLean/NTT/LazyButterfly.lean:150
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lazy_butterfly_sum
    AmoLean/NTT/LazyButterfly.lean:173
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lazy_butterfly_simulates_standard
    AmoLean/NTT/LazyButterfly.lean:190
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lazy_butterfly_reduce_bound
    AmoLean/NTT/LazyButterfly.lean:218
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  lemma intt_foldl_to_finset_sum
    AmoLean/NTT/ListFinsetBridge.lean:170
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  lemma intt_coeff_list_eq_finset
    AmoLean/NTT/ListFinsetBridge.lean:215
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ntt_intt_identity_list
    AmoLean/NTT/ListFinsetBridge.lean:238
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  lemma exp_mod_eq
    AmoLean/NTT/OrthogonalityProof.lean:109
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  lemma term_eq_pow_diff
    AmoLean/NTT/OrthogonalityProof.lean:287
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem sum_diff_eq_zero
    AmoLean/NTT/OrthogonalityProof.lean:295
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ntt_coeff_lower_half_split
    AmoLean/NTT/Phase3Proof.lean:1031
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem NTT_spec_upper_half_eq [PIPELINE]
    AmoLean/NTT/Phase3Proof.lean:1168
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem orthogonality_sum_lt
    AmoLean/NTT/Properties.lean:52
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem intt_ntt_identity_finset
    AmoLean/NTT/Properties.lean:89
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ntt_constant_nonzero
    AmoLean/NTT/Properties.lean:230
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem butterfly4_as_butterfly2_composition
    AmoLean/NTT/Radix4/Butterfly4.lean:95
    ⚠ T4-NO-WITNESS: 13 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem butterfly4_ibutterfly4_identity
    AmoLean/NTT/Radix4/Butterfly4.lean:188
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem interleave4_length
    AmoLean/NTT/Radix4/Stride4.lean:157
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem n_pos
    AmoLean/NTT/RootsOfUnity.lean:51
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem pow_mul_eq_one
    AmoLean/NTT/RootsOfUnity.lean:61
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem powSum_nonzero
    AmoLean/NTT/RootsOfUnity.lean:184
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem twiddle_half_eq_neg_one
    AmoLean/NTT/RootsOfUnity.lean:226
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem twiddle_shift
    AmoLean/NTT/RootsOfUnity.lean:249
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem squared_is_primitive
    AmoLean/NTT/RootsOfUnity.lean:268
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem nested_loop_alpha
    AmoLean/Verification/AlgebraicSemantics.lean:1276
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustBlock_produces_exactStructure
    AmoLean/Verification/AlgebraicSemantics.lean:1536
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustBlock_sameStructure_eval_eq_diffVar
    AmoLean/Verification/AlgebraicSemantics.lean:1673
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem loop_adjustBlock_sameStructure
    AmoLean/Verification/AlgebraicSemantics.lean:1785
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustStride_sameStructure_eval_eq_diffVar [SORRY]
    AmoLean/Verification/AlgebraicSemantics.lean:1808
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem loop_adjustStride_sameStructure
    AmoLean/Verification/AlgebraicSemantics.lean:1905
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustStride_produces_exactStructure
    AmoLean/Verification/AlgebraicSemantics.lean:2028
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem loop_adjustBlock_alpha_lower
    AmoLean/Verification/AlgebraicSemantics.lean:2122
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem loop_adjustStride_alpha_lower
    AmoLean/Verification/AlgebraicSemantics.lean:2146
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lowering_compute_contiguous_correct [PIPELINE]
    AmoLean/Verification/AlgebraicSemantics.lean:2533
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lower_hasNoSeqLower_contiguous
    AmoLean/Verification/AlgebraicSemantics.lean:2801
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalScatter_block_size_preserved
    AmoLean/Verification/AlgebraicSemantics.lean:3034
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalScatter_block_preserves_wm_size
    AmoLean/Verification/AlgebraicSemantics.lean:3059
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalScatter_stride_size_preserved
    AmoLean/Verification/AlgebraicSemantics.lean:3082
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalScatter_stride_preserves_wm_size
    AmoLean/Verification/AlgebraicSemantics.lean:3106
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustBlock_lower_preserves_size_gen
    AmoLean/Verification/AlgebraicSemantics.lean:3163
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustBlock_lower_preserves_size
    AmoLean/Verification/AlgebraicSemantics.lean:3316
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustStride_lower_preserves_size_gen
    AmoLean/Verification/AlgebraicSemantics.lean:3439
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem adjustStride_lower_preserves_size
    AmoLean/Verification/AlgebraicSemantics.lean:3587
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lower_preserves_size_ge
    AmoLean/Verification/AlgebraicSemantics.lean:3699
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem block_scatter_loop_inv
    AmoLean/Verification/AlgebraicSemantics.lean:4189
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem block_scatter_loop_wm_irrelevant
    AmoLean/Verification/AlgebraicSemantics.lean:4243
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lower_kernel_preserves_length
    AmoLean/Verification/AlgebraicSemantics.lean:4305
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem stride_writes_preserve_other
    AmoLean/Verification/AlgebraicSemantics.lean:4390
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem stride_writes_skip_pos
    AmoLean/Verification/AlgebraicSemantics.lean:4418
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem stride_writes_at_pos
    AmoLean/Verification/AlgebraicSemantics.lean:4447
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem stride_scatter_loop_inv
    AmoLean/Verification/AlgebraicSemantics.lean:4490
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem stride_scatter_loop_wm_irrelevant
    AmoLean/Verification/AlgebraicSemantics.lean:4541
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem compute_writeMem_irrelevant
    AmoLean/Verification/AlgebraicSemantics.lean:4581
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem evalSigmaAlg_writeMem_irrelevant
    AmoLean/Verification/AlgebraicSemantics.lean:4609
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem div_mul_eq
    AmoLean/Verification/AlgebraicSemantics.lean:4902
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lowering_compose_step
    AmoLean/Verification/AlgebraicSemantics.lean:5103
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem lowering_algebraic_correct [PIPELINE]
    AmoLean/Verification/AlgebraicSemantics.lean:5550
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem domain_size_after_rounds [PIPELINE]
    AmoLean/Verification/FRI_Properties.lean:123
    ⚠ T4-NO-WITNESS: 2 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem butterfly4_as_butterfly2_composition
    archive/NTT_Radix4/Butterfly4.lean:95
    ⚠ T4-NO-WITNESS: 13 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem butterfly4_ibutterfly4_identity
    archive/NTT_Radix4/Butterfly4.lean:188
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem interleave4_length
    archive/NTT_Radix4/Stride4.lean:157
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem block_scatter_loop_inv
    archive/tmp_infra.lean:52
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem block_scatter_loop_wm_irrelevant
    archive/tmp_infra.lean:101
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

✗ FAIL — Blocking spec issues detected (Tier 1 vacuity or pipeline sorry)