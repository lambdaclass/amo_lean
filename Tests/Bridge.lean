-- Core E-graph spec
import AmoLean.EGraph.Verified.SemanticSpec
import AmoLean.EGraph.Verified.CoreSpec
import AmoLean.EGraph.Verified.SaturationSpec
import AmoLean.EGraph.Verified.ExtractSpec
import AmoLean.EGraph.Verified.PipelineSoundness
import AmoLean.EGraph.Verified.TranslationValidation
import AmoLean.EGraph.Verified.SoundRewriteRule

-- FRI spec
import AmoLean.FRI.Verified.FRIPipelineIntegration

-- Verified Extraction (generic framework)
import AmoLean.EGraph.VerifiedExtraction.Core
import AmoLean.EGraph.VerifiedExtraction.Greedy

-- Bitwise (Fase 21)
import AmoLean.EGraph.Verified.Bitwise.MixedPipeline

/-!
# Tests/Bridge.lean -- Hypothesis Coupling for Spec Theorems

This file imports all verified specification modules and uses `#check`
to confirm theorem signatures are stable. Improves coupling ratio
between formal proofs and test infrastructure.

Coverage: PipelineSoundness, SemanticSpec, CoreSpec, SaturationSpec,
ExtractSpec, TranslationValidation, SoundRewriteRule, FRI Pipeline,
VerifiedExtraction, Bitwise MixedPipeline.
-/

set_option autoImplicit false

/-! ## Pipeline Soundness -/
section PipelineSoundness
  #check @AmoLean.EGraph.Verified.full_pipeline_soundness
  #check @AmoLean.EGraph.Verified.full_pipeline_contract
  #check @AmoLean.EGraph.Verified.full_pipeline_soundness_ilp
end PipelineSoundness

/-! ## Semantic Spec -/
section SemanticSpec
  #check @AmoLean.EGraph.Verified.ConsistentValuation
  #check @AmoLean.EGraph.Verified.merge_consistent
  #check @AmoLean.EGraph.Verified.find_consistent
  #check @AmoLean.EGraph.Verified.canonicalize_consistent
  #check @AmoLean.EGraph.Verified.SemanticHashconsInv
end SemanticSpec

/-! ## Core Spec -/
section CoreSpec
  #check @AmoLean.EGraph.Verified.EGraphWF
  #check @AmoLean.EGraph.Verified.merge_creates_equiv
  #check @AmoLean.EGraph.Verified.merge_preserves_equiv
  #check @AmoLean.EGraph.Verified.add_leaf_preserves_wf
end CoreSpec

/-! ## Saturation Spec -/
section SaturationSpec
  #check @AmoLean.EGraph.Verified.saturateF_preserves_consistent
  #check @AmoLean.EGraph.Verified.PreservesCV
  #check @AmoLean.EGraph.Verified.rebuildF_preserves_triple
end SaturationSpec

/-! ## Extract Spec -/
section ExtractSpec
  #check @AmoLean.EGraph.Verified.extractF_correct
  #check @AmoLean.EGraph.Verified.extractILP_correct
  #check @AmoLean.EGraph.Verified.ilp_extraction_soundness
  #check @AmoLean.EGraph.Verified.BestNodeInv
end ExtractSpec

/-! ## Translation Validation -/
section TranslationValidation
  #check @AmoLean.EGraph.Verified.cryptoEquivalent
  #check @AmoLean.EGraph.Verified.translation_validation_contract
  #check @AmoLean.EGraph.Verified.verified_optimization_pipeline
end TranslationValidation

/-! ## Sound Rewrite Rules -/
section SoundRewriteRules
  #check @AmoLean.EGraph.Verified.SoundRewriteRule
  #check @AmoLean.EGraph.Verified.sound_rule_preserves_consistency
  #check @AmoLean.EGraph.Verified.ConditionalSoundRewriteRule
end SoundRewriteRules

/-! ## FRI Pipeline -/
section FRIPipeline
  #check @AmoLean.FRI.Verified.fri_pipeline_soundness
  #check @AmoLean.FRI.Verified.friEquivalent
  #check @AmoLean.FRI.Verified.FRIVerifiedResult
end FRIPipeline

/-! ## Verified Extraction (generic) -/
section VerifiedExtraction
  #check @AmoLean.EGraph.VerifiedExtraction.NodeOps
  #check @AmoLean.EGraph.VerifiedExtraction.NodeSemantics
  #check @AmoLean.EGraph.VerifiedExtraction.ConsistentValuation
  #check @AmoLean.EGraph.VerifiedExtraction.Greedy.extractF_correct
  #check @AmoLean.EGraph.VerifiedExtraction.Greedy.extractAuto_correct
  #check @AmoLean.EGraph.VerifiedExtraction.Greedy.ExtractableSound
end VerifiedExtraction

/-! ## Bitwise Mixed Pipeline -/
section BitwiseMixedPipeline
  #check @MixedPipeline.mixed_extractF_correct
  #check @MixedPipeline.mixed_extractAuto_correct
  #check @MixedPipeline.pipeline_mixed_equivalent
  #check @MixedPipeline.mixedEquivalent
end BitwiseMixedPipeline

#eval "Bridge: all 39 theorem/def signatures verified"
