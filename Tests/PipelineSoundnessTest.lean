/-
  AMO-Lean v2.3.0 — Pipeline Soundness Integration Test
  Tests/PipelineSoundnessTest.lean

  N11.12: Integration tests for Fase 11 verified pipeline.
  Verifies that the e-graph pipeline (Level 1) and translation validation
  (Level 2) compose correctly with 0 custom axioms.

  Coverage:
  - N11.1-N11.2: SemanticSpec (CircuitEnv, ConsistentValuation)
  - N11.3: SaturationSpec (saturateF, rebuildF)
  - N11.4: ExtractSpec (extractF, extractILP)
  - N11.5: PipelineSoundness (full_pipeline_soundness, full_pipeline_contract)
  - N11.11: TranslationValidation (cryptoEquivalent, translation_validation_contract)
-/

import AmoLean.EGraph.Verified.PipelineSoundness
import AmoLean.EGraph.Verified.TranslationValidation

set_option autoImplicit false

namespace AmoLean.Tests.PipelineSoundnessTest

open AmoLean.EGraph.Verified

/-! ## TC-11.12.1: Axiom Audit — Pipeline Theorems

  All key theorems must depend only on standard Lean axioms
  (propext, Quot.sound, Classical.choice), NOT on custom axioms.
  Verified via `lean_verify` in the integration script;
  here we confirm the theorems are importable and well-typed. -/

-- Level 1: Pipeline soundness theorems exist and are well-typed
#check @full_pipeline_soundness
#check @full_pipeline_contract
#check @full_pipeline_soundness_ilp
#check @optimization_soundness_greedy
#check @optimization_soundness_ilp
#check @greedy_ilp_equivalent
#check @congruence_merge
#check @congruence_extract

-- Level 2: Translation validation theorems exist and are well-typed
#check @cryptoEquivalent
#check @cryptoEquivalent_refl
#check @cryptoEquivalent_symm
#check @cryptoEquivalent_trans
#check @cryptoEquivalent_add
#check @cryptoEquivalent_mul
#check @cryptoEquivalent_neg
#check @cryptoEquivalent_smul
#check @translation_validation_contract
#check @valid_witness_preserves_semantics
#check @verified_optimization_pipeline
#check @consistent_class_implies_equal

-- Structures exist
#check @CryptoProofWitness
#check @ValidatedOptResult
#check @ExprRewriteJustification
#check @TVStats
#check @ProofWitness

/-! ## TC-11.12.2: Level 1 + Level 2 Composition

  The verified_optimization_pipeline theorem correctly composes
  both levels: given a valid CryptoProofWitness, the optimized
  expression evaluates identically to the original. -/

-- Composition: Level 1 provides the witness, Level 2 validates it
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (w : CryptoProofWitness Expr) (h : w.isValid (Val := Val)) :
    ∀ env : CircuitEnv Val,
      CircuitEvalExpr.evalExpr w.optimized env =
      CircuitEvalExpr.evalExpr w.original env :=
  verified_optimization_pipeline w h

/-! ## TC-11.12.3: Equivalence Relation Properties

  cryptoEquivalent is a proper equivalence relation. -/

-- Reflexivity
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (e : Expr) : cryptoEquivalent (Val := Val) e e :=
  cryptoEquivalent_refl e

-- Symmetry
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (e1 e2 : Expr) (h : cryptoEquivalent (Val := Val) e1 e2) :
    cryptoEquivalent (Val := Val) e2 e1 :=
  cryptoEquivalent_symm h

-- Transitivity
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (e1 e2 e3 : Expr)
    (h12 : cryptoEquivalent (Val := Val) e1 e2)
    (h23 : cryptoEquivalent (Val := Val) e2 e3) :
    cryptoEquivalent (Val := Val) e1 e3 :=
  cryptoEquivalent_trans h12 h23

/-! ## TC-11.12.4: Congruence Closure

  All circuit operations preserve equivalence. -/

-- Addition congruence
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (a1 a2 b1 b2 : Expr)
    (ha : cryptoEquivalent (Val := Val) a1 a2)
    (hb : cryptoEquivalent (Val := Val) b1 b2)
    (env : CircuitEnv Val) :
    CircuitEvalExpr.evalExpr a1 env + CircuitEvalExpr.evalExpr b1 env =
    CircuitEvalExpr.evalExpr a2 env + CircuitEvalExpr.evalExpr b2 env :=
  cryptoEquivalent_add ha hb env

-- Multiplication congruence
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (a1 a2 b1 b2 : Expr)
    (ha : cryptoEquivalent (Val := Val) a1 a2)
    (hb : cryptoEquivalent (Val := Val) b1 b2)
    (env : CircuitEnv Val) :
    CircuitEvalExpr.evalExpr a1 env * CircuitEvalExpr.evalExpr b1 env =
    CircuitEvalExpr.evalExpr a2 env * CircuitEvalExpr.evalExpr b2 env :=
  cryptoEquivalent_mul ha hb env

-- Negation congruence
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (a1 a2 : Expr)
    (ha : cryptoEquivalent (Val := Val) a1 a2)
    (env : CircuitEnv Val) :
    -(CircuitEvalExpr.evalExpr a1 env) =
    -(CircuitEvalExpr.evalExpr a2 env) :=
  cryptoEquivalent_neg ha env

-- Scalar multiplication congruence
example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (Expr : Type) [CircuitExtractable Expr] [CircuitEvalExpr Expr Val]
    (a1 a2 : Expr) (c : Val)
    (ha : cryptoEquivalent (Val := Val) a1 a2)
    (env : CircuitEnv Val) :
    c * CircuitEvalExpr.evalExpr a1 env =
    c * CircuitEvalExpr.evalExpr a2 env :=
  cryptoEquivalent_smul c ha env

/-! ## TC-11.12.5: Bridge Theorem — E-graph to TV

  ConsistentValuation (Level 1 output) bridges to value equality
  (Level 2 input). Classes in the same equivalence class have equal values. -/

example (Val : Type) [Add Val] [Mul Val] [Neg Val]
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (id1 id2 : EClassId)
    (h_eq : UnionFind.root g.unionFind id1 = UnionFind.root g.unionFind id2) :
    v id1 = v id2 :=
  consistent_class_implies_equal g env v hcv id1 id2 h_eq

/-! ## TC-11.12.6: Axiom Census

  Codebase axiom inventory (as of v2.3.0):

  Pipeline (0 custom axioms):
  - SemanticSpec.lean: 0
  - SoundRewriteRule.lean: 0
  - SaturationSpec.lean: 0
  - ExtractSpec.lean: 0
  - PipelineSoundness.lean: 0
  - TranslationValidation.lean: 0

  Retained (documented, out of pipeline scope):
  - Perm.lean: 1 (applyIndex_tensor_eq — Lean eq-compiler limitation)
  - NTT/Radix4/*.lean: 8 (pending B35-B37)

  Poseidon sorry (out of scope):
  - Poseidon_Semantics.lean: 12 sorry (match splitter complexity)
-/

-- Axiom audit: print axioms for the 3 capstone theorems
#print axioms full_pipeline_soundness
#print axioms full_pipeline_contract
#print axioms verified_optimization_pipeline
#print axioms translation_validation_contract

end AmoLean.Tests.PipelineSoundnessTest
