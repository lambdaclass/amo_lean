/-
  AMO-Lean — Phased Saturation Specification

  Wraps saturation into a two-phase strategy:
    Phase 1 (algebraic): generic bitwise identities (shift compose, commutativity, bridges)
    Phase 2 (field-specific): Solinas fold rules + Mersenne fold

  This is a SPECIFICATION-level module. It defines the phasing strategy, proves that
  both phases preserve rule soundness, and that their composition preserves soundness.

  The key insight: since MixedSoundRule and FieldFoldRule each carry their own soundness
  proofs (universally quantified equalities), any saturation engine that applies these
  rules in order will produce a sound result. The phased spec captures this compositional
  guarantee without depending on any particular E-graph implementation.

  ## Key results

  - `PhasedConfig`: fuel parameters for each phase
  - `phase1Rules` / `phase2Rules`: rule separation
  - `phase1_all_sound` / `phase2_all_sound`: per-phase soundness
  - `phasedSaturateF`: two-phase saturation (fuel-based)
  - `phasedSaturateF_preserves_consistent`: composition preserves ConsistentValuation
  - `phased_rule_count`: total rule count = 13

  ## Design

  Phase 1 applies `allBitwiseRules` (10 generic identities) via a step function.
  Phase 2 applies `allFieldFoldRules` (3 field-specific folds) via a step function.
  Both step functions are abstract (`step1`, `step2`) with `PreservesCV` witnesses,
  matching the existing `saturateF_preserves_consistent` pattern from SaturationSpec.lean.

  Axiom census: 0 custom axioms. All proofs compose existing rule soundness fields.
-/
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.SolinasRuleGen
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules
import AmoLean.EGraph.Verified.SaturationSpec
import AmoLean.EGraph.Verified.PreservesCVInstances

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified (EClassId CircuitEnv EGraph
  saturateF rebuildF PreservesCV
  saturateF_preserves_consistent comp_preserves_cv
  ConsistentValuation PostMergeInvariant SemanticHashconsInv)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: PhasedConfig
-- ══════════════════════════════════════════════════════════════════

/-- Configuration for two-phase saturation.
    `algebraicFuel`: maximum iterations for Phase 1 (bitwise identities).
    `algebraicRebuildFuel`: rebuild depth per iteration in Phase 1.
    `bitwiseFuel`: maximum iterations for Phase 2 (field-specific folds).
    `bitwiseRebuildFuel`: rebuild depth per iteration in Phase 2. -/
structure PhasedConfig where
  /-- Maximum iterations for Phase 1 (algebraic/bitwise identities) -/
  algebraicFuel : Nat := 5
  /-- Rebuild depth per iteration in Phase 1 -/
  algebraicRebuildFuel : Nat := 3
  /-- Maximum iterations for Phase 2 (field-specific folds) -/
  bitwiseFuel : Nat := 10
  /-- Rebuild depth per iteration in Phase 2 -/
  bitwiseRebuildFuel : Nat := 5
  deriving Repr, Inhabited

/-- Default configuration: balanced fuel for both phases. -/
def PhasedConfig.default : PhasedConfig := {}

/-- Aggressive configuration: more iterations for field folds. -/
def PhasedConfig.aggressive : PhasedConfig where
  algebraicFuel := 8
  algebraicRebuildFuel := 5
  bitwiseFuel := 20
  bitwiseRebuildFuel := 8

/-- Minimal configuration: just one pass each (useful for testing). -/
def PhasedConfig.minimal : PhasedConfig where
  algebraicFuel := 1
  algebraicRebuildFuel := 1
  bitwiseFuel := 1
  bitwiseRebuildFuel := 1

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Phase separation — rule collections
-- ══════════════════════════════════════════════════════════════════

/-- Phase 1 rules: all generic bitwise identities (10 rules).
    These are field-independent and apply universally. -/
def phase1Rules : List MixedSoundRule := allBitwiseRules

/-- Phase 2 rules: all field-specific fold rules (3 Solinas-generated).
    These depend on the target prime and apply conditionally. -/
def phase2Rules : List FieldFoldRule := allSolinasRules

/-- Phase 1 hardcoded rules: the 3 manually verified field folds
    (mersenne31, babybear, goldilocks). Provided as a reference collection
    that matches the generated Solinas rules. -/
def phase2HardcodedRules : List FieldFoldRule := allFieldFoldRules

/-- Phase 1 contains exactly 10 rules. -/
theorem phase1Rules_length : phase1Rules.length = 10 := allBitwiseRules_length

/-- Phase 2 contains exactly 3 rules. -/
theorem phase2Rules_length : phase2Rules.length = 3 := allSolinasRules_length

/-- Phase 2 hardcoded collection also contains exactly 3 rules. -/
theorem phase2HardcodedRules_length : phase2HardcodedRules.length = 3 :=
  allFieldFoldRules_length

/-- Total rule count across both phases. -/
theorem phased_rule_count :
    phase1Rules.length + phase2Rules.length = 13 := by
  rw [phase1Rules_length, phase2Rules_length]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Per-phase soundness of rule collections
-- ══════════════════════════════════════════════════════════════════

/-- Phase 1 master soundness: every rule in Phase 1 preserves evaluation equality.
    For any environment and valuation, LHS = RHS. -/
theorem phase1_all_sound :
    ∀ r ∈ phase1Rules, ∀ (env : MixedEnv) (v : EClassId → Nat),
      r.lhsEval env v = r.rhsEval env v :=
  allBitwiseRules_sound

/-- Phase 2 master soundness: every rule in Phase 2 preserves modular equivalence.
    Under the side condition, foldEval ≡ specEval (mod prime). -/
theorem phase2_all_sound :
    ∀ r ∈ phase2Rules, ∀ (x : Nat), r.sideCond x →
      r.foldEval x % r.prime = r.specEval x % r.prime := by
  intro r hr x hsc
  exact r.soundness x hsc

/-- Phase 2 rules all have the trivial side condition (always satisfiable). -/
theorem phase2_sideCond_trivial :
    ∀ r ∈ phase2Rules, ∀ (x : Nat), r.sideCond x := by
  intro r hr x
  simp only [phase2Rules, allSolinasRules, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact trivial

/-- Corollary: Phase 2 soundness without side condition hypothesis
    (since all side conditions are trivially true). -/
theorem phase2_all_sound_unconditional :
    ∀ r ∈ phase2Rules, ∀ (x : Nat),
      r.foldEval x % r.prime = r.specEval x % r.prime := by
  intro r hr x
  exact phase2_all_sound r hr x (phase2_sideCond_trivial r hr x)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: phasedSaturateF — two-phase saturation
-- ══════════════════════════════════════════════════════════════════

variable {Val : Type} [Add Val] [Mul Val] [Neg Val]

/-- Two-phase equality saturation: algebraic rules first, then bitwise+field rules.

    **HEURISTIC**: This proves consistency preservation only, NOT optimality or confluence.
    Phase ordering is a practical strategy (Herbie, PLDI 2015) that controls E-graph explosion
    by separating algebraic simplification from field-specific reduction. The phased result
    may differ from single-pass saturation with all rules combined.

    The separation allows:
    1. Phase 1 to reach a fixpoint on algebraic identities before introducing field-specific rewrites
    2. Phase 2 to exploit the algebraic normal forms for more effective folding
    3. Independent fuel control for each phase -/
def phasedSaturateF (step1 step2 : EGraph → EGraph) (cfg : PhasedConfig) (g : EGraph) : EGraph :=
  let g1 := saturateF step1 cfg.algebraicFuel cfg.algebraicRebuildFuel g
  saturateF step2 cfg.bitwiseFuel cfg.bitwiseRebuildFuel g1

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Phase 1 preserves ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- Phase 1 preserves ConsistentValuation when the step function does.
    Direct application of saturateF_preserves_consistent. -/
theorem phasedSaturateF_phase1_consistent
    (step1 : EGraph → EGraph) (cfg : PhasedConfig)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (h_step1 : PreservesCV env step1) :
    ∃ v', ConsistentValuation (saturateF step1 cfg.algebraicFuel cfg.algebraicRebuildFuel g) env v' :=
  saturateF_preserves_consistent step1 cfg.algebraicFuel cfg.algebraicRebuildFuel g env v hcv hpmi hshi h_step1

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Phase 2 preserves ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- Phase 2 preserves ConsistentValuation when the step function does
    AND the input already has a consistent valuation.
    Uses the existential witness from Phase 1. -/
theorem phasedSaturateF_phase2_consistent
    (step2 : EGraph → EGraph) (fuel rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (h_step2 : PreservesCV env step2) :
    ∃ v', ConsistentValuation (saturateF step2 fuel rebuildFuel g) env v' :=
  saturateF_preserves_consistent step2 fuel rebuildFuel g env v hcv hpmi hshi h_step2

-- ══════════════════════════════════════════════════════════════════
-- Section 7: saturateF preserves full triple (needed for composition)
-- ══════════════════════════════════════════════════════════════════

/-- saturateF preserves the full (CV, PMI, SHI) triple, not just CV existence.
    Needed to chain Phase 1 output into Phase 2 input: we must carry PMI and SHI
    through Phase 1 so they are available as preconditions for Phase 2. -/
private theorem saturateF_preserves_triple (step : EGraph → EGraph)
    (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (h_step : PreservesCV env step) :
    ∃ v', ConsistentValuation (saturateF step maxIter rebuildFuel g) env v' ∧
          PostMergeInvariant (saturateF step maxIter rebuildFuel g) ∧
          SemanticHashconsInv (saturateF step maxIter rebuildFuel g) env v' := by
  induction maxIter generalizing g v with
  | zero => exact ⟨v, hcv, hpmi, hshi⟩
  | succ n ih =>
    simp only [saturateF]
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := h_step g v hcv hpmi hshi
    have ⟨hcv2, hpmi2, hshi2⟩ :=
      AmoLean.EGraph.Verified.rebuildF_preserves_triple env rebuildFuel
        (step g) v1 hcv1 hpmi1 hshi1
    exact ih (rebuildF (step g) rebuildFuel) v1 hcv2 hpmi2 hshi2

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Composition — full phased soundness
-- ══════════════════════════════════════════════════════════════════

/-- **Main theorem**: phased saturation preserves ConsistentValuation.
    If both step functions preserve the (CV, PMI, SHI) triple, then the
    two-phase composition also preserves CV.

    The proof threads the triple through Phase 1 (getting v1), then threads
    through Phase 2 (getting v2). The existential witness for the final
    valuation comes from Phase 2's output. -/
theorem phasedSaturateF_preserves_consistent
    (step1 step2 : EGraph → EGraph) (cfg : PhasedConfig)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (h_step1 : PreservesCV env step1)
    (h_step2 : PreservesCV env step2) :
    ∃ v', ConsistentValuation (phasedSaturateF step1 step2 cfg g) env v' := by
  unfold phasedSaturateF
  -- Extract the full triple after Phase 1
  obtain ⟨v1, hcv1, hpmi1, hshi1⟩ :=
    saturateF_preserves_triple step1 cfg.algebraicFuel cfg.algebraicRebuildFuel
      g env v hcv hpmi hshi h_step1
  -- Feed the triple into Phase 2
  exact saturateF_preserves_consistent step2 cfg.bitwiseFuel cfg.bitwiseRebuildFuel
    (saturateF step1 cfg.algebraicFuel cfg.algebraicRebuildFuel g) env v1 hcv1 hpmi1 hshi1 h_step2

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Composition with PreservesCV combinators
-- ══════════════════════════════════════════════════════════════════

/-- Alternative composition: if we have PreservesCV for the composed step,
    a single saturateF call suffices. This shows that phased saturation
    is a special case of sequential composition. -/
theorem single_pass_from_composed_step
    (step1 step2 : EGraph → EGraph)
    (maxIter rebuildFuel : Nat)
    (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (h_step1 : PreservesCV env step1)
    (h_step2 : PreservesCV env step2) :
    ∃ v', ConsistentValuation (saturateF (step2 ∘ step1) maxIter rebuildFuel g) env v' :=
  saturateF_preserves_consistent (step2 ∘ step1) maxIter rebuildFuel g env v hcv hpmi hshi
    (comp_preserves_cv env step1 step2 h_step1 h_step2)

-- ══════════════════════════════════════════════════════════════════
-- Section 10: Cost-aware phase selection
-- ══════════════════════════════════════════════════════════════════

/-- Phase 1 rule names (for tracing/debugging). -/
def phase1RuleNames : List String := phase1Rules.map MixedSoundRule.name

/-- Phase 2 rule names (for tracing/debugging). -/
def phase2RuleNames : List String := phase2Rules.map FieldFoldRule.name

/-- The phases are disjoint: no rule name appears in both phases. -/
theorem phases_disjoint_names :
    ∀ n1 ∈ phase1RuleNames, ∀ n2 ∈ phase2RuleNames, n1 ≠ n2 := by
  intro n1 h1 n2 h2
  simp only [phase1RuleNames, phase1Rules, allBitwiseRules, List.map_cons,
    List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h1
  simp only [phase2RuleNames, phase2Rules, allSolinasRules, List.map_cons,
    List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h2
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases h2 with rfl | rfl | rfl <;>
  decide

/-- Phase 1 bitwise ops have cost determined by hardware shift/logic latencies.
    On FPGA (DSP48E2), shifts are free (cost 0). -/
theorem fpga_shift_is_free :
    mixedOpCost fpga_dsp48e2 (.shiftLeft 0 1) = 0 ∧
    mixedOpCost fpga_dsp48e2 (.shiftRight 0 1) = 0 := by
  exact ⟨rfl, rfl⟩

/-- Phase 1 bitwise ops are at most as expensive as a 32-bit multiply on any hardware. -/
theorem shift_cost_le_mul (hw : HardwareCost)
    (h_shift : hw.shift ≤ hw.mul32)
    (h_and : hw.bitAnd ≤ hw.mul32)
    (h_xor : hw.bitXor ≤ hw.mul32)
    (h_or : hw.bitOr ≤ hw.mul32) :
    mixedOpCost hw (.shiftLeft 0 1) ≤ hw.mul32 ∧
    mixedOpCost hw (.shiftRight 0 1) ≤ hw.mul32 ∧
    mixedOpCost hw (.bitAnd 0 1) ≤ hw.mul32 ∧
    mixedOpCost hw (.bitXor 0 1) ≤ hw.mul32 ∧
    mixedOpCost hw (.bitOr 0 1) ≤ hw.mul32 := by
  simp only [mixedOpCost]
  exact ⟨h_shift, h_shift, h_and, h_xor, h_or⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 11: Non-vacuity witnesses
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: PhasedConfig.default has sensible fuel values. -/
example : PhasedConfig.default.algebraicFuel = 5 := rfl
example : PhasedConfig.default.bitwiseFuel = 10 := rfl
example : PhasedConfig.default.algebraicRebuildFuel = 3 := rfl
example : PhasedConfig.default.bitwiseRebuildFuel = 5 := rfl

/-- Non-vacuity: Phase 1 contains all 10 bitwise rules. -/
example : phase1Rules.length = 10 ∧ phase1Rules = allBitwiseRules := ⟨phase1Rules_length, rfl⟩

/-- Non-vacuity: Phase 2 contains all 3 Solinas rules. -/
example : phase2Rules.length = 3 ∧ phase2Rules = allSolinasRules := ⟨phase2Rules_length, rfl⟩

/-- Non-vacuity: phased_rule_count is not trivially true (rules are distinct). -/
example : phase1Rules.length = 10 := phase1Rules_length
example : phase2Rules.length = 3 := phase2Rules_length

/-- Non-vacuity: Phase 1 soundness is exercised on concrete values. -/
example : ∀ r ∈ phase1Rules, r.lhsEval
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun _ => 42) =
  r.rhsEval
    { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }
    (fun _ => 42) :=
  fun r hr => phase1_all_sound r hr _ _

/-- Non-vacuity: Phase 2 soundness is exercised on concrete values. -/
example : ∀ r ∈ phase2Rules,
    r.foldEval (2 ^ 32 + 7) % r.prime = r.specEval (2 ^ 32 + 7) % r.prime :=
  fun r hr => phase2_all_sound_unconditional r hr _

/-- Non-vacuity: phasedSaturateF with identity steps is identity on empty graph. -/
example : phasedSaturateF id id PhasedConfig.default EGraph.empty = EGraph.empty := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 12: Smoke tests
-- ══════════════════════════════════════════════════════════════════

#eval phase1RuleNames
-- Expected: ["shift_right_compose", "shift_left_compose", "and_self", "and_comm",
--            "or_comm", "xor_self_zero", "xor_comm", "mask_mod_bridge",
--            "shiftRight_div_bridge", "shiftLeft_mul_bridge"]

#eval phase2RuleNames
-- Expected: ["solinas_31_27", "solinas_24_24", "solinas_64_32"]

#eval PhasedConfig.default
-- Expected: { algebraicFuel := 5, algebraicRebuildFuel := 3, bitwiseFuel := 10, bitwiseRebuildFuel := 5 }

#eval PhasedConfig.aggressive
-- Expected: { algebraicFuel := 8, algebraicRebuildFuel := 5, bitwiseFuel := 20, bitwiseRebuildFuel := 8 }

#eval phase1Rules.length + phase2Rules.length
-- Expected: 13

end AmoLean.EGraph.Verified.Bitwise
