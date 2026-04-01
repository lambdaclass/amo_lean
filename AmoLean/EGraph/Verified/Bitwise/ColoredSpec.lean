/-
  AMO-Lean — ColoredSpec: Colored Soundness Specification (CCV)
  Fase 27 N27.3: Ported from OptiSat v2 ColoredSpec.lean.

  Defines `MixedCCV` (Colored Consistent Valuation): the semantic invariant
  for colored e-graphs. Extends base `ConsistentValuation` with color-gated
  equalities: for each color c with assumption φ_c, IF φ_c holds, THEN all
  classes merged under c have the same value in the valuation.

  Key insight: CCV projects to standard CV at the root color, preserving
  backward compatibility with all existing theorems.

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)

  Consumes: ColoredEGraph (SmallUF, compositeFind, ColoredLayer)
  Consumed by: MultiRelMixed (N27.5), HardwareColors (N27.8)
-/
import AmoLean.EGraph.Verified.Bitwise.ColoredEGraph
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.ColoredSpec

open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise (MixedSoundRule MixedEnv)
open AmoLean.EGraph.Verified.Bitwise.Colored

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Color Assumptions
-- ══════════════════════════════════════════════════════════════════

/-- An assumption function maps each color to a proposition on the environment.
    Root color (0) has trivial assumption `True`. -/
def ColorAssumption := ColorId → MixedEnv → Prop

/-- Well-formed assumptions: root is trivial, child implies parent. -/
def WellFormedAssumptions (assumptions : ColorAssumption)
    (hierarchy : ColorHierarchy) : Prop :=
  (∀ env, assumptions colorRoot env) ∧
  (∀ c : ColorId, c ≠ colorRoot →
    ∀ env, assumptions c env → assumptions (hierarchy.getParent c) env)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Colored Consistent Valuation (CCV)
-- ══════════════════════════════════════════════════════════════════

/-- MixedCCV: the semantic invariant for colored e-graphs specialized to Mixed types.

    Parameterized by:
    - `baseCV`: the base ConsistentValuation (a Prop, avoids importing EGraph)
    - `baseFind`: root-finding function from the base union-find
    - `cl`: the colored layer
    - `assumptions`: per-color assumption map
    - `env`: the circuit environment
    - `v`: the valuation (eclass → value) -/
def MixedCCV (baseCV : Prop) (baseFind : EClassId → EClassId)
    (cl : ColoredLayer) (assumptions : ColorAssumption)
    (env : MixedEnv) (v : EClassId → Nat) : Prop :=
  baseCV ∧
  (∀ c : ColorId, c ≠ colorRoot → assumptions c env →
    ∀ a b : EClassId,
    cl.equivUnderColor baseFind c a b = true →
    v a = v b)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: CCV ↔ CV Backward Compatibility
-- ══════════════════════════════════════════════════════════════════

/-- CCV implies standard CV: just project the first conjunct. -/
theorem CCV_implies_base_CV (baseCV : Prop) (baseFind : EClassId → EClassId)
    (cl : ColoredLayer) (assumptions : ColorAssumption)
    (env : MixedEnv) (v : EClassId → Nat)
    (hccv : MixedCCV baseCV baseFind cl assumptions env v) :
    baseCV :=
  hccv.1

/-- CV lifts to CCV when there are no non-root colors (empty colored layer). -/
theorem CV_implies_CCV_empty (baseCV : Prop) (baseFind : EClassId → EClassId)
    (env : MixedEnv) (v : EClassId → Nat)
    (hcv : baseCV)
    (hbase_eq : ∀ (x y : EClassId), (baseFind x == baseFind y) = true → v x = v y) :
    MixedCCV baseCV baseFind ColoredLayer.empty (fun _ _ => True) env v :=
  ⟨hcv, fun c _hc _ha a b hequiv => by
    rw [equivUnderColor_empty_layer] at hequiv
    exact hbase_eq a b hequiv⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Find Preserves Valuation
-- ══════════════════════════════════════════════════════════════════

/-- Colored find preserves valuation: the representative has the same value. -/
def FindPreservesVal (cl : ColoredLayer) (baseFind : EClassId → EClassId)
    (v : EClassId → Nat) (fuel : Nat) : Prop :=
  ∀ c : ColorId, ∀ id : EClassId,
    v (cl.findUnderColor baseFind c id fuel) = v id

private theorem foldl_deltaFind_preserves_val_aux
    (colorUFs : Std.HashMap ColorId SmallUF) (ancestors : List ColorId)
    (fuel : Nat) (v : EClassId → Nat)
    (hcolors : ∀ c id, v ((colorUFs.getD c SmallUF.empty).deltaFind id fuel) = v id) :
    ∀ acc, v (ancestors.foldl (fun acc c =>
      (colorUFs.getD c SmallUF.empty).deltaFind acc fuel) acc) = v acc := by
  induction ancestors with
  | nil => intro acc; rfl
  | cons c rest ih =>
    intro acc; simp only [List.foldl]
    have := ih ((colorUFs.getD c SmallUF.empty).deltaFind acc fuel)
    rw [this]; exact hcolors c acc

private theorem foldl_deltaFind_preserves_val
    (colorUFs : Std.HashMap ColorId SmallUF) (ancestors : List ColorId)
    (baseFind : EClassId → EClassId) (fuel : Nat)
    (v : EClassId → Nat)
    (hbase : ∀ id, v (baseFind id) = v id)
    (hcolors : ∀ c id, v ((colorUFs.getD c SmallUF.empty).deltaFind id fuel) = v id) :
    ∀ id, v (compositeFind colorUFs ancestors baseFind fuel id) = v id := by
  intro id; simp only [compositeFind]
  rw [foldl_deltaFind_preserves_val_aux colorUFs ancestors fuel v hcolors]
  exact hbase id

-- ══════════════════════════════════════════════════════════════════
-- Section 5: coloredMerge Preserves CCV
-- ══════════════════════════════════════════════════════════════════

private theorem addToWorklist_equivUnderColor (cl : ColoredLayer) (c : ColorId)
    (ids : List EClassId) (baseFind : EClassId → EClassId) (c' : ColorId)
    (a b : EClassId) (fuel : Nat) :
    (cl.addToWorklist c ids).equivUnderColor baseFind c' a b fuel =
    cl.equivUnderColor baseFind c' a b fuel := rfl

/-- Merging under a color preserves CCV when v(a) = v(b). -/
theorem coloredMerge_preserves_CCV (baseCV : Prop) (baseFind : EClassId → EClassId)
    (cl : ColoredLayer) (assumptions : ColorAssumption)
    (env : MixedEnv) (v : EClassId → Nat)
    (c : ColorId) (a b : EClassId) (fuel : Nat)
    (hccv : MixedCCV baseCV baseFind cl assumptions env v)
    (_hassume : assumptions c env)
    (hsound : v a = v b)
    (hbase_v : ∀ id, v (baseFind id) = v id)
    (hdelta : ∀ c_inner id f, v ((cl.colorUFs.getD c_inner SmallUF.empty).deltaFind id f) = v id)
    (hroot_repA : (cl.getUF c).delta.get?
        ((cl.getUF c).deltaFind
          (cl.findUnderColor baseFind c a fuel) fuel) = none)
    (hroot_repB : (cl.getUF c).delta.get?
        ((cl.getUF c).deltaFind
          (cl.findUnderColor baseFind c b fuel) fuel) = none) :
    MixedCCV baseCV baseFind
      (cl.mergeUnderColor baseFind c a b fuel).1
      assumptions env v := by
  constructor
  · exact hccv.1
  · intro c' hc' hassume' a' b' hequiv'
    simp only [ColoredLayer.mergeUnderColor] at hequiv'
    split at hequiv'
    · exact hccv.2 c' hc' hassume' a' b' hequiv'
    · rename_i hneq
      let repA := cl.findUnderColor baseFind c a fuel
      let repB := cl.findUnderColor baseFind c b fuel
      let mergedUF := (cl.getUF c).merge repA repB fuel
      have hdelta_fuel : ∀ c_inner id,
          v ((cl.colorUFs.getD c_inner SmallUF.empty).deltaFind id fuel) = v id :=
        fun c_inner id => hdelta c_inner id fuel
      have hv_repA : v repA = v a :=
        foldl_deltaFind_preserves_val cl.colorUFs _ baseFind fuel v
          hbase_v hdelta_fuel a
      have hv_repB : v repB = v b :=
        foldl_deltaFind_preserves_val cl.colorUFs _ baseFind fuel v
          hbase_v hdelta_fuel b
      have hab : v repA = v repB := hv_repA.trans (hsound.trans hv_repB.symm)
      have hold : ∀ id f, v ((cl.getUF c).deltaFind id f) = v id :=
        fun id f => by simp only [ColoredLayer.getUF]; exact hdelta c id f
      have hmod_delta : ∀ f_inner c_inner id_inner,
          v (((cl.colorUFs.insert c mergedUF).getD c_inner
            SmallUF.empty).deltaFind id_inner f_inner) = v id_inner := by
        intro f_inner c_inner id_inner
        rw [Std.HashMap.getD_insert]
        split
        · rename_i hceq
          have hceq' := beq_iff_eq.mp hceq; subst hceq'
          show v (((cl.getUF c).merge repA repB fuel).deltaFind id_inner f_inner) = v id_inner
          simp only [SmallUF.merge]
          split
          · simp only [ColoredLayer.getUF]; exact hdelta c id_inner f_inner
          · have hab_internal : v ((cl.getUF c).deltaFind repA fuel) =
                v ((cl.getUF c).deltaFind repB fuel) :=
              (hold repA fuel).trans (hab.trans (hold repB fuel).symm)
            exact SmallUF.deltaFind_insert_preserves_val (cl.getUF c)
              ((cl.getUF c).deltaFind repA fuel) ((cl.getUF c).deltaFind repB fuel) v
              hroot_repA hroot_repB hab_internal hold id_inner f_inner
        · exact hdelta c_inner id_inner f_inner
      have hequiv_clean : (cl.setUF c mergedUF).equivUnderColor baseFind c' a' b' = true := by
        have : ((cl.setUF c mergedUF).addToWorklist c [repA, repB], true).fst =
               (cl.setUF c mergedUF).addToWorklist c [repA, repB] := rfl
        rw [this] at hequiv'
        rw [addToWorklist_equivUnderColor] at hequiv'
        exact hequiv'
      simp only [ColoredLayer.equivUnderColor, ColoredLayer.findUnderColor,
                  ColoredLayer.setUF] at hequiv_clean
      have hbeq := beq_iff_eq.mp hequiv_clean
      have hmod_find : ∀ id, v (compositeFind (cl.colorUFs.insert c mergedUF)
          (cl.hierarchy.ancestors c').reverse baseFind 100 id) = v id :=
        foldl_deltaFind_preserves_val (cl.colorUFs.insert c mergedUF)
          (cl.hierarchy.ancestors c').reverse baseFind 100 v
          hbase_v (fun c_inner id => hmod_delta 100 c_inner id)
      calc v a' = v (compositeFind (cl.colorUFs.insert c mergedUF)
                    (cl.hierarchy.ancestors c').reverse baseFind 100 a') := (hmod_find a').symm
        _ = v (compositeFind (cl.colorUFs.insert c mergedUF)
                    (cl.hierarchy.ancestors c').reverse baseFind 100 b') := congrArg v hbeq
        _ = v b' := hmod_find b'

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Sound Colored Rules
-- ══════════════════════════════════════════════════════════════════

/-- A sound colored rewrite rule specialized to Mixed types.
    Carries a soundness proof that LHS = RHS under the color's assumption. -/
structure MixedColoredSoundRule where
  color : ColorId
  name : String
  lhsEval : MixedEnv → (EClassId → Nat) → Nat
  rhsEval : MixedEnv → (EClassId → Nat) → Nat
  assumption : MixedEnv → Prop
  soundness : ∀ (env : MixedEnv) (v : EClassId → Nat),
    assumption env → lhsEval env v = rhsEval env v

/-- An unconditional MixedSoundRule lifts to a colored rule at root color. -/
def MixedSoundRule.toColoredRule (r : MixedSoundRule) : MixedColoredSoundRule where
  color := colorRoot
  name := r.name
  lhsEval := r.lhsEval
  rhsEval := r.rhsEval
  assumption := fun _ => True
  soundness := fun env v _ => r.soundness env v

/-- Applying a sound colored rule preserves CCV. -/
theorem soundColoredRule_preserves_CCV (baseCV : Prop) (baseFind : EClassId → EClassId)
    (cl : ColoredLayer) (rule : MixedColoredSoundRule)
    (assumptions : ColorAssumption)
    (env : MixedEnv) (v : EClassId → Nat)
    (lhsId rhsId : EClassId) (fuel : Nat)
    (hccv : MixedCCV baseCV baseFind cl assumptions env v)
    (hassume : assumptions rule.color env)
    (h_color_match : rule.assumption = assumptions rule.color)
    (hbase_v : ∀ id, v (baseFind id) = v id)
    (hdelta : ∀ c_inner id f,
      v ((cl.colorUFs.getD c_inner SmallUF.empty).deltaFind id f) = v id)
    (hroot_repA : (cl.getUF rule.color).delta.get?
        ((cl.getUF rule.color).deltaFind
          (cl.findUnderColor baseFind rule.color lhsId fuel) fuel) = none)
    (hroot_repB : (cl.getUF rule.color).delta.get?
        ((cl.getUF rule.color).deltaFind
          (cl.findUnderColor baseFind rule.color rhsId fuel) fuel) = none)
    (h_lhs : v lhsId = rule.lhsEval env v)
    (h_rhs : v rhsId = rule.rhsEval env v) :
    MixedCCV baseCV baseFind
      (cl.mergeUnderColor baseFind rule.color lhsId rhsId fuel).1
      assumptions env v :=
  coloredMerge_preserves_CCV baseCV baseFind cl assumptions env v
    rule.color lhsId rhsId fuel
    hccv hassume (by rw [h_lhs, h_rhs]; exact rule.soundness env v (h_color_match ▸ hassume))
    hbase_v hdelta hroot_repA hroot_repB

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Extraction Under Color
-- ══════════════════════════════════════════════════════════════════

/-- Extraction correctness under a non-root color: if CCV holds and the color's
    assumption holds, then equivalent classes have equal values.
    For root-color extraction, use `CCV_implies_base_CV` + base extraction. -/
theorem extractColored_correct (baseCV : Prop) (baseFind : EClassId → EClassId)
    (cl : ColoredLayer) (assumptions : ColorAssumption)
    (env : MixedEnv) (v : EClassId → Nat)
    (c : ColorId) (classId : EClassId)
    (hccv : MixedCCV baseCV baseFind cl assumptions env v)
    (hnonroot : c ≠ colorRoot)
    (hassume : assumptions c env)
    (h_equiv : cl.equivUnderColor baseFind c classId
      (cl.findUnderColor baseFind c classId) = true) :
    v classId = v (cl.findUnderColor baseFind c classId) :=
  hccv.2 c hnonroot hassume classId _ h_equiv

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

example (baseCV : Prop) (baseFind : EClassId → EClassId)
    (cl : ColoredLayer) (assumptions : ColorAssumption)
    (env : MixedEnv) (v : EClassId → Nat)
    (hccv : MixedCCV baseCV baseFind cl assumptions env v) :
    baseCV :=
  CCV_implies_base_CV baseCV baseFind cl assumptions env v hccv

end AmoLean.EGraph.Verified.Bitwise.ColoredSpec
