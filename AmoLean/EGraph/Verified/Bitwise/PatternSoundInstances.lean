/-
  AmoLean.EGraph.Verified.Bitwise.PatternSoundInstances — Concrete PatternSoundRule instances

  B65+B66: All 10 soundness + all 20 WF proofs CLOSED. Zero sorry.
  envPrecond field enables conditional soundness (mul_bridge needs env.constVal setup).
-/
import AmoLean.EGraph.Verified.Bitwise.MixedPatternRules
import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AmoLean.EGraph.Verified.Bitwise.PatternSoundInstances

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp MixedEnv evalMixedOp mixedChildren)
open MixedEMatch (Pattern PatVarId Substitution RewriteRule)
open MixedPatternRules

def Pattern.eval : Pattern MixedNodeOp → MixedEnv → (PatVarId → Nat) → Nat
  | .patVar pv, _, σ => σ pv
  | .node skelOp subpats, env, σ =>
    let childVals := subpats.map (fun p => Pattern.eval p env σ)
    let children := NodeOps.children skelOp
    let w : EClassId → Nat := fun id =>
      match (children.zip childVals).lookup id with
      | some val => val
      | none => 0
    evalMixedOp skelOp env w

def AllDistinctChildren : Pattern MixedNodeOp → Prop
  | .patVar _ => True
  | .node skelOp subpats =>
    (NodeOps.children skelOp).Nodup ∧
    subpats.length = (NodeOps.children skelOp).length ∧
    ∀ p ∈ subpats, AllDistinctChildren p

structure PatternSoundRule where
  rule : RewriteRule MixedNodeOp
  /-- Environment precondition (default: True = unconditional). -/
  envPrecond : MixedEnv → Prop := fun _ => True
  soundness : ∀ (env : MixedEnv) (σ : PatVarId → Nat),
    envPrecond env → Pattern.eval rule.lhs env σ = Pattern.eval rule.rhs env σ
  lhs_wf : AllDistinctChildren rule.lhs
  rhs_wf : AllDistinctChildren rule.rhs

-- ══════════════════════════════════════════════════════════════════
-- WF tactic: unfold → simp skeleton → decide Nodup + rfl length + intro subpats
-- ══════════════════════════════════════════════════════════════════

-- WF tactic pattern: for each instance, inline the proof.
-- Binary patterns: unfold rule AllDistinctChildren; simp [...]; exact ⟨decide, rfl, subpats⟩
-- Unary patterns: same but one subpattern
-- Nested: recurse one level

-- ══════════════════════════════════════════════════════════════════
-- 10 PatternSoundRule instances
-- ══════════════════════════════════════════════════════════════════

def patAndComm_sound : PatternSoundRule where
  rule := patAndComm
  soundness := fun _ σ _ => by
    simp only [patAndComm, Pattern.eval, List.map, NodeOps.children,
      mixedChildren, skelBitAnd, evalMixedOp, List.zip]
    exact Nat.land_comm (σ 0) (σ 1)
  lhs_wf := by unfold patAndComm AllDistinctChildren; simp only [skelBitAnd, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩
  rhs_wf := by unfold patAndComm AllDistinctChildren; simp only [skelBitAnd, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩

def patOrComm_sound : PatternSoundRule where
  rule := patOrComm
  soundness := fun _ σ _ => by
    simp only [patOrComm, Pattern.eval, List.map, NodeOps.children,
      mixedChildren, skelBitOr, evalMixedOp, List.zip]
    exact Nat.lor_comm (σ 0) (σ 1)
  lhs_wf := by unfold patOrComm AllDistinctChildren; simp only [skelBitOr, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩
  rhs_wf := by unfold patOrComm AllDistinctChildren; simp only [skelBitOr, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩

def patXorComm_sound : PatternSoundRule where
  rule := patXorComm
  soundness := fun _ σ _ => by
    simp only [patXorComm, Pattern.eval, List.map, NodeOps.children,
      mixedChildren, skelBitXor, evalMixedOp, List.zip]
    exact Nat.xor_comm (σ 0) (σ 1)
  lhs_wf := by unfold patXorComm AllDistinctChildren; simp only [skelBitXor, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩
  rhs_wf := by unfold patXorComm AllDistinctChildren; simp only [skelBitXor, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩

def patAndSelf_sound : PatternSoundRule where
  rule := patAndSelf
  soundness := fun _ σ _ => by
    simp only [patAndSelf, Pattern.eval, List.map, NodeOps.children,
      mixedChildren, skelBitAnd, evalMixedOp, List.zip]
    exact Nat.and_self (σ 0)
  lhs_wf := by unfold patAndSelf AllDistinctChildren; simp only [skelBitAnd, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩
  rhs_wf := by unfold patAndSelf AllDistinctChildren; trivial

def patXorSelfZero_sound : PatternSoundRule where
  rule := patXorSelfZero
  soundness := fun _ σ _ => by
    -- LHS: xor(σ 0, σ 0) = 0. RHS: negGate(σ 0) = 0. Both sides are 0.
    unfold patXorSelfZero
    show Pattern.eval (.node (.bitXor 0 1) [.patVar 0, .patVar 0]) _ σ =
         Pattern.eval (.node (.negGate 0) [.patVar 0]) _ σ
    simp [Pattern.eval, NodeOps.children, mixedChildren, evalMixedOp,
      List.zip, List.zipWith, List.lookup]
    exact Nat.xor_self (σ 0)
  lhs_wf := by unfold patXorSelfZero AllDistinctChildren; simp only [skelBitXor, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; rcases hp with rfl | rfl <;> (unfold AllDistinctChildren; trivial)⟩
  rhs_wf := by
    unfold patXorSelfZero AllDistinctChildren
    simp only [NodeOps.children, mixedChildren]
    exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; trivial⟩

def patShiftRightCompose_sound (a b : Nat) : PatternSoundRule where
  rule := patShiftRightCompose a b
  soundness := fun _ σ _ => by
    simp only [patShiftRightCompose, Pattern.eval, List.map, NodeOps.children,
      mixedChildren, skelShiftRight, evalMixedOp, List.zip]
    exact (Nat.shiftRight_add (σ 0) a b).symm
  lhs_wf := by unfold patShiftRightCompose AllDistinctChildren; simp only [skelShiftRight, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; simp only [skelShiftRight, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun q hq => by simp at hq; subst hq; unfold AllDistinctChildren; trivial⟩⟩
  rhs_wf := by unfold patShiftRightCompose AllDistinctChildren; simp only [skelShiftRight, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; trivial⟩

def patShiftLeftCompose_sound (a b : Nat) : PatternSoundRule where
  rule := patShiftLeftCompose a b
  soundness := fun _ σ _ => by
    simp only [patShiftLeftCompose, Pattern.eval, List.map, NodeOps.children,
      mixedChildren, skelShiftLeft, evalMixedOp, List.zip]
    exact (Nat.shiftLeft_add (σ 0) a b).symm
  lhs_wf := by unfold patShiftLeftCompose AllDistinctChildren; simp only [skelShiftLeft, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; simp only [skelShiftLeft, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun q hq => by simp at hq; subst hq; unfold AllDistinctChildren; trivial⟩⟩
  rhs_wf := by unfold patShiftLeftCompose AllDistinctChildren; simp only [skelShiftLeft, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; trivial⟩

def patShiftLeftMulBridge_sound (n : Nat) : PatternSoundRule where
  rule := patShiftLeftMulBridge n
  envPrecond := fun env => env.constVal (2 ^ n) = 2 ^ n
  soundness := fun _ σ h => by
    simp only [patShiftLeftMulBridge, Pattern.eval, List.map, NodeOps.children,
      mixedChildren, skelShiftLeft, skelMulGate, evalMixedOp, List.zip, Nat.shiftLeft_eq, h]
  lhs_wf := by unfold patShiftLeftMulBridge AllDistinctChildren; simp only [skelShiftLeft, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; trivial⟩
  rhs_wf := by
    unfold patShiftLeftMulBridge AllDistinctChildren
    simp only [skelMulGate, NodeOps.children, mixedChildren]
    exact ⟨by decide, rfl, fun p hp => by
      simp at hp; rcases hp with rfl | rfl
      · unfold AllDistinctChildren; trivial
      · unfold AllDistinctChildren; simp only [NodeOps.children, mixedChildren]
        exact ⟨by decide, rfl, fun _ h => by simp at h⟩⟩

def patMaskModBridge_sound (n : Nat) : PatternSoundRule where
  rule := patMaskModBridge n
  soundness := fun _ _ _ => rfl
  lhs_wf := by
    unfold patMaskModBridge AllDistinctChildren
    simp only [skelBitAnd, NodeOps.children, mixedChildren]
    exact ⟨by decide, rfl, fun p hp => by
      simp at hp; rcases hp with rfl | rfl
      · unfold AllDistinctChildren; trivial
      · unfold AllDistinctChildren; simp only [NodeOps.children, mixedChildren]
        exact ⟨by decide, rfl, fun _ h => by simp at h⟩⟩
  rhs_wf := by
    unfold patMaskModBridge AllDistinctChildren
    simp only [skelBitAnd, NodeOps.children, mixedChildren]
    exact ⟨by decide, rfl, fun p hp => by
      simp at hp; rcases hp with rfl | rfl
      · unfold AllDistinctChildren; trivial
      · unfold AllDistinctChildren; simp only [NodeOps.children, mixedChildren]
        exact ⟨by decide, rfl, fun _ h => by simp at h⟩⟩

def patShiftRightDivBridge_sound (n : Nat) : PatternSoundRule where
  rule := patShiftRightDivBridge n
  soundness := fun _ _ _ => rfl
  lhs_wf := by unfold patShiftRightDivBridge AllDistinctChildren; simp only [skelShiftRight, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; trivial⟩
  rhs_wf := by unfold patShiftRightDivBridge AllDistinctChildren; simp only [skelShiftRight, NodeOps.children, mixedChildren]; exact ⟨by decide, rfl, fun p hp => by simp at hp; subst hp; unfold AllDistinctChildren; trivial⟩

-- ══════════════════════════════════════════════════════════════════
-- Collection + master soundness
-- ══════════════════════════════════════════════════════════════════

def allPatternSoundRules : List PatternSoundRule :=
  [ patShiftRightCompose_sound 4 4, patShiftLeftCompose_sound 4 4
  , patAndSelf_sound, patAndComm_sound, patOrComm_sound
  , patXorSelfZero_sound, patXorComm_sound
  , patShiftLeftMulBridge_sound 8, patMaskModBridge_sound 8
  , patShiftRightDivBridge_sound 8 ]

theorem allPatternSoundRules_length : allPatternSoundRules.length = 10 := rfl

theorem allPatternSoundRules_sound :
    ∀ psr ∈ allPatternSoundRules, ∀ (env : MixedEnv) (σ : PatVarId → Nat),
      psr.envPrecond env →
      Pattern.eval psr.rule.lhs env σ = Pattern.eval psr.rule.rhs env σ :=
  fun psr _ env σ hpre => psr.soundness env σ hpre

end AmoLean.EGraph.Verified.Bitwise.PatternSoundInstances
