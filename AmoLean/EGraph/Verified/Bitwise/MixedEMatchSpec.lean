/-
  AmoLean.EGraph.Verified.Bitwise.MixedEMatchSpec — Soundness for MixedNodeOp E-Matching

  Provides:
  - Pattern.eval: denotational semantics for patterns
  - SameShapeSemantics per-constructor: ops with same skeleton evaluate identically
  - PatternSoundRule: structure connecting pattern rules to semantic soundness
  - Concrete soundness instances for binary and unary constructors

  Adapted from OptiSat LambdaSat/EMatchSpec.lean (semantic framework).
-/
import AmoLean.EGraph.Verified.Bitwise.MixedSaturation
import AmoLean.EGraph.Verified.Bitwise.MixedPatternRules
import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge

namespace MixedEMatchSpec

open AmoLean.EGraph.VerifiedExtraction (EClassId NodeOps)
open AmoLean.EGraph.Verified.Bitwise (MixedNodeOp evalMixedOp MixedEnv)
open MixedEMatch (Pattern PatVarId Substitution sameShape)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Pattern.eval — Denotational Semantics
-- ══════════════════════════════════════════════════════════════════

/-- Denotational semantics for patterns over MixedNodeOp.
    - `patVar pv` evaluates to `σ pv`
    - `node skelOp subpats` evaluates subpatterns, builds child valuation
      via zip+lookup, applies `evalMixedOp`.

    The skeleton op must have DISTINCT child IDs for binary ops
    (e.g., `.bitAnd 0 1` not `.bitAnd 0 0`) to ensure correct lookup. -/
@[simp] def Pattern.eval : Pattern MixedNodeOp → (Nat → Nat) → (PatVarId → Nat) → Nat
  | .patVar pv, _, σ => σ pv
  | .node skelOp subpats, env, σ =>
    let childVals := subpats.map (fun p => Pattern.eval p env σ)
    let children := NodeOps.children skelOp
    let w : EClassId → Nat := fun id =>
      match (children.zip childVals).lookup id with
      | some val => val
      | none => 0
    evalMixedOp skelOp ⟨env, env, env⟩ w

-- ══════════════════════════════════════════════════════════════════
-- Section 2: SameShapeSemantics — per-constructor instances
-- ══════════════════════════════════════════════════════════════════

/-- SameShapeSemantics for binary ops: ops with same skeleton evaluate identically
    when corresponding children have matching values. -/
theorem sameShape_bitAnd (a₁ b₁ a₂ b₂ : EClassId)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat)
    (h₀ : v₁ a₁ = v₂ a₂) (h₁ : v₁ b₁ = v₂ b₂) :
    evalMixedOp (.bitAnd a₁ b₁) env v₁ = evalMixedOp (.bitAnd a₂ b₂) env v₂ := by
  simp only [evalMixedOp]; rw [h₀, h₁]

theorem sameShape_bitXor (a₁ b₁ a₂ b₂ : EClassId)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat)
    (h₀ : v₁ a₁ = v₂ a₂) (h₁ : v₁ b₁ = v₂ b₂) :
    evalMixedOp (.bitXor a₁ b₁) env v₁ = evalMixedOp (.bitXor a₂ b₂) env v₂ := by
  simp only [evalMixedOp]; rw [h₀, h₁]

theorem sameShape_bitOr (a₁ b₁ a₂ b₂ : EClassId)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat)
    (h₀ : v₁ a₁ = v₂ a₂) (h₁ : v₁ b₁ = v₂ b₂) :
    evalMixedOp (.bitOr a₁ b₁) env v₁ = evalMixedOp (.bitOr a₂ b₂) env v₂ := by
  simp only [evalMixedOp]; rw [h₀, h₁]

theorem sameShape_addGate (a₁ b₁ a₂ b₂ : EClassId)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat)
    (h₀ : v₁ a₁ = v₂ a₂) (h₁ : v₁ b₁ = v₂ b₂) :
    evalMixedOp (.addGate a₁ b₁) env v₁ = evalMixedOp (.addGate a₂ b₂) env v₂ := by
  simp only [evalMixedOp]; rw [h₀, h₁]

theorem sameShape_mulGate (a₁ b₁ a₂ b₂ : EClassId)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat)
    (h₀ : v₁ a₁ = v₂ a₂) (h₁ : v₁ b₁ = v₂ b₂) :
    evalMixedOp (.mulGate a₁ b₁) env v₁ = evalMixedOp (.mulGate a₂ b₂) env v₂ := by
  simp only [evalMixedOp]; rw [h₀, h₁]

theorem sameShape_shiftRight (a₁ a₂ : EClassId) (n : Nat)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat) (h₀ : v₁ a₁ = v₂ a₂) :
    evalMixedOp (.shiftRight a₁ n) env v₁ = evalMixedOp (.shiftRight a₂ n) env v₂ := by
  simp only [evalMixedOp]; rw [h₀]

theorem sameShape_shiftLeft (a₁ a₂ : EClassId) (n : Nat)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat) (h₀ : v₁ a₁ = v₂ a₂) :
    evalMixedOp (.shiftLeft a₁ n) env v₁ = evalMixedOp (.shiftLeft a₂ n) env v₂ := by
  simp only [evalMixedOp]; rw [h₀]

theorem sameShape_smulGate (a₁ a₂ : EClassId) (c : Nat)
    (env : MixedEnv) (v₁ v₂ : EClassId → Nat) (h₀ : v₁ a₁ = v₂ a₂) :
    evalMixedOp (.smulGate c a₁) env v₁ = evalMixedOp (.smulGate c a₂) env v₂ := by
  simp only [evalMixedOp]; rw [h₀]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: PatternSoundRule
-- ══════════════════════════════════════════════════════════════════

/-- A pattern-based rewrite rule with a soundness proof.
    For all environments and pattern variable assignments,
    evaluating the LHS and RHS patterns produces the same value. -/
structure PatternSoundRule where
  rule : MixedEMatch.RewriteRule MixedNodeOp
  soundness : ∀ (env : Nat → Nat) (σ : PatVarId → Nat),
    Pattern.eval rule.lhs env σ = Pattern.eval rule.rhs env σ

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Core bitwise identities as direct theorems
-- ══════════════════════════════════════════════════════════════════

/-- `bitAnd(x, x) = x` for all Nat x. -/
theorem and_self_nat (x : Nat) : Nat.land x x = x := Nat.and_self x

/-- `bitXor(x, x) = 0` for all Nat x. -/
theorem xor_self_nat (x : Nat) : Nat.xor x x = 0 := Nat.xor_self x

/-- `bitAnd(x, y) = bitAnd(y, x)` for all Nat x y. -/
theorem and_comm_nat (x y : Nat) : Nat.land x y = Nat.land y x := Nat.land_comm x y

/-- `bitOr(x, y) = bitOr(y, x)` for all Nat x y. -/
theorem or_comm_nat (x y : Nat) : Nat.lor x y = Nat.lor y x := Nat.lor_comm x y

/-- `bitXor(x, y) = bitXor(y, x)` for all Nat x y. -/
theorem xor_comm_nat (x y : Nat) : Nat.xor x y = Nat.xor y x := Nat.xor_comm x y

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests — non-vacuity
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: Pattern.eval patVar returns the bound value. -/
example : Pattern.eval (Pattern.patVar (Op := MixedNodeOp) 0) (fun _ => 42) (fun n => n * 10) = 0 := by
  simp [Pattern.eval]

/-- Non-vacuity: and_self identity. -/
example : Nat.land 7 7 = 7 := by native_decide

/-- Non-vacuity: xor_self identity. -/
example : Nat.xor 42 42 = 0 := by native_decide

/-- Non-vacuity: SameShapeSemantics concrete instance. -/
example : evalMixedOp (.bitAnd 0 1) ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩
    (fun i => if i == 0 then 15 else 7) =
  evalMixedOp (.bitAnd 2 3) ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩
    (fun i => if i == 2 then 15 else 7) := by native_decide

/-- Non-vacuity: and_comm on concrete values. -/
example : Nat.land 0xFF 0x0F = Nat.land 0x0F 0xFF := by native_decide

end MixedEMatchSpec
