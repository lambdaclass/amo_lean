/-
  AMO-Lean — Sound Rewrite Rules
  Fase 11 N11.3: SoundRewriteRule structure + consistency preservation.

  Provides verified rewrite rules that carry a semantic soundness proof:
  the LHS and RHS expressions evaluate identically for all environments.
  Adapted from OptiSat/SoundRule.lean for the AMO circuit domain.

  Key components:
  - `SoundRewriteRule`: unconditional sound rewrite rule
  - `ConditionalSoundRewriteRule`: rule with a side condition
  - `sound_rule_preserves_consistency`: merging after a sound rule preserves CV
-/
import AmoLean.EGraph.Verified.SemanticSpec

namespace AmoLean.EGraph.Verified

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: SoundRewriteRule
-- ══════════════════════════════════════════════════════════════════

variable {Val : Type} [Add Val] [Mul Val] [Neg Val]

/-- A sound rewrite rule carries a syntactic `RewriteRule` for e-matching
    plus a semantic proof that LHS and RHS expressions evaluate identically.

    `Expr` is the expression type for semantic reasoning.
    `Val` is the semantic domain (e.g., `ZMod p` for crypto fields).

    The `eval` field provides expression evaluation — instantiated to
    the circuit-level evaluator when connecting to the extraction pipeline.

    Adapted from OptiSat `SoundRewriteRule (Op Expr Val)`, specialized
    to `CircuitNodeOp` (AMO-Lean uses a single fixed operation type). -/
structure SoundRewriteRule (Expr : Type) (Val : Type) where
  /-- Rule name for debugging/display -/
  name : String
  /-- Syntactic rewrite rule for e-matching -/
  rule : RewriteRule
  /-- Semantic LHS expression parameterized by variable assignment -/
  lhsExpr : (Nat → Expr) → Expr
  /-- Semantic RHS expression parameterized by variable assignment -/
  rhsExpr : (Nat → Expr) → Expr
  /-- Expression evaluator -/
  eval : Expr → CircuitEnv Val → Val
  /-- Soundness: LHS and RHS evaluate to the same value for all environments -/
  soundness : ∀ (env : CircuitEnv Val) (vars : Nat → Expr),
    eval (lhsExpr vars) env = eval (rhsExpr vars) env

-- ══════════════════════════════════════════════════════════════════
-- Section 2: ConditionalSoundRewriteRule
-- ══════════════════════════════════════════════════════════════════

/-- A conditional sound rewrite rule extends `SoundRewriteRule` with a side
    condition that must hold for the rule to apply. The soundness proof
    guarantees that IF the condition holds, THEN LHS = RHS semantically.

    For unconditional rules, use `SoundRewriteRule.toConditional`. -/
structure ConditionalSoundRewriteRule (Expr : Type) (Val : Type) where
  name : String
  rule : RewriteRule
  lhsExpr : (Nat → Expr) → Expr
  rhsExpr : (Nat → Expr) → Expr
  eval : Expr → CircuitEnv Val → Val
  sideCond : CircuitEnv Val → (Nat → Expr) → Prop
  soundness : ∀ (env : CircuitEnv Val) (vars : Nat → Expr),
    sideCond env vars →
    eval (lhsExpr vars) env = eval (rhsExpr vars) env

/-- Lift an unconditional rule to a conditional one with trivial side condition. -/
def SoundRewriteRule.toConditional
    (r : SoundRewriteRule Expr Val) : ConditionalSoundRewriteRule Expr Val where
  name := r.name
  rule := r.rule
  lhsExpr := r.lhsExpr
  rhsExpr := r.rhsExpr
  eval := r.eval
  sideCond := fun _ _ => True
  soundness := fun env vars _ => r.soundness env vars

/-- A conditional rule is sound if its proof holds for all valid inputs. -/
def ConditionalSoundRewriteRule.IsSound
    (r : ConditionalSoundRewriteRule Expr Val) : Prop :=
  ∀ (env : CircuitEnv Val) (vars : Nat → Expr),
    r.sideCond env vars →
    r.eval (r.lhsExpr vars) env = r.eval (r.rhsExpr vars) env

set_option linter.unusedSectionVars false in
theorem ConditionalSoundRewriteRule.isSound
    (r : ConditionalSoundRewriteRule Expr Val) : r.IsSound :=
  r.soundness

-- ══════════════════════════════════════════════════════════════════
-- Section 3: sound_rule_preserves_consistency
-- ══════════════════════════════════════════════════════════════════

/-- Applying a SoundRewriteRule (which guarantees lhs.eval = rhs.eval)
    via merge preserves ConsistentValuation.

    This is a direct corollary of `merge_consistent` + `rule.soundness`:
    since the rule guarantees semantic equality between LHS and RHS,
    the merge is semantically valid. -/
theorem sound_rule_preserves_consistency
    (g : EGraph) (rule : SoundRewriteRule Expr Val)
    (lhsId rhsId : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (h1 : lhsId < g.unionFind.parent.size) (h2 : rhsId < g.unionFind.parent.size)
    (vars : Nat → Expr)
    (h_lhs : v (root g.unionFind lhsId) = rule.eval (rule.lhsExpr vars) env)
    (h_rhs : v (root g.unionFind rhsId) = rule.eval (rule.rhsExpr vars) env) :
    ConsistentValuation (g.merge lhsId rhsId) env v :=
  merge_consistent g lhsId rhsId env v hv hwf h1 h2
    (by rw [h_lhs, h_rhs, rule.soundness env vars])

/-- Conditional version: if the side condition holds, merging preserves CV. -/
theorem conditional_sound_rule_preserves_consistency
    (g : EGraph) (rule : ConditionalSoundRewriteRule Expr Val)
    (lhsId rhsId : EClassId)
    (env : CircuitEnv Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (h1 : lhsId < g.unionFind.parent.size) (h2 : rhsId < g.unionFind.parent.size)
    (vars : Nat → Expr)
    (h_cond : rule.sideCond env vars)
    (h_lhs : v (root g.unionFind lhsId) = rule.eval (rule.lhsExpr vars) env)
    (h_rhs : v (root g.unionFind rhsId) = rule.eval (rule.rhsExpr vars) env) :
    ConsistentValuation (g.merge lhsId rhsId) env v :=
  merge_consistent g lhsId rhsId env v hv hwf h1 h2
    (by rw [h_lhs, h_rhs, rule.soundness env vars h_cond])

end AmoLean.EGraph.Verified
