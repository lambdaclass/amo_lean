/-
  AMO-Lean - Pruebas de Corrección

  Este archivo contiene las pruebas de que las reglas de reescritura
  preservan la semántica de las expresiones.
-/

import AmoLean.Basic
import Mathlib.Algebra.Ring.Basic

namespace AmoLean

open Expr

/-! ## Parte 1: Teoremas de Preservación Semántica -/

/--
Cada regla de reescritura debe preservar la denotación.
Este es el teorema central que garantiza corrección.
-/
theorem denote_preserved_by_rule {α : Type} [Add α] [Mul α]
    (rule : RewriteRule α) (e e' : Expr α) (env : VarId → α)
    (h : rule e = some e')
    (h_sound : ∀ x y, rule x = some y → denote env x = denote env y) :
    denote env e = denote env e' :=
  h_sound e e' h

/-! ## Parte 2: Lemas auxiliares para BEq -/

/-- Si c == 0 es true y tenemos LawfulBEq, entonces c = 0 -/
lemma beq_zero_eq {α : Type} [BEq α] [LawfulBEq α] [OfNat α 0] (c : α)
    (h : (c == (0 : α)) = true) : c = 0 := by
  exact eq_of_beq h

/-- Si c == 1 es true y tenemos LawfulBEq, entonces c = 1 -/
lemma beq_one_eq {α : Type} [BEq α] [LawfulBEq α] [OfNat α 1] (c : α)
    (h : (c == (1 : α)) = true) : c = 1 := by
  exact eq_of_beq h

/-! ## Parte 3: Pruebas para Reglas Individuales -/

section RuleProofs

variable {α : Type} [Semiring α] [DecidableEq α]
variable (env : VarId → α)

-- Instancia de LawfulBEq para tipos con DecidableEq
instance : LawfulBEq α := inferInstance

/-- Corrección de e + 0 → e -/
theorem rule_add_zero_right_sound :
    ∀ e e' : Expr α, rule_add_zero_right e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_add_zero_right] at h
  | var _ => simp [rule_add_zero_right] at h
  | mul _ _ => simp [rule_add_zero_right] at h
  | add e1 (const c) =>
    simp only [rule_add_zero_right] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [denote]
      have hc : c = 0 := beq_zero_eq c (by assumption)
      rw [hc, add_zero]
    · contradiction
  | add e1 (var _) => simp [rule_add_zero_right] at h
  | add e1 (add _ _) => simp [rule_add_zero_right] at h
  | add e1 (mul _ _) => simp [rule_add_zero_right] at h

/-- Corrección de 0 + e → e -/
theorem rule_add_zero_left_sound :
    ∀ e e' : Expr α, rule_add_zero_left e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_add_zero_left] at h
  | var _ => simp [rule_add_zero_left] at h
  | mul _ _ => simp [rule_add_zero_left] at h
  | add (const c) e2 =>
    simp only [rule_add_zero_left] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [denote]
      have hc : c = 0 := beq_zero_eq c (by assumption)
      rw [hc, zero_add]
    · contradiction
  | add (var _) _ => simp [rule_add_zero_left] at h
  | add (add _ _) _ => simp [rule_add_zero_left] at h
  | add (mul _ _) _ => simp [rule_add_zero_left] at h

/-- Corrección de e * 1 → e -/
theorem rule_mul_one_right_sound :
    ∀ e e' : Expr α, rule_mul_one_right e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_mul_one_right] at h
  | var _ => simp [rule_mul_one_right] at h
  | add _ _ => simp [rule_mul_one_right] at h
  | mul e1 (const c) =>
    simp only [rule_mul_one_right] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [denote]
      have hc : c = 1 := beq_one_eq c (by assumption)
      rw [hc, mul_one]
    · contradiction
  | mul _ (var _) => simp [rule_mul_one_right] at h
  | mul _ (add _ _) => simp [rule_mul_one_right] at h
  | mul _ (mul _ _) => simp [rule_mul_one_right] at h

/-- Corrección de 1 * e → e -/
theorem rule_mul_one_left_sound :
    ∀ e e' : Expr α, rule_mul_one_left e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_mul_one_left] at h
  | var _ => simp [rule_mul_one_left] at h
  | add _ _ => simp [rule_mul_one_left] at h
  | mul (const c) e2 =>
    simp only [rule_mul_one_left] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [denote]
      have hc : c = 1 := beq_one_eq c (by assumption)
      rw [hc, one_mul]
    · contradiction
  | mul (var _) _ => simp [rule_mul_one_left] at h
  | mul (add _ _) _ => simp [rule_mul_one_left] at h
  | mul (mul _ _) _ => simp [rule_mul_one_left] at h

/-- Corrección de e * 0 → 0 -/
theorem rule_mul_zero_right_sound :
    ∀ e e' : Expr α, rule_mul_zero_right e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_mul_zero_right] at h
  | var _ => simp [rule_mul_zero_right] at h
  | add _ _ => simp [rule_mul_zero_right] at h
  | mul e1 (const c) =>
    simp only [rule_mul_zero_right] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [denote]
      have hc : c = 0 := beq_zero_eq c (by assumption)
      rw [hc, mul_zero]
    · contradiction
  | mul _ (var _) => simp [rule_mul_zero_right] at h
  | mul _ (add _ _) => simp [rule_mul_zero_right] at h
  | mul _ (mul _ _) => simp [rule_mul_zero_right] at h

/-- Corrección de 0 * e → 0 -/
theorem rule_mul_zero_left_sound :
    ∀ e e' : Expr α, rule_mul_zero_left e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_mul_zero_left] at h
  | var _ => simp [rule_mul_zero_left] at h
  | add _ _ => simp [rule_mul_zero_left] at h
  | mul (const c) e2 =>
    simp only [rule_mul_zero_left] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [denote]
      have hc : c = 0 := beq_zero_eq c (by assumption)
      rw [hc, zero_mul]
    · contradiction
  | mul (var _) _ => simp [rule_mul_zero_left] at h
  | mul (add _ _) _ => simp [rule_mul_zero_left] at h
  | mul (mul _ _) _ => simp [rule_mul_zero_left] at h

omit [DecidableEq α] in
/-- Corrección de la distributividad izquierda: a * (b + c) → a*b + a*c -/
theorem rule_distrib_left_sound :
    ∀ e e' : Expr α, rule_distrib_left e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_distrib_left] at h
  | var _ => simp [rule_distrib_left] at h
  | add _ _ => simp [rule_distrib_left] at h
  | mul e1 (add b c) =>
    simp only [rule_distrib_left, Option.some.injEq] at h
    subst h
    simp only [denote, left_distrib]
  | mul _ (const _) => simp [rule_distrib_left] at h
  | mul _ (var _) => simp [rule_distrib_left] at h
  | mul _ (mul _ _) => simp [rule_distrib_left] at h

omit [DecidableEq α] in
/-- Corrección de la distributividad derecha: (a + b) * c → a*c + b*c -/
theorem rule_distrib_right_sound :
    ∀ e e' : Expr α, rule_distrib_right e = some e' →
    denote env e = denote env e' := by
  intro e e' h
  match e with
  | const _ => simp [rule_distrib_right] at h
  | var _ => simp [rule_distrib_right] at h
  | add _ _ => simp [rule_distrib_right] at h
  | mul (add a b) e2 =>
    simp only [rule_distrib_right, Option.some.injEq] at h
    subst h
    simp only [denote, right_distrib]
  | mul (const _) _ => simp [rule_distrib_right] at h
  | mul (var _) _ => simp [rule_distrib_right] at h
  | mul (mul _ _) _ => simp [rule_distrib_right] at h

end RuleProofs

/-! ## Parte 4: Teorema Principal de Corrección -/

/-- Lema auxiliar: applyFirst preserva semántica si todas las reglas lo hacen -/
lemma applyFirst_sound {α : Type} [Add α] [Mul α]
    (rules : List (RewriteRule α)) (env : VarId → α)
    (h_rules_sound : ∀ rule ∈ rules, ∀ e e', rule e = some e' → denote env e = denote env e')
    (e e' : Expr α) (h : applyFirst rules e = some e') :
    denote env e = denote env e' := by
  induction rules with
  | nil => simp [applyFirst, List.findSome?] at h
  | cons rule rest ih =>
    simp only [applyFirst, List.findSome?] at h
    cases hr : rule e with
    | none =>
      simp only [hr, Option.none_orElse] at h
      exact ih (fun r hr' => h_rules_sound r (List.mem_cons_of_mem _ hr')) h
    | some result =>
      simp only [hr, Option.some_orElse, Option.some.injEq] at h
      rw [← h]
      exact h_rules_sound rule (List.mem_cons_self _ _) e result hr

/-- Lema auxiliar: rewriteAtRoot preserva semántica -/
lemma rewriteAtRoot_sound {α : Type} [Add α] [Mul α]
    (rules : List (RewriteRule α)) (env : VarId → α)
    (h_rules_sound : ∀ rule ∈ rules, ∀ e e', rule e = some e' → denote env e = denote env e')
    (e : Expr α) :
    denote env (rewriteAtRoot rules e) = denote env e := by
  simp only [rewriteAtRoot]
  cases h : applyFirst rules e with
  | none => rfl
  | some e' =>
    exact (applyFirst_sound rules env h_rules_sound e e' h).symm

/--
La reescritura bottom-up preserva la semántica.
NOTA: Esta prueba requiere inducción bien fundada sobre Expr.
La versión actual usa sorry porque rewriteBottomUp está definida como `partial`.
Para una prueba completa, necesitaríamos redefinir rewriteBottomUp usando
recursión bien fundada (por ejemplo, basada en el tamaño de la expresión).
-/
theorem rewriteBottomUp_sound {α : Type} [Add α] [Mul α]
    (rules : List (RewriteRule α)) (env : VarId → α)
    (h_rules_sound : ∀ rule ∈ rules, ∀ e e', rule e = some e' → denote env e = denote env e')
    (e : Expr α) :
    denote env (rewriteBottomUp rules e) = denote env e := by
  sorry -- Requiere redefinir rewriteBottomUp sin `partial` para permitir inducción

/--
La simplificación preserva la semántica.
NOTA: Depende de rewriteBottomUp_sound, que requiere redefinición sin `partial`.
-/
theorem simplify_sound {α : Type} [Semiring α] [DecidableEq α] [BEq (Expr α)]
    (env : VarId → α)
    (e : Expr α) (fuel : Nat) :
    denote env (simplify e fuel) = denote env e := by
  sorry -- Depende de rewriteBottomUp_sound y rewriteToFixpoint_sound

end AmoLean
