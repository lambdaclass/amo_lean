/-
  AMO-Lean Toy Model - Pruebas de Corrección
  
  Este archivo contiene las pruebas de que las reglas de reescritura
  preservan la semántica de las expresiones.
  
  Aquí es donde conectamos con las propiedades algebraicas que
  eventualmente vendrán de Mathlib.
-/

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
    (h_sound : ∀ x y, rule x = some y → ⟦x⟧ env = ⟦y⟧ env) :
    ⟦e⟧ env = ⟦e'⟧ env := 
  h_sound e e' h

/-! ## Parte 2: Pruebas para Reglas Individuales -/

section RuleProofs

variable {α : Type} [Add α] [Mul α] [BEq α] [OfNat α 0] [OfNat α 1]
variable (env : VarId → α)

/-- Corrección de e + 0 → e (requiere que 0 sea identidad aditiva) -/
theorem rule_add_zero_right_sound [LawfulBEq α] 
    (h_add_zero : ∀ a : α, a + 0 = a) :
    ∀ e e' : Expr α, rule_add_zero_right e = some e' → 
    ⟦e⟧ env = ⟦e'⟧ env := by
  intro e e' h
  match e with
  | const _ => simp [rule_add_zero_right] at h
  | var _ => simp [rule_add_zero_right] at h
  | mul _ _ => simp [rule_add_zero_right] at h
  | add e1 e2 =>
    simp [rule_add_zero_right] at h
    split at h
    · rename_i c heq
      simp at h
      split at h
      · simp at h
        cases h
        simp [denote, h_add_zero]
        -- Aquí usaríamos que c == 0 implica c = 0
        sorry -- Requiere más lemas sobre BEq
      · contradiction
    · contradiction

/-- Corrección de 0 + e → e -/
theorem rule_add_zero_left_sound [LawfulBEq α]
    (h_zero_add : ∀ a : α, 0 + a = a) :
    ∀ e e' : Expr α, rule_add_zero_left e = some e' → 
    ⟦e⟧ env = ⟦e'⟧ env := by
  intro e e' h
  match e with
  | const _ => simp [rule_add_zero_left] at h
  | var _ => simp [rule_add_zero_left] at h  
  | mul _ _ => simp [rule_add_zero_left] at h
  | add e1 e2 =>
    simp [rule_add_zero_left] at h
    split at h
    · rename_i c heq
      simp at h
      split at h
      · simp at h
        cases h
        simp [denote, h_zero_add]
        sorry -- Requiere más lemas
      · contradiction
    · contradiction

/-- Corrección de e * 0 → 0 -/
theorem rule_mul_zero_right_sound [LawfulBEq α]
    (h_mul_zero : ∀ a : α, a * 0 = 0) :
    ∀ e e' : Expr α, rule_mul_zero_right e = some e' → 
    ⟦e⟧ env = ⟦e'⟧ env := by
  intro e e' h
  match e with
  | const _ => simp [rule_mul_zero_right] at h
  | var _ => simp [rule_mul_zero_right] at h
  | add _ _ => simp [rule_mul_zero_right] at h
  | mul e1 e2 =>
    simp [rule_mul_zero_right] at h
    split at h
    · rename_i c heq
      simp at h
      split at h
      · simp at h
        cases h
        simp [denote, h_mul_zero]
        sorry
      · contradiction
    · contradiction

/-- Corrección de la distributividad: a * (b + c) → a*b + a*c -/
theorem rule_distrib_left_sound 
    (h_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c) :
    ∀ e e' : Expr α, rule_distrib_left e = some e' → 
    ⟦e⟧ env = ⟦e'⟧ env := by
  intro e e' h
  match e with
  | const _ => simp [rule_distrib_left] at h
  | var _ => simp [rule_distrib_left] at h
  | add _ _ => simp [rule_distrib_left] at h
  | mul e1 e2 =>
    match e2 with
    | add b c =>
      simp [rule_distrib_left] at h
      cases h
      simp [denote, h_distrib]
    | _ => simp [rule_distrib_left] at h

/-- Corrección de la distributividad derecha: (a + b) * c → a*c + b*c -/
theorem rule_distrib_right_sound
    (h_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c) :
    ∀ e e' : Expr α, rule_distrib_right e = some e' → 
    ⟦e⟧ env = ⟦e'⟧ env := by
  intro e e' h
  match e with
  | const _ => simp [rule_distrib_right] at h
  | var _ => simp [rule_distrib_right] at h
  | add _ _ => simp [rule_distrib_right] at h
  | mul e1 e2 =>
    match e1 with
    | add a b =>
      simp [rule_distrib_right] at h
      cases h
      simp [denote, h_distrib]
    | _ => simp [rule_distrib_right] at h

end RuleProofs

/-! ## Parte 3: Teorema Principal de Corrección -/

/-- 
La reescritura bottom-up preserva la semántica.
Este es el teorema que necesitamos para garantizar corrección del optimizador.
-/
theorem rewriteBottomUp_sound {α : Type} [Add α] [Mul α]
    (rules : List (RewriteRule α)) (env : VarId → α)
    (h_rules_sound : ∀ rule ∈ rules, ∀ e e', rule e = some e' → ⟦e⟧ env = ⟦e'⟧ env)
    (e : Expr α) :
    ⟦rewriteBottomUp rules e⟧ env = ⟦e⟧ env := by
  -- La prueba procede por inducción estructural sobre e
  -- Cada caso usa la hipótesis de que las reglas son sound
  sorry -- Requiere inducción bien fundada

/-- La simplificación preserva la semántica -/
theorem simplify_sound {α : Type} [Add α] [Mul α] [BEq α] [BEq (Expr α)]
    [OfNat α 0] [OfNat α 1]
    (env : VarId → α)
    (h_ring : ∀ a : α, a + 0 = a ∧ 0 + a = a ∧ 
                        a * 1 = a ∧ 1 * a = a ∧
                        a * 0 = 0 ∧ 0 * a = 0)
    (e : Expr α) (fuel : Nat) :
    ⟦simplify e fuel⟧ env = ⟦e⟧ env := by
  sorry -- Requiere las pruebas de las reglas individuales + teorema de punto fijo

end AmoLean
