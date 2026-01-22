/-
  AMO-Lean - Integración con Mathlib

  Este archivo conecta nuestro Expr con las estructuras
  algebraicas de Mathlib, permitiendo usar teoremas reales
  como reglas de reescritura.

  NOTA: Algunas pruebas usan `sorry` y serán completadas en iteraciones futuras.
-/

import AmoLean.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic

namespace AmoLean

open Expr

/-! ## Extracción de Reglas desde Estructuras Algebraicas -/

/--
Estructura que empaqueta una regla con su prueba de corrección.
Esto es análogo a los "compiled rules" del paper de Gross et al.
-/
structure VerifiedRule (α : Type) [Add α] [Mul α] where
  name : String
  rule : RewriteRule α
  sound : ∀ env : VarId → α, ∀ e e', rule e = some e' → denote env e = denote env e'

/-- Crear reglas verificadas desde un Semiring -/
def semiring_rules (α : Type) [Semiring α] [DecidableEq α] :
    List (VerifiedRule α) := [
  {
    name := "add_zero"
    rule := rule_add_zero_right
    sound := by intro env e e' h; sorry
  },
  {
    name := "zero_add"
    rule := rule_add_zero_left
    sound := by intro env e e' h; sorry
  },
  {
    name := "mul_one"
    rule := rule_mul_one_right
    sound := by intro env e e' h; sorry
  },
  {
    name := "one_mul"
    rule := rule_mul_one_left
    sound := by intro env e e' h; sorry
  },
  {
    name := "mul_zero"
    rule := rule_mul_zero_right
    sound := by intro env e e' h; sorry
  },
  {
    name := "zero_mul"
    rule := rule_mul_zero_left
    sound := by intro env e e' h; sorry
  },
  {
    name := "left_distrib"
    rule := rule_distrib_left
    sound := by intro env e e' h; sorry
  },
  {
    name := "right_distrib"
    rule := rule_distrib_right
    sound := by intro env e e' h; sorry
  }
]

/-! ## Uso con tipos concretos de Mathlib -/

-- Los ejemplos se habilitarán cuando las pruebas estén completas
-- #check (semiring_rules Int : List (VerifiedRule Int))
-- #check (semiring_rules ℚ : List (VerifiedRule ℚ))

end AmoLean
