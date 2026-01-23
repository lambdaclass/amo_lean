/-
  AMO-Lean - Integración con Mathlib

  Este archivo conecta nuestro Expr con las estructuras
  algebraicas de Mathlib, permitiendo usar teoremas reales
  como reglas de reescritura.
-/

import AmoLean.Basic
import AmoLean.Correctness
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
    sound := fun env => rule_add_zero_right_sound env
  },
  {
    name := "zero_add"
    rule := rule_add_zero_left
    sound := fun env => rule_add_zero_left_sound env
  },
  {
    name := "mul_one"
    rule := rule_mul_one_right
    sound := fun env => rule_mul_one_right_sound env
  },
  {
    name := "one_mul"
    rule := rule_mul_one_left
    sound := fun env => rule_mul_one_left_sound env
  },
  {
    name := "mul_zero"
    rule := rule_mul_zero_right
    sound := fun env => rule_mul_zero_right_sound env
  },
  {
    name := "zero_mul"
    rule := rule_mul_zero_left
    sound := fun env => rule_mul_zero_left_sound env
  },
  {
    name := "left_distrib"
    rule := rule_distrib_left
    sound := fun env => rule_distrib_left_sound env
  },
  {
    name := "right_distrib"
    rule := rule_distrib_right
    sound := fun env => rule_distrib_right_sound env
  }
]

/-! ## Uso con tipos concretos de Mathlib -/

-- Los ejemplos se habilitarán cuando las pruebas estén completas
-- #check (semiring_rules Int : List (VerifiedRule Int))
-- #check (semiring_rules ℚ : List (VerifiedRule ℚ))

end AmoLean
