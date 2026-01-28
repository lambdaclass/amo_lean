/-
  Generate FRI fold validation test file
-/

import AmoLean.FRI.Validation

open AmoLean.FRI.Validation

def main : IO Unit := do
  generateValidationFile "generated/fri_fold_validation.c"
