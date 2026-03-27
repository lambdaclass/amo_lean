/-
  AMO-Lean — Non-Vacuity Witness for dit_bottomUp_eq_ntt_spec

  Demonstrates that the hypotheses of the DIT NTT correctness theorem
  are jointly satisfiable. Uses Rat (rationals) as the field — computable
  and has Mathlib's Field instance.

  Strategy: logN=1 (N=2, single butterfly), omega = -1 (primitive 2nd root).
  Axiom census: 0 custom axioms, 0 sorry.
-/
import AmoLean.NTT.StageSimulation

namespace Tests.NonVacuity.NTTDIT

open AmoLean.NTT.StageSimulation
open AmoLean.NTT (IsPrimitiveRoot)

/-- -1 is a primitive 2nd root of unity over the rationals. -/
private theorem neg_one_primitive_root_2 : IsPrimitiveRoot (-1 : Rat) 2 where
  pow_eq_one := by norm_num
  pow_ne_one_of_lt := by
    intro k hk hk2
    interval_cases k
    norm_num

/-- Non-vacuity: the core hypotheses of dit_bottomUp_eq_ntt_spec are jointly satisfiable.
    Witnesses: F = Rat, logN = 1 (N=2), omega = -1, data = [1, 2]. -/
example : ∃ (F : Type) (_ : Field F) (_ : DecidableEq F) (_ : Inhabited F)
    (data : List F) (omega : F) (logN : Nat),
    data.length = 2 ^ logN ∧
    IsPrimitiveRoot omega (2 ^ logN) ∧
    logN > 0 :=
  ⟨Rat, inferInstance, inferInstance, inferInstance,
   [1, 2], -1, 1,
   by simp,
   by simpa using neg_one_primitive_root_2,
   by omega⟩

end Tests.NonVacuity.NTTDIT
