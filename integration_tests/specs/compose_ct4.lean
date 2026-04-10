import AmoLean.Spec
open AmoLean.Spec
-- Cooley-Tukey DFT-4 = (DFT_2 ⊗ I_2) · (I_2 ⊗ DFT_2)
-- Should produce the same result as dft 4
def spec : Spec :=
  compose (kron (dft 2) (Spec.identity 2)) (kron (Spec.identity 2) (dft 2))
