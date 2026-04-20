import AmoLean.Spec
open AmoLean.Spec
-- 3 independent butterflies on 6 elements
def spec : Spec := kron (Spec.identity 3) (dft 2)
