import AmoLean.Spec
open AmoLean.Spec

def spec : Spec := kron (Spec.identity 4) (dft 2)
