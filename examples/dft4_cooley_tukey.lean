import AmoLean.Spec
open AmoLean.Spec

def spec : Spec :=
  let dft2 := dft 2
  let i2 := Spec.identity 2
  compose (kron dft2 i2) (kron i2 dft2)
