open AmoLean.Matrix (MatExpr)

def spec : MatExpr Int 4 4 :=
  let dft2 : MatExpr Int 2 2 := .dft 2
  let i2 : MatExpr Int 2 2 := .identity 2
  .compose (.kron dft2 i2) (.kron i2 dft2)
