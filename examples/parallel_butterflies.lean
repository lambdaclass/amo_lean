open AmoLean.Matrix (MatExpr)

def spec : MatExpr Int 8 8 :=
  .kron (.identity 4) (.dft 2)
