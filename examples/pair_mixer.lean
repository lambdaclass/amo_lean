open AmoLean.Matrix (MatExpr)

-- Apply independent butterflies to 3 adjacent pairs of elements.
-- Input:  [a, b, c, d, e, f]
-- Output: [a+b, a-b, c+d, c-d, e+f, e-f]
def spec : MatExpr Int 6 6 :=
  .kron (.identity 3) (.dft 2)
