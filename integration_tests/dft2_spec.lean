open AmoLean.Matrix (MatExpr)

-- DFT_2: the 2-point Walsh-Hadamard Transform (butterfly)
-- y0 = x0 + x1, y1 = x0 - x1.
def spec : MatExpr Int 2 2 := .dft 2
