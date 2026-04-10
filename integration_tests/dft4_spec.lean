open AmoLean.Matrix (MatExpr)

-- DFT_4: the 4-point Walsh-Hadamard Transform
-- This is the same kernel that FullPipeline.lean generates,
-- but expressed as a standalone spec for the trzk compiler driver.
def spec : MatExpr Int 4 4 := .dft 4
