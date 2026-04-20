import AmoLean.Spec
open AmoLean.Spec

-- Apply independent butterflies to 3 adjacent pairs of elements.
-- Input:  [a, b, c, d, e, f]
-- Output: [a+b, a-b, c+d, c-d, e+f, e-f]
def spec : Spec := kron (Spec.identity 3) (dft 2)
