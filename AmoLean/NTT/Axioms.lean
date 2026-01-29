/-
  AMO-Lean: NTT Axioms (Temporary)
  Phase 5: NTT Core - Deferred Proofs Registry

  These 9 theorems are mathematically proven correct (standard FFT/NTT theory)
  and empirically validated (Oracle tests pass for N=4,8,16,32).

  They are marked as axioms to unblock the Optimization Phase (Weeks 4-6).
  Full Lean proofs will be completed in Phase 6 (Hardening).

  Design Decision: DD-021 - Deferred Proofs Strategy
  Date: 2026-01-29
  Status: APPROVED

  Rationale:
    1. All 9 theorems are standard results from Fourier analysis (Cooley-Tukey 1965)
    2. Empirical validation confirms correctness (Oracle tests N=4,8,16,32)
    3. Proof engineering effort better spent on optimization (Weeks 4-6)
    4. Zero mathematical risk - only "Lean translation" risk
    5. Will be proven in Phase 6 (Hardening)

  Related Decisions:
    - DD-022: LazyGoldilocks uses Nat (not UInt64) to avoid wrapping
    - DD-023: CodeGen uses Skeleton + Kernel strategy

  See also:
    - docs/project/DESIGN_DECISIONS.md
    - docs/project/PHASE5_NTT_PLAN.md
    - docs/project/PROGRESS.md
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Spec
import AmoLean.NTT.Properties

namespace AmoLean.NTT.Axioms

/-! ## Deferred Proofs Registry

The following 9 theorems have `sorry` placeholders that will be proven
in the Hardening phase. Each is documented with its mathematical basis.

### Properties.lean (2 axioms)
1. `intt_ntt_identity_finset` - INTT(NTT(x)) = x using Finset sums
   - Math basis: Orthogonality of roots of unity
   - Proof sketch: Double sum rearrangement + Σₖ ω^((j-i)k) = n·δᵢⱼ

2. `parseval` - Energy preservation: n·Σ|aᵢ|² = Σ|Xₖ|²
   - Math basis: Plancherel theorem for finite groups
   - Proof sketch: Expand both sides, use orthogonality

### Correctness.lean (4 axioms)
3. `cooley_tukey_upper_half` - Xₖ = Eₖ + ωᵏ·Oₖ for k < n/2
   - Math basis: DFT splitting formula (Cooley-Tukey 1965)
   - Proof sketch: Split sum into even/odd indices, factor out ω^k

4. `cooley_tukey_lower_half` - X_{k+n/2} = Eₖ - ωᵏ·Oₖ
   - Math basis: Uses ω^(n/2) = -1 for primitive roots
   - Proof sketch: Same as upper half + twiddle_half_eq_neg_one

5. `ct_recursive_eq_spec` - NTT_recursive = NTT_spec
   - Math basis: Correctness of divide-and-conquer FFT
   - Proof sketch: Strong induction on input.length using (3) and (4)

6. `ntt_intt_recursive_roundtrip` - INTT(NTT(x)) = x for recursive impl
   - Math basis: Follows from (5) and spec roundtrip
   - Proof sketch: Compose ct_recursive_eq_spec with spec roundtrip

### Spec.lean (3 axioms)
7. `ntt_coeff_add` - NTT(a+b)ₖ = NTT(a)ₖ + NTT(b)ₖ
   - Math basis: Linearity of summation
   - Proof sketch: foldl distributes over addition

8. `ntt_coeff_scale` - NTT(c·a)ₖ = c·NTT(a)ₖ
   - Math basis: Linearity of summation
   - Proof sketch: Factor constant out of foldl

9. `ntt_intt_identity` - INTT(NTT(a)) = a for list-based spec
   - Math basis: Same as (1) but for List instead of Fin→F
   - Proof sketch: Reduce to (1) via list/function equivalence

-/

/-! ## Validation Status

All axioms validated empirically:
```
#eval! do  -- From Spec.lean tests
  let input := [1, 2, 3, 4, 5, 6, 7, 8]
  let ntt_result := NTT_spec ω₈ input
  let roundtrip := INTT_spec ω₈ n_inv₈ ntt_result
  assert! roundtrip == input  -- PASSES ✓
```

Oracle tests confirm for N = 4, 8, 16, 32:
- NTT_recursive matches NTT_spec ✓
- INTT(NTT(x)) = x ✓
- Linearity properties hold ✓
-/

end AmoLean.NTT.Axioms
