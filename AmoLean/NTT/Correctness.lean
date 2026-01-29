/-
  AMO-Lean: NTT Correctness Proofs
  Phase 5: NTT Core - Task 3.2

  This module proves that NTT_recursive computes the same result as NTT_spec.
  This is the central correctness theorem for the Cooley-Tukey implementation.

  Main Theorem:
    ct_recursive_eq_spec: NTT_recursive ω input = NTT_spec ω input

  Proof Strategy:
  1. Show base case (N=1): Both return the single element
  2. Show inductive case: The butterfly combination produces correct coefficients
  3. Use the Cooley-Tukey recurrence relation to link recursive and spec definitions
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Spec
import AmoLean.NTT.CooleyTukey
import AmoLean.NTT.Goldilocks
import AmoLean.NTT.Properties

namespace AmoLean.NTT

/-! ## Part 1: Base Case -/

section BaseCase

-- Use only NTTFieldLawful to avoid instance diamond with NTTField
variable {F : Type*} [NTTFieldLawful F]

/-- Base case: NTT_recursive of a single element is just that element -/
theorem ntt_recursive_singleton (ω : F) (x : F) :
    NTT_recursive ω [x] = [x] := by
  unfold NTT_recursive
  simp only [List.length_singleton, ↓reduceDIte, decide_true]

/-- Base case equality: Both NTT implementations agree on singletons

    The proof uses: ω^0 = 1, x * 1 = x, 0 + x = x
-/
theorem ntt_eq_singleton (ω : F) (x : F) :
    NTT_recursive ω [x] = NTT_spec ω [x] := by
  rw [ntt_recursive_singleton]
  rw [NTT_spec_singleton]
  -- Goal: [x] = [0 + x * (pow ω 0)]
  congr 1
  -- After pow_zero: x = 0 + x * 1
  rw [NTTFieldLawful.pow_zero]
  -- Goal: x = Add.add Zero.zero (Mul.mul x 1)
  -- Convert to notation and use axioms
  show x = (0 : F) + x * 1
  rw [NTTFieldLawful.mul_one, NTTFieldLawful.zero_add]

end BaseCase

/-! ## Part 2: Cooley-Tukey Recurrence -/

section CTRecurrence

variable {F : Type*} [inst : NTTField F] [CommRing F] [IsDomain F]

/-- The Cooley-Tukey recurrence: X_k = E_k + ω^k · O_k for k < n/2

    Where:
    - X_k is the k-th NTT coefficient of the full input
    - E_k is the k-th NTT coefficient of even-indexed elements (with ω²)
    - O_k is the k-th NTT coefficient of odd-indexed elements (with ω²)
-/
theorem cooley_tukey_upper_half {n : ℕ} (hn : n > 0) (hn_even : 2 ∣ n)
    (ω : F) (hω : IsPrimitiveRoot ω n)
    (input : List F) (h_len : input.length = n)
    (E O : List F) (hE : E = NTT_spec (inst.pow ω 2) (evens input))
    (hO : O = NTT_spec (inst.pow ω 2) (odds input))
    (k : ℕ) (hk : k < n / 2) :
    -- X_k = E_k + ω^k · O_k
    (NTT_spec ω input)[k]? =
    some (inst.add (E[k]?.getD inst.zero) (inst.mul (inst.pow ω k) (O[k]?.getD inst.zero))) := by
  sorry -- The detailed proof uses the DFT splitting formula

/-- The Cooley-Tukey recurrence for lower half: X_{k+n/2} = E_k - ω^k · O_k

    Uses the fact that ω^(n/2) = -1 for primitive roots
-/
theorem cooley_tukey_lower_half {n : ℕ} (hn : n > 2) (hn_even : 2 ∣ n)
    (ω : F) (hω : IsPrimitiveRoot ω n)
    (input : List F) (h_len : input.length = n)
    (E O : List F) (hE : E = NTT_spec (inst.pow ω 2) (evens input))
    (hO : O = NTT_spec (inst.pow ω 2) (odds input))
    (k : ℕ) (hk : k < n / 2) :
    -- X_{k+n/2} = E_k - ω^k · O_k
    (NTT_spec ω input)[k + n/2]? =
    some (inst.sub (E[k]?.getD inst.zero) (inst.mul (inst.pow ω k) (O[k]?.getD inst.zero))) := by
  sorry -- Uses ω^(n/2) = -1 property

end CTRecurrence

/-! ## Part 3: Main Correctness Theorem -/

section MainTheorem

variable {F : Type*} [inst : NTTField F]

/-- Helper: The recursive NTT produces a list of the correct length
    Note: This only holds for power-of-2 lengths; see NTT_recursive_length in CooleyTukey.lean -/
theorem ntt_recursive_length_eq (ω : F) (input : List F)
    (hpow2 : ∃ k : ℕ, input.length = 2^k) :
    (NTT_recursive ω input).length = input.length :=
  NTT_recursive_length ω input hpow2

/-- The central correctness theorem: NTT_recursive computes NTT_spec

    This theorem establishes that our O(n log n) Cooley-Tukey implementation
    produces identical results to the O(n²) specification.
-/
theorem ct_recursive_eq_spec (ω : F) (input : List F)
    (h_pow2 : ∃ k : ℕ, input.length = 2^k) :
    NTT_recursive ω input = NTT_spec ω input := by
  sorry -- Main proof by strong induction on input.length

/-- Corollary: NTT roundtrip works for recursive version

    The parameter n_as_field represents the length as a field element,
    constructed appropriately for the NTTField.
-/
theorem ntt_intt_recursive_roundtrip (ω n_inv : F) (input : List F)
    (h_pow2 : ∃ k : ℕ, input.length = 2^k)
    (n_as_field : F)
    (h_inv : inst.mul n_inv n_as_field = inst.one) :
    INTT_recursive ω n_inv (NTT_recursive ω input) = input := by
  -- By correctness, NTT_recursive = NTT_spec
  have h_ntt := ct_recursive_eq_spec ω input h_pow2
  rw [h_ntt]
  -- Now we need to show INTT_recursive(NTT_spec(...)) = input
  -- This follows from INTT_recursive = INTT_spec and the spec roundtrip
  sorry -- Uses INTT correctness

end MainTheorem

/-! ## Part 4: Testing Consistency -/

section TestConsistency

open AmoLean.Field.Goldilocks

/-- Compile-time verification for small sizes -/
example : NTT_recursive (primitiveRoot 4 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] =
          NTT_spec (primitiveRoot 4 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩] := by
  native_decide

example : NTT_recursive (primitiveRoot 8 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩] =
          NTT_spec (primitiveRoot 8 (by decide)) [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩] := by
  native_decide

end TestConsistency

end AmoLean.NTT
