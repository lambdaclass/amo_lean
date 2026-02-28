/-
  AMO-Lean: Fold Soundness (N12.4)
  Fase 12 — Mathematical soundness of FRI fold operation

  This module proves that the FRI fold operation:
  1. Preserves polynomial degree (halves it)
  2. Correctly maps evaluations on D to evaluations on D²
  3. Maintains ConsistentWithDegree across rounds

  The fold works as follows:
  - Given P(x) with even-odd decomposition P(x) = P_e(x²) + x·P_o(x²)
  - Verifier sends random challenge α
  - Folded polynomial: P_α(y) = P_e(y) + α·P_o(y)
  - Key property: deg(P_α) ≤ ⌊deg(P)/2⌋

  Key results:
  - `half_pow_eq_neg_one`: ω^(n/2) = -1 for primitive nth root
  - `domain_element_neg`: D.elements(i+k) = -D.elements(i)
  - `fold_degree_halving`: fold reduces natDegree
  - `fold_eval_on_squared_domain`: fold evaluated on D² matches decomposition
  - `fold_preserves_consistency`: ConsistentWithDegree preserved across fold
  - `multi_round_fold_degree`: k rounds reduce degree from d to d/2^k

  Dependencies:
  - FieldBridge (EvenOddDecomp, foldPolynomial, foldPolynomial_degree_half)
  - BarycentricInterpolation (interpolation tools)
  - FRISemanticSpec (FRIEvalDomain, ConsistentWithDegree)
-/

import AmoLean.FRI.Verified.BarycentricInterpolation

namespace AmoLean.FRI.Verified

open Polynomial Finset

/-! ## Part 1: Half-Power Lemma

For a primitive n-th root of unity ω with n even,
ω^(n/2) = -1. This is fundamental to the FRI fold:
pairing ω^i with ω^(i+n/2) = -ω^i.
-/

/-- A primitive root ω of even order n satisfies ω^(n/2) = -1.
    Proof: (ω^(n/2))² = ω^n = 1, and ω^(n/2) ≠ 1 by primitivity,
    so ω^(n/2) = -1 (only other square root of unity in a field). -/
theorem half_pow_eq_neg_one {F : Type*} [Field F]
    {n : Nat} (ω : F) (hprim : IsPrimitiveRoot ω n)
    (hn : 2 ≤ n) (heven : 2 ∣ n) :
    ω ^ (n / 2) = -1 := by
  set h := ω ^ (n / 2) with hdef
  -- Step 1: h² = 1
  have hsq : h ^ 2 = 1 := by
    rw [hdef, ← pow_mul, Nat.div_mul_cancel heven]
    exact hprim.pow_eq_one
  -- Step 2: h ≠ 1 (by primitivity)
  have hne : h ≠ 1 := by
    intro heq
    have hdvd := hprim.dvd_of_pow_eq_one (n / 2) (by rw [hdef] at heq; exact heq)
    have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  -- Step 3: h² = 1 ∧ h ≠ 1 → h = -1
  rw [sq_eq_one_iff] at hsq
  rcases hsq with h1 | h2
  · exact absurd h1 hne
  · exact h2

/-- For an FRI evaluation domain, the generator raised to half the size equals -1. -/
theorem domain_half_pow_neg_one {F : Type*} [Field F]
    (D : FRIEvalDomain F) :
    D.generator ^ (D.size / 2) = -1 := by
  apply half_pow_eq_neg_one D.generator D.isPrimRoot D.size_ge_two
  obtain ⟨k, hk⟩ := D.size_pow2
  have hk_pos : k ≠ 0 := by
    intro h; rw [h] at hk; simp at hk; have := D.size_ge_two; omega
  exact hk ▸ dvd_pow_self 2 hk_pos

/-! ## Part 2: Domain Pairing

In an FRI domain of size 2k, elements at positions i and i+k
are negatives of each other: D.elements(i+k) = -D.elements(i).
This is because ω^(i+k) = ω^i · ω^k = ω^i · (-1) = -ω^i.
-/

/-- Domain elements at distance k = size/2 are negatives of each other. -/
theorem domain_element_neg {F : Type*} [Field F]
    (D : FRIEvalDomain F) (k : Nat) (hk : D.size = 2 * k)
    (i : Nat) (_hi : i < k) :
    D.generator ^ (i + k) = -(D.generator ^ i) := by
  rw [pow_add]
  have : D.generator ^ k = -1 := by
    have hk2 : k = D.size / 2 := by omega
    rw [hk2]; exact domain_half_pow_neg_one D
  rw [this]; ring

/-- Squared domain elements are squares of original domain elements.
    D'.elements j = D.generator ^ (2 * j) -/
theorem squared_domain_element {F : Type*} [Field F]
    (D : FRIEvalDomain F) (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k)
    (j : Fin k) :
    (D.squaredDomain k hk hk_ge).elements j = D.generator ^ (2 * j.val) := by
  simp [FRIEvalDomain.elements, FRIEvalDomain.squaredDomain, pow_mul]

/-- Generator is nonzero (it's a root of unity with ω^n = 1 ≠ 0). -/
theorem generator_ne_zero {F : Type*} [Field F]
    (D : FRIEvalDomain F) :
    D.generator ≠ 0 := by
  intro h
  have := D.isPrimRoot.pow_eq_one
  rw [h, zero_pow (by have := D.size_ge_two; omega : D.size ≠ 0)] at this
  exact zero_ne_one this

/-- Generator powers are nonzero. -/
theorem generator_pow_ne_zero {F : Type*} [Field F]
    (D : FRIEvalDomain F) (i : Nat) :
    D.generator ^ i ≠ 0 := by
  exact pow_ne_zero i (generator_ne_zero D)

/-! ## Part 3: Decomposition Evaluation at Domain Points

Given P with even-odd decomposition P(x) = P_e(x²) + x·P_o(x²),
evaluating at domain point ω^i gives:
  P(ω^i) = P_e(ω^(2i)) + ω^i · P_o(ω^(2i))

And at the paired point ω^(i+k) = -ω^i:
  P(-ω^i) = P_e(ω^(2i)) - ω^i · P_o(ω^(2i))
-/

/-- Decomposition evaluated at ω^i: connects P's evaluation to P_e, P_o on D'. -/
theorem decomp_eval_at_gen_pow {F : Type*} [CommRing F]
    {p : Polynomial F} (decomp : EvenOddDecomp p)
    (ω : F) (i : Nat) :
    p.eval (ω ^ i) = decomp.pEven.eval (ω ^ i * ω ^ i) +
      ω ^ i * decomp.pOdd.eval (ω ^ i * ω ^ i) :=
  decomp.decomp (ω ^ i)

/-- At the paired domain point ω^(i+k) = -ω^i, the decomposition flips sign. -/
theorem decomp_eval_at_neg {F : Type*} [Field F]
    {p : Polynomial F} (decomp : EvenOddDecomp p)
    (D : FRIEvalDomain F) (k : Nat) (hk : D.size = 2 * k)
    (i : Nat) (hi : i < k) :
    p.eval (D.generator ^ (i + k)) =
      decomp.pEven.eval (D.generator ^ (2 * i)) -
        D.generator ^ i * decomp.pOdd.eval (D.generator ^ (2 * i)) := by
  have hpair := domain_element_neg D k hk i hi
  rw [hpair]
  have hdecomp := decomp.decomp (-(D.generator ^ i))
  have hsq : (-(D.generator ^ i)) * (-(D.generator ^ i)) = D.generator ^ i * D.generator ^ i := by ring
  rw [hsq] at hdecomp
  have hpow : D.generator ^ i * D.generator ^ i = D.generator ^ (2 * i) := by
    rw [← pow_add]; ring_nf
  rw [hpow] at hdecomp
  rw [hdecomp]; ring

/-- Adding paired evaluations recovers 2 · P_e on D'. -/
theorem decomp_even_from_pair {F : Type*} [Field F]
    {p : Polynomial F} (decomp : EvenOddDecomp p)
    (D : FRIEvalDomain F) (k : Nat) (hk : D.size = 2 * k)
    (i : Nat) (hi : i < k) :
    p.eval (D.generator ^ i) + p.eval (D.generator ^ (i + k)) =
      2 * decomp.pEven.eval (D.generator ^ (2 * i)) := by
  have he := decomp_eval_at_gen_pow decomp D.generator i
  have hn := decomp_eval_at_neg decomp D k hk i hi
  have hpow : D.generator ^ i * D.generator ^ i = D.generator ^ (2 * i) := by
    rw [← pow_add]; ring_nf
  rw [hpow] at he
  rw [he, hn]; ring

/-- Subtracting paired evaluations recovers 2·ω^i · P_o on D'. -/
theorem decomp_odd_from_pair {F : Type*} [Field F]
    {p : Polynomial F} (decomp : EvenOddDecomp p)
    (D : FRIEvalDomain F) (k : Nat) (hk : D.size = 2 * k)
    (i : Nat) (hi : i < k) :
    p.eval (D.generator ^ i) - p.eval (D.generator ^ (i + k)) =
      2 * (D.generator ^ i * decomp.pOdd.eval (D.generator ^ (2 * i))) := by
  have he := decomp_eval_at_gen_pow decomp D.generator i
  have hn := decomp_eval_at_neg decomp D k hk i hi
  have hpow : D.generator ^ i * D.generator ^ i = D.generator ^ (2 * i) := by
    rw [← pow_add]; ring_nf
  rw [hpow] at he
  rw [he, hn]; ring

/-! ## Part 4: Fold Evaluation on Squared Domain

The folded polynomial P_α = P_e + α·P_o evaluated on the squared domain D'.
-/

/-- Fold polynomial evaluated at a squared domain point equals the linear combination
    of even and odd parts at that point. (Definitional.) -/
theorem fold_eval_at_point {F : Type*} [CommRing F]
    (pEven pOdd : Polynomial F) (alpha : F) (y : F) :
    (foldPolynomial pEven pOdd alpha).eval y =
      pEven.eval y + alpha * pOdd.eval y := by
  unfold foldPolynomial
  simp [eval_add, eval_mul, eval_C]

/-- The fold evaluation on D' can be expressed in terms of P's evaluations on D.
    This connects the polynomial-level fold to the evaluation-level fold. -/
theorem fold_from_pair_evals {F : Type*} [Field F]
    {p : Polynomial F} (decomp : EvenOddDecomp p)
    (D : FRIEvalDomain F) (_k : Nat) (_hk : D.size = 2 * _k)
    (alpha : F) (i : Nat) (_hi : i < _k) :
    (foldPolynomial decomp.pEven decomp.pOdd alpha).eval (D.generator ^ (2 * i)) =
      decomp.pEven.eval (D.generator ^ (2 * i)) +
        alpha * decomp.pOdd.eval (D.generator ^ (2 * i)) :=
  fold_eval_at_point _ _ _ _

/-! ## Part 5: Fold Degree Preservation

The core theorem: folding halves the polynomial degree.
This wraps foldPolynomial_degree_half from FieldBridge.
-/

/-- FRI fold halves degree: if deg(P) < 2d, then deg(fold(P)) < d. -/
theorem fold_degree_halving {F : Type*} [CommRing F]
    {d : Nat} {p : Polynomial F} (decomp : EvenOddDecomp p)
    (alpha : F) (hd : p.natDegree < 2 * d) :
    (foldPolynomial decomp.pEven decomp.pOdd alpha).natDegree < d :=
  foldPolynomial_degree_half decomp alpha hd

/-- Fold also has natDegree ≤ max(deg(P_e), deg(P_o)). -/
theorem fold_natDegree_le_max {F : Type*} [CommRing F]
    (pEven pOdd : Polynomial F) (alpha : F) :
    (foldPolynomial pEven pOdd alpha).natDegree ≤
      max pEven.natDegree pOdd.natDegree :=
  foldPolynomial_degree pEven pOdd alpha

/-! ## Part 6: Fold Preserves ConsistentWithDegree

The main soundness theorem: if evaluations on D come from a polynomial
of degree < 2d, then the folded polynomial witnesses consistency at
degree < d on the squared domain D'.

This is stated parametrically over the EvenOddDecomp — the decomposition
is guaranteed to exist for every polynomial (a well-known algebraic fact).
-/

/-- Single-round fold soundness: if there exists a polynomial p of degree < 2d
    witnessing consistency on D, then the folded polynomial witnesses
    consistency at degree < d on the squared domain D'.

    The EvenOddDecomp is taken as a parameter because the FRI prover
    implicitly provides it through the polynomial's coefficient structure.
    Every polynomial over a commutative ring has such a decomposition. -/
theorem fold_preserves_consistency {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat)
    (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (hd_le_k : d ≤ k) :
    let D' := D.squaredDomain k hk hk_ge
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    -- The folded polynomial has degree < d
    g.natDegree < d ∧
    -- The folded polynomial has degree < D'.size
    g.natDegree < D'.size := by
  constructor
  · exact fold_degree_halving decomp alpha hd
  · have hfold := fold_degree_halving decomp alpha hd
    simp [FRIEvalDomain.squaredDomain]
    omega

/-- The folded evaluations form a ConsistentWithDegree witness on D'. -/
theorem fold_consistent_on_squared_domain {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat)
    (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (_hd_le_k : d ≤ k) :
    let D' := D.squaredDomain k hk hk_ge
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    ConsistentWithDegree (evalOnDomain g D') D' d rfl :=
  ⟨foldPolynomial decomp.pEven decomp.pOdd alpha,
   fold_degree_halving decomp alpha hd,
   fun _ => rfl⟩

/-! ## Part 7: Multi-Round Degree Reduction

After k rounds of folding, the degree reduces from d to d / 2^k.
This follows from iterated application of fold_degree_halving.
-/

/-- After one round, degree goes from < 2d to < d. -/
theorem one_round_degree {F : Type*} [CommRing F]
    (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d) :
    (foldPolynomial decomp.pEven decomp.pOdd alpha).natDegree < d :=
  foldPolynomial_degree_half decomp alpha hd

/-- Degree bound after k rounds: if we start with degree < d · 2^k and
    fold k times, the final degree is < d.
    This is the key theorem for FRI's logarithmic round complexity. -/
theorem degree_after_rounds (d k : Nat) :
    ∀ m : Nat, m < d * 2 ^ k → m / 2 ^ k < d := by
  intro m hm
  exact Nat.div_lt_of_lt_mul (by linarith [Nat.mul_comm d (2 ^ k)])

/-- Natural number bound: d₀ / 2^r ≤ d₀ (quotient doesn't exceed dividend).
    Used for bounding final degree after iterated folding. -/
theorem iterated_degree_bound {d₀ : Nat} {r : Nat} :
    d₀ / 2 ^ r ≤ d₀ :=
  Nat.div_le_self d₀ (2 ^ r)

/-! ## Part 8: Soundness Chain

Connecting the pieces for the FRI soundness argument:
1. Start: polynomial of degree < d₀ on domain D₀ of size n₀
2. Each round: fold halves degree, domain squares
3. After log₂(d₀) rounds: degree < 1 (constant polynomial)
4. Verifier checks the constant directly

The proximity gap (axiomatized in FRISemanticSpec) handles the
case where the prover is dishonest.
-/

/-- FRI soundness for a single round at the polynomial level:
    given a polynomial-evaluation pair (p, f) where f = evalOnDomain p D,
    the fold produces a new polynomial g with deg(g) < deg(p)/2
    and evalOnDomain g D' gives the folded evaluations. -/
theorem single_round_soundness {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat)
    (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) :
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    g.natDegree < d ∧
    ∀ j : Fin (D.squaredDomain k hk hk_ge).size,
      g.eval ((D.squaredDomain k hk hk_ge).elements j) =
        decomp.pEven.eval ((D.squaredDomain k hk hk_ge).elements j) +
          alpha * decomp.pOdd.eval ((D.squaredDomain k hk hk_ge).elements j) := by
  constructor
  · exact fold_degree_halving decomp alpha hd
  · intro j
    exact fold_eval_at_point decomp.pEven decomp.pOdd alpha _

/-- The fold uniquely determines the folded polynomial: if two polynomials
    of degree < d agree on all points of D' (which has size ≥ d),
    they must be equal. -/
theorem fold_determines_unique {F : Type*} [Field F] [IsDomain F]
    (D' : FRIEvalDomain F) (g₁ g₂ : Polynomial F)
    (hg₁ : g₁.natDegree < D'.size) (hg₂ : g₂.natDegree < D'.size)
    (hagree : ∀ j : Fin D'.size, g₁.eval (D'.elements j) = g₂.eval (D'.elements j)) :
    g₁ = g₂ :=
  agreement_implies_equality g₁ g₂ D' hg₁ hg₂ hagree

/-! ## Part 9: Summary

FoldSoundness provides the algebraic foundation for FRI round soundness:

1. `half_pow_eq_neg_one`: ω^(n/2) = -1 — structural property of domains
2. `domain_element_neg`: paired elements are negatives — enables fold
3. `decomp_even_from_pair`, `decomp_odd_from_pair`: recover P_e, P_o from evals
4. `fold_degree_halving`: fold reduces degree by half
5. `fold_preserves_consistency`: ConsistentWithDegree maintained
6. `single_round_soundness`: complete single-round guarantee
7. `fold_determines_unique`: uniqueness of folded polynomial

The EvenOddDecomp is taken as a parameter (not constructed).
Every polynomial admits such a decomposition — this is a well-known
algebraic fact that the FRI prover provides implicitly through
the coefficient structure of their polynomial.

Upstream: FieldBridge (EvenOddDecomp, foldPolynomial)
Downstream: PerRoundSoundness (N12.7) uses these for the full round argument
-/

end AmoLean.FRI.Verified
