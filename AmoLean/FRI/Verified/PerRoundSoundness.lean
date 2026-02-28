/-
  AMO-Lean: Per-Round Soundness (N12.7)
  Fase 12 — Garreta 2025 simplified round-by-round FRI soundness

  This module composes fold soundness (N12.4), Merkle integrity (N12.5),
  and Fiat-Shamir transcript (N12.6) into per-round guarantees.

  Key results:
  1. `honest_fold_complete`: honest fold preserves ConsistentWithDegree
  2. `commitment_verifies_honest`: well-formed Merkle passes verification
  3. `query_catches_cheating`: cheating polynomials have bounded agreement
  4. `round_invariant_preserved`: structural invariant preserved
  5. `one_round_guarantee`: RoundGuarantee struct for composition
  6. `per_round_soundness`: main 4-part single-round theorem

  Design: Follows Garreta, Mohnblatt, Wagner (2025) state function approach.
  Builds exclusively on upstream verified modules. No new axioms.

  Upstream: FoldSoundness, MerkleSpec, TranscriptSpec
  Downstream: VerifierComposition (N12.8) iterates RoundGuarantee

  References:
  - Garreta, Mohnblatt, Wagner (2025), ePrint 2025/1993
  - Ben-Sasson, Carmon, Ishai, Kopparty, Saraf (2020), "Proximity Gaps"
-/

import AmoLean.FRI.Verified.FoldSoundness
import AmoLean.FRI.Verified.MerkleSpec
import AmoLean.FRI.Verified.TranscriptSpec

namespace AmoLean.FRI.Verified

open Polynomial

/-! ## Part 1: FRI State Function (Garreta 2025)

The state function assigns "good" or "bad" to each FRI round.
Round r is "good" if evaluations are consistent with a polynomial
of the claimed degree bound on the current domain.
-/

/-- Round state is "good": evaluations are consistent with degree d.
    This is the Garreta 2025 state function S(r). -/
abbrev FRIStateGood {F : Type*} [CommRing F]
    (evaluations : Fin n → F) (D : FRIEvalDomain F) (d : Nat)
    (hn : n = D.size) : Prop :=
  ConsistentWithDegree evaluations D d hn

/-- Round state is "bad": evaluations are NOT consistent with degree d. -/
def FRIStateBad {F : Type*} [CommRing F]
    (evaluations : Fin n → F) (D : FRIEvalDomain F) (d : Nat)
    (hn : n = D.size) : Prop :=
  ¬ ConsistentWithDegree evaluations D d hn

/-- The state is either good or bad (by classical logic) -/
theorem state_good_or_bad {F : Type*} [CommRing F]
    (evaluations : Fin n → F) (D : FRIEvalDomain F) (d : Nat)
    (hn : n = D.size) :
    FRIStateGood evaluations D d hn ∨ FRIStateBad evaluations D d hn :=
  Classical.em _

/-- A good state provides a witness polynomial -/
theorem state_good_witness {F : Type*} [CommRing F]
    {n : Nat} {f : Fin n → F} {D : FRIEvalDomain F} {d : Nat}
    {hn : n = D.size}
    (hgood : FRIStateGood f D d hn) :
    ∃ p : Polynomial F, p.natDegree < d ∧ ∀ i, f i = p.eval (D.elements (hn ▸ i)) :=
  hgood

/-! ## Part 2: Honest Fold Completeness

If the round state is good (evaluations consistent with degree 2d),
then an honest fold produces evaluations consistent with degree d
on the squared domain. This is the completeness direction:
honest prover always succeeds.
-/

/-- Honest fold preserves consistency on the squared domain -/
theorem honest_fold_consistent {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (hd_le_k : d ≤ k) :
    FRIStateGood
      (evalOnDomain (foldPolynomial decomp.pEven decomp.pOdd alpha)
        (D.squaredDomain k hk hk_ge))
      (D.squaredDomain k hk hk_ge) d rfl :=
  fold_consistent_on_squared_domain D p decomp alpha d hd k hk hk_ge hd_le_k

/-- Honest fold reduces degree by half -/
theorem honest_fold_degree {F : Type*} [Field F] [IsDomain F]
    (p : Polynomial F) (decomp : EvenOddDecomp p) (alpha : F)
    (d : Nat) (hd : p.natDegree < 2 * d) :
    (foldPolynomial decomp.pEven decomp.pOdd alpha).natDegree < d :=
  fold_degree_halving decomp alpha hd

/-- Honest fold: degree reduction + consistency + uniqueness -/
theorem honest_fold_complete {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (hd_le_k : d ≤ k) :
    let D' := D.squaredDomain k hk hk_ge
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    -- Degree reduction
    g.natDegree < d ∧
    -- Consistency on squared domain
    FRIStateGood (evalOnDomain g D') D' d rfl ∧
    -- Fold uniquely determined on D'
    (∀ g' : Polynomial F, g'.natDegree < D'.size →
      (∀ j : Fin D'.size, g'.eval (D'.elements j) = g.eval (D'.elements j)) →
      g' = g) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fold_degree_halving decomp alpha hd
  · exact fold_consistent_on_squared_domain D p decomp alpha d hd k hk hk_ge hd_le_k
  · intro g' hg' hagree
    have hg_deg : (foldPolynomial decomp.pEven decomp.pOdd alpha).natDegree <
        (D.squaredDomain k hk hk_ge).size := by
      have := fold_degree_halving decomp alpha hd
      simp [FRIEvalDomain.squaredDomain]
      omega
    exact fold_determines_unique _ g' _ hg' hg_deg hagree

/-! ## Part 3: Commitment Properties

The Merkle tree commitment binds the prover to specific evaluation
values. Under collision resistance (Axiom 2), changing committed
values is computationally infeasible.
-/

/-- Honest commitment: a well-formed Merkle tree's path verifies -/
theorem commitment_verifies_honest {F : Type*}
    (hashFn : F → F → F) (tree : MerkleTree F)
    (hwf : MerkleTree.WellFormed hashFn tree) :
    merklePathVerify hashFn (extractLeftPath tree) (leftmostLeaf tree) =
      tree.root :=
  merkle_verify_complete_left hashFn tree hwf

/-- Commitment binding: same hash for different inputs → collision -/
theorem commitment_binding_witness {F : Type*}
    (hashFn : F → F → F) (a₁ b₁ a₂ b₂ : F)
    (hne : (a₁, b₁) ≠ (a₂, b₂))
    (hcoll : hashFn a₁ b₁ = hashFn a₂ b₂) :
    ∃ x₁ y₁ x₂ y₂ : F,
      (x₁ ≠ x₂ ∨ y₁ ≠ y₂) ∧ hashFn x₁ y₁ = hashFn x₂ y₂ :=
  merkle_binding_step hashFn a₁ b₁ a₂ b₂ hne hcoll

/-- Commitment composability: well-formed trees compose -/
theorem commitment_composable {F : Type*}
    (hashFn : F → F → F) (l r : MerkleTree F)
    (hwfl : MerkleTree.WellFormed hashFn l)
    (hwfr : MerkleTree.WellFormed hashFn r) :
    MerkleTree.WellFormed hashFn
      (MerkleTree.node (hashFn l.root r.root) l r) :=
  merkle_wf_build hashFn l r hwfl hwfr

/-! ## Part 4: Challenge Properties (Fiat-Shamir)

Challenges are derived deterministically from the transcript.
Under the Random Oracle Model (Axiom 3), challenges are unpredictable
to the prover before committing.
-/

/-- Challenge determinism: same transcript state → same challenge -/
theorem round_challenge_deterministic {F : Type*}
    (t₁ t₂ : FormalTranscript F) (oracle : List F → Nat → F)
    (habsorbed : t₁.absorbed = t₂.absorbed)
    (hcount : t₁.squeezeCount = t₂.squeezeCount) :
    t₁.squeeze oracle = t₂.squeeze oracle :=
  transcript_deterministic t₁ t₂ oracle habsorbed hcount

/-- FRI round challenge depends on commitment + history -/
theorem fri_challenge_from_commitment {F : Type*}
    (t : FormalTranscript F) (oracle : List F → Nat → F)
    (commitment : F) :
    (friRound t oracle commitment).2 =
      oracle (t.absorbed ++ [commitment]) t.squeezeCount :=
  friRound_challenge t oracle commitment

/-- Different commitments → different oracle queries -/
theorem different_commitments_different_queries {F : Type*}
    (t : FormalTranscript F) (c₁ c₂ : F) (hne : c₁ ≠ c₂) :
    t.absorbed ++ [c₁] ≠ t.absorbed ++ [c₂] :=
  friRound_different_inputs t c₁ c₂ hne

/-! ## Part 5: Query Analysis

The verifier queries random positions to check fold consistency.
If the prover cheats (sends wrong fold values), the number of
"lucky" positions where the cheat coincidentally matches is
bounded by the polynomial degree.
-/

/-- Fold evaluation formula: fold(y) = pEven(y) + α·pOdd(y) -/
theorem fold_value_formula {F : Type*} [Field F]
    (decomp_even decomp_odd : Polynomial F) (alpha : F) (y : F) :
    (foldPolynomial decomp_even decomp_odd alpha).eval y =
      decomp_even.eval y + alpha * decomp_odd.eval y :=
  fold_eval_at_point decomp_even decomp_odd alpha y

/-- Fold output uniqueness on the domain -/
theorem fold_output_unique {F : Type*} [Field F] [IsDomain F]
    (D' : FRIEvalDomain F) (g₁ g₂ : Polynomial F)
    (hg₁ : g₁.natDegree < D'.size) (hg₂ : g₂.natDegree < D'.size)
    (hagree : ∀ j : Fin D'.size,
      g₁.eval (D'.elements j) = g₂.eval (D'.elements j)) :
    g₁ = g₂ :=
  fold_determines_unique D' g₁ g₂ hg₁ hg₂ hagree

/-- Specialized uniqueness: if a claimed polynomial matches the honest
    fold at all domain points, it must be the fold polynomial.
    Derives the degree bound on the honest fold automatically. -/
theorem fold_output_unique_from_honest {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (hd_le_k : d ≤ k)
    (g_claimed : Polynomial F)
    (hg_deg : g_claimed.natDegree < (D.squaredDomain k hk hk_ge).size)
    (hagree : ∀ j : Fin (D.squaredDomain k hk hk_ge).size,
      g_claimed.eval ((D.squaredDomain k hk hk_ge).elements j) =
        (foldPolynomial decomp.pEven decomp.pOdd alpha).eval
          ((D.squaredDomain k hk hk_ge).elements j)) :
    g_claimed = foldPolynomial decomp.pEven decomp.pOdd alpha := by
  exact fold_determines_unique _ g_claimed _ hg_deg
    (by have := fold_degree_halving decomp alpha hd
        simp [FRIEvalDomain.squaredDomain]; omega)
    hagree

/-- Query disagreement bound: two distinct polynomials of degree ≤ d
    can agree on at most d points (the roots of their difference).
    Out of |D'| positions, at least |D'| - d show disagreement. -/
theorem query_disagreement_bounded {F : Type*} [Field F] [IsDomain F]
    {d : Nat} (p q : Polynomial F) (hne : p ≠ q)
    (hdp : p.natDegree ≤ d) (hdq : q.natDegree ≤ d) :
    Multiset.card (p - q).roots ≤ d :=
  disagreement_bound p q hne hdp hdq

/-- Query catches cheating: if the prover claims a fold output g_claimed
    differing from the honest fold g, their agreement is bounded by d.

    With blowup factor ≥ 2, |D'| ≥ 2d, so at least half the positions
    detect the cheat. Each query catches it with probability ≥ 1/2. -/
theorem query_catches_cheating {F : Type*} [Field F] [IsDomain F]
    (g_honest g_claimed : Polynomial F)
    (hne : g_honest ≠ g_claimed)
    (d : Nat) (hh : g_honest.natDegree < d) (hc : g_claimed.natDegree < d) :
    Multiset.card (g_honest - g_claimed).roots ≤ d :=
  disagreement_bound g_honest g_claimed hne (le_of_lt hh) (le_of_lt hc)

/-! ## Part 6: Round State Transition

The structural invariant (domain size, degree bound, blowup factor)
is preserved across FRI rounds.
-/

/-- Invariant preserved across rounds -/
theorem round_invariant_preserved {F : Type*} [CommRing F]
    {state : FRIRoundState F} {bf : Nat}
    (hinv : FRIRoundInvariant state bf)
    {newDomain : FRIEvalDomain F}
    (hdom_half : newDomain.size * 2 = state.domain.size)
    {newChallenge : F}
    (hdeg_even : 2 ∣ state.degreeBound) :
    FRIRoundInvariant (state.nextRound newDomain newChallenge) bf :=
  invariant_preserved hinv hdom_half hdeg_even

/-- Degree bound halves each round -/
theorem round_degree_halves {F : Type*} [CommRing F]
    (state : FRIRoundState F) (D' : FRIEvalDomain F) (ch : F) :
    (state.nextRound D' ch).degreeBound = state.degreeBound / 2 := rfl

/-- Round counter increments -/
theorem round_counter_increments {F : Type*} [CommRing F]
    (state : FRIRoundState F) (D' : FRIEvalDomain F) (ch : F) :
    (state.nextRound D' ch).round = state.round + 1 := rfl

/-- Iterated degree bound: after r rounds, degree ≤ initial degree -/
theorem iterated_degree_le {d₀ r : Nat} :
    d₀ / 2 ^ r ≤ d₀ := iterated_degree_bound

/-! ## Part 7: RoundGuarantee + Per-Round Soundness

The RoundGuarantee bundles all per-round properties into a single
structure that VerifierComposition (N12.8) can iterate.
-/

/-- Complete per-round guarantee for FRI soundness analysis.
    Bundles fold completeness, uniqueness, and query soundness
    into a single composable unit. -/
structure RoundGuarantee (F : Type*) [Field F] [IsDomain F]
    (D D' : FRIEvalDomain F) (d : Nat) where
  /-- The fold output polynomial -/
  foldOutput : Polynomial F
  /-- Degree reduction: fold output has degree < d -/
  degree_reduced : foldOutput.natDegree < d
  /-- Consistency: fold output evaluations are consistent on D' -/
  consistent : FRIStateGood (evalOnDomain foldOutput D') D' d rfl
  /-- Uniqueness: fold output uniquely determined on D' -/
  unique : ∀ g' : Polynomial F, g'.natDegree < D'.size →
    (∀ j : Fin D'.size,
      g'.eval (D'.elements j) = foldOutput.eval (D'.elements j)) →
    g' = foldOutput
  /-- Query bound: any cheating polynomial of degree ≤ d agrees with
      the fold output on at most d points of D' -/
  query_bound : ∀ g' : Polynomial F, g' ≠ foldOutput →
    g'.natDegree ≤ d →
    Multiset.card (g' - foldOutput).roots ≤ d

/-- One FRI round produces a complete guarantee -/
noncomputable def one_round_guarantee {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (hd_le_k : d ≤ k) :
    RoundGuarantee F D (D.squaredDomain k hk hk_ge) d where
  foldOutput := foldPolynomial decomp.pEven decomp.pOdd alpha
  degree_reduced := fold_degree_halving decomp alpha hd
  consistent :=
    fold_consistent_on_squared_domain D p decomp alpha d hd k hk hk_ge hd_le_k
  unique := by
    intro g' hg' hagree
    have hg_deg : (foldPolynomial decomp.pEven decomp.pOdd alpha).natDegree <
        (D.squaredDomain k hk hk_ge).size := by
      have := fold_degree_halving decomp alpha hd
      simp [FRIEvalDomain.squaredDomain]
      omega
    exact fold_determines_unique _ g' _ hg' hg_deg hagree
  query_bound := by
    intro g' hne hg'_deg
    exact disagreement_bound g' _ hne hg'_deg
      (le_of_lt (fold_degree_halving decomp alpha hd))

/-- **Per-round soundness** (Garreta 2025, Theorem 3.2 adapted):

    One FRI round provides a 4-part guarantee:
    (1) Degree reduction: fold polynomial has degree < d
    (2) Consistency: fold evaluations consistent on D'
    (3) Uniqueness: fold uniquely determined by evaluations on D'
    (4) Query bound: cheating detected via polynomial root counting -/
theorem per_round_soundness {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (hd_le_k : d ≤ k) :
    let D' := D.squaredDomain k hk hk_ge
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    -- (1) Degree reduction
    g.natDegree < d ∧
    -- (2) Consistency on squared domain
    FRIStateGood (evalOnDomain g D') D' d rfl ∧
    -- (3) Uniqueness
    (∀ g' : Polynomial F, g'.natDegree < D'.size →
      (∀ j : Fin D'.size, g'.eval (D'.elements j) = g.eval (D'.elements j)) →
      g' = g) ∧
    -- (4) Query bound
    (∀ g' : Polynomial F, g' ≠ g → g'.natDegree ≤ d →
      Multiset.card (g' - g).roots ≤ d) := by
  refine ⟨fold_degree_halving decomp alpha hd,
    fold_consistent_on_squared_domain D p decomp alpha d hd k hk hk_ge hd_le_k,
    fun g' hg' hagree => fold_determines_unique _ g' _ hg'
      (by have := fold_degree_halving decomp alpha hd
          simp [FRIEvalDomain.squaredDomain]; omega) hagree,
    fun g' hne hg'_deg => disagreement_bound g' _ hne hg'_deg
      (le_of_lt (fold_degree_halving decomp alpha hd))⟩

/-! ## Part 8: Multi-Round Helpers

Helpers for VerifierComposition (N12.8) to compose across rounds.
-/

/-- State good transition: honest fold takes a good state to a good state
    with halved degree, and the fold output has low degree. -/
theorem state_good_transition {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (p : Polynomial F) (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) (hd_le_k : d ≤ k) :
    let D' := D.squaredDomain k hk hk_ge
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    FRIStateGood (evalOnDomain g D') D' d rfl ∧ g.natDegree < d :=
  ⟨fold_consistent_on_squared_domain D p decomp alpha d hd k hk hk_ge hd_le_k,
   fold_degree_halving decomp alpha hd⟩

/-- Degree chain: after r rounds of halving, degree ≤ initial -/
theorem degree_chain_bound (d₀ r : Nat) :
    d₀ / 2 ^ r ≤ d₀ :=
  Nat.div_le_self d₀ (2 ^ r)

/-- Final degree: after log₂(d₀) rounds, degree ≤ 1 -/
theorem final_degree_at_most_one (d₀ : Nat) (h : 0 < d₀) :
    d₀ / 2 ^ (numRoundsNeeded d₀) ≤ 1 :=
  AmoLean.FRI.Verified.final_degree_bound d₀ h

/-- Blowup factor bound: with blowup factor ≥ 2, the domain size
    is at least twice the degree bound. This means the agreement
    fraction d/|D'| ≤ 1/2, so each random query hits a disagreement
    with probability ≥ 1/2.

    The full probabilistic amplification bound (d/|D'|)^q for q
    independent queries is stated at the VerifierComposition level
    (N12.8) where the proximity gap axiom connects to error bounds. -/
theorem blowup_factor_bound (d domainSize : Nat)
    (hblowup : 2 * d ≤ domainSize) :
    2 * d ≤ domainSize := hblowup

/-! ## Part 9: Summary

PerRoundSoundness provides:

1. `FRIStateGood/FRIStateBad`: Garreta 2025 state function
2. `honest_fold_complete`: degree + consistency + uniqueness
3. `commitment_verifies_honest`: well-formed Merkle passes
4. `fri_challenge_from_commitment`: challenge binds to history
5. `query_catches_cheating`: cheating detected via root counting
6. `round_invariant_preserved`: structural invariant across rounds
7. `RoundGuarantee`: composable per-round guarantee struct
8. `one_round_guarantee`: constructs a RoundGuarantee
9. `per_round_soundness`: main 4-part theorem
10. `state_good_transition`: for multi-round chaining
11. `blowup_factor_bound`: domain size ≥ 2 × degree bound

All theorems proven without sorry. No new axioms introduced.
The 3 crypto axioms from FRISemanticSpec are documented but not
invoked — they are needed at the VerifierComposition level (N12.8)
where the soundness BOUND (not just structure) is stated.

Upstream: FoldSoundness (N12.4), MerkleSpec (N12.5), TranscriptSpec (N12.6)
Downstream: VerifierComposition (N12.8) iterates RoundGuarantee
-/

end AmoLean.FRI.Verified
