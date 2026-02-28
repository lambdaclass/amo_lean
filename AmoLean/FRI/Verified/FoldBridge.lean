/-
  AMO-Lean: Fold Bridge (N13.4)
  Fase 13 — Connecting operational friFold with verified foldPolynomial

  This module bridges:
  - Operational: friFold (FRI/Fold.lean) — Vec-based fold with FRIField
  - Verified: foldPolynomial (FRI/Verified/FieldBridge.lean) — Polynomial-level fold

  Strategy:
  1. Define `foldSpec`: function-level fold matching friFold's mathematical content
  2. Prove `foldSpec` = `evalOnDomain ∘ foldPolynomial` under even/odd interpretation
  3. Show degree preservation through the bridge
  4. Connect to ConsistentWithDegree for the soundness chain

  The bridge does NOT resolve implementation-specific ordering conventions.
  Instead, it proves: under the correct interpretation of input values,
  the operational fold agrees with the polynomial fold.

  Architecture:
  - Uses FieldBridge.evalOnDomain as intermediate representation
  - Uses FoldSoundness.fold_eval_at_point for algebraic equality
  - Uses FoldSoundness.fold_preserves_consistency for degree bounds
  - Imports DomainBridge for domain conversion utilities
-/

import AmoLean.FRI.Verified.FoldSoundness
import AmoLean.FRI.Verified.DomainBridge

namespace AmoLean.FRI.Verified

open Polynomial

/-! ## Part 1: Function-Level Fold Specification

`foldSpec` is the mathematical content of `friFold` expressed as a function
on `Fin` indices, without Vec or FRIField dependencies. This is the
"universal interface" for the fold bridge. -/

/-- Function-level fold specification: combines even-indexed and odd-indexed
    elements with challenge α. This captures the mathematical content of
    `friFold` without the Vec/FRIField machinery.

    foldSpec[i] = input[2i] + α * input[2i+1] -/
noncomputable def foldSpec {F : Type*} [CommRing F] (n : Nat)
    (input : Fin (2 * n) → F) (alpha : F) : Fin n → F :=
  fun i => input ⟨2 * i.val, by omega⟩ + alpha * input ⟨2 * i.val + 1, by omega⟩

/-- foldSpec at index i returns input[2i] + α * input[2i+1] -/
theorem foldSpec_def {F : Type*} [CommRing F] {n : Nat}
    (input : Fin (2 * n) → F) (alpha : F) (i : Fin n) :
    foldSpec n input alpha i =
    input ⟨2 * i.val, by omega⟩ + alpha * input ⟨2 * i.val + 1, by omega⟩ :=
  rfl

/-! ## Part 2: Even/Odd Interpretation

For the bridge to work, we need an interpretation of the input values.
The `EvenOddInterpretation` structure says: the values at even/odd indices
in the input correspond to the even/odd polynomial parts evaluated on
the squared domain D'. -/

/-- An interpretation of input values as even/odd polynomial evaluations.
    This is the bridge hypothesis: the operational input is arranged so that
    input[2i] = pEven.eval(D'.elements i) and
    input[2i+1] = pOdd.eval(D'.elements i). -/
structure EvenOddInterpretation {F : Type*} [CommRing F]
    (n : Nat) (input : Fin (2 * n) → F)
    (D' : FRIEvalDomain F) (hn : n = D'.size)
    (pEven pOdd : Polynomial F) : Prop where
  /-- Even-indexed values are evaluations of pEven on D' -/
  even_interp : ∀ i : Fin n,
    input ⟨2 * i.val, by omega⟩ = pEven.eval (D'.elements (hn ▸ i))
  /-- Odd-indexed values are evaluations of pOdd on D' -/
  odd_interp : ∀ i : Fin n,
    input ⟨2 * i.val + 1, by omega⟩ = pOdd.eval (D'.elements (hn ▸ i))

/-! ## Part 3: The Fold Bridge Theorem

THE main theorem: under even/odd interpretation, foldSpec produces
evaluations of foldPolynomial on D'. -/

/-- **Fold Bridge Equivalence**: under even/odd interpretation,
    the function-level fold equals evaluation of foldPolynomial on D'.

    This is THE bridge theorem connecting operational fold to verified fold.

    Proof:
      foldSpec[i] = input[2i] + α * input[2i+1]              [by definition]
                  = pEven.eval(D'.elements i) + α * pOdd.eval(D'.elements i)
                                                               [by interpretation]
                  = (foldPolynomial pEven pOdd α).eval(D'.elements i)
                                                               [by fold_eval_at_point]
                  = evalOnDomain (foldPolynomial pEven pOdd α) D' i
                                                               [by evalOnDomain def] -/
theorem foldBridge_equivalence {F : Type*} [CommRing F]
    {n : Nat} (input : Fin (2 * n) → F)
    (D' : FRIEvalDomain F) (hn : n = D'.size)
    {p : Polynomial F} (decomp : EvenOddDecomp p) (alpha : F)
    (interp : EvenOddInterpretation n input D' hn decomp.pEven decomp.pOdd) :
    ∀ i : Fin n,
      foldSpec n input alpha i =
      (foldPolynomial decomp.pEven decomp.pOdd alpha).eval (D'.elements (hn ▸ i)) := by
  intro i
  simp only [foldSpec]
  rw [interp.even_interp i, interp.odd_interp i]
  exact (fold_eval_at_point decomp.pEven decomp.pOdd alpha (D'.elements (hn ▸ i))).symm

/-- The fold bridge output equals evalOnDomain of foldPolynomial on D' -/
theorem foldBridge_eq_evalOnDomain {F : Type*} [CommRing F]
    {n : Nat} (input : Fin (2 * n) → F)
    (D' : FRIEvalDomain F) (hn : n = D'.size)
    {p : Polynomial F} (decomp : EvenOddDecomp p) (alpha : F)
    (interp : EvenOddInterpretation n input D' hn decomp.pEven decomp.pOdd) :
    ∀ i : Fin n,
      foldSpec n input alpha i =
      evalOnDomain (foldPolynomial decomp.pEven decomp.pOdd alpha) D' (hn ▸ i) := by
  intro i
  simp only [evalOnDomain]
  exact foldBridge_equivalence input D' hn decomp alpha interp i

/-! ## Part 4: Degree Preservation

The fold bridge preserves degree bounds: if the input comes from a
polynomial of degree < 2d, the fold output is consistent with degree < d. -/

/-- **Fold Bridge Degree Preservation**: under interpretation, the fold
    output is consistent with degree < d on D'.

    This connects the operational fold to `fold_preserves_consistency`. -/
theorem foldBridge_preserves_degree {F : Type*} [Field F] [IsDomain F]
    {n : Nat} (_input : Fin (2 * n) → F)
    (D : FRIEvalDomain F) (hn2 : 2 * n = D.size)
    {p : Polynomial F} (decomp : EvenOddDecomp p) (alpha : F)
    (d : Nat) (hd : p.natDegree < 2 * d)
    (hk_ge : 2 ≤ n) (hd_le : d ≤ n) :
    let D' := D.squaredDomain n hn2.symm hk_ge
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    -- The folded polynomial has degree < d
    g.natDegree < d ∧
    -- The folded polynomial has degree < D'.size
    g.natDegree < D'.size :=
  fold_preserves_consistency D p decomp alpha d hd n hn2.symm hk_ge hd_le

/-- The fold output is ConsistentWithDegree on D' -/
theorem foldBridge_consistent {F : Type*} [Field F] [IsDomain F]
    {n : Nat} (_input : Fin (2 * n) → F)
    (D : FRIEvalDomain F) (hn2 : 2 * n = D.size)
    {p : Polynomial F} (decomp : EvenOddDecomp p) (alpha : F)
    (d : Nat) (hd : p.natDegree < 2 * d)
    (hk_ge : 2 ≤ n) (hd_le : d ≤ n)
    (D' : FRIEvalDomain F) (hD' : D' = D.squaredDomain n hn2.symm hk_ge) :
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    ConsistentWithDegree (evalOnDomain g D') D' d rfl := by
  subst hD'
  exact fold_consistent_on_squared_domain D p decomp alpha d hd n hn2.symm hk_ge hd_le

/-! ## Part 5: FoldBridgeResult

A proof-carrying structure that bundles the fold bridge output with
its provenance, for downstream use by the integration node (N13.6). -/

/-- A fold bridge result bundles the folded evaluations with their
    connection to both the operational and verified worlds. -/
structure FoldBridgeResult (F : Type*) [CommRing F] where
  /-- The squared domain (fold target) -/
  domain : FRIEvalDomain F
  /-- The folded polynomial -/
  foldedPoly : Polynomial F
  /-- Degree bound of the folded polynomial -/
  degreeBound : Nat
  /-- The folded polynomial has degree < degreeBound -/
  degree_lt : foldedPoly.natDegree < degreeBound

/-- Construct a FoldBridgeResult from a fold operation -/
noncomputable def mkFoldBridgeResult {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) {p : Polynomial F} (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) :
    FoldBridgeResult F :=
  { domain := D.squaredDomain k hk hk_ge
    foldedPoly := foldPolynomial decomp.pEven decomp.pOdd alpha
    degreeBound := d
    degree_lt := fold_degree_halving decomp alpha hd }

/-- The fold bridge result's domain size is half the original -/
theorem FoldBridgeResult.domain_size {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) {p : Polynomial F} (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : D.size = 2 * k) (hk_ge : 2 ≤ k) :
    (mkFoldBridgeResult D decomp alpha d hd k hk hk_ge).domain.size = k :=
  rfl

/-! ## Part 6: Composition with Domain Bridge

Connecting the fold bridge with the domain bridge (N13.2) for
end-to-end operational-to-verified composition. -/

/-- Fold bridge composes with domain bridge: given valid FRI params and
    a polynomial on the bridged domain, folding preserves the bridge. -/
theorem foldBridge_composes_with_domain {F : Type*} [Field F] [IsDomain F]
    (params : FRIParams) (ω : F)
    (h_valid : ValidFRIParams params)
    (h_prim : IsPrimitiveRoot ω (initialDomainSize params))
    {p : Polynomial F} (decomp : EvenOddDecomp p)
    (alpha : F) (d : Nat) (hd : p.natDegree < 2 * d)
    (k : Nat) (hk : initialDomainSize params = 2 * k) (hk_ge : 2 ≤ k)
    (hd_le : d ≤ k) :
    let D := friParamsToDomain params ω h_valid h_prim
    let D' := D.squaredDomain k (by exact hk) hk_ge
    let g := foldPolynomial decomp.pEven decomp.pOdd alpha
    g.natDegree < d ∧ g.natDegree < D'.size := by
  exact fold_preserves_consistency
    (friParamsToDomain params ω h_valid h_prim) p decomp alpha d hd k
    (by exact hk) hk_ge hd_le

/-! ## Part 7: Algebraic Properties of foldSpec

Properties of foldSpec that mirror the verified fold properties. -/

/-- foldSpec is linear in alpha -/
theorem foldSpec_linear_alpha {F : Type*} [CommRing F] {n : Nat}
    (input : Fin (2 * n) → F) (alpha beta : F) (i : Fin n) :
    foldSpec n input (alpha + beta) i =
    foldSpec n input alpha i + beta * input ⟨2 * i.val + 1, by omega⟩ := by
  simp only [foldSpec]
  ring

/-- foldSpec with alpha = 0 just extracts even-indexed elements -/
theorem foldSpec_alpha_zero {F : Type*} [CommRing F] {n : Nat}
    (input : Fin (2 * n) → F) (i : Fin n) :
    foldSpec n input 0 i = input ⟨2 * i.val, by omega⟩ := by
  simp only [foldSpec, zero_mul, add_zero]

/-- foldSpec with alpha = 1 sums even and odd elements -/
theorem foldSpec_alpha_one {F : Type*} [CommRing F] {n : Nat}
    (input : Fin (2 * n) → F) (i : Fin n) :
    foldSpec n input 1 i =
    input ⟨2 * i.val, by omega⟩ + input ⟨2 * i.val + 1, by omega⟩ := by
  simp only [foldSpec, one_mul]

/-- foldSpec preserves equality: same inputs, same outputs -/
theorem foldSpec_ext {F : Type*} [CommRing F] {n : Nat}
    (input₁ input₂ : Fin (2 * n) → F) (alpha : F)
    (h : ∀ j, input₁ j = input₂ j) :
    ∀ i : Fin n, foldSpec n input₁ alpha i = foldSpec n input₂ alpha i := by
  intro i
  simp only [foldSpec, h]

/-! ## Part 8: Bridge Summary

FoldBridge provides:

1. `foldSpec`: function-level fold matching friFold semantics
2. `EvenOddInterpretation`: bridge hypothesis (input values = poly evals)
3. `foldBridge_equivalence`: THE main theorem — foldSpec = foldPoly eval
4. `foldBridge_eq_evalOnDomain`: version with evalOnDomain
5. `foldBridge_preserves_degree`: degree halving through the bridge
6. `foldBridge_consistent`: ConsistentWithDegree on D'
7. `FoldBridgeResult`: proof-carrying fold output for downstream
8. `foldBridge_composes_with_domain`: composition with domain bridge (N13.2)
9. `foldSpec_linear_alpha` / `_alpha_zero` / `_alpha_one`: algebraic properties

Upstream:
- FoldSoundness.lean (N12.4): fold_eval_at_point, fold_preserves_consistency
- FieldBridge.lean (N12.2): EvenOddDecomp, foldPolynomial, evalOnDomain
- DomainBridge.lean (N13.2): friParamsToDomain, ValidFRIParams

Downstream:
- BridgeIntegration.lean (N13.6): integration theorem
-/

end AmoLean.FRI.Verified
