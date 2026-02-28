/-
  AMO-Lean: Barycentric Interpolation (N12.3)
  Fase 12 — Novel formalization connecting barycentric to Lagrange

  This module formalizes barycentric interpolation and proves its equivalence
  with Mathlib's `Lagrange.interpolate`. While Mathlib already contains
  `Lagrange.nodalWeight` (= barycentric weight) and
  `eval_interpolate_not_at_node'` (= second barycentric form), this module
  provides:

  1. An explicit, clean API for barycentric interpolation
  2. Connection to FRI evaluation domains (roots of unity)
  3. Degree bound proofs for the barycentric form
  4. The key `barycentric_eq_lagrange` theorem

  The first barycentric form is:
    p(x) = Σᵢ (wᵢ * rᵢ * ∏ⱼ≠ᵢ (x - xⱼ))

  The second barycentric form (numerically stable) is:
    p(x) = (Σᵢ wᵢ/(x-xᵢ) * rᵢ) / (Σᵢ wᵢ/(x-xᵢ))

  where wᵢ = 1/∏ⱼ≠ᵢ(xᵢ - xⱼ) are the barycentric weights.

  References:
  - Berrut & Trefethen (2004), "Barycentric Lagrange Interpolation"
  - Mathlib.LinearAlgebra.Lagrange (nodalWeight, interpolate)
-/

import AmoLean.FRI.Verified.FieldBridge
import Mathlib.LinearAlgebra.Lagrange

namespace AmoLean.FRI.Verified

open Polynomial Lagrange Finset

/-! ## Part 1: Barycentric Weights

The barycentric weight for node xᵢ among {x₀,...,xₙ₋₁} is:
  wᵢ = 1 / ∏_{j≠i} (xᵢ - xⱼ)

Mathlib calls this `Lagrange.nodalWeight`. We provide a clean wrapper
and prove it equals the standard definition.
-/

/-- Barycentric weight: the inverse product of differences.
    This is exactly `Lagrange.nodalWeight` from Mathlib. -/
noncomputable def barycentricWeight {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (i : Fin n) : F :=
  Lagrange.nodalWeight Finset.univ nodes i

/-- Barycentric weights are nonzero for distinct nodes -/
theorem barycentricWeight_ne_zero {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (hinj : Function.Injective nodes) (i : Fin n) :
    barycentricWeight nodes i ≠ 0 := by
  unfold barycentricWeight
  apply Lagrange.nodalWeight_ne_zero
  · intro a _ b _ hab
    exact hinj hab
  · exact Finset.mem_univ i

/-! ## Part 2: First Barycentric Form

The interpolating polynomial in the first barycentric form:
  p(x) = Σᵢ rᵢ · wᵢ · ∏_{j≠i} (x - xⱼ)

This equals Lagrange.interpolate applied to the values.
-/

/-- Barycentric interpolation: construct the interpolating polynomial
    from nodes and values. This IS Lagrange.interpolate — we just
    provide a friendlier interface for FRI use. -/
noncomputable def barycentricInterp {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (values : Fin n → F) : Polynomial F :=
  Lagrange.interpolate Finset.univ nodes values

/-- **Key theorem**: barycentric interpolation equals Lagrange interpolation.
    This is true by definition (both call Lagrange.interpolate), but the
    explicit statement serves as documentation and API boundary. -/
theorem barycentric_eq_lagrange {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (values : Fin n → F) :
    barycentricInterp nodes values = Lagrange.interpolate Finset.univ (nodes ·) (values ·) := by
  rfl

/-! ## Part 3: Correctness Theorems -/

/-- Barycentric interpolation evaluates correctly at all nodes -/
theorem barycentric_eval_correct {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (values : Fin n → F)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (barycentricInterp nodes values).eval (nodes i) = values i := by
  unfold barycentricInterp
  exact Lagrange.eval_interpolate_at_node _ (fun _ ha _ hb h => hinj h) (Finset.mem_univ i)

/-- Barycentric interpolation has degree < n (number of nodes) -/
theorem barycentric_degree_lt {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (values : Fin n → F)
    (hinj : Function.Injective nodes) :
    (barycentricInterp nodes values).degree < n := by
  unfold barycentricInterp
  have hlt := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := nodes)
    values (fun _ ha _ hb h => hinj h)
  simp at hlt
  exact hlt

/-- Barycentric interpolation has natDegree ≤ n - 1 -/
theorem barycentric_natDegree_le {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (values : Fin n → F)
    (hinj : Function.Injective nodes) :
    (barycentricInterp nodes values).natDegree ≤ n - 1 := by
  unfold barycentricInterp
  have hle := Lagrange.degree_interpolate_le (s := Finset.univ) (v := nodes)
    values (fun _ ha _ hb h => hinj h)
  simp at hle
  exact Polynomial.natDegree_le_of_degree_le hle

/-- Uniqueness: the interpolating polynomial is the unique polynomial of
    degree < n that agrees with the values at all nodes. -/
theorem barycentric_unique {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (values : Fin n → F)
    (hinj : Function.Injective nodes) (p : Polynomial F)
    (hdeg : p.natDegree < n) (hagree : ∀ i : Fin n, p.eval (nodes i) = values i) :
    p = barycentricInterp nodes values := by
  classical
  -- Both p and barycentricInterp agree at all n distinct nodes
  -- and both have degree < n, so they must be equal
  set q := barycentricInterp nodes values with hq_def
  by_contra hne
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hne
  -- Degree of difference < n
  have hdeg_q : q.natDegree ≤ n - 1 :=
    barycentric_natDegree_le nodes values hinj
  have hdeg_diff : (p - q).natDegree < n :=
    calc (p - q).natDegree
        ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
      _ < n := by omega
  -- All nodes are roots of p - q
  have hroot : ∀ i : Fin n, Polynomial.IsRoot (p - q) (nodes i) := by
    intro i
    simp [Polynomial.IsRoot, eval_sub]
    rw [hagree i, hq_def, barycentric_eval_correct nodes values hinj i]; ring
  -- Count roots
  have hmem : ∀ i : Fin n, nodes i ∈ (p - q).roots := by
    intro i
    rw [Polynomial.mem_roots hdiff]
    exact hroot i
  have hge : n ≤ Multiset.card (p - q).roots := by
    have hsub : Finset.univ.image nodes ⊆ (p - q).roots.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, hi⟩ := hx
      rw [Multiset.mem_toFinset, ← hi]
      exact hmem i
    calc n
        = Fintype.card (Fin n) := by simp
      _ = (Finset.univ.image nodes).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
  have hcard : Multiset.card (p - q).roots ≤ (p - q).natDegree := Polynomial.card_roots' _
  omega

/-! ## Part 4: Connection to FRI Evaluation Domains

For FRI, the nodes are roots of unity: {ω^0, ω^1, ..., ω^(n-1)}.
This gives a special structure to the barycentric weights.
-/

/-- Barycentric interpolation on an FRI evaluation domain -/
noncomputable def barycentricOnDomain {F : Type*} [Field F]
    (D : FRIEvalDomain F) (values : Fin D.size → F) : Polynomial F :=
  barycentricInterp D.elements values

/-- Evaluation correctness on FRI domain -/
theorem barycentricOnDomain_eval_correct {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (values : Fin D.size → F) (i : Fin D.size) :
    (barycentricOnDomain D values).eval (D.elements i) = values i := by
  unfold barycentricOnDomain
  exact barycentric_eval_correct D.elements values D.elements_injective i

/-- Degree bound on FRI domain -/
theorem barycentricOnDomain_degree_lt {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (values : Fin D.size → F) :
    (barycentricOnDomain D values).degree < D.size := by
  unfold barycentricOnDomain
  exact barycentric_degree_lt D.elements values D.elements_injective

/-- natDegree bound on FRI domain -/
theorem barycentricOnDomain_natDegree_le {F : Type*} [Field F] [IsDomain F]
    (D : FRIEvalDomain F) (values : Fin D.size → F) :
    (barycentricOnDomain D values).natDegree ≤ D.size - 1 := by
  unfold barycentricOnDomain
  exact barycentric_natDegree_le D.elements values D.elements_injective

/-! ## Part 5: Barycentric Evaluation Identity

The second barycentric form provides an efficient evaluation formula:
  p(x) = (Σᵢ wᵢ/(x-xᵢ) · rᵢ) / (Σᵢ wᵢ/(x-xᵢ))

This is already proven in Mathlib as `eval_interpolate_not_at_node'`.
We provide a clean wrapper for FRI use.
-/

/-- Second barycentric form evaluation: for x ≠ any node,
    the interpolant evaluates via the ratio formula.
    This wraps Mathlib's `Lagrange.eval_interpolate_not_at_node'`. -/
theorem barycentric_second_form {F : Type*} [Field F]
    {n : Nat} (nodes : Fin n → F) (values : Fin n → F)
    (hinj : Function.Injective nodes) (x : F)
    (hne : ∀ i : Fin n, x ≠ nodes i) (hne' : (Finset.univ : Finset (Fin n)).Nonempty) :
    (barycentricInterp nodes values).eval x =
      (∑ i : Fin n, barycentricWeight nodes i * (x - nodes i)⁻¹ * values i) /
      (∑ i : Fin n, barycentricWeight nodes i * (x - nodes i)⁻¹) := by
  unfold barycentricInterp barycentricWeight
  have hinj' : Set.InjOn nodes (↑(Finset.univ : Finset (Fin n))) :=
    fun _ ha _ hb h => hinj h
  have hne'' : ∀ i : Fin n, i ∈ (Finset.univ : Finset (Fin n)) → x ≠ nodes i :=
    fun i _ => hne i
  rw [Lagrange.eval_interpolate_not_at_node' _ hinj' hne' hne'']

/-! ## Part 6: Summary

The BarycentricInterpolation module provides:

1. `barycentricWeight`: clean API for Lagrange.nodalWeight
2. `barycentricInterp`: interpolation from nodes+values
3. `barycentric_eq_lagrange`: equivalence with Mathlib's Lagrange
4. `barycentric_eval_correct`: evaluates correctly at nodes
5. `barycentric_degree_lt`: degree < number of nodes
6. `barycentric_unique`: uniqueness of interpolant (0 sorry)
7. `barycentricOnDomain`: specialization to FRI evaluation domains
8. `barycentric_second_form`: efficient evaluation formula

All theorems are proven without sorry. The `barycentric_unique` theorem uses
a direct root-counting argument (same technique as `agreement_implies_equality`
in FieldBridge but without requiring an FRIEvalDomain).
-/

end AmoLean.FRI.Verified
