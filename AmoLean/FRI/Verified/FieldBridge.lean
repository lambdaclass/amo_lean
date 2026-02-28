/-
  AMO-Lean: Field Bridge (N12.2)
  Fase 12 — Bridge between operational FRIField and Mathlib Field

  This module connects the operational field types (FRIField, FieldConfig)
  used in FRI implementation to Mathlib's algebraic hierarchy (Field, Polynomial).
  The bridge enables formal reasoning about FRI operations using Mathlib's
  polynomial theory while maintaining compatibility with executable code.

  Key Design Decisions:
  1. FRIFieldBridge typeclass: operational FRIField + Mathlib Field + embedding
  2. ZMod p serves as the canonical formal field (already has Field instance)
  3. evalPoly bridges evaluation representation (Vec) to Polynomial.eval
  4. degree_via_roots: connects polynomial degree to root counting
  5. Risk mitigation (L-015): avoid ring on large ZMod, use toZMod homomorphisms

  References:
  - AMO-Lean Goldilocks.lean, BabyBear.lean (toZMod pattern)
  - Mathlib Polynomial.card_roots'
-/

import AmoLean.FRI.Verified.FRISemanticSpec
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod

namespace AmoLean.FRI.Verified

open Polynomial

/-! ## Part 1: FRIFieldBridge Typeclass

The bridge connects an operational field type (with executable arithmetic)
to a formal field type (with Mathlib's algebraic structure). The key is
a ring homomorphism `toFormal` from operational to formal.
-/

/-- Bridge between an operational FRI field and its formal counterpart.

    `OpF` is the operational type (e.g., GoldilocksField with UInt64 arithmetic).
    `F` is the formal type (e.g., ZMod p with Mathlib's Field instance).
    `toFormal` is a ring homomorphism connecting them. -/
class FRIFieldBridge (OpF : Type*) (F : Type*)
    [Add OpF] [Mul OpF] [Zero OpF] [One OpF] [Neg OpF]
    [CommRing F] where
  /-- Convert operational field element to formal field element -/
  toFormal : OpF → F
  /-- Convert formal field element back to operational (partial inverse) -/
  ofFormal : F → OpF
  /-- toFormal is injective (different operational values map to different formal values) -/
  toFormal_injective : Function.Injective toFormal
  /-- toFormal preserves addition -/
  toFormal_add : ∀ a b : OpF, toFormal (a + b) = toFormal a + toFormal b
  /-- toFormal preserves multiplication -/
  toFormal_mul : ∀ a b : OpF, toFormal (a * b) = toFormal a * toFormal b
  /-- toFormal preserves zero -/
  toFormal_zero : toFormal (0 : OpF) = (0 : F)
  /-- toFormal preserves one -/
  toFormal_one : toFormal (1 : OpF) = (1 : F)

attribute [simp] FRIFieldBridge.toFormal_add FRIFieldBridge.toFormal_mul
  FRIFieldBridge.toFormal_zero FRIFieldBridge.toFormal_one

/-! ## Part 2: Polynomial Evaluation on Domains

Bridge between evaluation-vector representation and Polynomial.eval.
-/

/-- Evaluate a formal polynomial at all domain points, producing a function.
    This bridges the coefficient world (Polynomial F) to the evaluation world. -/
noncomputable def evalPolyOnDomain {F : Type*} [CommRing F]
    (p : Polynomial F) (D : FRIEvalDomain F) : Fin D.size → F :=
  fun i => p.eval (D.elements i)

/-- Evaluation at domain point i matches Polynomial.eval at generator^i -/
theorem evalPolyOnDomain_eq {F : Type*} [CommRing F]
    (p : Polynomial F) (D : FRIEvalDomain F) (i : Fin D.size) :
    evalPolyOnDomain p D i = p.eval (D.generator ^ (i : Nat)) := by
  simp [evalPolyOnDomain, FRIEvalDomain.elements]

/-- Two polynomials agreeing on all domain points agree as evaluations -/
theorem evalPolyOnDomain_ext {F : Type*} [CommRing F]
    (p q : Polynomial F) (D : FRIEvalDomain F)
    (heq : ∀ i : Fin D.size, p.eval (D.elements i) = q.eval (D.elements i)) :
    evalPolyOnDomain p D = evalPolyOnDomain q D := by
  ext i
  exact heq i

/-! ## Part 3: Degree and Root Counting

The key connection: polynomial degree limits the number of roots,
which bounds the number of agreeing points with any other polynomial.
This replaces Schwartz-Zippel (which is for multivariate polynomials).
-/

/-- A polynomial has at most natDegree roots (counted with multiplicity).
    This is `Polynomial.card_roots'` from Mathlib. -/
theorem roots_le_degree {F : Type*} [CommRing F] [IsDomain F]
    (p : Polynomial F) :
    Multiset.card p.roots ≤ p.natDegree :=
  Polynomial.card_roots' p

/-- If two distinct polynomials of degree ≤ d, their difference has at most d roots. -/
theorem disagreement_bound {F : Type*} [CommRing F] [IsDomain F]
    {d : Nat}
    (p q : Polynomial F) (_hp : p ≠ q)
    (hdp : p.natDegree ≤ d) (hdq : q.natDegree ≤ d) :
    Multiset.card (p - q).roots ≤ d := by
  calc Multiset.card (p - q).roots
      ≤ (p - q).natDegree := Polynomial.card_roots' _
    _ ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
    _ ≤ d := max_le hdp hdq

/-! ## Part 4: Even-Odd Polynomial Decomposition

The mathematical foundation of FRI folding: every polynomial P(x) can be
uniquely decomposed as P(x) = P_even(x²) + x · P_odd(x²).
-/

/-- Decomposition theorem statement: P(x) = P_even(x²) + x · P_odd(x²)
    where P_even, P_odd have degree at most ⌊deg(P)/2⌋.

    This is the mathematical justification for FRI's fold operation. -/
structure EvenOddDecomp {F : Type*} [CommRing F] (p : Polynomial F) where
  /-- The even-coefficient polynomial: P_even(y) = Σ a_{2i} y^i -/
  pEven : Polynomial F
  /-- The odd-coefficient polynomial: P_odd(y) = Σ a_{2i+1} y^i -/
  pOdd : Polynomial F
  /-- The decomposition identity: P(x) = P_even(x²) + x · P_odd(x²) -/
  decomp : ∀ x : F, p.eval x = pEven.eval (x * x) + x * pOdd.eval (x * x)
  /-- Degree bound for even part -/
  even_degree : pEven.natDegree ≤ p.natDegree / 2
  /-- Degree bound for odd part -/
  odd_degree : pOdd.natDegree ≤ p.natDegree / 2

/-- The FRI fold at the polynomial level: given P and challenge α,
    compute P_α(y) = P_even(y) + α · P_odd(y).
    The folded polynomial has degree at most deg(P)/2. -/
noncomputable def foldPolynomial {F : Type*} [CommRing F]
    (pEven pOdd : Polynomial F) (alpha : F) : Polynomial F :=
  pEven + Polynomial.C alpha * pOdd

/-- The folded polynomial has degree ≤ max(deg(P_even), deg(P_odd)) -/
theorem foldPolynomial_degree {F : Type*} [CommRing F]
    (pEven pOdd : Polynomial F) (alpha : F) :
    (foldPolynomial pEven pOdd alpha).natDegree ≤
      max pEven.natDegree pOdd.natDegree := by
  unfold foldPolynomial
  calc (pEven + C alpha * pOdd).natDegree
      ≤ max pEven.natDegree (C alpha * pOdd).natDegree := natDegree_add_le _ _
    _ ≤ max pEven.natDegree pOdd.natDegree := by
        apply max_le_max_left
        calc (C alpha * pOdd).natDegree
            ≤ (C alpha).natDegree + pOdd.natDegree := natDegree_mul_le
          _ = pOdd.natDegree := by simp [natDegree_C]

/-- Key theorem: if P has degree < 2d, then P_α has degree < d -/
theorem foldPolynomial_degree_half {F : Type*} [CommRing F]
    {d : Nat} {p : Polynomial F} (decomp : EvenOddDecomp p)
    (alpha : F) (hd : p.natDegree < 2 * d) :
    (foldPolynomial decomp.pEven decomp.pOdd alpha).natDegree < d := by
  have hfold := foldPolynomial_degree decomp.pEven decomp.pOdd alpha
  have heven := decomp.even_degree
  have hodd := decomp.odd_degree
  have hmax : max decomp.pEven.natDegree decomp.pOdd.natDegree < d := by
    apply max_lt <;> omega
  omega

/-! ## Part 5: Concrete Field Types

ZMod p abbreviations for the two main fields used in FRI.
The actual Field instances come from Mathlib given Fact (Nat.Prime p).
-/

/-- The formal Goldilocks field as ZMod p, where p = 2^64 - 2^32 + 1 -/
abbrev GoldilocksZMod := ZMod 18446744069414584321

/-- The formal BabyBear field as ZMod p, where p = 2^31 - 2^27 + 1 -/
abbrev BabyBearZMod := ZMod 2013265921

/-- Goldilocks prime -/
theorem goldilocks_prime : Nat.Prime 18446744069414584321 := by native_decide

/-- BabyBear prime -/
theorem babybear_prime : Nat.Prime 2013265921 := by native_decide

instance : Fact (Nat.Prime 18446744069414584321) := ⟨goldilocks_prime⟩
instance : Fact (Nat.Prime 2013265921) := ⟨babybear_prime⟩

-- Field instances are now automatic from Mathlib's ZMod.instField + Fact

/-! ## Part 6: Agreement-Equality Theorem

The fundamental bridge: polynomial evaluations on a domain D
uniquely determine the polynomial (when deg < |D|).
-/

/-- If two polynomials of degree < |D| agree on all domain points, they are equal.
    Proof: their difference has degree < |D| but vanishes on |D| distinct points,
    so it must be zero. -/
theorem agreement_implies_equality {F : Type*} [CommRing F] [IsDomain F]
    (p q : Polynomial F) (D : FRIEvalDomain F)
    (hdp : p.natDegree < D.size) (hdq : q.natDegree < D.size)
    (hagree : ∀ i : Fin D.size, p.eval (D.elements i) = q.eval (D.elements i)) :
    p = q := by
  classical
  by_contra hne
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hne
  -- Degree of difference is < D.size
  have hdeg : (p - q).natDegree < D.size := by
    calc (p - q).natDegree
        ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
      _ < D.size := max_lt hdp hdq
  -- All domain elements are roots of p - q
  have hroot : ∀ i : Fin D.size, Polynomial.IsRoot (p - q) (D.elements i) := by
    intro i
    simp [Polynomial.IsRoot, eval_sub, hagree i]
  -- Domain elements are distinct
  have hinj := D.elements_injective
  -- roots.card ≤ natDegree
  have hcard : Multiset.card (p - q).roots ≤ (p - q).natDegree := Polynomial.card_roots' _
  -- Each domain point is a root
  have hmem : ∀ i : Fin D.size, D.elements i ∈ (p - q).roots := by
    intro i
    rw [Polynomial.mem_roots hdiff]
    exact hroot i
  -- D.size distinct elements are all in roots → D.size ≤ roots.card
  have hge : D.size ≤ Multiset.card (p - q).roots := by
    have hsub : Finset.univ.image D.elements ⊆ (p - q).roots.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, hi⟩ := hx
      rw [Multiset.mem_toFinset, ← hi]
      exact hmem i
    calc D.size
        = Fintype.card (Fin D.size) := by simp
      _ = (Finset.univ.image D.elements).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
  -- Contradiction: D.size ≤ roots.card ≤ natDegree < D.size
  omega

/-- Corollary: evaluations on a domain uniquely determine the polynomial -/
theorem eval_determines_poly {F : Type*} [CommRing F] [IsDomain F]
    (D : FRIEvalDomain F) (p q : Polynomial F)
    (hdp : p.natDegree < D.size) (hdq : q.natDegree < D.size)
    (heq : ∀ i : Fin D.size, p.eval (D.elements i) = q.eval (D.elements i)) :
    p = q :=
  agreement_implies_equality p q D hdp hdq heq

/-! ## Part 7: Summary of Bridge API

The FieldBridge provides:
1. `FRIFieldBridge` typeclass: operational ↔ formal field
2. `evalPolyOnDomain`: polynomial evaluation on FRI domains
3. `roots_le_degree`: root count bound (replaces Schwartz-Zippel)
4. `disagreement_bound`: two polynomials agree on at most d points
5. `EvenOddDecomp`: P(x) = P_even(x²) + x·P_odd(x²)
6. `foldPolynomial`: algebraic fold operation
7. `foldPolynomial_degree_half`: fold halves degree
8. `agreement_implies_equality`: evaluations determine polynomial (0 sorry)
-/

end AmoLean.FRI.Verified
