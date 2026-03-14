/-
  AMO-Lean: Fp4 Degree-4 Extension Field
  N18.3 (PARALELO) -- Fp4 Tower Extension Field

  Defines a degree-4 extension Fp4 = F[u]/(u^4 - W) as a standalone struct
  with 4 components (NOT Fp2(Fp2)) to avoid nested instance diamonds.

  CommRing: proved mechanically via ext + ring.
  Field: noncomputable, using explicit inverse via conjugate tower with
  norm_ne_zero proved from IsIrreducibleQuartic hypothesis.

  0 sorry, 0 axioms.
-/

import AmoLean.Field.ExtField.Fp2Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Classical

namespace AmoLean.Field.ExtField

/-- Degree-4 extension field: F[u]/(u^4 - W). -/
structure Fp4 (F : Type*) [Field F] (W : F) where
  c0 : F
  c1 : F
  c2 : F
  c3 : F
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] {W : F}

namespace Fp4

@[ext]
theorem ext {a b : Fp4 F W} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) (h3 : a.c3 = b.c3) : a = b := by
  cases a; cases b; simp_all

protected def zero : Fp4 F W := ⟨0, 0, 0, 0⟩
protected def one : Fp4 F W := ⟨1, 0, 0, 0⟩
protected def add (a b : Fp4 F W) : Fp4 F W :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩
protected def neg (a : Fp4 F W) : Fp4 F W := ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩
protected def sub (a b : Fp4 F W) : Fp4 F W :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩
protected def mul (a b : Fp4 F W) : Fp4 F W :=
  ⟨a.c0 * b.c0 + W * (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1),
   a.c0 * b.c1 + a.c1 * b.c0 + W * (a.c2 * b.c3 + a.c3 * b.c2),
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + W * (a.c3 * b.c3),
   a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0⟩
protected def npow : Nat → Fp4 F W → Fp4 F W
  | 0, _ => Fp4.one
  | n + 1, a => Fp4.mul a (Fp4.npow n a)
protected def natCast (n : Nat) : Fp4 F W := ⟨(n : F), 0, 0, 0⟩
protected def intCast (z : Int) : Fp4 F W := ⟨(z : F), 0, 0, 0⟩

instance : Zero (Fp4 F W) := ⟨Fp4.zero⟩
instance : One (Fp4 F W) := ⟨Fp4.one⟩
instance : Add (Fp4 F W) := ⟨Fp4.add⟩
instance : Neg (Fp4 F W) := ⟨Fp4.neg⟩
instance : Sub (Fp4 F W) := ⟨Fp4.sub⟩
instance : Mul (Fp4 F W) := ⟨Fp4.mul⟩
instance : NatCast (Fp4 F W) := ⟨Fp4.natCast⟩
instance : IntCast (Fp4 F W) := ⟨Fp4.intCast⟩
instance : Inhabited (Fp4 F W) := ⟨0⟩

@[simp] theorem zero_c0 : (0 : Fp4 F W).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp4 F W).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Fp4 F W).c2 = 0 := rfl
@[simp] theorem zero_c3 : (0 : Fp4 F W).c3 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp4 F W).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp4 F W).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Fp4 F W).c2 = 0 := rfl
@[simp] theorem one_c3 : (1 : Fp4 F W).c3 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp4 F W) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp4 F W) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Fp4 F W) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem add_c3 (a b : Fp4 F W) : (a + b).c3 = a.c3 + b.c3 := rfl
@[simp] theorem neg_c0 (a : Fp4 F W) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp4 F W) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Fp4 F W) : (-a).c2 = -a.c2 := rfl
@[simp] theorem neg_c3 (a : Fp4 F W) : (-a).c3 = -a.c3 := rfl
@[simp] theorem sub_c0 (a b : Fp4 F W) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp4 F W) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Fp4 F W) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem sub_c3 (a b : Fp4 F W) : (a - b).c3 = a.c3 - b.c3 := rfl
@[simp] theorem mul_c0 (a b : Fp4 F W) :
    (a * b).c0 = a.c0 * b.c0 + W * (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : Fp4 F W) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + W * (a.c2 * b.c3 + a.c3 * b.c2) := rfl
@[simp] theorem mul_c2 (a b : Fp4 F W) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + W * (a.c3 * b.c3) := rfl
@[simp] theorem mul_c3 (a b : Fp4 F W) :
    (a * b).c3 = a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0 := rfl
@[simp] theorem natCast_c0 (n : Nat) : (n : Fp4 F W).c0 = (n : F) := rfl
@[simp] theorem natCast_c1 (n : Nat) : (n : Fp4 F W).c1 = 0 := rfl
@[simp] theorem natCast_c2 (n : Nat) : (n : Fp4 F W).c2 = 0 := rfl
@[simp] theorem natCast_c3 (n : Nat) : (n : Fp4 F W).c3 = 0 := rfl
@[simp] theorem intCast_c0 (z : Int) : (z : Fp4 F W).c0 = (z : F) := rfl
@[simp] theorem intCast_c1 (z : Int) : (z : Fp4 F W).c1 = 0 := rfl
@[simp] theorem intCast_c2 (z : Int) : (z : Fp4 F W).c2 = 0 := rfl
@[simp] theorem intCast_c3 (z : Int) : (z : Fp4 F W).c3 = 0 := rfl

instance instCommRing : CommRing (Fp4 F W) where
  add_assoc := fun a b c => by ext <;> simp [add_assoc]
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp [add_comm]
  neg := Fp4.neg
  neg_add_cancel := fun a => by
    show Fp4.add (Fp4.neg a) a = Fp4.zero
    cases a; simp [Fp4.add, Fp4.neg, Fp4.zero, neg_add_cancel]
  sub := Fp4.sub
  sub_eq_add_neg := fun a b => by
    show Fp4.sub a b = Fp4.add a (Fp4.neg b)
    cases a; cases b; simp [Fp4.sub, Fp4.add, Fp4.neg, sub_eq_add_neg]
  nsmul := fun n a => ⟨n • a.c0, n • a.c1, n • a.c2, n • a.c3⟩
  nsmul_zero := fun a => by ext <;> simp
  nsmul_succ := fun n a => by ext <;> simp [add_mul, add_comm]
  zsmul := fun z a => ⟨z • a.c0, z • a.c1, z • a.c2, z • a.c3⟩
  zsmul_zero' := fun a => by ext <;> simp
  zsmul_succ' := fun n a => by ext <;> simp [add_mul, add_comm]
  zsmul_neg' := fun n a => by
    show (⟨Int.negSucc n • a.c0, Int.negSucc n • a.c1,
          Int.negSucc n • a.c2, Int.negSucc n • a.c3⟩ : Fp4 F W) =
         Fp4.neg ⟨(↑(n + 1) : Int) • a.c0, (↑(n + 1) : Int) • a.c1,
                  (↑(n + 1) : Int) • a.c2, (↑(n + 1) : Int) • a.c3⟩
    simp only [Fp4.neg, negSucc_zsmul, Nat.cast_succ, ← natCast_zsmul]
  mul_assoc := fun a b c => by ext <;> simp <;> ring
  one_mul := fun a => by ext <;> simp
  mul_one := fun a => by ext <;> simp
  mul_comm := fun a b => by ext <;> simp <;> ring
  left_distrib := fun a b c => by ext <;> simp <;> ring
  right_distrib := fun a b c => by ext <;> simp <;> ring
  zero_mul := fun a => by ext <;> simp
  mul_zero := fun a => by ext <;> simp
  natCast := Fp4.natCast
  natCast_zero := by
    show Fp4.natCast 0 = Fp4.zero; simp [Fp4.natCast, Fp4.zero, Nat.cast_zero]
  natCast_succ := fun n => by
    show Fp4.natCast (n + 1) = Fp4.add (Fp4.natCast n) Fp4.one
    simp [Fp4.natCast, Fp4.add, Fp4.one, Nat.cast_succ]
  intCast := Fp4.intCast
  intCast_ofNat := fun n => by
    show Fp4.intCast (↑n) = Fp4.natCast n; simp [Fp4.intCast, Fp4.natCast, Int.cast_natCast]
  intCast_negSucc := fun n => by
    show Fp4.intCast (Int.negSucc n) = Fp4.neg (Fp4.natCast (n + 1))
    simp [Fp4.intCast, Fp4.neg, Fp4.natCast, Int.cast_negSucc]
  npow := fun n a => Fp4.npow n a
  npow_zero := fun a => by show Fp4.npow 0 a = 1; rfl
  npow_succ := fun n a => by
    show Fp4.npow (n + 1) a = Fp4.mul (Fp4.npow n a) a
    simp only [Fp4.npow]
    cases a; simp [Fp4.mul]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

def ofBase (c : F) : Fp4 F W := ⟨c, 0, 0, 0⟩
def u : Fp4 F W := ⟨0, 1, 0, 0⟩

theorem u_pow4 : (u : Fp4 F W) * u * u * u = ofBase W := by ext <;> simp [u, ofBase]

def conjOdd (a : Fp4 F W) : Fp4 F W := ⟨a.c0, -a.c1, a.c2, -a.c3⟩

@[simp] theorem conjOdd_c0 (a : Fp4 F W) : (conjOdd a).c0 = a.c0 := rfl
@[simp] theorem conjOdd_c1 (a : Fp4 F W) : (conjOdd a).c1 = -a.c1 := rfl
@[simp] theorem conjOdd_c2 (a : Fp4 F W) : (conjOdd a).c2 = a.c2 := rfl
@[simp] theorem conjOdd_c3 (a : Fp4 F W) : (conjOdd a).c3 = -a.c3 := rfl

/-- The degree-4 norm to the base field via two-step tower. -/
def norm (a : Fp4 F W) : F :=
  let q0 := a.c0 * a.c0 + W * (a.c2 * a.c2 - 2 * a.c1 * a.c3)
  let q2 := 2 * a.c0 * a.c2 - a.c1 * a.c1 - W * (a.c3 * a.c3)
  q0 * q0 - W * (q2 * q2)

/-- x^4 - W is irreducible over F when W and -W are both non-squares. -/
class IsIrreducibleQuartic {F : Type*} [Field F] (W : F) : Prop where
  not_square : ∀ x : F, x * x ≠ W
  neg_not_square : ∀ x : F, x * x ≠ -W

/-- The norm of a nonzero Fp4 element is nonzero when x^4 - W is irreducible. -/
theorem norm_ne_zero [IsIrreducibleQuartic W] (a : Fp4 F W) (ha : a ≠ 0) :
    norm a ≠ 0 := by
  intro hn
  set q0 := a.c0 * a.c0 + W * (a.c2 * a.c2 - 2 * a.c1 * a.c3)
  set q2 := 2 * a.c0 * a.c2 - a.c1 * a.c1 - W * (a.c3 * a.c3)
  have hn_eq : norm a = q0 * q0 - W * (q2 * q2) := rfl
  rw [hn_eq] at hn
  have hsq : q0 * q0 = W * (q2 * q2) := sub_eq_zero.mp hn
  by_cases hq2 : q2 = 0
  · rw [hq2, mul_zero, mul_zero] at hsq
    have hq0 : q0 = 0 := mul_self_eq_zero.mp hsq
    have hQ0 : a.c0 * a.c0 + W * (a.c2 * a.c2 - 2 * a.c1 * a.c3) = 0 := hq0
    have hQ2 : 2 * a.c0 * a.c2 - a.c1 * a.c1 - W * (a.c3 * a.c3) = 0 := hq2
    by_cases ha1 : a.c1 = 0
    · by_cases ha3 : a.c3 = 0
      · rw [ha1, ha3] at hQ0; simp only [mul_zero, sub_zero] at hQ0
        by_cases ha2 : a.c2 = 0
        · rw [ha2, mul_zero, mul_zero, add_zero] at hQ0
          exact ha (ext (mul_self_eq_zero.mp hQ0) ha1 ha2 ha3)
        · exact absurd (show (a.c0 / a.c2) * (a.c0 / a.c2) = -W by
            field_simp; linear_combination hQ0) (IsIrreducibleQuartic.neg_not_square _)
      · rw [ha1] at hQ0 hQ2; simp only [mul_zero, sub_zero, zero_mul] at hQ0 hQ2
        by_cases ha2 : a.c2 = 0
        · rw [ha2, mul_zero, mul_zero, add_zero] at hQ0
          have ha0 := mul_self_eq_zero.mp hQ0
          have hWa3 : W * (a.c3 * a.c3) = 0 := by rw [ha0, ha2] at hQ2; simpa using hQ2
          have hW : W ≠ 0 := fun hW0 =>
            absurd (show (0:F) * 0 = W from by rw [mul_zero, hW0]) (IsIrreducibleQuartic.not_square 0)
          exact ha (ext ha0 ha1 ha2
            (mul_self_eq_zero.mp ((mul_eq_zero.mp hWa3).resolve_left hW)))
        · exact absurd (show (a.c0 / a.c2) * (a.c0 / a.c2) = -W by
            field_simp; linear_combination hQ0) (IsIrreducibleQuartic.neg_not_square _)
    · by_cases hN : a.c1 * a.c1 - W * (a.c3 * a.c3) = 0
      · have ha3 : a.c3 ≠ 0 := by
          intro h3; rw [h3, mul_zero, mul_zero, sub_zero] at hN
          exact ha1 (mul_self_eq_zero.mp hN)
        exact absurd (show (a.c1 / a.c3) * (a.c1 / a.c3) = W by
          field_simp; linear_combination sub_eq_zero.mp hN)
          (IsIrreducibleQuartic.not_square _)
      · -- Identity 1: A^2 + W*B^2 = 0
        have heq_poly : (a.c0 * a.c1 - W * a.c2 * a.c3) *
            (a.c0 * a.c1 - W * a.c2 * a.c3) +
            W * ((a.c2 * a.c1 - a.c0 * a.c3) * (a.c2 * a.c1 - a.c0 * a.c3)) = 0 := by
          have h1 : a.c0 * a.c0 + W * a.c2 * a.c2 = 2 * W * a.c1 * a.c3 := by
            linear_combination hQ0
          have h2 : a.c1 * a.c1 + W * (a.c3 * a.c3) = 2 * a.c0 * a.c2 := by
            linear_combination -hQ2
          have h3 : (a.c0 * a.c0 + W * a.c2 * a.c2) * (a.c1 * a.c1 + W * (a.c3 * a.c3)) =
              4 * W * a.c0 * a.c1 * a.c2 * a.c3 := by rw [h1, h2]; ring
          linear_combination h3
        -- Identity 2: 2*A*B = N^2
        have heq_prod : 2 * (a.c0 * a.c1 - W * a.c2 * a.c3) *
            (a.c2 * a.c1 - a.c0 * a.c3) =
            (a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3)) := by
          linear_combination (-2 * a.c1 * a.c3) * hQ0 +
            (a.c1 * a.c1 + W * (a.c3 * a.c3)) * hQ2
        -- A /= 0
        have hA_ne : a.c0 * a.c1 - W * a.c2 * a.c3 ≠ 0 := by
          intro h0; simp only [h0, zero_mul, mul_zero] at heq_prod
          exact hN (mul_self_eq_zero.mp heq_prod.symm)
        -- 4A^4 + WN^4 = 0 via: 4A^2(A^2+WB^2) + W(N^4-(2AB)^2) = 0
        have key4 : 4 * (a.c0 * a.c1 - W * a.c2 * a.c3) ^ 2 *
            (a.c0 * a.c1 - W * a.c2 * a.c3) ^ 2 +
            W * ((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3))) *
            ((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3))) = 0 := by
          have step : 4 * (a.c0 * a.c1 - W * a.c2 * a.c3) ^ 2 *
              (a.c0 * a.c1 - W * a.c2 * a.c3) ^ 2 +
              W * ((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3))) *
              ((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3))) =
            4 * (a.c0 * a.c1 - W * a.c2 * a.c3) ^ 2 *
              ((a.c0 * a.c1 - W * a.c2 * a.c3) * (a.c0 * a.c1 - W * a.c2 * a.c3) +
              W * ((a.c2 * a.c1 - a.c0 * a.c3) * (a.c2 * a.c1 - a.c0 * a.c3))) +
            W * (((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3))) *
              ((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3))) -
              (2 * (a.c0 * a.c1 - W * a.c2 * a.c3) * (a.c2 * a.c1 - a.c0 * a.c3)) *
              (2 * (a.c0 * a.c1 - W * a.c2 * a.c3) * (a.c2 * a.c1 - a.c0 * a.c3))) := by ring
          rw [step, heq_poly, heq_prod]; ring
        -- (2A^2/N^2)^2 = -W
        have hNN := mul_ne_zero hN hN
        exact absurd (show (2 * (a.c0 * a.c1 - W * a.c2 * a.c3) ^ 2 /
            ((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3)))) *
            (2 * (a.c0 * a.c1 - W * a.c2 * a.c3) ^ 2 /
            ((a.c1 * a.c1 - W * (a.c3 * a.c3)) * (a.c1 * a.c1 - W * (a.c3 * a.c3)))) = -W by
          rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hNN hNN)]
          have := key4; linear_combination this) (IsIrreducibleQuartic.neg_not_square _)
  · exact absurd (show (q0 / q2) * (q0 / q2) = W by
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hq2 hq2)]
      linear_combination hsq) (IsIrreducibleQuartic.not_square _)

theorem zero_ne_one : (0 : Fp4 F W) ≠ 1 := by
  intro h; have := congr_arg Fp4.c0 h; simp at this

noncomputable def inv' [IsIrreducibleQuartic W] (a : Fp4 F W) : Fp4 F W :=
  if a = 0 then 0
  else
    let co := conjOdd a
    let p := a * co
    let pconj : Fp4 F W := ⟨p.c0, 0, -p.c2, 0⟩
    let n := norm a
    ⟨(co * pconj).c0 / n, (co * pconj).c1 / n,
     (co * pconj).c2 / n, (co * pconj).c3 / n⟩

noncomputable def div' [IsIrreducibleQuartic W] (a b : Fp4 F W) : Fp4 F W :=
  a * inv' b

theorem mul_inv_cancel' [IsIrreducibleQuartic W] (a : Fp4 F W) (ha : a ≠ 0) :
    a * inv' a = 1 := by
  have hn : norm a ≠ 0 := norm_ne_zero a ha
  unfold inv'; rw [if_neg ha]
  have hn' : norm a = (a.c0 * a.c0 + W * (a.c2 * a.c2 - 2 * a.c1 * a.c3)) *
      (a.c0 * a.c0 + W * (a.c2 * a.c2 - 2 * a.c1 * a.c3)) -
      W * ((2 * a.c0 * a.c2 - a.c1 * a.c1 - W * (a.c3 * a.c3)) *
           (2 * a.c0 * a.c2 - a.c1 * a.c1 - W * (a.c3 * a.c3))) := rfl
  ext
  all_goals simp only [mul_c0, mul_c1, mul_c2, mul_c3, one_c0, one_c1, one_c2, one_c3,
    conjOdd_c0, conjOdd_c1, conjOdd_c2, conjOdd_c3]
  all_goals (field_simp [show norm a ≠ 0 from hn]; rw [hn']; ring)

theorem inv_zero' [IsIrreducibleQuartic W] : inv' (0 : Fp4 F W) = 0 := by
  unfold inv'; rw [if_pos rfl]

noncomputable instance instField [IsIrreducibleQuartic W] : Field (Fp4 F W) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  inv := inv'
  mul_inv_cancel := fun a ha => mul_inv_cancel' a ha
  inv_zero := inv_zero'
  div := div'
  div_eq_mul_inv := fun _ _ => rfl
  zpow := fun n a =>
    if n ≥ 0 then Fp4.npow n.toNat a
    else inv' (Fp4.npow (-n).toNat a)
  zpow_zero' := fun _ => by
    simp only [ge_iff_le, le_refl, ↓reduceIte, Int.toNat_zero, Fp4.npow]; rfl
  zpow_succ' := fun n a => by
    simp only [ge_iff_le]
    rw [if_pos (Int.natCast_nonneg n.succ), if_pos (Int.natCast_nonneg n)]
    simp only [Int.toNat_natCast]
    show Fp4.npow (n + 1) a = Fp4.npow n a * a
    simp only [Fp4.npow]
    ext <;> simp [Fp4.mul] <;> ring
  zpow_neg' := fun n a => by
    simp only [ge_iff_le]
    rw [if_neg (Int.not_le.mpr (Int.negSucc_lt_zero n)),
        if_pos (Int.natCast_nonneg (n + 1))]
    simp only [Int.negSucc_eq, neg_neg, Int.toNat_natCast]; rfl
  nnratCast := fun q => div' (q.num : Fp4 F W) (q.den : Fp4 F W)
  nnratCast_def := fun _ => rfl
  nnqsmul := fun q a => div' (q.num : Fp4 F W) (q.den : Fp4 F W) * a
  nnqsmul_def := fun _ _ => rfl
  ratCast := fun q => div' (q.num : Fp4 F W) (q.den : Fp4 F W)
  ratCast_def := fun _ => rfl
  qsmul := fun q a => div' (q.num : Fp4 F W) (q.den : Fp4 F W) * a
  qsmul_def := fun _ _ => rfl

section SmokeTests

noncomputable example {F : Type*} [Field F] {W : F} [IsIrreducibleQuartic W] :
    Field (Fp4 F W) := inferInstance
example : CommRing (Fp4 Rat 2) := inferInstance
example : (u : Fp4 Rat 2) * u = ⟨0, 0, 1, 0⟩ := by ext <;> simp [u]
example : (u : Fp4 Rat 7) * u * u * u = ofBase 7 := u_pow4

end SmokeTests

end Fp4

end AmoLean.Field.ExtField
