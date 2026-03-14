/-
  AMO-Lean: Fp2 Quadratic Extension Field
  N18.1 (FUNDACIONAL) — Fp2 Extension Field Definition + CommRing

  Defines a quadratic extension field Fp2 = F[u]/(u^2 - W) where W is a
  non-residue in the base field F.

  Elements are pairs (c0, c1) representing c0 + c1 * u where u^2 = W.
  Operations:
  - Addition: componentwise
  - Multiplication: (a0 + a1*u)(b0 + b1*u) = (a0*b0 + W*a1*b1) + (a0*b1 + a1*b0)*u
  - Negation: componentwise
  - CommRing axioms proved directly via ext + ring on F-components

  Design: W is baked into the type via a parameter, making Fp2 F W a distinct
  type for each choice of non-residue. This is essential for BabyBear (W=11)
  vs Mersenne31 (W=TBD).

  0 sorry, 0 axioms.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.Rat

namespace AmoLean.Field.ExtField

/-! ## Part 1: Structure Definition -/

/-- Quadratic extension field: F[u]/(u^2 - W).
    Elements are pairs (c0, c1) representing c0 + c1 * u where u^2 = W. -/
structure Fp2 (F : Type*) [Field F] (W : F) where
  /-- Real part (coefficient of 1) -/
  c0 : F
  /-- Imaginary part (coefficient of u) -/
  c1 : F
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] {W : F}

namespace Fp2

/-! ## Part 2: Extensionality -/

/-- Extensionality: two Fp2 elements are equal iff both components are equal. -/
@[ext]
theorem ext {a b : Fp2 F W} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

/-! ## Part 3: Ring Operations -/

/-- Zero element: 0 + 0*u -/
protected def zero : Fp2 F W := ⟨0, 0⟩

/-- One element: 1 + 0*u -/
protected def one : Fp2 F W := ⟨1, 0⟩

/-- Addition (componentwise): (a0 + a1*u) + (b0 + b1*u) = (a0+b0) + (a1+b1)*u -/
protected def add (a b : Fp2 F W) : Fp2 F W := ⟨a.c0 + b.c0, a.c1 + b.c1⟩

/-- Negation (componentwise): -(a0 + a1*u) = (-a0) + (-a1)*u -/
protected def neg (a : Fp2 F W) : Fp2 F W := ⟨-a.c0, -a.c1⟩

/-- Subtraction (componentwise): (a0 + a1*u) - (b0 + b1*u) = (a0-b0) + (a1-b1)*u -/
protected def sub (a b : Fp2 F W) : Fp2 F W := ⟨a.c0 - b.c0, a.c1 - b.c1⟩

/-- Multiplication using the relation u^2 = W:
    (a0 + a1*u)(b0 + b1*u) = (a0*b0 + W*a1*b1) + (a0*b1 + a1*b0)*u -/
protected def mul (a b : Fp2 F W) : Fp2 F W :=
  ⟨a.c0 * b.c0 + W * (a.c1 * b.c1), a.c0 * b.c1 + a.c1 * b.c0⟩

/-- Natural number power (by repeated squaring). -/
protected def npow : Nat → Fp2 F W → Fp2 F W
  | 0, _ => Fp2.one
  | n + 1, a => Fp2.mul a (Fp2.npow n a)

/-- Natural number cast: embed n as (n : F) + 0*u -/
protected def natCast (n : Nat) : Fp2 F W := ⟨(n : F), 0⟩

/-- Integer cast: embed z as (z : F) + 0*u -/
protected def intCast (z : Int) : Fp2 F W := ⟨(z : F), 0⟩

/-! ## Part 4: Basic Typeclass Instances -/

instance : Zero (Fp2 F W) := ⟨Fp2.zero⟩
instance : One (Fp2 F W) := ⟨Fp2.one⟩
instance : Add (Fp2 F W) := ⟨Fp2.add⟩
instance : Neg (Fp2 F W) := ⟨Fp2.neg⟩
instance : Sub (Fp2 F W) := ⟨Fp2.sub⟩
instance : Mul (Fp2 F W) := ⟨Fp2.mul⟩
instance : NatCast (Fp2 F W) := ⟨Fp2.natCast⟩
instance : IntCast (Fp2 F W) := ⟨Fp2.intCast⟩

instance : Inhabited (Fp2 F W) := ⟨0⟩

/-! ## Part 5: Simp Lemmas for Component Access -/

@[simp] theorem zero_c0 : (0 : Fp2 F W).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2 F W).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2 F W).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2 F W).c1 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp2 F W) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2 F W) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2 F W) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2 F W) : (-a).c1 = -a.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp2 F W) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp2 F W) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2 F W) : (a * b).c0 = a.c0 * b.c0 + W * (a.c1 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : Fp2 F W) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl
@[simp] theorem natCast_c0 (n : Nat) : (n : Fp2 F W).c0 = (n : F) := rfl
@[simp] theorem natCast_c1 (n : Nat) : (n : Fp2 F W).c1 = 0 := rfl
@[simp] theorem intCast_c0 (z : Int) : (z : Fp2 F W).c0 = (z : F) := rfl
@[simp] theorem intCast_c1 (z : Int) : (z : Fp2 F W).c1 = 0 := rfl

/-! ## Part 6: CommRing Instance

    Strategy: prove each axiom by `ext` which reduces to two goals on F,
    then close each with `simp` + `ring`. Since F is a Field, `ring` handles
    all polynomial identities on the components. -/

instance instCommRing : CommRing (Fp2 F W) where
  add_assoc := fun a b c => by ext <;> simp [add_assoc]
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp [add_comm]
  neg := Fp2.neg
  neg_add_cancel := fun a => by
    show Fp2.add (Fp2.neg a) a = Fp2.zero
    cases a; simp [Fp2.add, Fp2.neg, Fp2.zero, neg_add_cancel]
  sub := Fp2.sub
  sub_eq_add_neg := fun a b => by
    show Fp2.sub a b = Fp2.add a (Fp2.neg b)
    cases a; cases b; simp [Fp2.sub, Fp2.add, Fp2.neg, sub_eq_add_neg]
  nsmul := fun n a => ⟨n • a.c0, n • a.c1⟩
  nsmul_zero := fun a => by ext <;> simp
  nsmul_succ := fun n a => by ext <;> simp [add_mul, add_comm]
  zsmul := fun z a => ⟨z • a.c0, z • a.c1⟩
  zsmul_zero' := fun a => by ext <;> simp
  zsmul_succ' := fun n a => by ext <;> simp [add_mul, add_comm]
  zsmul_neg' := fun n a => by
    show (⟨Int.negSucc n • a.c0, Int.negSucc n • a.c1⟩ : Fp2 F W) =
         Fp2.neg ⟨(↑(n + 1) : Int) • a.c0, (↑(n + 1) : Int) • a.c1⟩
    simp only [Fp2.neg, negSucc_zsmul, Nat.cast_succ, ← natCast_zsmul]
  mul_assoc := fun a b c => by ext <;> simp <;> ring
  one_mul := fun a => by ext <;> simp
  mul_one := fun a => by ext <;> simp
  mul_comm := fun a b => by ext <;> simp <;> ring
  left_distrib := fun a b c => by ext <;> simp <;> ring
  right_distrib := fun a b c => by ext <;> simp <;> ring
  zero_mul := fun a => by ext <;> simp
  mul_zero := fun a => by ext <;> simp
  natCast := Fp2.natCast
  natCast_zero := by
    show Fp2.natCast 0 = Fp2.zero
    simp [Fp2.natCast, Fp2.zero, Nat.cast_zero]
  natCast_succ := fun n => by
    show Fp2.natCast (n + 1) = Fp2.add (Fp2.natCast n) Fp2.one
    simp [Fp2.natCast, Fp2.add, Fp2.one, Nat.cast_succ]
  intCast := Fp2.intCast
  intCast_ofNat := fun n => by
    show Fp2.intCast (↑n) = Fp2.natCast n
    simp [Fp2.intCast, Fp2.natCast, Int.cast_natCast]
  intCast_negSucc := fun n => by
    show Fp2.intCast (Int.negSucc n) = Fp2.neg (Fp2.natCast (n + 1))
    simp [Fp2.intCast, Fp2.neg, Fp2.natCast, Int.cast_negSucc]
  npow := fun n a => Fp2.npow n a
  npow_zero := fun a => by
    show Fp2.npow 0 a = 1
    rfl
  npow_succ := fun n a => by
    show Fp2.npow (n + 1) a = Fp2.mul (Fp2.npow n a) a
    simp only [Fp2.npow]
    cases a; simp [Fp2.mul]; constructor <;> ring

/-! ## Part 7: Embedding from Base Field -/

/-- Embed a base field element into Fp2 as c + 0*u. -/
def ofBase (c : F) : Fp2 F W := ⟨c, 0⟩

/-- The imaginary unit u, satisfying u^2 = W. -/
def u : Fp2 F W := ⟨0, 1⟩

/-- Every Fp2 element decomposes as ofBase c0 + ofBase c1 * u. -/
theorem decompose (a : Fp2 F W) : a = ofBase a.c0 + ofBase a.c1 * u := by
  ext <;> simp [ofBase, u]

/-- u^2 = W (the defining relation of the extension). -/
theorem u_sq : (u : Fp2 F W) * u = ofBase W := by
  ext <;> simp [u, ofBase]

/-- ofBase preserves zero. -/
theorem ofBase_zero : ofBase (0 : F) = (0 : Fp2 F W) := by
  ext <;> simp [ofBase]

/-- ofBase preserves one. -/
theorem ofBase_one : ofBase (1 : F) = (1 : Fp2 F W) := by
  ext <;> simp [ofBase]

/-- ofBase preserves addition. -/
theorem ofBase_add (a b : F) : ofBase (a + b) = (ofBase a : Fp2 F W) + ofBase b := by
  ext <;> simp [ofBase]

/-- ofBase preserves multiplication. -/
theorem ofBase_mul (a b : F) : ofBase (a * b) = (ofBase a : Fp2 F W) * ofBase b := by
  ext <;> simp [ofBase]

/-- ofBase preserves negation. -/
theorem ofBase_neg (a : F) : ofBase (-a) = -(ofBase a : Fp2 F W) := by
  ext <;> simp [ofBase]

/-- ofBase is injective. -/
theorem ofBase_injective : Function.Injective (ofBase : F → Fp2 F W) := by
  intro a b h
  have := congr_arg Fp2.c0 h
  simpa [ofBase] using this

/-! ## Part 8: Conjugation and Norm -/

/-- Conjugation: swap sign of imaginary part.
    conj(c0 + c1*u) = c0 - c1*u -/
def conj (a : Fp2 F W) : Fp2 F W := ⟨a.c0, -a.c1⟩

/-- Norm: a * conj(a) = c0^2 - W*c1^2 (lives in the base field). -/
def norm (a : Fp2 F W) : F := a.c0 * a.c0 - W * (a.c1 * a.c1)

/-- a * conj(a) = ofBase(norm(a)). -/
theorem mul_conj (a : Fp2 F W) : a * conj a = ofBase (norm a) := by
  ext <;> simp [conj, norm, ofBase] <;> ring

/-- conj(a) * a = ofBase(norm(a)). -/
theorem conj_mul (a : Fp2 F W) : conj a * a = ofBase (norm a) := by
  ext <;> simp [conj, norm, ofBase] <;> ring

/-- Conjugation is an involution. -/
theorem conj_conj (a : Fp2 F W) : conj (conj a) = a := by
  ext <;> simp [conj]

/-- Norm of zero is zero. -/
theorem norm_zero : norm (0 : Fp2 F W) = 0 := by simp [norm]

/-- Norm of one is one. -/
theorem norm_one : norm (1 : Fp2 F W) = 1 := by simp [norm, sub_zero]

/-! ## Part 9: Smoke Tests (Computable over Rat) -/

section SmokeTests

-- Use Rat as a concrete computable field for testing.
-- W = -1 gives the Gaussian rationals Q[i] where i^2 = -1.

/-- 0 + 0 = 0 in Fp2 Rat (-1). -/
example : (0 : Fp2 Rat (-1)) + 0 = 0 := by ext <;> simp

/-- 1 * 1 = 1 in Fp2 Rat (-1). -/
example : (1 : Fp2 Rat (-1)) * 1 = 1 := by ext <;> simp

/-- (1 + u) * (1 - u) = 1 - u^2 = 1 - (-1) = 2 in Q[i]. -/
example : (⟨1, 1⟩ : Fp2 Rat (-1)) * ⟨1, -1⟩ = ⟨2, 0⟩ := by
  ext
  · simp; norm_num
  · simp

/-- (1 + u)^2 = 1 + 2u + u^2 = 1 + 2u + (-1) = 2u in Q[i]. -/
example : (⟨1, 1⟩ : Fp2 Rat (-1)) * ⟨1, 1⟩ = ⟨0, 2⟩ := by
  ext
  · simp
  · simp; norm_num

/-- norm(1 + u) = 1 - (-1)*1 = 2 in Q[i]. -/
example : norm (⟨1, 1⟩ : Fp2 Rat (-1)) = 2 := by simp [norm]; ring

/-- u^2 = W: the defining relation holds for W = 3. -/
example : (u : Fp2 Rat 3) * u = ofBase 3 := u_sq

/-- Addition is componentwise. -/
example : (⟨2, 3⟩ : Fp2 Rat 5) + ⟨4, 7⟩ = ⟨6, 10⟩ := by ext <;> simp <;> norm_num

/-- Multiplication with W = 5: (2 + 3u)(4 + 7u) = (8 + 5*21) + (14 + 12)u = 113 + 26u. -/
example : (⟨2, 3⟩ : Fp2 Rat 5) * ⟨4, 7⟩ = ⟨113, 26⟩ := by ext <;> simp <;> norm_num

end SmokeTests

end Fp2

end AmoLean.Field.ExtField
