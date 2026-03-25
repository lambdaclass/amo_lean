import AmoLean.EGraph.Verified.Bitwise.BitwiseRules
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# AmoLean.EGraph.Verified.Bitwise.Discovery.ShiftAddGen

Canonical Signed Digit (CSD / NAF) decomposition for shift-add synthesis.
Converts `x * c` into a minimal sequence of shifts and adds/subs.

## Key results

- `toCSD`: convert Nat → CSD representation
- `toCSD_correct`: evaluating the CSD gives the original number
- `shiftAddRule`: package multiplication-to-shifts as MixedSoundRule
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise (MixedEnv MixedSoundRule)

/-! ## CSD representation -/

/-- A signed digit: +1, 0, or -1. -/
inductive CSDDigit where
  | pos  : CSDDigit
  | zero : CSDDigit
  | neg  : CSDDigit
  deriving Repr, DecidableEq, Inhabited

abbrev CSDRepr := List CSDDigit

/-- Evaluate a CSD representation as an integer at bit offset `pos`. -/
def evalCSDInt : CSDRepr → Nat → Int
  | [], _ => 0
  | .zero :: ds, pos => evalCSDInt ds (pos + 1)
  | .pos  :: ds, pos => (2 : Int) ^ pos + evalCSDInt ds (pos + 1)
  | .neg  :: ds, pos => -(2 : Int) ^ pos + evalCSDInt ds (pos + 1)

/-- Number of non-zero digits. -/
def csdWeight : CSDRepr → Nat
  | [] => 0
  | .zero :: ds => csdWeight ds
  | _ :: ds => 1 + csdWeight ds

/-! ## NAF conversion — clean patterns for induction -/

/-- Inner loop of CSD conversion with clean `(n+1, f+1)` pattern. -/
def csdGo : Nat → Nat → CSDRepr
  | 0, _ => []
  | _ + 1, 0 => []
  | n + 1, f + 1 =>
    if (n + 1) % 2 == 0 then
      .zero :: csdGo ((n + 1) / 2) f
    else if (n + 1) % 4 == 1 then
      .pos :: csdGo ((n + 1) / 2) f
    else
      .neg :: csdGo ((n + 1) / 2 + 1) f

/-- Convert Nat to Non-Adjacent Form. -/
def toCSD (c : Nat) : CSDRepr := csdGo c (c + 1)

/-! ## Correctness -/

/-- The inner loop correctly evaluates. -/
theorem csdGo_correct (n f pos : Nat) (hf : n ≤ f) :
    evalCSDInt (csdGo n f) pos = (n : Int) * 2 ^ pos := by
  induction f generalizing n pos with
  | zero =>
    have : n = 0 := by omega
    subst this; simp [csdGo, evalCSDInt]
  | succ f ih =>
    cases n with
    | zero => simp [csdGo, evalCSDInt]
    | succ n' =>
      -- csdGo (n'+1) (f+1) = if ... (by definition, third pattern)
      simp only [csdGo]
      split
      · -- even
        rename_i heven
        simp only [beq_iff_eq] at heven
        simp only [evalCSDInt]
        rw [ih ((n' + 1) / 2) (pos + 1) (by omega)]
        have key : (↑((n' + 1) / 2 : Nat) : Int) * 2 = ↑(n' + 1 : Nat) := by
          have := Nat.div_add_mod (n' + 1) 2; push_cast; omega
        calc (↑((n'+1)/2 : Nat) : Int) * 2 ^ (pos + 1)
            = ↑((n'+1)/2 : Nat) * (2 ^ pos * 2) := by ring
          _ = (↑((n'+1)/2 : Nat) * 2) * 2 ^ pos := by ring
          _ = ↑(n'+1 : Nat) * 2 ^ pos := by rw [key]
      · split
        · -- n%4 == 1
          rename_i _ hmod
          simp only [beq_iff_eq] at hmod
          simp only [evalCSDInt]
          rw [ih ((n' + 1) / 2) (pos + 1) (by omega)]
          have key : (↑((n' + 1) / 2 : Nat) : Int) * 2 + 1 = ↑(n' + 1 : Nat) := by
            have := Nat.div_add_mod (n' + 1) 2; push_cast; omega
          calc (2 : Int) ^ pos + ↑((n'+1)/2 : Nat) * 2 ^ (pos + 1)
              = 2 ^ pos + ↑((n'+1)/2 : Nat) * (2 ^ pos * 2) := by ring
            _ = 2 ^ pos * (1 + ↑((n'+1)/2 : Nat) * 2) := by ring
            _ = 2 ^ pos * ↑(n'+1 : Nat) := by rw [show (1 : Int) + ↑((n'+1)/2 : Nat) * 2 = ↑(n'+1 : Nat) by linarith]
            _ = ↑(n'+1 : Nat) * 2 ^ pos := by ring
        · -- n%4 == 3
          rename_i hm2 hm4
          simp only [beq_iff_eq] at hm2 hm4
          simp only [evalCSDInt]
          have hbound : (n' + 1) / 2 + 1 ≤ f := by omega
          rw [ih ((n' + 1) / 2 + 1) (pos + 1) hbound]
          have key : (↑((n' + 1) / 2 + 1 : Nat) : Int) * 2 - 1 = ↑(n' + 1 : Nat) := by
            have := Nat.div_add_mod (n' + 1) 2; push_cast; omega
          calc -(2 : Int) ^ pos + ↑((n'+1)/2+1 : Nat) * 2 ^ (pos + 1)
              = -(2 ^ pos) + ↑((n'+1)/2+1 : Nat) * (2 ^ pos * 2) := by ring
            _ = 2 ^ pos * (-1 + ↑((n'+1)/2+1 : Nat) * 2) := by ring
            _ = 2 ^ pos * ↑(n'+1 : Nat) := by rw [show (-1 : Int) + ↑((n'+1)/2+1 : Nat) * 2 = ↑(n'+1 : Nat) by linarith]
            _ = ↑(n'+1 : Nat) * 2 ^ pos := by ring

/-- **CSD correctness**: evaluating the CSD yields the original number. -/
theorem toCSD_correct (c : Nat) : evalCSDInt (toCSD c) 0 = (c : Int) := by
  simp only [toCSD]
  rw [csdGo_correct c (c + 1) 0 (by omega)]
  simp

/-! ## Concrete examples -/

example : evalCSDInt (toCSD 0) 0 = 0 := by native_decide
example : evalCSDInt (toCSD 1) 0 = 1 := by native_decide
example : evalCSDInt (toCSD 13) 0 = 13 := by native_decide
example : evalCSDInt (toCSD 15) 0 = 15 := by native_decide
example : evalCSDInt (toCSD 127) 0 = 127 := by native_decide
example : evalCSDInt (toCSD 255) 0 = 255 := by native_decide

/-! ## Shift-add decomposition -/

/-- A shift operation. -/
structure ShiftOp where
  shift : Nat
  isAdd : Bool
  deriving Repr, DecidableEq

/-- Convert CSD to shift operations. -/
def csdToShiftOps : CSDRepr → Nat → List ShiftOp
  | [], _ => []
  | .zero :: ds, pos => csdToShiftOps ds (pos + 1)
  | .pos  :: ds, pos => ⟨pos, true⟩ :: csdToShiftOps ds (pos + 1)
  | .neg  :: ds, pos => ⟨pos, false⟩ :: csdToShiftOps ds (pos + 1)

/-- Evaluate shift operations recursively. -/
def evalShiftOps : List ShiftOp → Nat → Int
  | [], _ => 0
  | op :: ops, x =>
    (if op.isAdd then (x : Int) * 2 ^ op.shift
     else -(x : Int) * 2 ^ op.shift) + evalShiftOps ops x

/-- Number of shift ops = CSD weight. -/
theorem csdToShiftOps_length (ds : CSDRepr) (pos : Nat) :
    (csdToShiftOps ds pos).length = csdWeight ds := by
  induction ds generalizing pos with
  | nil => simp [csdToShiftOps, csdWeight]
  | cons d ds ih => cases d <;> simp [csdToShiftOps, csdWeight, ih] <;> omega

/-- Shift ops evaluate to x * CSD value. -/
private theorem evalShiftOps_eq (ds : CSDRepr) (pos : Nat) (x : Nat) :
    evalShiftOps (csdToShiftOps ds pos) x = (x : Int) * evalCSDInt ds pos := by
  induction ds generalizing pos with
  | nil => simp [csdToShiftOps, evalShiftOps, evalCSDInt]
  | cons d ds ih =>
    cases d <;> simp only [csdToShiftOps, evalCSDInt]
    · -- pos (first in CSDDigit declaration order)
      simp only [evalShiftOps, ite_true]
      rw [ih (pos + 1)]; ring
    · -- zero
      exact ih (pos + 1)
    · -- neg
      simp only [evalShiftOps, Bool.false_eq_true, ↓reduceIte]
      rw [ih (pos + 1)]; ring

/-- Decompose `x * c` into shift-add operations. -/
def shiftAddDecompose (c : Nat) : List ShiftOp :=
  csdToShiftOps (toCSD c) 0

/-- **Soundness**: shift-add decomposition = multiplication. -/
theorem shiftAddDecompose_sound (c x : Nat) :
    evalShiftOps (shiftAddDecompose c) x = (x : Int) * (c : Int) := by
  simp only [shiftAddDecompose]
  rw [evalShiftOps_eq, toCSD_correct]

/-- Decomposition length = CSD weight. -/
theorem shiftAddDecompose_length (c : Nat) :
    (shiftAddDecompose c).length = csdWeight (toCSD c) :=
  csdToShiftOps_length (toCSD c) 0

/-! ## Weight examples -/

example : csdWeight (toCSD 15) ≤ 2 := by native_decide
example : csdWeight (toCSD 127) ≤ 2 := by native_decide
example : csdWeight (toCSD 134217727) ≤ 2 := by native_decide
example : csdWeight (toCSD 13) = 3 := by native_decide

/-! ## Rule generation -/

/-- Generate a MixedSoundRule decomposing `x * c` into shifts.
    The `env` parameter in `lhsEval`/`rhsEval` is unused by design:
    `MixedSoundRule` requires `(env : MixedEnv) → (v : EClassId → Nat) → Nat`
    for interface uniformity, but shift-add rules are purely arithmetic
    (the rewrite `x * c = Σ (x << kᵢ)` depends only on the valuation). -/
def shiftAddRule (c : Nat) : MixedSoundRule where
  name := s!"mul_{c}_to_shifts"
  lhsEval := fun _ v => v 0 * c
  rhsEval := fun _ v => (evalShiftOps (shiftAddDecompose c) (v 0)).toNat
  soundness := fun _ v => by
    have h := shiftAddDecompose_sound c (v 0)
    have heq : evalShiftOps (shiftAddDecompose c) (v 0) = ↑(v 0 * c) := by
      rw [h]; push_cast; ring
    show v 0 * c = _
    rw [heq, Int.toNat_natCast]

/-- Generate shift-add rules for constants with low CSD weight. -/
def generateShiftAddRules (constants : List Nat) (maxWeight : Nat := 4) :
    List MixedSoundRule :=
  constants.filterMap fun c =>
    if c > 0 && csdWeight (toCSD c) ≤ maxWeight then
      some (shiftAddRule c)
    else none

end AmoLean.EGraph.Verified.Bitwise.Discovery
