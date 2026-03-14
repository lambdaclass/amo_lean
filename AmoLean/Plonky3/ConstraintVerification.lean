/-
  Constraint Verification — N20.2 (CRITICO)
  Decidable Bool checkers for constraint satisfaction
  with soundness/completeness proofs.
-/
import AmoLean.Plonky3.AIRConstraint

namespace AmoLean.Plonky3.ConstraintVerification

open AmoLean.Plonky3.AIRConstraint

-- ── Decidable checkers ────────────────────────────────────────────────

/-- Check if a single constraint is satisfied (decidable). -/
def checkConstraint [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (w : Witness F) : Bool :=
  evalExpr c.expr w == 0

/-- Check if all constraints in a system are satisfied. -/
def checkSystem [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (cs : ConstraintSystem F) (w : Witness F) : Bool :=
  cs.constraints.all (checkConstraint · w)

-- ── Soundness ─────────────────────────────────────────────────────────

/-- Soundness: if checkConstraint returns true, the constraint is satisfied. -/
theorem checkConstraint_sound [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (w : Witness F) (h : checkConstraint c w = true) :
    satisfies c w := by
  simp [checkConstraint, beq_iff_eq] at h
  exact h

/-- System soundness: if checkSystem returns true, all constraints are satisfied. -/
theorem checkSystem_sound [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (cs : ConstraintSystem F) (w : Witness F) (h : checkSystem cs w = true) :
    systemSatisfied cs w := by
  intro c hc
  simp [checkSystem, List.all_eq_true] at h
  simp [checkConstraint, beq_iff_eq] at h
  exact h c hc

-- ── Completeness ──────────────────────────────────────────────────────

/-- Completeness: if constraint is satisfied, checkConstraint returns true. -/
theorem checkConstraint_complete [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (w : Witness F) (h : satisfies c w) :
    checkConstraint c w = true := by
  simp [checkConstraint, beq_iff_eq, satisfies] at *
  exact h

/-- System completeness: if all constraints satisfied, checkSystem returns true. -/
theorem checkSystem_complete [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (cs : ConstraintSystem F) (w : Witness F) (h : systemSatisfied cs w) :
    checkSystem cs w = true := by
  simp [checkSystem, List.all_eq_true, checkConstraint, beq_iff_eq]
  intro c hc
  exact h c hc

-- ── Decidability iff ──────────────────────────────────────────────────

/-- Constraint checker is iff satisfaction. -/
theorem checkConstraint_iff [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (w : Witness F) :
    checkConstraint c w = true ↔ satisfies c w := by
  simp [checkConstraint, beq_iff_eq, satisfies]

/-- System checker is iff system satisfaction. -/
theorem checkSystem_iff [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (cs : ConstraintSystem F) (w : Witness F) :
    checkSystem cs w = true ↔ systemSatisfied cs w := by
  simp [checkSystem, List.all_eq_true, checkConstraint, beq_iff_eq,
        systemSatisfied, satisfies]

-- ── Decidability instance ─────────────────────────────────────────────

/-- Decidable instance for single constraint satisfaction. -/
instance instDecidableSatisfies [DecidableEq F] [Add F] [Mul F] [Neg F] [Sub F] [Zero F]
    (c : Constraint F) (w : Witness F) : Decidable (satisfies c w) :=
  if h : evalExpr c.expr w = 0 then isTrue h else isFalse h

-- ── Smoke tests over Int ──────────────────────────────────────────────

#eval checkConstraint (mulGate : Constraint Int)
  (fun | 0 => 3 | 1 => 7 | 2 => 21 | _ => 0)
-- Expected: true

#eval checkConstraint (mulGate : Constraint Int)
  (fun | 0 => 3 | 1 => 7 | 2 => 20 | _ => 0)
-- Expected: false

#eval checkSystem (⟨[mulGate, constGate 2 (6 : Int)], 3⟩ : ConstraintSystem Int)
  (fun | 0 => 2 | 1 => 3 | 2 => 6 | _ => 0)
-- Expected: true

#eval checkSystem (⟨[mulGate, constGate 2 (6 : Int)], 3⟩ : ConstraintSystem Int)
  (fun | 0 => 2 | 1 => 3 | 2 => 7 | _ => 0)
-- Expected: false

-- ── Non-vacuity examples ─────────────────────────────────────────────

/-- Non-vacuity: checkConstraint returns true for a satisfied mulGate. -/
example : checkConstraint (mulGate : Constraint Int)
    (fun | 0 => 3 | 1 => 7 | 2 => 21 | _ => 0) = true := by native_decide

/-- Non-vacuity: checkConstraint returns false for an unsatisfied mulGate. -/
example : checkConstraint (mulGate : Constraint Int)
    (fun | 0 => 3 | 1 => 7 | 2 => 20 | _ => 0) = false := by native_decide

/-- Non-vacuity: checkSystem returns true for a 2-constraint system. -/
example : checkSystem (⟨[mulGate, constGate 2 (6 : Int)], 3⟩ : ConstraintSystem Int)
    (fun | 0 => 2 | 1 => 3 | 2 => 6 | _ => 0) = true := by native_decide

/-- Non-vacuity: soundness + completeness compose (iff round-trip). -/
example : let c := (mulGate : Constraint Int)
    let w := fun | 0 => 3 | 1 => 7 | 2 => 21 | _ => 0
    satisfies c w ↔ checkConstraint c w = true :=
  (checkConstraint_iff _ _).symm

/-- Non-vacuity: system iff round-trip on concrete system. -/
example : let cs : ConstraintSystem Int := ⟨[mulGate, addGate], 3⟩
    let w := fun | 0 => 2 | 1 => 3 | 2 => 6 | 3 => 5 | _ => 0
    checkSystem cs w = true ↔ systemSatisfied cs w :=
  checkSystem_iff _ _

end AmoLean.Plonky3.ConstraintVerification
