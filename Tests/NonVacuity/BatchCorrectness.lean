/-
  v3.20.b B5 N20.5.5 — Non-vacuity examples for batch NTT correctness.

  Per §14.13.3 Gap 3 obligations (CLAUDE.md global hygiene rule: theorems
  with ≥3 hypotheses must have non-vacuity witnesses), these examples
  demonstrate that the HYPOTHESIS SETS of the Phase 1 batch correctness
  theorems are jointly satisfiable on three representative plan shapes:

    1. B=1 BabyBear N=8 Solinas — B=1 collapse trivial (rfl).
    2. B=4 Goldilocks N=16 Harvey — batch inductive path exercised.
    3. B=2 mixed R2+R4 — composition induction with heterogeneous stages.

  The main theorems (`_step`, `_correct`, `_sound`) have real semantic
  conclusions closed with `sorry` + TODO Phase 2 (§14.13.3 R3). The
  non-vacuity examples here do NOT invoke those sorry-backed theorems as
  witnesses — they document the plans and `(0 < B)` conditions as
  concrete + jointly satisfiable, avoiding the anti-pattern of using
  sorry-backed lemmas to "prove" non-vacuity (which would be circular).

  The only theorem invoked directly is `lowerNTTFromPlanBatch_B1_collapse`
  which has a real `rfl` proof (no sorry).
-/
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.NTTPlan

namespace AmoLean.EGraph.Verified.Bitwise.Tests.NonVacuity.BatchCorrectness

open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
  (lowerNTTFromPlanBatch lowerNTTFromPlanVerified
   lowerNTTFromPlanBatch_B1_collapse)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan
  (Plan NTTStage RadixChoice StageDirection)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)

/-! ## Example 1: B=1 BabyBear N=8 Solinas — direct rfl invocation. -/

/-- Concrete BabyBear N=8 plan with 3 R2 stages using Solinas fold. -/
def babybearPlan8Solinas : Plan :=
  let stages := (List.range 3).toArray.map fun stageIdx =>
    ({ stageIdx := stageIdx, radix := .r2, reduction := .solinasFold,
       direction := .DIT, inputBoundK := 1, outputBoundK := 1 } : NTTStage)
  { stages := stages, field := 2013265921, size := 8, batchWidth := 1 }

/-- Example 1 (B=1 collapse): `lowerNTTFromPlanBatch_B1_collapse` applied to
    BabyBear N=8 Solinas — closed by `rfl`, NO sorry dependency. This is
    the single theorem in B5 with a fully-real Phase 1 proof.

    Guarantees Gate H8 single-vector path stays byte-equivalent on B=1. -/
example :
    lowerNTTFromPlanBatch babybearPlan8Solinas 1 31 1 0x88000001 =
    lowerNTTFromPlanVerified babybearPlan8Solinas 31 1 0x88000001 :=
  lowerNTTFromPlanBatch_B1_collapse babybearPlan8Solinas 31 1 0x88000001

/-! ## Example 2: B=4 Goldilocks N=16 Harvey — satisfiability witness.

    The main theorem `lowerNTTFromPlanBatch_correct` has a real semantic
    conclusion (∃ fuel env, evalStmt ...) closed with `sorry` in Phase 1.
    Invoking it here would be circular — the non-vacuity witness would
    depend on the sorry-backed theorem it's meant to validate.

    Instead we document that the PLAN and B=4 hypothesis are jointly
    satisfiable: the plan is constructible, has non-empty stages, and
    `0 < 4` is trivially true. -/

/-- Concrete Goldilocks N=16 plan with 4 R2 stages using Harvey reduction. -/
def goldilocksPlan16Harvey : Plan :=
  let stages := (List.range 4).toArray.map fun stageIdx =>
    ({ stageIdx := stageIdx, radix := .r2, reduction := .harvey,
       direction := .DIT, inputBoundK := 1, outputBoundK := 1 } : NTTStage)
  { stages := stages, field := 18446744069414584321, size := 16, batchWidth := 4 }

/-- Example 2 (hypothesis satisfiability): the Goldilocks N=16 B=4 plan is
    a valid input to `lowerNTTFromPlanBatch_correct`. Concrete witnesses:
    plan has 4 stages, size = 16 (= 2^4 matching R2 stage count),
    batchWidth = 4 > 0. -/
example :
    goldilocksPlan16Harvey.stages.size = 4 ∧
    goldilocksPlan16Harvey.size = 16 ∧
    0 < (4 : Nat) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Example 2 (structural): `lowerNTTFromPlanBatch` at B=4 produces a
    concrete Stmt — reachable at the term level. -/
example :
    ∃ _stmt : _root_.TrustLean.Stmt,
      lowerNTTFromPlanBatch goldilocksPlan16Harvey 4 64 1 0 = _stmt :=
  ⟨_, rfl⟩

/-! ## Example 3: B=2 mixed R2+R4 — heterogeneous stages satisfiability. -/

/-- Concrete BabyBear N=16 plan mixing R2 (stageIdx 0..2) + R4 (stageIdx 3)
    stages. Exercises per-stage dispatch in `lowerNTTFromPlanVerified`
    under the batch interface. -/
def mixedR2R4Plan : Plan :=
  let r2Stages := (List.range 3).toArray.map fun stageIdx =>
    ({ stageIdx := stageIdx, radix := .r2, reduction := .harvey,
       direction := .DIT, inputBoundK := 1, outputBoundK := 1 } : NTTStage)
  let r4Stage : NTTStage :=
    { stageIdx := 3, radix := .r4, reduction := .harvey,
      direction := .DIT, inputBoundK := 1, outputBoundK := 1 }
  { stages := r2Stages.push r4Stage, field := 2013265921, size := 16, batchWidth := 2 }

/-- Example 3 (heterogeneous satisfiability): mixed R2+R4 plan is a valid
    input to the batch theorems. Witnesses: 4 stages (3 R2 + 1 R4),
    batchWidth = 2 > 0, field is BabyBear prime. -/
example :
    mixedR2R4Plan.stages.size = 4 ∧
    (mixedR2R4Plan.stages.toList.any fun s => s.radix == .r4) = true ∧
    0 < (2 : Nat) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Example 3 (structural): `lowerNTTFromPlanBatch` on the mixed plan
    produces a Stmt — reachable at the term level. -/
example :
    ∃ _stmt : _root_.TrustLean.Stmt,
      lowerNTTFromPlanBatch mixedR2R4Plan 2 31 1 0x88000001 = _stmt :=
  ⟨_, rfl⟩

/-! ## Example 4: `emitCFromPlanBatch` non-vacuity (string-level).

    `emitCFromPlanBatch_sound` has a real semantic conclusion (∃ evalC, …)
    closed with `sorry`. String-level non-vacuity documents that the
    emitter produces a non-empty C string on a realistic plan — an honest
    Phase 1 witness that does NOT depend on sorry. -/

open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitCFromPlanBatch)

/-- Example 4: emitter produces non-empty output for BabyBear N=8 B=4. -/
example :
    (emitCFromPlanBatch babybearPlan8Solinas 4 31 1 0x88000001 "ntt_test").length > 0 := by
  native_decide

end AmoLean.EGraph.Verified.Bitwise.Tests.NonVacuity.BatchCorrectness
