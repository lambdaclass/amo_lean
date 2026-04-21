/-
  v3.20.b B4.5 N20.45.2: Packed batch NTT C emission driver.

  Calls `emitCFromPlanBatch_Packed` (SIMDEmitter.lean B4.5 N20.45.2) and
  writes the result to stdout. This is the packed-dispatch counterpart of
  emit_batch_code.lean (B4 scalar loop wrapping): same CLI, different
  underlying emitter.

  Usage:
    lake env lean Tests/benchmark/emit_packed_batch.lean -- <field> <logN> <B>
  Example:
    lake env lean Tests/benchmark/emit_packed_batch.lean -- babybear 6 4
-/
import AmoLean.EGraph.Verified.Bitwise.SIMDEmitter
import AmoLean.EGraph.Verified.Bitwise.NTTPlan
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen

open AmoLean.EGraph.Verified.Bitwise.SIMDEmitter
  (emitCFromPlanBatch_Packed shouldUsePackedPath)
open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitCFromPlanBatch)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan
  (Plan NTTStage RadixChoice StageDirection)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)

/-- Simple uniform R2 Harvey plan for N = 2^logN with the given field prime. -/
def mkHarveyPlan (p n logN : Nat) : Plan :=
  let stages := (List.range logN).toArray.map fun stageIdx =>
    ({ stageIdx := stageIdx, radix := .r2, reduction := .solinasFold,
       direction := .DIT, inputBoundK := 1, outputBoundK := 1
     } : NTTStage)
  { stages := stages, field := p, size := n }

def main (args : List String) : IO Unit := do
  match args with
  | [field, logNStr, bStr] =>
    let p : Nat := match field with
      | "babybear"   => 2013265921
      | _ => 0
    if p == 0 then IO.eprintln s!"Unsupported field for packed path: {field}"; return
    let some logN := logNStr.toNat?
      | IO.eprintln s!"Invalid logN: {logNStr}"; return
    let some B := bStr.toNat?
      | IO.eprintln s!"Invalid batchWidth: {bStr}"; return
    let n := 2 ^ logN
    let plan := mkHarveyPlan p n logN
    -- BabyBear Solinas fold constants: k=31, c=2^31-p=134217727, mu=Montgomery
    let (k, c, mu) : Nat × Nat × Nat := (31, 134217727, 0x88000001)
    let funcName := s!"{field}_ntt_batch_packed"
    -- Guard: packed path only applicable when shouldUsePackedPath returns true.
    if ¬ (shouldUsePackedPath plan B k) then
      IO.eprintln s!"Plan not packed-eligible (B={B}, k={k}, field={field}), emitting loop-wrap fallback"
      IO.println (emitCFromPlanBatch plan B k c mu funcName)
    else
      let packedC := emitCFromPlanBatch_Packed plan B k c mu funcName
      IO.println packedC
      IO.eprintln s!"/* emit_packed_batch: field={field} logN={logN} N={n} B={B} */"
      IO.eprintln s!"/* emission length: {packedC.length} bytes */"
  | _ =>
    IO.eprintln "Usage: emit_packed_batch <field> <logN> <B>"
    IO.eprintln "  field: babybear (only supported field in Phase 1)"
    IO.eprintln "  logN:  4 | 6 | 8 | ... (need log2(N) >= 3 for halfSize>=4 stages)"
    IO.eprintln "  B:     batch width (must be multiple of 4; B=4,8,16,...)"
