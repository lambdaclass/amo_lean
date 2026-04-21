/-
  v3.20.b B4 N20.4.3/4.5: Minimal batch-NTT C emission driver.

  Emits the Phase 1 additive-bridge batch wrapper via `emitCFromPlanBatch`
  around the existing single-vector `emitCFromPlanStandard`. Takes a field,
  logN, and batch width; writes a runnable C file to stdout that:
    - defines `{fc.name}_ntt_single(data, twiddles)` (single-vector NTT)
    - defines `{fc.name}_ntt_batch(data_base, twiddles, B)` (batch wrapper)
    - includes a minimal `main` that validates batch[b] = single-vector of input[b*N..]
      for all `b ∈ [0, B)` using a trivially-deterministic input/twiddle stub.

  This is a sidecar — does NOT modify any TRZK file. Gate B4 correctness witness.

  Usage:
    lake env lean Tests/benchmark/emit_batch_code.lean -- <field> <logN> <B>
  Example:
    lake env lean Tests/benchmark/emit_batch_code.lean -- babybear 6 4
-/
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.NTTPlan

open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitCFromPlanBatch)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice StageDirection)
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
      | "koalabear"  => 2130706433
      | "mersenne31" => 2147483647
      | "goldilocks" => 18446744069414584321
      | _ => 0
    if p == 0 then IO.eprintln s!"Unknown field: {field}"; return
    let some logN := logNStr.toNat?
      | IO.eprintln s!"Invalid logN: {logNStr}"; return
    let some B := bStr.toNat?
      | IO.eprintln s!"Invalid batchWidth: {bStr}"; return
    let n := 2 ^ logN
    let plan := mkHarveyPlan p n logN
    -- BabyBear Solinas fold parameters (k=31, c=1, mu=0x88000001).
    let (k, c, mu) : Nat × Nat × Nat :=
      if field == "goldilocks" then (64, 1, 0) else (31, 134217727, 0x88000001)
    let funcName := s!"{field}_ntt_batch"
    let batchC := emitCFromPlanBatch plan B k c mu funcName
    IO.println batchC
    IO.eprintln s!"/* emit_batch_code: field={field} logN={logN} N={n} B={B} */"
    IO.eprintln s!"/* emission length: {batchC.length} bytes */"
  | _ =>
    IO.eprintln "Usage: emit_batch_code <field> <logN> <B>"
    IO.eprintln "  field: babybear | koalabear | mersenne31 | goldilocks"
    IO.eprintln "  logN:  4 | 6 | 8 | ..."
    IO.eprintln "  B:     batch width (1 collapses to single-vector)"
