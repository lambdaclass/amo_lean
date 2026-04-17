/-
  Minimal Rust emitter (v3.17.0 B5.5 companion to emit_standard.lean).
  Emits ONLY the Rust NTT function + preambles (no main).
  Python benchmark_plonky3.py wraps with timing harness.

  Usage: lake env lean --run Tests/benchmark/emit_standard_rust.lean <field> <logN> [--r4]
-/
import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.NTTPlanSelection

open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitRustFromPlanStandard)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (mkUniformPlan mkMixedRadixPlan)

/-- Build same plan as emit_standard.lean (R2 uniform Harvey + ILP2 for k>32). -/
def emitStandardRust (p k c mu : Nat) (logN : Nat) (funcName : String)
    (useR4 : Bool := false) : String :=
  let n := 2^logN
  let plan := if useR4 then mkMixedRadixPlan p n
    else mkUniformPlan p n .r2 .harvey
  let plan := if k > 32 then
    { plan with stages := plan.stages.map fun s =>
      if s.radix == .r2 then { s with ilpFactor := 2 } else s }
    else plan
  emitRustFromPlanStandard plan k c mu funcName

def main (args : List String) : IO Unit := do
  let useR4 := args.contains "--r4"
  let args' := args.filter (· != "--r4")
  match args' with
  | [field, logNStr] =>
    let some logN := logNStr.toNat?
      | IO.eprintln s!"Invalid logN: {logNStr}" ; return
    let (p, k, c, mu) := match field with
      | "babybear"   => (2013265921,          31, 134217727,  0x88000001)
      | "goldilocks" => (18446744069414584321, 64, 4294967295, 0)
      | _ => (0, 0, 0, 0)
    if p == 0 then
      IO.eprintln s!"Unknown field: {field}"
      return
    let funcName := s!"{field}_ntt_standard"
    IO.print (emitStandardRust p k c mu logN funcName useR4)
  | _ =>
    IO.eprintln "Usage: emit_standard_rust <field> <logN> [--r4]"
