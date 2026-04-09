/-
  Diagnostic: dump full Ultra pipeline report for a field.
  Usage: lake env lean --run Tests/benchmark/dump_report.lean babybear 14
-/
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline

open AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
open AmoLean.EGraph.Verified.Bitwise (arm_cortex_a76 HardwareCost)
open AmoLean.EGraph.Verified.Bitwise.UltraPipeline (ultraPipeline UltraConfig)

def getField (name : String) : Option FieldConfig :=
  match name with
  | "babybear" => some babybearConfig
  | "koalabear" => some koalabearConfig
  | "mersenne31" => some mersenne31Config
  | "goldilocks" => some goldilocksConfig
  | _ => none

def main (args : List String) : IO Unit := do
  match args with
  | [field, logNStr] =>
    let some fc := getField field
      | IO.eprintln s!"Unknown field: {field}" ; return
    let some logN := logNStr.toNat?
      | IO.eprintln s!"Invalid logN: {logNStr}" ; return
    let n := 2^logN
    let hw := arm_cortex_a76
    let ucfg : UltraConfig := { hw := hw, k := fc.k, c := fc.cNat, mu := fc.muNat, targetColor := 1 }
    let (cCode, rustCode, report) := ultraPipeline default [] fc.pNat n ucfg
      s!"{fc.name.toLower}_ntt_ultra"
    IO.println "═══════════════════════════════════════════════"
    IO.println s!"FULL ULTRA PIPELINE REPORT: {fc.name} N=2^{logN}"
    IO.println "═══════════════════════════════════════════════"
    IO.println report
    IO.println ""
    IO.println s!"C code length:    {cCode.length} chars"
    IO.println s!"Rust code length: {rustCode.length} chars"
    IO.println ""
    -- Also dump the plan details via costReport
    IO.println "═══════════════════════════════════════════════"
    IO.println "COST REPORT (from optimizeReduction)"
    IO.println "═══════════════════════════════════════════════"
    IO.println (costReport fc)
  | _ =>
    IO.eprintln "Usage: dump_report <field> <logN>"
