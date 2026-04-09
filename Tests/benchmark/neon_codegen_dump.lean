import AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen
import AmoLean.EGraph.Verified.Bitwise.SIMDEmitter
import AmoLean.EGraph.Verified.Bitwise.NTTPlan

open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice StageDirection)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.VerifiedPlanCodeGen (emitCFromPlanVerified)
open AmoLean.EGraph.Verified.Bitwise.SIMDEmitter (emitSIMDNTTC SIMDTarget)

/-- Build a simple R2 plan for N=2^logN with uniform reduction. -/
def mkSimplePlan (p n logN : Nat) (red : ReductionChoice := .solinasFold) : Plan :=
  let stages := (List.range logN).map fun i =>
    { stageIdx := i, radix := .r2, reduction := red,
      direction := .DIT, inputBoundK := 1, outputBoundK := 1 : NTTStage }
  { stages := stages.toArray, field := p, size := n }

structure FieldParams where
  name : String
  p : Nat
  k : Nat
  c : Nat
  mu : Nat
  gen : Nat  -- primitive root for NTT

def fields : List FieldParams := [
  { name := "babybear",   p := 2013265921, k := 31, c := 134217727, mu := 2281701377, gen := 31 },
  { name := "koalabear",  p := 2130706433, k := 31, c := 16777215,  mu := 2164260865, gen := 3 },
  { name := "mersenne31", p := 2147483647, k := 31, c := 1,         mu := 2147483647, gen := 7 }
]

def main : IO Unit := do
  let logN := 4
  let n := 2^logN
  for fp in fields do
    let planSol := mkSimplePlan fp.p n logN .solinasFold
    let planMon := mkSimplePlan fp.p n logN .montgomery
    -- Scalar + Solinas
    let ss := emitCFromPlanVerified planSol fp.k fp.c fp.mu s!"ntt_{fp.name}_scalar_sol"
    IO.FS.writeFile ⟨s!"/tmp/neon_v_{fp.name}_scalar_sol.c"⟩ ss
    -- NEON + Solinas
    let ns := emitSIMDNTTC planSol SIMDTarget.neon fp.k fp.c fp.mu s!"ntt_{fp.name}_neon_sol"
    IO.FS.writeFile ⟨s!"/tmp/neon_v_{fp.name}_neon_sol.c"⟩ ns
    -- Scalar + Montgomery (should now emit Solinas via Fix B)
    let sm := emitCFromPlanVerified planMon fp.k fp.c fp.mu s!"ntt_{fp.name}_scalar_mon"
    IO.FS.writeFile ⟨s!"/tmp/neon_v_{fp.name}_scalar_mon.c"⟩ sm
    -- NEON + Montgomery
    let nm := emitSIMDNTTC planMon SIMDTarget.neon fp.k fp.c fp.mu s!"ntt_{fp.name}_neon_mon"
    IO.FS.writeFile ⟨s!"/tmp/neon_v_{fp.name}_neon_mon.c"⟩ nm
    IO.println s!"{fp.name}: ss={ss.length} ns={ns.length} sm={sm.length} nm={nm.length}"
  IO.println "Done. 12 files in /tmp/neon_v_*.c"
