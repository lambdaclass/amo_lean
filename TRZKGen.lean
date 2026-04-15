/-
  TRZKGen: Native binary for running the Ultra pipeline at compiled speed.
  v3.13.0 E.2: Discovery for N=2^14 completes in ~1-2s native vs >5min interpreted.
  Usage: lake build trzk-gen && .lake/build/bin/trzk-gen [babybear|goldilocks] [logN]
-/
import AmoLean.EGraph.Verified.Bitwise.UltraPipeline

open AmoLean.EGraph.Verified.Bitwise.UltraPipeline
  (UltraConfig babyBearUltra goldilocksUltra)

def main (args : List String) : IO Unit := do
  let field := args.getD 0 "babybear"
  let logN := (args.getD 1 "14").toNat!
  let n := 2 ^ logN

  IO.println s!"trzk-gen: {field} N=2^{logN} ({n})"
  IO.println "Generating..."

  let code := match field with
    | "goldilocks" | "goldi" =>
      goldilocksUltra n { hw := AmoLean.EGraph.Verified.Bitwise.arm_cortex_a76 }
    | _ =>
      babyBearUltra n {}

  IO.println s!"Generated {code.length} chars of C code."
  IO.println "--- BEGIN CODE ---"
  IO.println code
  IO.println "--- END CODE ---"
