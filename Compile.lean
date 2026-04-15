/-
  trzk — Verified compiler for crypto primitives

  v3.13.0 F.1: Routes to Path A (UltraPipeline) for NTT, Path A (PrimitiveOptimizer)
  for FRI fold / Horner / dot product. Legacy spec file mode kept for backward compat.

  Usage:
    .lake/build/bin/trzk ntt babybear 1024 --target c
    .lake/build/bin/trzk fri_fold goldilocks --target c
    .lake/build/bin/trzk spec.lean --target c  (legacy mode)
-/
import AmoLean.EGraph.Verified.Bitwise.UltraPipeline
import AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer
import AmoLean.Matrix.Basic

open AmoLean.EGraph.Verified.Bitwise.UltraPipeline
  (UltraConfig babyBearUltra goldilocksUltra)
open AmoLean.EGraph.Verified.Bitwise.PrimitiveOptimizer
  (friFoldToC hornerToC dotProductToC)
open AmoLean.EGraph.Verified.Bitwise
  (arm_cortex_a76 babybear_prime goldilocks_prime mersenne31_prime)
open AmoLean.Matrix (MatExpr)

structure CompileConfig where
  primitive : String := ""      -- ntt | fri_fold | horner | dot_product
  field : String := "babybear"  -- babybear | goldilocks | mersenne31
  size : Nat := 1024            -- N for NTT
  target : String := "c"
  output : Option String := none
  funcName : Option String := none
  help : Bool := false
  specFile : Option String := none  -- legacy mode

partial def parseArgs : List String → CompileConfig → CompileConfig
  | [], cfg => cfg
  | "--target" :: v :: rest, cfg => parseArgs rest { cfg with target := v }
  | "--output" :: v :: rest, cfg => parseArgs rest { cfg with output := some v }
  | "--name" :: v :: rest, cfg => parseArgs rest { cfg with funcName := some v }
  | "--help" :: rest, cfg => parseArgs rest { cfg with help := true }
  | v :: rest, cfg =>
    if v.startsWith "--" then parseArgs rest cfg
    else if cfg.primitive == "" then
      if v.endsWith ".lean" then parseArgs rest { cfg with specFile := some v }
      else parseArgs rest { cfg with primitive := v }
    else if cfg.field == "babybear" && (v == "goldilocks" || v == "mersenne31" || v == "babybear") then
      parseArgs rest { cfg with field := v }
    else
      match v.toNat? with
      | some n => parseArgs rest { cfg with size := n }
      | none => parseArgs rest { cfg with field := v }

def showHelp : IO Unit := do
  IO.println "trzk — Verified compiler for crypto primitives"
  IO.println ""
  IO.println "Usage:"
  IO.println "  trzk ntt babybear 1024 --target c     Generate NTT via UltraPipeline (Path A)"
  IO.println "  trzk fri_fold goldilocks --target c    Generate FRI fold (Path A)"
  IO.println "  trzk horner babybear 7 --target c      Generate Horner poly eval degree 7"
  IO.println "  trzk dot_product mersenne31             Generate dot product"
  IO.println "  trzk spec.lean --target c              Legacy mode (Path B)"
  IO.println ""
  IO.println "Options:"
  IO.println "  --target c|rust    Target language (default: c)"
  IO.println "  --output <file>    Output file (default: stdout)"
  IO.println "  --name <funcname>  Function name override"
  IO.println "  --help             Show this help"

def fieldPrime (f : String) : Nat :=
  match f with
  | "goldilocks" | "goldi" => goldilocks_prime
  | "mersenne31" | "m31" => mersenne31_prime
  | _ => babybear_prime

def defaultFuncName (prim field : String) : String :=
  s!"{prim}_{field}"

def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args {}

  if cfg.help then
    showHelp
    return 0

  -- Legacy spec file mode (backward compat)
  if let some _specFile := cfg.specFile then
    IO.eprintln "Legacy spec file mode: use TRZKGen for native pipeline."
    IO.eprintln "Run: lake build trzk-gen && .lake/build/bin/trzk-gen <field> <logN>"
    return 1

  if cfg.primitive == "" then
    IO.eprintln "Error: no primitive specified. Run with --help."
    return 1

  let p := fieldPrime cfg.field
  let hw := arm_cortex_a76
  let fname := cfg.funcName.getD (defaultFuncName cfg.primitive cfg.field)

  let code ← match cfg.primitive with
    | "ntt" =>
      let n := cfg.size
      pure <| match cfg.field with
        | "goldilocks" | "goldi" => goldilocksUltra n { hw }
        | _ => babyBearUltra n {}
    | "fri_fold" =>
      pure <| friFoldToC hw p cfg.size fname
    | "horner" =>
      pure <| hornerToC hw p cfg.size fname
    | "dot_product" | "dot" =>
      pure <| dotProductToC hw p fname
    | other =>
      IO.eprintln s!"Unknown primitive: {other}. Use: ntt, fri_fold, horner, dot_product"
      return 1

  -- Output
  match cfg.output with
  | some path =>
    IO.FS.writeFile ⟨path⟩ code
    IO.println s!"Generated: {path}"
  | none =>
    IO.println code

  return 0
