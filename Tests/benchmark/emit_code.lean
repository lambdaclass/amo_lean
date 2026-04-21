/-
  Minimal code emitter for the benchmark harness.
  Generates C or Rust NTT benchmark programs and prints to stdout.
  Sidecar — does NOT modify any TRZK file.

  Usage:
    lake env lean Tests/benchmark/emit_code.lean -- <field> <logN> <lang> <hardware>
  Example:
    lake env lean Tests/benchmark/emit_code.lean -- babybear 14 c arm-scalar
-/
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline

open AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
open AmoLean.EGraph.Verified.Bitwise (arm_cortex_a76 arm_neon_simd x86_avx2_simd HardwareCost)

def getField (name : String) : Option FieldConfig :=
  match name with
  | "babybear" => some babybearConfig
  | "koalabear" => some koalabearConfig
  | "mersenne31" => some mersenne31Config
  | "goldilocks" => some goldilocksConfig
  | _ => none

def getHW (name : String) : HardwareCost :=
  match name with
  | "arm-neon" => arm_neon_simd
  | "x86-avx2" => x86_avx2_simd
  | _ => arm_cortex_a76

def main (args : List String) : IO Unit := do
  -- Parse optional flags
  let verifiedSIMD := args.contains "--verified-simd"
  let rustSIMD := args.contains "--rust-simd"
  -- v3.15.0 B5: default standard DFT. --use-legacy reverts to ref_dit.
  let useStandard := !args.contains "--use-legacy"
  -- v3.20.b B3.5 N20.35.2: bitrev fusion (skip bit_reverse_permute preamble +
  -- route first-executed stage through bitrev-fused hs1 kernel).
  let bitrevFusion := args.contains "--bitrev-fusion"
  let args' := args.filter fun a =>
    a != "--verified-simd" && a != "--rust-simd" && a != "--use-standard" &&
    a != "--use-legacy" && a != "--bitrev-fusion"
  match args' with
  | [field, logNStr, lang, hw] =>
    let some fc := getField field
      | IO.eprintln s!"Unknown field: {field}" ; return
    let some logN := logNStr.toNat?
      | IO.eprintln s!"Invalid logN: {logNStr}" ; return
    let hwCost := getHW hw
    let iters := 10
    let code := if lang == "rust" then
      genOptimizedBenchRust_ultra fc logN iters hwCost rustSIMD useStandard
    else
      genOptimizedBenchC_ultra fc logN iters hwCost verifiedSIMD rustSIMD useStandard bitrevFusion
    IO.println code
  | _ =>
    IO.eprintln "Usage: emit_code <field> <logN> <lang> <hardware> [flags]"
    IO.eprintln "  field:    babybear | koalabear | mersenne31 | goldilocks"
    IO.eprintln "  logN:     14 | 16 | 18 | 20 | 22"
    IO.eprintln "  lang:     c | rust"
    IO.eprintln "  hardware: arm-scalar | arm-neon | x86-avx2"
    IO.eprintln "  --verified-simd: C verified SIMD (v3.7.0)"
    IO.eprintln "  --rust-simd: Rust verified SIMD (v3.8.0)"
    IO.eprintln "  --use-standard: v3.15.0 standard DFT (bitrev + DIT small→large)"
    IO.eprintln "  --bitrev-fusion: v3.20.b B3.5 bitrev fusion (C arm-neon)"
