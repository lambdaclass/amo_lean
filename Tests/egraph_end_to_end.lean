/-
  End-to-end pipeline: e-graph cost model → UnifiedCodeGen → C files
  Then compile and benchmark externally.
-/
import AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen
import AmoLean.EGraph.Verified.Bitwise.CostModelDef

open AmoLean.EGraph.Verified.Bitwise
open AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║  E-Graph End-to-End: Cost Model → Generated C              ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Show what the e-graph selects for each target
  for (label, hw) in [
    ("ARM Scalar", arm_cortex_a76),
    ("ARM NEON SIMD", arm_neon_simd),
    ("x86 AVX2 SIMD", x86_avx2_simd)] do
    let cfg := selectConfig hw babybear_prime
    IO.println s!"  {label}: mode={toString cfg.mode}, reduction={toString cfg.reduction}"

  IO.println ""

  -- Generate all targets
  IO.println "Generating NTT code for BabyBear N=4096..."
  writeAllTargets "generated/unified" 4096 babybear_prime

  IO.println ""
  IO.println "Generating NTT code for Mersenne31 N=4096..."
  writeAllTargets "generated/unified_m31" 4096 mersenne31_prime

  IO.println ""

  -- Show Goldilocks selection
  IO.println "Goldilocks strategy selection:"
  let glCfg := selectConfig arm_neon_simd goldilocks_prime
  IO.println s!"  Even with NEON target: mode={toString glCfg.mode}, reduction={toString glCfg.reduction}, wordSize=u{glCfg.wordSize}"
  IO.println "  (64-bit field → scalar mode forced, Solinas fold, u64 arrays)"
  IO.println ""

  IO.println "Generating NTT code for Goldilocks N=4096..."
  writeAllTargets "generated/unified_gl" 4096 goldilocks_prime

  IO.println ""
  IO.println "Done. Compile and benchmark:"
  IO.println "  cc -O2 -o ntt_neon generated/unified/ntt_simd_neon.c   # BabyBear NEON"
  IO.println "  cc -O2 -o ntt_gl generated/unified_gl/ntt_scalar_arm.c # Goldilocks scalar"
