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

  -- Generate Rust NTTs for fair Plonky3 comparison
  IO.println "Generating Rust NTTs (for fair rustc -O comparison)..."
  IO.FS.createDirAll "generated/rust_ntt"
  for (name, p, sz) in [
    ("koalabear", (2130706433 : Nat), (1 <<< 20 : Nat)),
    ("koalabear_22", (2130706433 : Nat), (1 <<< 22 : Nat)),
    ("babybear", babybear_prime, (1 <<< 20 : Nat)),
    ("babybear_22", babybear_prime, (1 <<< 22 : Nat)),
    ("mersenne31", mersenne31_prime, (1 <<< 20 : Nat))] do
    let code := generateRustNTT arm_cortex_a76 sz p s!"ntt_{name}"
    let path := s!"generated/rust_ntt/ntt_{name}.rs"
    IO.FS.writeFile ⟨path⟩ code
    IO.println s!"  {path} ({code.length} bytes)"

  IO.println ""
  IO.println "Done. Compile and benchmark:"
  IO.println "  cc -O2 -o ntt_neon generated/unified/ntt_simd_neon.c   # BabyBear NEON C"
  IO.println "  rustc -O -o ntt_kb generated/rust_ntt/ntt_koalabear.rs && ./ntt_kb  # KoalaBear Rust"
  IO.println "  rustc -O -o ntt_kb22 generated/rust_ntt/ntt_koalabear_22.rs && ./ntt_kb22"
