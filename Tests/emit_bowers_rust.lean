/-
  Emit Bowers Rust NTT files for KoalaBear and Goldilocks.
  Run: lake env lean --run Tests/emit_bowers_rust.lean
-/
import AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen

open AmoLean.EGraph.Verified.Bitwise.UnifiedCodeGen (generateRustNTT_Bowers)
open AmoLean.EGraph.Verified.Bitwise (arm_cortex_a76 goldilocks_prime)

def koalabear_prime : Nat := 2130706433  -- 0x7F000001

def main : IO Unit := do
  IO.FS.createDirAll "generated/bowers_rust"

  -- KoalaBear N=2^20
  let kb := generateRustNTT_Bowers arm_cortex_a76 (1 <<< 20) koalabear_prime "ntt_bowers"
  IO.FS.writeFile ⟨"generated/bowers_rust/ntt_bowers_koalabear.rs"⟩ kb
  IO.println "Generated: ntt_bowers_koalabear.rs"

  -- Goldilocks N=2^20
  let gl := generateRustNTT_Bowers arm_cortex_a76 (1 <<< 20) goldilocks_prime "ntt_bowers"
  IO.FS.writeFile ⟨"generated/bowers_rust/ntt_bowers_goldilocks.rs"⟩ gl
  IO.println "Generated: ntt_bowers_goldilocks.rs"

  IO.println "\nBoth files ready in generated/bowers_rust/"
