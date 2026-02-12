import AmoLean.Protocols.Poseidon.CodeGen

open AmoLean.Protocols.Poseidon.CodeGen

def main : IO Unit := do
  -- Generate Goldilocks SIMD file
  let goldilocksConfig : CodeGenConfig := {
    fieldType := .Goldilocks
    stateSize := 12
    sboxExp := 7
  }
  let goldilocksCode := genGoldilocksSIMDFile goldilocksConfig
  IO.FS.writeFile "generated/poseidon_sbox_goldilocks_simd.h" goldilocksCode
  IO.println "Generated: generated/poseidon_sbox_goldilocks_simd.h"

  -- Generate BN254 Batch SIMD file
  let bn254Config : CodeGenConfig := {
    fieldType := .BN254
    stateSize := 3
    sboxExp := 5
  }
  let bn254Code := genBN254BatchSIMDFile bn254Config
  IO.FS.writeFile "generated/poseidon_sbox_bn254_batch.h" bn254Code
  IO.println "Generated: generated/poseidon_sbox_bn254_batch.h"

  IO.println "Done!"
