/-
  Extended Performance Benchmark for Phase 1 Infrastructure
  Step 5.3 - Detailed Timing Analysis

  This benchmark uses larger iteration counts to get meaningful timing data.
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Fields.BN254
import AmoLean.FRI.Fields.TestField

namespace Tests.ExtendedBenchmark

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Fields.BN254 (BN254)
open AmoLean.FRI.Fields.TestField (TestField)

/-- Timing helper -/
def timeMs (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  return (result, stop - start)

/-- Extended benchmark with configurable iterations -/
def runExtendedBenchmark : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║     EXTENDED PERFORMANCE BENCHMARK - Phase 1 Infrastructure         ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝\n"

  -- Configuration
  let invIterations := 10000
  let mulIterations := 100000
  let hashIterations := 10000
  let foldIterations := 50000

  IO.println "Configuration:"
  IO.println s!"  Inversion iterations: {invIterations}"
  IO.println s!"  Multiplication iterations: {mulIterations}"
  IO.println s!"  Hash iterations: {hashIterations}"
  IO.println s!"  Fold iterations: {foldIterations}"
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════════
  -- BN254 BENCHMARKS
  -- ═══════════════════════════════════════════════════════════════════════
  IO.println "┌───────────────────────────────────────────────────────────────┐"
  IO.println "│  BN254 (254-bit prime field with Poseidon2)                   │"
  IO.println "└───────────────────────────────────────────────────────────────┘"

  -- BN254 Inversion
  let (_, bn_inv_time) ← timeMs do
    for i in List.range invIterations do
      let x : BN254 := FRIField.ofNat (12345 + i)
      let _ := FRIField.fdiv FRIField.one x
    return ()
  let bn_inv_per_op := (bn_inv_time * 1000000) / invIterations
  IO.println s!"  Modular Inversion ({invIterations} ops):"
  IO.println s!"    Total: {bn_inv_time} ms"
  IO.println s!"    Per op: {bn_inv_per_op / 1000}.{bn_inv_per_op % 1000} μs"

  -- BN254 Multiplication
  let (_, bn_mul_time) ← timeMs do
    for i in List.range mulIterations do
      let x : BN254 := FRIField.ofNat (12345 + i)
      let y : BN254 := FRIField.ofNat (67890 + i)
      let _ := x * y
    return ()
  let bn_mul_per_op := (bn_mul_time * 1000000) / mulIterations
  IO.println s!"  Multiplication ({mulIterations} ops):"
  IO.println s!"    Total: {bn_mul_time} ms"
  IO.println s!"    Per op: {bn_mul_per_op / 1000}.{bn_mul_per_op % 1000} μs"

  -- BN254 Addition
  let (_, bn_add_time) ← timeMs do
    for i in List.range mulIterations do
      let x : BN254 := FRIField.ofNat (12345 + i)
      let y : BN254 := FRIField.ofNat (67890 + i)
      let _ := x + y
    return ()
  let bn_add_per_op := (bn_add_time * 1000000) / mulIterations
  IO.println s!"  Addition ({mulIterations} ops):"
  IO.println s!"    Total: {bn_add_time} ms"
  IO.println s!"    Per op: {bn_add_per_op / 1000}.{bn_add_per_op % 1000} μs"

  -- BN254 Hash (Poseidon2)
  let (_, bn_hash_time) ← timeMs do
    for i in List.range hashIterations do
      let a : BN254 := FRIField.ofNat i
      let b : BN254 := FRIField.ofNat (i + 1)
      let _ := CryptoHash.hash2to1 a b
    return ()
  let bn_hash_per_op := (bn_hash_time * 1000000) / hashIterations
  IO.println s!"  Poseidon2 Hash ({hashIterations} ops):"
  IO.println s!"    Total: {bn_hash_time} ms"
  IO.println s!"    Per op: {bn_hash_per_op / 1000}.{bn_hash_per_op % 1000} μs"
  let bn_hash_per_sec := if bn_hash_time > 0 then (hashIterations * 1000) / bn_hash_time else 0
  IO.println s!"    Throughput: ~{bn_hash_per_sec} hashes/sec"

  -- BN254 FRI-like fold
  let (_, bn_fold_time) ← timeMs do
    for i in List.range foldIterations do
      let even : BN254 := FRIField.ofNat (i * 2)
      let odd : BN254 := FRIField.ofNat (i * 2 + 1)
      let alpha : BN254 := FRIField.ofNat 42
      let _ := even + alpha * odd
    return ()
  let bn_fold_per_op := (bn_fold_time * 1000000) / foldIterations
  IO.println s!"  FRI Fold (even + α*odd) ({foldIterations} ops):"
  IO.println s!"    Total: {bn_fold_time} ms"
  IO.println s!"    Per op: {bn_fold_per_op / 1000}.{bn_fold_per_op % 1000} μs"

  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════════
  -- TESTFIELD BENCHMARKS
  -- ═══════════════════════════════════════════════════════════════════════
  IO.println "┌───────────────────────────────────────────────────────────────┐"
  IO.println "│  TestField (61-bit Mersenne prime with XOR hash)              │"
  IO.println "└───────────────────────────────────────────────────────────────┘"

  -- TestField Inversion
  let (_, tf_inv_time) ← timeMs do
    for i in List.range invIterations do
      let x : TestField := FRIField.ofNat (12345 + i)
      let _ := FRIField.fdiv FRIField.one x
    return ()
  let tf_inv_per_op := (tf_inv_time * 1000000) / invIterations
  IO.println s!"  Modular Inversion ({invIterations} ops):"
  IO.println s!"    Total: {tf_inv_time} ms"
  IO.println s!"    Per op: {tf_inv_per_op / 1000}.{tf_inv_per_op % 1000} μs"

  -- TestField Multiplication
  let (_, tf_mul_time) ← timeMs do
    for i in List.range mulIterations do
      let x : TestField := FRIField.ofNat (12345 + i)
      let y : TestField := FRIField.ofNat (67890 + i)
      let _ := x * y
    return ()
  let tf_mul_per_op := (tf_mul_time * 1000000) / mulIterations
  IO.println s!"  Multiplication ({mulIterations} ops):"
  IO.println s!"    Total: {tf_mul_time} ms"
  IO.println s!"    Per op: {tf_mul_per_op / 1000}.{tf_mul_per_op % 1000} μs"

  -- TestField Addition
  let (_, tf_add_time) ← timeMs do
    for i in List.range mulIterations do
      let x : TestField := FRIField.ofNat (12345 + i)
      let y : TestField := FRIField.ofNat (67890 + i)
      let _ := x + y
    return ()
  let tf_add_per_op := (tf_add_time * 1000000) / mulIterations
  IO.println s!"  Addition ({mulIterations} ops):"
  IO.println s!"    Total: {tf_add_time} ms"
  IO.println s!"    Per op: {tf_add_per_op / 1000}.{tf_add_per_op % 1000} μs"

  -- TestField Hash (XOR)
  let (_, tf_hash_time) ← timeMs do
    for i in List.range hashIterations do
      let a : TestField := FRIField.ofNat i
      let b : TestField := FRIField.ofNat (i + 1)
      let _ := CryptoHash.hash2to1 a b
    return ()
  let tf_hash_per_op := (tf_hash_time * 1000000) / hashIterations
  IO.println s!"  XOR Hash ({hashIterations} ops):"
  IO.println s!"    Total: {tf_hash_time} ms"
  IO.println s!"    Per op: {tf_hash_per_op / 1000}.{tf_hash_per_op % 1000} μs"
  let tf_hash_per_sec := if tf_hash_time > 0 then (hashIterations * 1000) / tf_hash_time else 0
  IO.println s!"    Throughput: ~{tf_hash_per_sec} hashes/sec"

  -- TestField FRI-like fold
  let (_, tf_fold_time) ← timeMs do
    for i in List.range foldIterations do
      let even : TestField := FRIField.ofNat (i * 2)
      let odd : TestField := FRIField.ofNat (i * 2 + 1)
      let alpha : TestField := FRIField.ofNat 42
      let _ := even + alpha * odd
    return ()
  let tf_fold_per_op := (tf_fold_time * 1000000) / foldIterations
  IO.println s!"  FRI Fold (even + α*odd) ({foldIterations} ops):"
  IO.println s!"    Total: {tf_fold_time} ms"
  IO.println s!"    Per op: {tf_fold_per_op / 1000}.{tf_fold_per_op % 1000} μs"

  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════════
  -- COMPARISON
  -- ═══════════════════════════════════════════════════════════════════════
  IO.println "┌───────────────────────────────────────────────────────────────┐"
  IO.println "│  COMPARISON: BN254 vs TestField                               │"
  IO.println "└───────────────────────────────────────────────────────────────┘"

  let inv_ratio := if tf_inv_time > 0 then bn_inv_time * 100 / tf_inv_time else 0
  let mul_ratio := if tf_mul_time > 0 then bn_mul_time * 100 / tf_mul_time else 0
  let add_ratio := if tf_add_time > 0 then bn_add_time * 100 / tf_add_time else 0
  let hash_ratio := if tf_hash_time > 0 then bn_hash_time * 100 / tf_hash_time else 0
  let fold_ratio := if tf_fold_time > 0 then bn_fold_time * 100 / tf_fold_time else 0

  IO.println s!"  Inversion: BN254 is {inv_ratio}% of TestField speed"
  IO.println s!"  Multiplication: BN254 is {mul_ratio}% of TestField speed"
  IO.println s!"  Addition: BN254 is {add_ratio}% of TestField speed"
  IO.println s!"  Hash: Poseidon2 is {hash_ratio}% of XOR hash speed"
  IO.println s!"  FRI Fold: BN254 is {fold_ratio}% of TestField speed"

  IO.println ""
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║     ANALYSIS SUMMARY                                                ║"
  IO.println "╠══════════════════════════════════════════════════════════════════════╣"
  IO.println "║  BN254 (Production):                                                ║"
  IO.println s!"║    - Poseidon2 hash: ~{bn_hash_per_sec} H/s                             ║"
  IO.println "║    - Full 254-bit security                                          ║"
  IO.println "║    - Suitable for production FRI                                    ║"
  IO.println "║                                                                     ║"
  IO.println "║  TestField (Testing):                                               ║"
  IO.println s!"║    - XOR hash: ~{tf_hash_per_sec} H/s                                   ║"
  IO.println "║    - Fast for CI/testing                                            ║"
  IO.println "║    - NOT cryptographically secure                                   ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"

#eval runExtendedBenchmark

end Tests.ExtendedBenchmark
