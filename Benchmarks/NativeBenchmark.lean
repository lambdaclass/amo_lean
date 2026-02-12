/-
  FRI Native Benchmark Executable
  Phase 3 - Performance Testing

  This module provides a compiled benchmark for testing FRI
  with large polynomials (degree > 64) where #eval! would be too slow.

  Usage:
    lake build fri-benchmark
    ./.lake/build/bin/fri-benchmark
-/

import AmoLean.FRI.Fold
import AmoLean.FRI.Hash
import AmoLean.FRI.Proof
import AmoLean.FRI.Prover
import AmoLean.FRI.Verifier
import AmoLean.FRI.Fields.TestField
import AmoLean.FRI.Fields.BN254

namespace Benchmarks.NativeBenchmark

open AmoLean.FRI.Fold (FRIField)
open AmoLean.FRI.Hash (CryptoHash)
open AmoLean.FRI.Proof (FRIConfig FRIProof VerifyError)
open AmoLean.FRI.Prover (prove productionConfig)
open AmoLean.FRI.Verifier (verify verifyMessage)
open AmoLean.FRI.Fields.TestField (TestField)
open AmoLean.FRI.Fields.BN254 (BN254)

/-! ## Benchmark Helpers -/

/-- Generate constant evaluations (degree 0 polynomial) -/
def generateConstantEvaluations {F : Type} [FRIField F] (value : Nat) (size : Nat) : Array F :=
  Array.mkArray size (FRIField.ofNat value)

/-- Time an IO action and return milliseconds -/
def timeIO (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  pure (result, stop - start)

/-- Run benchmark for a specific degree -/
def runBenchmark {F : Type} [FRIField F] [CryptoHash F] [Inhabited F] [BEq F]
    (fieldName : String) (degree : Nat) (numQueries : Nat := 30) : IO Unit := do
  let config := productionConfig degree numQueries
  -- Use constant polynomial (degree 0) for valid FRI verification
  let evaluations : Array F := generateConstantEvaluations 42 (config.initialDomainSize)

  IO.println s!"  Degree {degree}:"
  IO.println s!"    Domain size: {config.initialDomainSize}"
  IO.println s!"    Rounds: {config.numRounds}"
  IO.println s!"    Queries: {config.numQueries}"

  -- Prove
  let (proveResult, proveTime) ← timeIO (prove evaluations config)

  match proveResult with
  | .error msg =>
    IO.println s!"    ✗ Prove FAILED: {msg}"
  | .ok proof =>
    IO.println s!"    Prove: {proveTime}ms"

    -- Verify
    let (verifyResult, verifyTime) ← timeIO (pure (verify proof))
    match verifyResult with
    | .ok () =>
      IO.println s!"    Verify: {verifyTime}ms"
      IO.println s!"    ✓ PASSED"
    | .error err =>
      IO.println s!"    ✗ Verify FAILED: {VerifyError.toString err}"

/-! ## Main Benchmark Suite -/

def main : IO Unit := do
  IO.println ""
  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║              FRI NATIVE BENCHMARK - Phase 3                         ║"
  IO.println "║                  Compiled Executable Tests                          ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- TestField benchmarks (XOR hash - fast)
  IO.println "┌──────────────────────────────────────────────────────────────────────┐"
  IO.println "│  TestField (XOR Hash) Benchmarks                                    │"
  IO.println "└──────────────────────────────────────────────────────────────────────┘"

  for degree in [16, 64, 256, 1024] do
    runBenchmark (F := TestField) "TestField" degree 10
    IO.println ""

  -- BN254 benchmarks (Poseidon2 - slower but cryptographically secure)
  IO.println "┌──────────────────────────────────────────────────────────────────────┐"
  IO.println "│  BN254 (Poseidon2 Hash) Benchmarks                                  │"
  IO.println "└──────────────────────────────────────────────────────────────────────┘"

  for degree in [16, 64, 256] do
    runBenchmark (F := BN254) "BN254" degree 10
    IO.println ""

  IO.println "╔══════════════════════════════════════════════════════════════════════╗"
  IO.println "║                    BENCHMARK COMPLETE                               ║"
  IO.println "╚══════════════════════════════════════════════════════════════════════╝"

end Benchmarks.NativeBenchmark

-- Export main for executable entry point
def main : IO Unit := Benchmarks.NativeBenchmark.main
