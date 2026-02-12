/-
  AMO-Lean: Phase 0 FRI Fold Benchmark
  Differential Benchmark: Lean vs Generated C

  This module measures the performance of:
  1. Native Lean FRI fold implementation
  2. Generated C implementation (via subprocess)

  And reports the speedup factor.
-/

import AmoLean.FRI.FoldExpr
import AmoLean.Vector.Basic

namespace Benchmarks.Phase0.FriFold

open AmoLean.FRI.FoldExpr (foldDirect)
open AmoLean.Vector (Vec)

/-! ## Part 1: Timing Infrastructure -/

/-- Get current time in nanoseconds -/
def getTimeNs : IO Nat := do
  let start ← IO.monoNanosNow
  return start

/-- Measure execution time of an IO action -/
def timeAction (action : IO α) : IO (α × Nat) := do
  let start ← getTimeNs
  let result ← action
  let endTime ← getTimeNs
  return (result, endTime - start)

/-! ## Part 2: Lean Implementation Benchmark -/

/-- Create a test vector of given size with pseudo-random values -/
def makeTestVec (size : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut arr := Array.mkEmpty size
  let mut x := seed
  for _ in [0:size] do
    x := x * 6364136223846793005 + 1442695040888963407  -- LCG
    arr := arr.push x
  return arr

/-- Reference FRI fold implementation using Array -/
def friFoldArray (even odd : Array UInt64) (alpha : UInt64) : Array UInt64 :=
  Array.zipWith even odd (fun e o => e + alpha * o)

/-- Benchmark Lean implementation -/
def benchmarkLean (size : Nat) (iterations : Nat) : IO (Nat × UInt64) := do
  -- Create test data
  let even := makeTestVec size 12345
  let odd := makeTestVec size 67890
  let alpha : UInt64 := 0xDEADBEEFCAFEBABE

  -- Warmup
  for _ in [0:10] do
    let _ := friFoldArray even odd alpha

  -- Benchmark
  let start ← getTimeNs
  let mut result := Array.empty
  for _ in [0:iterations] do
    result := friFoldArray even odd alpha
  let endTime ← getTimeNs

  let totalNs := endTime - start
  let checksum := result.foldl (· + ·) 0

  return (totalNs, checksum)

/-! ## Part 3: C Implementation Benchmark (via subprocess) -/

/-- Parse JSON output from C benchmark -/
def parseJsonResult (output : String) : Option (Nat × Float) := do
  -- Simple parsing for: {"size": N, "iterations": I, "total_ns": T, "avg_ns": A}
  let parts := output.splitOn "\"total_ns\": "
  if parts.length < 2 then none
  else
    let rest := parts[1]!
    let numParts := rest.splitOn ","
    if numParts.isEmpty then none
    else
      let totalNsStr := numParts[0]!.trim
      let totalNs := totalNsStr.toNat?
      match totalNs with
      | none => none
      | some ns =>
        -- Parse avg_ns
        let avgParts := output.splitOn "\"avg_ns\": "
        if avgParts.length < 2 then some (ns, 0.0)
        else
          let avgStr := avgParts[1]!.splitOn "}" |>.head!.trim
          let avgNs := avgStr.toNat?.getD 0
          some (ns, avgNs.toFloat)

/-- Benchmark C implementation by calling external executable -/
def benchmarkC (size : Nat) (iterations : Nat) : IO (Option Nat) := do
  let benchPath := "generated/bench_fri_fold"

  -- Run the benchmark
  let output ← IO.Process.output {
    cmd := benchPath
    args := #[toString size, toString iterations]
    cwd := some "."
  }

  if output.exitCode != 0 then
    IO.eprintln s!"C benchmark failed: {output.stderr}"
    return none

  -- Parse the result
  match parseJsonResult output.stdout with
  | none =>
    IO.eprintln s!"Failed to parse C benchmark output: {output.stdout}"
    return none
  | some (totalNs, _) =>
    return some totalNs

/-! ## Part 4: Differential Benchmark -/

/-- Result of a single benchmark run -/
structure BenchResult where
  size : Nat
  iterations : Nat
  leanNs : Nat
  cNs : Option Nat
  speedup : Option Float
  deriving Repr

/-- Run benchmark for a given size -/
def runBenchmark (size : Nat) (iterations : Nat) : IO BenchResult := do
  IO.println s!"  Benchmarking size={size}, iterations={iterations}..."

  -- Benchmark Lean
  let (leanNs, _) ← benchmarkLean size iterations
  IO.println s!"    Lean: {leanNs} ns total"

  -- Benchmark C
  let cNsOpt ← benchmarkC size iterations
  match cNsOpt with
  | none =>
    IO.println s!"    C: FAILED"
    return { size, iterations, leanNs, cNs := none, speedup := none }
  | some cNs =>
    IO.println s!"    C:    {cNs} ns total"
    let speedup := leanNs.toFloat / cNs.toFloat
    IO.println s!"    Speedup: {speedup}x"
    return { size, iterations, leanNs, cNs := some cNs, speedup := some speedup }

/-! ## Part 5: Report Generation -/

/-- Generate Markdown report from benchmark results -/
def generateReport (results : List BenchResult) : String :=
  let header := "# Phase 0: FRI Fold Benchmark Report\n\n"
  let metadata := "Generated: 2026-01-28\n\n"
  let tableHeader := "| Size | Iterations | Lean (ns) | C (ns) | Speedup |\n|------|------------|-----------|--------|--------|\n"

  let rows := results.map fun r =>
    let cStr := match r.cNs with | some ns => toString ns | none => "FAILED"
    let speedupStr := match r.speedup with | some s => s!"{s}x" | none => "N/A"
    s!"| {r.size} | {r.iterations} | {r.leanNs} | {cStr} | {speedupStr} |\n"

  let speedups := results.filterMap (·.speedup)
  let avgSpeedup := if speedups.isEmpty then 0.0
                    else speedups.foldl (· + ·) 0.0 / speedups.length.toFloat

  let summary := s!"\n## Summary\n\n- Average Speedup: **{avgSpeedup}x**\n"

  let interpretation := if avgSpeedup > 1.0 then
    s!"- **C is {avgSpeedup}x faster than Lean** ✅\n"
  else if avgSpeedup < 1.0 then
    s!"- **Lean is {1.0/avgSpeedup}x faster than C** ⚠️ (unexpected)\n"
  else
    "- **C and Lean have similar performance**\n"

  header ++ metadata ++ tableHeader ++ String.join rows ++ summary ++ interpretation

/-! ## Part 6: Main Entry Point -/

/-- Standard benchmark sizes -/
def benchmarkSizes : List (Nat × Nat) := [
  (16, 100000),
  (64, 50000),
  (256, 10000),
  (1024, 5000),
  (4096, 1000)
]

/-- Main benchmark function -/
def runBenchmarks : IO UInt32 := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     PHASE 0 BENCHMARK: FRI FOLD (Lean vs C)                  ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let mut results : List BenchResult := []

  for (size, iterations) in benchmarkSizes do
    let result ← runBenchmark size iterations
    results := results ++ [result]

  IO.println ""
  IO.println "════════════════════════════════════════════════════════════════"
  IO.println "BENCHMARK COMPLETE"
  IO.println "════════════════════════════════════════════════════════════════"
  IO.println ""

  -- Generate and print report
  let report := generateReport results
  IO.println report

  -- Save report to file
  IO.FS.writeFile "docs/option-a/BENCHMARK_RESULTS.md" report
  IO.println s!"Report saved to: docs/option-a/BENCHMARK_RESULTS.md"

  return 0

/-! ## Part 7: Quick Test -/

#eval! do
  IO.println "Quick benchmark test (small size):"
  let result ← runBenchmark 16 1000
  IO.println s!"Result: {repr result}"

end Benchmarks.Phase0.FriFold

/-- Main entry point for executable -/
def main : IO UInt32 := Benchmarks.Phase0.FriFold.runBenchmarks
