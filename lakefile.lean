import Lake
open Lake DSL

package «amo-lean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

@[default_target]
lean_lib «AmoLean» where
  roots := #[`AmoLean]

lean_lib «Benchmarks» where
  roots := #[`Benchmarks.FRI_DiffTest, `Benchmarks.Phase0.FriFold, `Benchmarks.Phase2.Optimization]

lean_lib «Tests» where
  roots := #[`Tests.MigrationRegression, `Tests.AbstractionBenchmark, `Tests.FullStackCheck, `Tests.InfrastructureSanity, `Tests.ExtendedBenchmark, `Tests.E2EProverVerifier, `Tests.Phase3Audit, `Tests.Safety.CodeGenChecks, `Tests.Oracle.FriFoldOracle, `Tests.Optimization.QABenchmark]

-- Phase 0 test executables
lean_exe «safety-checks» where
  root := `Tests.Safety.Main

lean_exe «phase0-bench» where
  root := `Benchmarks.Phase0.FriFold

lean_exe «oracle-test» where
  root := `Tests.Oracle.FriFoldOracle

-- Native executable for large-scale benchmarks
lean_exe «fri-benchmark» where
  root := `Benchmarks.NativeBenchmark

-- Phase 0 test script: run all tests
script «phase0-test» do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     PHASE 0 TEST SUITE                                       ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Run safety checks
  IO.println ">>> Running Safety Checks..."
  let safetyResult ← IO.Process.output {
    cmd := "./.lake/build/bin/safety-checks"
    cwd := some "."
  }
  IO.println safetyResult.stdout
  if safetyResult.exitCode != 0 then
    IO.println "❌ Safety checks failed!"
    return 1

  -- Run oracle tests
  IO.println ">>> Running Oracle Tests..."
  let oracleResult ← IO.Process.output {
    cmd := "./.lake/build/bin/oracle-test"
    cwd := some "."
  }
  IO.println oracleResult.stdout
  if oracleResult.exitCode != 0 then
    IO.println "❌ Oracle tests failed!"
    return 1

  IO.println ""
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     ALL PHASE 0 TESTS PASSED ✅                              ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  return 0
