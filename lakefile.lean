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
  roots := #[`Benchmarks.FRI_DiffTest]
