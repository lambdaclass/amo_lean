/-
  AMO-Lean — Verified Production E2E Tests (Fase 30)
  Verifies that ALL production primitives produce non-empty C + Rust
  code via Path A (verified Stmt lowering).
  0 sorry, 0 new axioms.
-/
import AmoLean.Bridge.VerifiedProductionCodegen

set_option autoImplicit false

namespace Tests.VerifiedProductionE2E

open AmoLean.Bridge.VerifiedProductionCodegen

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Verify all generators produce non-empty output
-- ══════════════════════════════════════════════════════════════════

def runProductionTests : IO Unit := do
  let mut passed := 0
  let mut failed := 0

  let tests : List (String × String) := [
    -- Field reductions (C + Rust)
    ("babybear_reduce_c", babybear_reduce_c),
    ("babybear_reduce_rust", babybear_reduce_rust),
    ("mersenne31_reduce_c", mersenne31_reduce_c),
    ("mersenne31_reduce_rust", mersenne31_reduce_rust),
    ("koalabear_reduce_c", koalabear_reduce_c),
    ("koalabear_reduce_rust", koalabear_reduce_rust),
    ("goldilocks_reduce_c", goldilocks_reduce_c),
    ("goldilocks_reduce_rust", goldilocks_reduce_rust),
    -- DIF Butterfly (C + Rust)
    ("babybear_butterfly_c", babybear_butterfly_c),
    ("babybear_butterfly_rust", babybear_butterfly_rust),
    ("mersenne31_butterfly_c", mersenne31_butterfly_c),
    ("mersenne31_butterfly_rust", mersenne31_butterfly_rust),
    ("koalabear_butterfly_c", koalabear_butterfly_c),
    ("koalabear_butterfly_rust", koalabear_butterfly_rust),
    ("goldilocks_butterfly_c", goldilocks_butterfly_c),
    ("goldilocks_butterfly_rust", goldilocks_butterfly_rust),
    -- NTT (C + Rust, logN=4 → 16-point)
    ("babybear_ntt_c", babybear_ntt_c 4),
    ("babybear_ntt_rust", babybear_ntt_rust 4),
    ("mersenne31_ntt_c", mersenne31_ntt_c 4),
    ("mersenne31_ntt_rust", mersenne31_ntt_rust 4),
    ("koalabear_ntt_c", koalabear_ntt_c 4),
    ("koalabear_ntt_rust", koalabear_ntt_rust 4),
    ("goldilocks_ntt_c", goldilocks_ntt_c 4),
    ("goldilocks_ntt_rust", goldilocks_ntt_rust 4),
    -- FRI fold (C + Rust, n=8)
    ("friFold_c_8", friFold_c 8),
    ("friFold_rust_8", friFold_rust 8),
    -- Poseidon S-box (C + Rust)
    ("poseidon_sbox5_c", poseidon_sbox5_c),
    ("poseidon_sbox5_rust", poseidon_sbox5_rust),
    ("poseidon_sbox7_c", poseidon_sbox7_c),
    ("poseidon_sbox7_rust", poseidon_sbox7_rust)
  ]

  for (name, code) in tests do
    if code.length > 0 then
      passed := passed + 1
    else
      IO.println s!"FAIL: {name} produced empty output"
      failed := failed + 1

  IO.println s!"═══ VERIFIED PRODUCTION CODEGEN: {passed}/{passed + failed} ALL OUTPUTS NON-EMPTY ═══"
  if failed > 0 then
    IO.println "SOME TESTS FAILED"
  else
    IO.println "ALL PASS — Every primitive produces verified C + Rust via Path A"

#eval runProductionTests

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Show sample outputs
-- ══════════════════════════════════════════════════════════════════

def showSampleOutputs : IO Unit := do
  IO.println "\n═══ SAMPLE VERIFIED CODE OUTPUT ═══\n"

  IO.println "--- BabyBear Reduce (C) ---"
  IO.println babybear_reduce_c

  IO.println "\n--- BabyBear Reduce (Rust) ---"
  IO.println babybear_reduce_rust

  IO.println "\n--- Poseidon S-box x⁵ (C) ---"
  IO.println poseidon_sbox5_c

  IO.println "\n--- Poseidon S-box x⁵ (Rust) ---"
  IO.println poseidon_sbox5_rust

  IO.println "\n--- FRI Fold n=8 (C) ---"
  IO.println (friFold_c 8)

  IO.println "\n--- FRI Fold n=8 (Rust) ---"
  IO.println (friFold_rust 8)

  IO.println "\n--- BabyBear 16-point NTT (Rust) ---"
  IO.println (babybear_ntt_rust 4)

#eval showSampleOutputs

end Tests.VerifiedProductionE2E
