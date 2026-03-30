/-
  AMO-Lean — Verified Optimized NTT E2E Tests (Fase 32)
  Tests all optimization variants: radix-4, unrolling, cache blocking, bit-reversal.
  Verifies code generation produces non-empty C + Rust for all primes.
  0 sorry, 0 new axioms.
-/
import AmoLean.EGraph.Verified.Bitwise.VerifiedNTTOptimizations
import AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDCodeGen

set_option autoImplicit false

namespace Tests.VerifiedOptimizedNTTE2E

open AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
  (emitRadix4ButterflyC emitRadix4ButterflyRust
   emitBitReverseC emitBitReverseRust
   emitBitReverseRuntimeC emitBitReverseRuntimeRust
   emitNTTCFn emitNTTRustFn
   lowerRadix4ButterflyStmt)

open AmoLean.EGraph.Verified.Bitwise.VerifiedNTTOptimizations
  (emitNTTUnrolledC emitNTTUnrolledRust
   emitNTTBlockedC emitNTTBlockedRust
   butterfly_groups_disjoint butterfly_ij_distinct butterfly_cross_disjoint)

open AmoLean.EGraph.Verified.Bitwise.VerifiedSIMDCodeGen
  (babybear_ntt_neon_c babybear_ntt_avx2_c
   koalabear_ntt_neon_c koalabear_ntt_avx2_c
   mersenne31_ntt_neon_c mersenne31_ntt_avx2_c)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Optimization Coverage — all variants produce non-empty code
-- ══════════════════════════════════════════════════════════════════

/-- Test that ALL optimization variants produce non-empty C/Rust code. -/
def runOptimizationCoverage : IO Unit := do
  -- BabyBear: p = 2013265921, k = 27, c = 134217727
  -- KoalaBear: p = 2130706433, k = 24, c = 16777215
  -- Mersenne31: p = 2147483647, k = 31, c = 1
  -- Goldilocks: p = 18446744069414584321, k = 32, c = 4294967295
  let tests : List (String × String) := [
    -- Radix-4 butterfly (C + Rust)
    ("r4_bb_c",
      emitRadix4ButterflyC "a" "b" "c" "d" "w1" "w2" "w3" 2013265921 27 134217727),
    ("r4_bb_rust",
      emitRadix4ButterflyRust "a" "b" "c" "d" "w1" "w2" "w3" 2013265921 27 134217727),
    -- Bit-reversal (compile-time + runtime, C + Rust)
    ("bitrev_3_c", emitBitReverseC 3),
    ("bitrev_3_rust", emitBitReverseRust 3),
    ("bitrev_rt_3_c", emitBitReverseRuntimeC 3),
    ("bitrev_rt_3_rust", emitBitReverseRuntimeRust 3),
    -- Unrolled NTT (K=4, BabyBear)
    ("unrolled_bb_c", emitNTTUnrolledC 4 2013265921 27 134217727 4),
    ("unrolled_bb_rust", emitNTTUnrolledRust 4 2013265921 27 134217727 4),
    -- Cache-blocked NTT (blockSize=64, BabyBear)
    ("blocked_bb_c", emitNTTBlockedC 4 2013265921 27 134217727 64),
    ("blocked_bb_rust", emitNTTBlockedRust 4 2013265921 27 134217727 64),
    -- SIMD variants (NEON + AVX2)
    ("simd_neon_bb", babybear_ntt_neon_c 4),
    ("simd_avx2_bb", babybear_ntt_avx2_c 4),
    ("simd_neon_kb", koalabear_ntt_neon_c 4),
    ("simd_avx2_kb", koalabear_ntt_avx2_c 4),
    ("simd_neon_m31", mersenne31_ntt_neon_c 4),
    ("simd_avx2_m31", mersenne31_ntt_avx2_c 4),
    -- All primes: baseline scalar NTT (C)
    ("bb_ntt_c", emitNTTCFn 4 2013265921 27 134217727 "bb_ntt"),
    ("kb_ntt_c", emitNTTCFn 4 2130706433 24 16777215 "kb_ntt"),
    ("m31_ntt_c", emitNTTCFn 4 2147483647 31 1 "m31_ntt"),
    ("gl_ntt_c", emitNTTCFn 4 18446744069414584321 32 4294967295 "gl_ntt"),
    -- All primes: baseline scalar NTT (Rust)
    ("bb_ntt_rust", emitNTTRustFn 4 2013265921 27 134217727 "bb_ntt"),
    ("kb_ntt_rust", emitNTTRustFn 4 2130706433 24 16777215 "kb_ntt"),
    ("m31_ntt_rust", emitNTTRustFn 4 2147483647 31 1 "m31_ntt"),
    ("gl_ntt_rust", emitNTTRustFn 4 18446744069414584321 32 4294967295 "gl_ntt")
  ]
  let mut passed := 0
  let mut failed := 0
  for (name, code) in tests do
    if code.length > 0 then passed := passed + 1
    else do IO.println s!"FAIL: {name} produced empty output"; failed := failed + 1
  IO.println s!"═══ Optimization Coverage: {passed}/{tests.length} produce non-empty output ═══"
  if failed == 0 then IO.println "ALL PASS" else IO.println s!"{failed} FAILED"

#eval runOptimizationCoverage

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Show optimized code samples
-- ══════════════════════════════════════════════════════════════════

/-- Display representative samples of each optimization variant. -/
def showOptimizedSamples : IO Unit := do
  IO.println "\n═══ RADIX-4 BUTTERFLY (BabyBear, C) ═══"
  IO.println (emitRadix4ButterflyC "a" "b" "c" "d" "w1" "w2" "w3" 2013265921 27 134217727)

  IO.println "\n═══ BIT-REVERSAL COMPILE-TIME (logN=3, C) ═══"
  IO.println (emitBitReverseC 3)

  IO.println "\n═══ BIT-REVERSAL RUNTIME (logN=4, C) ═══"
  IO.println (emitBitReverseRuntimeC 4)

  IO.println "\n═══ UNROLLED NTT (K=4, BabyBear, C) ═══"
  IO.println (emitNTTUnrolledC 4 2013265921 27 134217727 4)

  IO.println "\n═══ CACHE-BLOCKED NTT (blockSize=64, BabyBear, C) ═══"
  IO.println (emitNTTBlockedC 4 2013265921 27 134217727 64)

  IO.println "\n═══ SIMD NTT NEON (BabyBear, logN=4, C) ═══"
  IO.println (babybear_ntt_neon_c 4)

#eval showOptimizedSamples

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Verification summary — compile-time proofs
-- ══════════════════════════════════════════════════════════════════

-- Disjointness is not vacuous: base1=0, base2=8, span=8
-- Group 0: [0,8), Group 1: [8,16). i1=2, i2=9 => distinct.
example : (2 : Nat) ≠ 9 :=
  butterfly_groups_disjoint 0 8 8 (by omega) 2
    ⟨by omega, by omega⟩ 9 ⟨by omega, by omega⟩

-- Within-group i != j when half > 0
example : (2 : Nat) ≠ 6 :=
  butterfly_ij_distinct 4 0 2 (by omega)

-- Cross-group disjointness
example : (2 : Nat) ≠ 13 :=
  butterfly_cross_disjoint 0 8 4 2 1 (by omega) (by omega) (by omega)

-- Radix-4 butterfly C output is non-empty (native_decide)
example : (emitRadix4ButterflyC "a" "b" "c" "d" "w1" "w2" "w3"
    2013265921 27 134217727).length > 0 := by native_decide

-- Unrolled NTT C output is non-empty
example : (emitNTTUnrolledC 3 17 4 1 2).length > 0 := by native_decide

-- Blocked NTT C output is non-empty
example : (emitNTTBlockedC 3 17 4 1 4).length > 0 := by native_decide

-- Bit-reversal compile-time C output is non-empty
example : (emitBitReverseC 3).length > 0 := by native_decide

-- Bit-reversal runtime C output is non-empty
example : (emitBitReverseRuntimeC 3).length > 0 := by native_decide

-- SIMD NEON BabyBear NTT produces non-empty output
example : (babybear_ntt_neon_c 4).length > 0 := by native_decide

-- SIMD AVX2 BabyBear NTT produces non-empty output
example : (babybear_ntt_avx2_c 4).length > 0 := by native_decide

end Tests.VerifiedOptimizedNTTE2E
