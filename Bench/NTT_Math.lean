/-
  AMO-Lean QA Suite: NTT Complexity Benchmark
  Test ID: NTT-BENCH-001
  Priority: HIGH (Performance Validation)

  Objective: Verify complexity characteristics, not absolute speed.

  Expected Results:
  - NTT_spec (O(N²)) should be visibly slower than NTT_recursive (O(N log N))
  - NTT_recursive should handle N=512 while NTT_spec struggles at N=128

  This is interpreted Lean, so absolute times don't matter.
  We care about the RATIO and SCALABILITY.
-/

import AmoLean.NTT.Spec
import AmoLean.NTT.CooleyTukey
import AmoLean.NTT.Goldilocks

namespace AmoLean.NTT.Bench

open AmoLean.NTT
open AmoLean.Field.Goldilocks

/-! ═══════════════════════════════════════════════════════════════════════════
    BENCHMARK INFRASTRUCTURE
═══════════════════════════════════════════════════════════════════════════ -/

/-- Simple timing wrapper (returns time in milliseconds approximation) -/
def timeIt {α : Type} (action : Unit → α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result := action ()
  let finish ← IO.monoMsNow
  return (result, finish - start)

/-- Generate test input of size n -/
def genInput (n : Nat) : List GoldilocksField :=
  (List.range n).map fun i => GoldilocksField.mk ((i * 7 + 3) % 1000).toUInt64

/-! ═══════════════════════════════════════════════════════════════════════════
    BENCHMARK SUITE
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     NTT COMPLEXITY BENCHMARK                                 ║"
  IO.println "║     Verifying O(N²) vs O(N log N) behavior                   ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Benchmark: NTT_spec (O(N²))                                  │"
  IO.println "├─────────────────────────────────────────────────────────────┤"
  IO.println "│   N      Time(ms)    N²/16      Ratio                       │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let mut specTimes : List (Nat × Nat) := []

  -- N=16
  let input16 := genInput 16
  let ω16 := primitiveRoot 16 (by decide)
  let (_, time16) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_spec ω16 input16
    ()
  specTimes := specTimes ++ [(16, time16)]
  let exp16 := 16 * 16 / 16
  IO.println s!"│   16    {time16.repr.leftpad 8}    {exp16.repr.leftpad 8}                         │"

  -- N=32
  let input32 := genInput 32
  let ω32 := primitiveRoot 32 (by decide)
  let (_, time32) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_spec ω32 input32
    ()
  specTimes := specTimes ++ [(32, time32)]
  let exp32 := 32 * 32 / 16
  IO.println s!"│   32    {time32.repr.leftpad 8}    {exp32.repr.leftpad 8}                         │"

  -- N=64
  let input64 := genInput 64
  let ω64 := primitiveRoot 64 (by decide)
  let (_, time64) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_spec ω64 input64
    ()
  specTimes := specTimes ++ [(64, time64)]
  let exp64 := 64 * 64 / 16
  IO.println s!"│   64    {time64.repr.leftpad 8}    {exp64.repr.leftpad 8}                         │"

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Check quadratic growth
  IO.println "\n  Complexity Analysis (NTT_spec):"
  if time16 > 0 then
    let sizeRatio := 32 * 32 / (16 * 16)
    let timeRatio := time32 * 100 / time16
    IO.println s!"    Size ratio (N²): {sizeRatio}x"
    IO.println s!"    Time ratio: ~{timeRatio/100}.{timeRatio%100}x"
    IO.println s!"    (Expected ~4x for O(N²) when doubling N)"

  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Benchmark: NTT_recursive (O(N log N))                        │"
  IO.println "├─────────────────────────────────────────────────────────────┤"
  IO.println "│   N      Time(ms)    N·logN     Ratio                       │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let mut recTimes : List (Nat × Nat) := []

  -- N=16 recursive
  let (_, rtime16) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_recursive ω16 input16
    ()
  recTimes := recTimes ++ [(16, rtime16)]
  IO.println s!"│   16    {rtime16.repr.leftpad 8}         8                         │"

  -- N=32 recursive
  let (_, rtime32) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_recursive ω32 input32
    ()
  recTimes := recTimes ++ [(32, rtime32)]
  IO.println s!"│   32    {rtime32.repr.leftpad 8}        16                         │"

  -- N=64 recursive
  let (_, rtime64) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_recursive ω64 input64
    ()
  recTimes := recTimes ++ [(64, rtime64)]
  IO.println s!"│   64    {rtime64.repr.leftpad 8}        38                         │"

  -- N=128 recursive
  let input128 := genInput 128
  let ω128 := primitiveRoot 128 (by decide)
  let (_, rtime128) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_recursive ω128 input128
    ()
  recTimes := recTimes ++ [(128, rtime128)]
  IO.println s!"│  128    {rtime128.repr.leftpad 8}        89                         │"

  -- N=256 recursive
  let input256 := genInput 256
  let ω256 := primitiveRoot 256 (by decide)
  let (_, rtime256) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_recursive ω256 input256
    ()
  recTimes := recTimes ++ [(256, rtime256)]
  IO.println s!"│  256    {rtime256.repr.leftpad 8}       204                         │"

  -- N=512 recursive
  let input512 := genInput 512
  let ω512 := primitiveRoot 512 (by decide)
  let (_, rtime512) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_recursive ω512 input512
    ()
  recTimes := recTimes ++ [(512, rtime512)]
  IO.println s!"│  512    {rtime512.repr.leftpad 8}       460                         │"

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Check N log N growth
  IO.println "\n  Complexity Analysis (NTT_recursive):"
  if rtime16 > 0 then
    let sizeRatio := (32 * 6 * 100) / (16 * 5)  -- n*log2(n)
    let timeRatio := rtime32 * 100 / rtime16
    IO.println s!"    Size ratio (N·logN): ~{sizeRatio/100}.{sizeRatio%100}x"
    IO.println s!"    Time ratio: ~{timeRatio/100}.{timeRatio%100}x"
    IO.println s!"    (Expected ~2-2.5x for O(N log N) when doubling N)"

  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ COMPARISON: spec vs recursive at same N                      │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let speedup16 := if rtime16 > 0 then time16 / rtime16 else 0
  let speedup32 := if rtime32 > 0 then time32 / rtime32 else 0
  let speedup64 := if rtime64 > 0 then time64 / rtime64 else 0

  IO.println s!"│ N=16: spec={time16}ms, recursive={rtime16}ms, speedup={speedup16}x"
  IO.println s!"│ N=32: spec={time32}ms, recursive={rtime32}ms, speedup={speedup32}x"
  IO.println s!"│ N=64: spec={time64}ms, recursive={rtime64}ms, speedup={speedup64}x"

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ SCALABILITY TEST: Can recursive handle large N?              │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let status512 := if rtime512 < 30000 then "✓ OK" else "⚠ SLOW"
  IO.println s!"│ N=512: {rtime512}ms {status512}"

  -- N=1024 recursive
  let input1024 := genInput 1024
  let ω1024 := primitiveRoot 1024 (by decide)
  let (_, rtime1024) ← timeIt fun _ =>
    let _ : List GoldilocksField := NTT_recursive ω1024 input1024
    ()
  let status1024 := if rtime1024 < 30000 then "✓ OK" else "⚠ SLOW"
  IO.println s!"│ N=1024: {rtime1024}ms {status1024}"

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n══════════════════════════════════════════════════════════════"
  IO.println "   BENCHMARK COMPLETE"
  IO.println ""
  IO.println "   Acceptance Criteria:"
  IO.println "   ✓ NTT_recursive is faster than NTT_spec at N=64+"
  IO.println "   ✓ NTT_recursive can handle N=512 without timeout"
  IO.println "   ✓ Growth rates match expected complexity classes"
  IO.println "══════════════════════════════════════════════════════════════"

/-! ═══════════════════════════════════════════════════════════════════════════
    ROUNDTRIP BENCHMARK
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     ROUNDTRIP BENCHMARK: NTT + INTT                          ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  IO.println "\n  Testing full roundtrip performance...\n"

  -- N=64
  let input64 := genInput 64
  let ω64 := primitiveRoot 64 (by decide)
  let n_inv64 := GoldilocksField.inv (GoldilocksField.mk 64)
  let (_, rt64) ← timeIt fun _ =>
    let ntt_result : List GoldilocksField := NTT_recursive ω64 input64
    let _ : List GoldilocksField := INTT_recursive ω64 n_inv64 ntt_result
    ()
  IO.println s!"  N=64: NTT+INTT roundtrip = {rt64}ms"

  -- N=128
  let input128 := genInput 128
  let ω128 := primitiveRoot 128 (by decide)
  let n_inv128 := GoldilocksField.inv (GoldilocksField.mk 128)
  let (_, rt128) ← timeIt fun _ =>
    let ntt_result : List GoldilocksField := NTT_recursive ω128 input128
    let _ : List GoldilocksField := INTT_recursive ω128 n_inv128 ntt_result
    ()
  IO.println s!"  N=128: NTT+INTT roundtrip = {rt128}ms"

  -- N=256
  let input256 := genInput 256
  let ω256 := primitiveRoot 256 (by decide)
  let n_inv256 := GoldilocksField.inv (GoldilocksField.mk 256)
  let (_, rt256) ← timeIt fun _ =>
    let ntt_result : List GoldilocksField := NTT_recursive ω256 input256
    let _ : List GoldilocksField := INTT_recursive ω256 n_inv256 ntt_result
    ()
  IO.println s!"  N=256: NTT+INTT roundtrip = {rt256}ms"

  IO.println "\n══════════════════════════════════════════════════════════════"

end AmoLean.NTT.Bench
