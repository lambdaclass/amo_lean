/-
  AMO-Lean QA Suite: Golden Correctness Test
  Test ID: NTT-TEST-003
  Priority: CRITICAL (Algorithm Validation)

  THE GOLDEN TEST: NTT_spec (O(N²)) == NTT_recursive (O(N log N))

  If these don't match, one of the implementations is WRONG.
  NTT_spec is the reference specification; NTT_recursive is the optimized algorithm.

  Test Strategy:
  1. Compile-time proofs using native_decide for small N
  2. Runtime fuzzing with random vectors for larger N
-/

import AmoLean.NTT.Spec
import AmoLean.NTT.CooleyTukey
import AmoLean.NTT.Goldilocks

namespace AmoLean.NTT.Tests.Correctness

open AmoLean.NTT
open AmoLean.Field.Goldilocks

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: COMPILE-TIME VERIFICATION
    If these examples compile, the algorithms are provably equal for these inputs
═══════════════════════════════════════════════════════════════════════════ -/

-- Helper function to compare two GoldilocksField lists by value
def gfListEq (xs ys : List GoldilocksField) : Bool :=
  xs.length == ys.length &&
  (xs.zip ys).all fun (x, y) => x.value == y.value

-- Fixed test vectors
def testVec4 : List GoldilocksField := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩]
def testVec8 : List GoldilocksField := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩]

/-! ### Compile-Time Proof: N=4 -/

-- This is the compile-time equivalence proof
-- If it compiles, NTT_spec == NTT_recursive for testVec4
example : gfListEq (NTT_spec (primitiveRoot 4 (by decide)) testVec4)
                   (NTT_recursive (primitiveRoot 4 (by decide)) testVec4) = true := by
  native_decide

/-! ### Compile-Time Proof: N=8 -/

example : gfListEq (NTT_spec (primitiveRoot 8 (by decide)) testVec8)
                   (NTT_recursive (primitiveRoot 8 (by decide)) testVec8) = true := by
  native_decide

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: RUNTIME EQUIVALENCE TESTING
    Systematic testing for various input patterns
═══════════════════════════════════════════════════════════════════════════ -/

/-- Test equivalence for a given input -/
def testEquivalence (input : List UInt64) : Bool :=
  let n := input.length
  if h : n > 0 then
    let gf_input : List GoldilocksField := input.map fun x => ⟨x⟩
    let ω := primitiveRoot n h
    let spec_result := NTT_spec ω gf_input
    let rec_result := NTT_recursive ω gf_input
    gfListEq spec_result rec_result
  else
    true

/-- Test equivalence with detailed output -/
def testEquivalenceDetailed (input : List UInt64) : IO Bool := do
  let n := input.length
  if h : n > 0 then
    let gf_input : List GoldilocksField := input.map fun x => ⟨x⟩
    let ω := primitiveRoot n h

    let spec_result := NTT_spec ω gf_input
    let rec_result := NTT_recursive ω gf_input

    let passed := gfListEq spec_result rec_result

    if !passed then
      IO.println s!"  MISMATCH DETECTED!"
      IO.println s!"    Input: {input}"
      IO.println s!"    NTT_spec:     {spec_result.map (·.value)}"
      IO.println s!"    NTT_recursive: {rec_result.map (·.value)}"

      -- Find first differing position
      for i in List.range n do
        let s := spec_result[i]?.map (·.value)
        let r := rec_result[i]?.map (·.value)
        if s != r then
          IO.println s!"    First diff at index {i}: spec={s}, rec={r}"
          break

    return passed
  else
    return true

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 3: RUNTIME TEST SUITE
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     GOLDEN TEST: NTT_spec vs NTT_recursive                   ║"
  IO.println "║     If these don't match, the implementation is BROKEN       ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  let mut allPassed := true

  -- Test 1: Fixed vectors (same as compile-time)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 1: Fixed Test Vectors                                   │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let fixedVectors : List (List UInt64 × String) := [
    ([1, 2, 3, 4], "N=4"),
    ([1, 2, 3, 4, 5, 6, 7, 8], "N=8"),
    ((List.range 16).map fun i => (i + 1).toUInt64, "N=16"),
    ((List.range 32).map fun i => (i + 1).toUInt64, "N=32")
  ]

  for (vec, name) in fixedVectors do
    let input := vec
    let passed ← testEquivalenceDetailed input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ {name}: spec == recursive ? {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 2: Delta function
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 2: Delta Function [1, 0, 0, ...]                        │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in [4, 8, 16, 32] do
    let input : List UInt64 := 1 :: List.replicate (n - 1) 0
    let passed ← testEquivalenceDetailed input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}: {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 3: Constant function
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 3: Constant Function [c, c, c, ...]                     │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in [4, 8, 16, 32] do
    let input := List.replicate n (42 : UInt64)
    let passed ← testEquivalenceDetailed input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}, c=42: {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 4: Alternating pattern
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 4: Alternating [1, 0, 1, 0, ...]                        │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in [4, 8, 16, 32] do
    let input := (List.range n).map fun i => if i % 2 == 0 then (1 : UInt64) else 0
    let passed ← testEquivalenceDetailed input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}: {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 5: Random fuzzing (50 vectors per size)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 5: Random Fuzzing (50 vectors per size)                 │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in [4, 8, 16, 32] do
    let mut localPassed := 0
    for seed in List.range 50 do
      let input := (List.range n).map fun i =>
        (((seed + 1) * 1103515245 + i * 12345 + 1) % 10000).toUInt64
      let passed := testEquivalence input
      if passed then localPassed := localPassed + 1

    let status := if localPassed == 50 then "✓ ALL PASS" else s!"✗ {50 - localPassed} FAILED"
    IO.println s!"│ N={n}: {localPassed}/50 {status}"
    if localPassed != 50 then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 6: Edge cases
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 6: Edge Cases                                           │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  -- All zeros
  let zeros := List.replicate 8 (0 : UInt64)
  let zerosPass ← testEquivalenceDetailed zeros
  IO.println s!"│ All zeros N=8: {if zerosPass then "✓ PASS" else "✗ FAIL"}"
  if !zerosPass then allPassed := false

  -- Single element at end
  let singleEnd := List.replicate 7 (0 : UInt64) ++ [1]
  let singleEndPass ← testEquivalenceDetailed singleEnd
  IO.println s!"│ Single at end N=8: {if singleEndPass then "✓ PASS" else "✗ FAIL"}"
  if !singleEndPass then allPassed := false

  -- Large values
  let large := (List.range 8).map fun i => (ORDER.toNat - i - 1).toUInt64
  let largePass ← testEquivalenceDetailed large
  IO.println s!"│ Large values N=8: {if largePass then "✓ PASS" else "✗ FAIL"}"
  if !largePass then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n══════════════════════════════════════════════════════════════"
  if allPassed then
    IO.println "   GOLDEN TEST RESULT: ALL TESTS PASSED ✓"
    IO.println "   NTT_spec and NTT_recursive are EQUIVALENT"
  else
    IO.println "   GOLDEN TEST RESULT: SOME TESTS FAILED ✗"
    IO.println "   IMPLEMENTATION ERROR DETECTED - INVESTIGATE IMMEDIATELY"
  IO.println "══════════════════════════════════════════════════════════════"

  return allPassed

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 4: INVERSE EQUIVALENCE TEST
    INTT_spec vs INTT_recursive
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     INVERSE GOLDEN TEST: INTT_spec vs INTT_recursive         ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  let mut allPassed := true

  -- Test N=4
  let input4 : List GoldilocksField := (List.range 4).map fun i => GoldilocksField.mk (i + 1).toUInt64
  let ω4 := primitiveRoot 4 (by decide)
  let n_inv4 := GoldilocksField.inv (GoldilocksField.mk 4)
  let ntt4 : List GoldilocksField := NTT_spec ω4 input4
  let intt_spec4 : List GoldilocksField := INTT_spec ω4 n_inv4 ntt4
  let intt_rec4 : List GoldilocksField := INTT_recursive ω4 n_inv4 ntt4
  let passed4 := gfListEq intt_spec4 intt_rec4
  let rt4 := gfListEq intt_spec4 input4
  IO.println s!"  N=4: INTT_spec == INTT_recursive ? {if passed4 then "✓ PASS" else "✗ FAIL"}"
  IO.println s!"       INTT(NTT(x)) == x ? {if rt4 then "✓ PASS" else "✗ FAIL"}"
  if !passed4 || !rt4 then allPassed := false

  -- Test N=8
  let input8 : List GoldilocksField := (List.range 8).map fun i => GoldilocksField.mk (i + 1).toUInt64
  let ω8 := primitiveRoot 8 (by decide)
  let n_inv8 := GoldilocksField.inv (GoldilocksField.mk 8)
  let ntt8 : List GoldilocksField := NTT_spec ω8 input8
  let intt_spec8 : List GoldilocksField := INTT_spec ω8 n_inv8 ntt8
  let intt_rec8 : List GoldilocksField := INTT_recursive ω8 n_inv8 ntt8
  let passed8 := gfListEq intt_spec8 intt_rec8
  let rt8 := gfListEq intt_spec8 input8
  IO.println s!"  N=8: INTT_spec == INTT_recursive ? {if passed8 then "✓ PASS" else "✗ FAIL"}"
  IO.println s!"       INTT(NTT(x)) == x ? {if rt8 then "✓ PASS" else "✗ FAIL"}"
  if !passed8 || !rt8 then allPassed := false

  -- Test N=16
  let input16 : List GoldilocksField := (List.range 16).map fun i => GoldilocksField.mk (i + 1).toUInt64
  let ω16 := primitiveRoot 16 (by decide)
  let n_inv16 := GoldilocksField.inv (GoldilocksField.mk 16)
  let ntt16 : List GoldilocksField := NTT_spec ω16 input16
  let intt_spec16 : List GoldilocksField := INTT_spec ω16 n_inv16 ntt16
  let intt_rec16 : List GoldilocksField := INTT_recursive ω16 n_inv16 ntt16
  let passed16 := gfListEq intt_spec16 intt_rec16
  let rt16 := gfListEq intt_spec16 input16
  IO.println s!"  N=16: INTT_spec == INTT_recursive ? {if passed16 then "✓ PASS" else "✗ FAIL"}"
  IO.println s!"       INTT(NTT(x)) == x ? {if rt16 then "✓ PASS" else "✗ FAIL"}"
  if !passed16 || !rt16 then allPassed := false

  IO.println "\n══════════════════════════════════════════════════════════════"
  if allPassed then
    IO.println "   INVERSE GOLDEN TEST: PASSED ✓"
  else
    IO.println "   INVERSE GOLDEN TEST: FAILED ✗"
  IO.println "══════════════════════════════════════════════════════════════"

end AmoLean.NTT.Tests.Correctness
