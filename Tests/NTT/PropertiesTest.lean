/-
  AMO-Lean QA Suite: NTT Functional Properties
  Test ID: NTT-TEST-004
  Priority: HIGH (Correctness Validation)

  Validates key functional properties:
  1. Invertibility: INTT(NTT(x)) = x
  2. Length Preservation: |NTT(x)| = |x|
  3. N^(-1) Factor: Common bug detection

  If invertibility fails, the implementation is BROKEN.
-/

import AmoLean.NTT.Spec
import AmoLean.NTT.Goldilocks

namespace AmoLean.NTT.Tests.Properties

open AmoLean.NTT
open AmoLean.Field.Goldilocks

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: INVERTIBILITY TESTS
    THE MOST CRITICAL TEST: INTT(NTT(x)) = x
═══════════════════════════════════════════════════════════════════════════ -/

/-- Helper: Convert UInt64 list to GoldilocksField list -/
def toGF (xs : List UInt64) : List GoldilocksField :=
  xs.map fun x => ⟨x⟩

/-- Helper: Convert GoldilocksField list to UInt64 list -/
def fromGF (xs : List GoldilocksField) : List UInt64 :=
  xs.map fun x => x.value

/-- Test roundtrip for a given input -/
def testRoundtrip (input : List UInt64) : Bool :=
  let n := input.length
  if h : n > 0 then
    let gf_input := toGF input
    let ω := primitiveRoot n h
    let n_inv := GoldilocksField.inv ⟨n.toUInt64⟩

    let ntt_result : List GoldilocksField := NTT_spec ω gf_input
    let intt_result : List GoldilocksField := INTT_spec ω n_inv ntt_result

    fromGF intt_result == input
  else
    true  -- Empty list trivially passes

/-- Test roundtrip with detailed error reporting -/
def testRoundtripDetailed (input : List UInt64) : IO Bool := do
  let n := input.length
  if h : n > 0 then
    let gf_input := toGF input
    let ω := primitiveRoot n h
    let n_inv := GoldilocksField.inv ⟨n.toUInt64⟩

    let ntt_result : List GoldilocksField := NTT_spec ω gf_input
    let intt_result : List GoldilocksField := INTT_spec ω n_inv ntt_result

    let output := fromGF intt_result
    let passed := output == input

    if !passed then
      IO.println s!"    INPUT:  {input}"
      IO.println s!"    OUTPUT: {output}"
      -- Check for common N^(-1) bug
      let ratio := if output[0]? != some 0 && input[0]? != some 0 then
        (output[0]?.getD 1).toNat * n / (input[0]?.getD 1).toNat
      else 0
      if ratio == n then
        IO.println s!"    DIAGNOSIS: Missing N⁻¹ factor! Output = Input * {n}"
      else if ratio == 1 then
        IO.println s!"    DIAGNOSIS: Unknown error"
      else
        IO.println s!"    DIAGNOSIS: Scale factor appears to be {ratio}"

    return passed
  else
    return true

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: LENGTH PRESERVATION TESTS
═══════════════════════════════════════════════════════════════════════════ -/

/-- Test that NTT preserves length -/
def testNTTLength (n : Nat) (hn : n > 0) : Bool :=
  let input := toGF ((List.range n).map fun i => i.toUInt64)
  let ω := primitiveRoot n hn
  let output := NTT_spec ω input
  output.length == n

/-- Test that INTT preserves length -/
def testINTTLength (n : Nat) (hn : n > 0) : Bool :=
  let input := toGF ((List.range n).map fun i => i.toUInt64)
  let ω := primitiveRoot n hn
  let n_inv := GoldilocksField.inv (GoldilocksField.mk n.toUInt64)
  let output := INTT_spec ω n_inv input
  output.length == n

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 3: SPECIFIC INPUT PATTERNS
═══════════════════════════════════════════════════════════════════════════ -/

/-- Delta function: [1, 0, 0, ..., 0] -/
def deltaInput (n : Nat) : List UInt64 :=
  if n == 0 then [] else 1 :: List.replicate (n - 1) 0

/-- Constant function: [c, c, c, ..., c] -/
def constantInput (n : Nat) (c : UInt64) : List UInt64 :=
  List.replicate n c

/-- Ramp function: [0, 1, 2, ..., n-1] -/
def rampInput (n : Nat) : List UInt64 :=
  (List.range n).map (·.toUInt64)

/-- Alternating: [1, 0, 1, 0, ...] -/
def alternatingInput (n : Nat) : List UInt64 :=
  (List.range n).map fun i => if i % 2 == 0 then 1 else 0

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 4: RUNTIME VALIDATION SUITE
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     Properties QA Suite - NTT Correctness Validation         ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  let mut allPassed := true

  -- Test 1: Basic Roundtrip for Various Sizes
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 1: Roundtrip INTT(NTT(x)) = x                           │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let testSizes := [4, 8, 16, 32]

  for n in testSizes do
    let input := rampInput n
    let passed := testRoundtrip input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n} (ramp [0..{n-1}]): {status}"
    if !passed then
      _ ← testRoundtripDetailed input
      allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 2: Delta Function
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 2: Delta Function [1, 0, 0, ...]                        │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in testSizes do
    let input := deltaInput n
    let passed := testRoundtrip input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}: {status}"
    if !passed then
      _ ← testRoundtripDetailed input
      allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 3: Constant Function
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 3: Constant Function [c, c, c, ...]                     │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in testSizes do
    let input := constantInput n 42
    let passed := testRoundtrip input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}, c=42: {status}"
    if !passed then
      _ ← testRoundtripDetailed input
      allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 4: Alternating Pattern
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 4: Alternating [1, 0, 1, 0, ...]                        │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for n in testSizes do
    let input := alternatingInput n
    let passed := testRoundtrip input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n}: {status}"
    if !passed then
      _ ← testRoundtripDetailed input
      allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 5: Random-ish Values
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 5: Pseudo-Random Values                                 │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  -- Generate pseudo-random values using a simple LCG
  for n in testSizes do
    let input := (List.range n).map fun i =>
      ((i * 1103515245 + 12345) % 1000).toUInt64
    let passed := testRoundtrip input
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N={n} (LCG values): {status}"
    if !passed then
      _ ← testRoundtripDetailed input
      allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 6: Length Preservation (unrolled to avoid by omega in loop)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 6: Length Preservation                                  │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let ntt4Ok := testNTTLength 4 (by decide)
  let intt4Ok := testINTTLength 4 (by decide)
  IO.println s!"│ N=4: |NTT| = |INTT| = 4 ? {if ntt4Ok && intt4Ok then "✓ PASS" else "✗ FAIL"}"
  if !ntt4Ok || !intt4Ok then allPassed := false

  let ntt8Ok := testNTTLength 8 (by decide)
  let intt8Ok := testINTTLength 8 (by decide)
  IO.println s!"│ N=8: |NTT| = |INTT| = 8 ? {if ntt8Ok && intt8Ok then "✓ PASS" else "✗ FAIL"}"
  if !ntt8Ok || !intt8Ok then allPassed := false

  let ntt16Ok := testNTTLength 16 (by decide)
  let intt16Ok := testINTTLength 16 (by decide)
  IO.println s!"│ N=16: |NTT| = |INTT| = 16 ? {if ntt16Ok && intt16Ok then "✓ PASS" else "✗ FAIL"}"
  if !ntt16Ok || !intt16Ok then allPassed := false

  let ntt32Ok := testNTTLength 32 (by decide)
  let intt32Ok := testINTTLength 32 (by decide)
  IO.println s!"│ N=32: |NTT| = |INTT| = 32 ? {if ntt32Ok && intt32Ok then "✓ PASS" else "✗ FAIL"}"
  if !ntt32Ok || !intt32Ok then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 7: NTT of Delta is All-Ones (unrolled)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 7: NTT([1,0,0,...]) = [1,1,1,...]                       │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let delta4 := toGF (deltaInput 4)
  let ω4d := primitiveRoot 4 (by decide)
  let ntt_delta4 : List GoldilocksField := NTT_spec ω4d delta4
  let allOnes4 := ntt_delta4.all fun x => x.value == 1
  IO.println s!"│ N=4: NTT(delta) = all 1s ? {if allOnes4 then "✓ PASS" else "✗ FAIL"}"
  if !allOnes4 then
    IO.println s!"│   Got: {fromGF ntt_delta4}"
    allPassed := false

  let delta8 := toGF (deltaInput 8)
  let ω8d := primitiveRoot 8 (by decide)
  let ntt_delta8 : List GoldilocksField := NTT_spec ω8d delta8
  let allOnes8 := ntt_delta8.all fun x => x.value == 1
  IO.println s!"│ N=8: NTT(delta) = all 1s ? {if allOnes8 then "✓ PASS" else "✗ FAIL"}"
  if !allOnes8 then
    IO.println s!"│   Got: {fromGF ntt_delta8}"
    allPassed := false

  let delta16 := toGF (deltaInput 16)
  let ω16d := primitiveRoot 16 (by decide)
  let ntt_delta16 : List GoldilocksField := NTT_spec ω16d delta16
  let allOnes16 := ntt_delta16.all fun x => x.value == 1
  IO.println s!"│ N=16: NTT(delta) = all 1s ? {if allOnes16 then "✓ PASS" else "✗ FAIL"}"
  if !allOnes16 then
    IO.println s!"│   Got: {fromGF ntt_delta16}"
    allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  -- Test 8: NTT of Constants (unrolled)
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test 8: NTT([c,c,...]) = [n*c, 0, 0, ...]                    │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let c : UInt64 := 1
  let const4 := toGF (constantInput 4 c)
  let ω4c := primitiveRoot 4 (by decide)
  let ntt_const4 : List GoldilocksField := NTT_spec ω4c const4
  let first4Ok := ntt_const4[0]?.map (fun (x : GoldilocksField) => x.value) == some (4 * c)
  let rest4Zero := (ntt_const4.drop 1).all fun x => x.value == 0
  IO.println s!"│ N=4, c={c}: X₀=4*{c}, rest=0 ? {if first4Ok && rest4Zero then "✓ PASS" else "✗ FAIL"}"
  if !first4Ok || !rest4Zero then
    IO.println s!"│   Got: {fromGF ntt_const4}"
    allPassed := false

  let const8 := toGF (constantInput 8 c)
  let ω8c := primitiveRoot 8 (by decide)
  let ntt_const8 : List GoldilocksField := NTT_spec ω8c const8
  let first8Ok := ntt_const8[0]?.map (fun (x : GoldilocksField) => x.value) == some (8 * c)
  let rest8Zero := (ntt_const8.drop 1).all fun x => x.value == 0
  IO.println s!"│ N=8, c={c}: X₀=8*{c}, rest=0 ? {if first8Ok && rest8Zero then "✓ PASS" else "✗ FAIL"}"
  if !first8Ok || !rest8Zero then
    IO.println s!"│   Got: {fromGF ntt_const8}"
    allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n══════════════════════════════════════════════════════════════"
  if allPassed then
    IO.println "   RESULT: ALL PROPERTY TESTS PASSED ✓"
  else
    IO.println "   RESULT: SOME TESTS FAILED ✗"
  IO.println "══════════════════════════════════════════════════════════════"

  return allPassed

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 5: LARGE-SCALE FUZZING
    50 random vectors for each size
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     Fuzz Testing: 50 Random Vectors per Size                 ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  let mut totalTests := 0
  let mut passedTests := 0

  for n in [4, 8, 16] do  -- Limited sizes for O(N²) performance
    IO.println s!"\n  Testing N={n}..."
    let mut localPassed := 0

    for seed in List.range 50 do
      -- Generate pseudo-random input
      let input := (List.range n).map fun i =>
        (((seed + 1) * 1103515245 + i * 12345 + 1) % 10000).toUInt64
      let passed := testRoundtrip input
      totalTests := totalTests + 1
      if passed then
        passedTests := passedTests + 1
        localPassed := localPassed + 1

    IO.println s!"    N={n}: {localPassed}/50 passed"

  IO.println s!"\n  TOTAL: {passedTests}/{totalTests} tests passed"

  if passedTests == totalTests then
    IO.println "  STATUS: ALL FUZZ TESTS PASSED ✓"
  else
    IO.println s!"  STATUS: {totalTests - passedTests} TESTS FAILED ✗"

end AmoLean.NTT.Tests.Properties
