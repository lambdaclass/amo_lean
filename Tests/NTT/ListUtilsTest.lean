/-
  AMO-Lean QA Suite: ListUtils Validation
  Test ID: NTT-TEST-001
  Priority: CRITICAL (Foundation)

  If ListUtils fails, the entire NTT algorithm fails.
  These tests validate structural integrity and edge cases.

  Test Categories:
  1. Structural Integrity - Length preservation, roundtrip
  2. Edge Cases - Empty, singleton, odd-length lists
  3. Index Correspondence - evens_get, odds_get correctness
-/

import AmoLean.NTT.ListUtils

namespace AmoLean.NTT.Tests.ListUtils

open AmoLean.NTT

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: STRUCTURAL INTEGRITY TESTS
    Critical invariants that must hold for any input
═══════════════════════════════════════════════════════════════════════════ -/

/-! ### Test 1.1: Length Preservation Theorem
    length(evens(l)) + length(odds(l)) = length(l)
    This is a compile-time proof - if it compiles, it's correct. -/

example : ∀ (l : List Nat), (evens l).length + (odds l).length = l.length :=
  evens_odds_length

/-! ### Test 1.2: Roundtrip Property (THE CRITICAL TEST)
    interleave(evens(l), odds(l)) = l
    If this fails, Cooley-Tukey will produce garbage. -/

example : ∀ (l : List Nat), interleave (evens l) (odds l) = l :=
  interleave_evens_odds

/-! ### Test 1.3: Interleave Length
    length(interleave(xs, ys)) = length(xs) + length(ys) -/

example : ∀ (xs ys : List Nat), (interleave xs ys).length = xs.length + ys.length :=
  interleave_length

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: EDGE CASE TESTS
    Boundary conditions that often cause bugs
═══════════════════════════════════════════════════════════════════════════ -/

/-! ### Test 2.1: Empty List -/

-- evens of empty is empty
example : evens ([] : List Nat) = [] := rfl

-- odds of empty is empty
example : odds ([] : List Nat) = [] := rfl

-- roundtrip on empty
example : interleave (evens ([] : List Nat)) (odds []) = [] := rfl

/-! ### Test 2.2: Singleton List [x] -/

-- evens of [x] is [x]
example : evens [42] = [42] := rfl

-- odds of [x] is []
example : odds [42] = ([] : List Nat) := rfl

-- roundtrip on singleton
example : interleave (evens [42]) (odds [42]) = [42] := rfl

/-! ### Test 2.3: Two-element List [x, y] -/

example : evens [1, 2] = [1] := rfl
example : odds [1, 2] = [2] := rfl
example : interleave (evens [1, 2]) (odds [1, 2]) = [1, 2] := rfl

/-! ### Test 2.4: Odd-length List [x, y, z] -/

example : evens [1, 2, 3] = [1, 3] := rfl
example : odds [1, 2, 3] = [2] := rfl
example : interleave (evens [1, 2, 3]) (odds [1, 2, 3]) = [1, 2, 3] := rfl

/-! ### Test 2.5: Odd-length List [a, b, c, d, e] -/

example : evens [1, 2, 3, 4, 5] = [1, 3, 5] := rfl
example : odds [1, 2, 3, 4, 5] = [2, 4] := rfl
example : interleave (evens [1, 2, 3, 4, 5]) (odds [1, 2, 3, 4, 5]) = [1, 2, 3, 4, 5] := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 3: POWER-OF-2 TESTS (NTT-Critical)
    These sizes are used in actual NTT computations
═══════════════════════════════════════════════════════════════════════════ -/

/-! ### Test 3.1: N=4 (minimum NTT size) -/

def test4 : List Nat := [0, 1, 2, 3]

example : evens test4 = [0, 2] := rfl
example : odds test4 = [1, 3] := rfl
example : interleave (evens test4) (odds test4) = test4 := rfl
example : (evens test4).length = 2 := rfl
example : (odds test4).length = 2 := rfl

/-! ### Test 3.2: N=8 -/

def test8 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

example : evens test8 = [0, 2, 4, 6] := rfl
example : odds test8 = [1, 3, 5, 7] := rfl
example : interleave (evens test8) (odds test8) = test8 := rfl

/-! ### Test 3.3: N=16 -/

def test16 : List Nat := List.range 16

-- Compile-time verification using native_decide
example : evens test16 = [0, 2, 4, 6, 8, 10, 12, 14] := by native_decide
example : odds test16 = [1, 3, 5, 7, 9, 11, 13, 15] := by native_decide
example : interleave (evens test16) (odds test16) = test16 := by native_decide

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 4: INDEX CORRESPONDENCE TESTS
    Verify that evens[i] = original[2*i] and odds[i] = original[2*i+1]
═══════════════════════════════════════════════════════════════════════════ -/

/-! ### Test 4.1: evens_get correspondence -/

-- For test8: evens[0] = test8[0], evens[1] = test8[2], evens[2] = test8[4], evens[3] = test8[6]
example : (evens test8)[0]? = test8[0]? := rfl
example : (evens test8)[1]? = test8[2]? := rfl
example : (evens test8)[2]? = test8[4]? := rfl
example : (evens test8)[3]? = test8[6]? := rfl

/-! ### Test 4.2: odds_get correspondence -/

-- For test8: odds[0] = test8[1], odds[1] = test8[3], odds[2] = test8[5], odds[3] = test8[7]
example : (odds test8)[0]? = test8[1]? := rfl
example : (odds test8)[1]? = test8[3]? := rfl
example : (odds test8)[2]? = test8[5]? := rfl
example : (odds test8)[3]? = test8[7]? := rfl

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 5: RUNTIME VALIDATION (#eval tests)
    These tests run at compile time and print results
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     ListUtils QA Suite - Runtime Validation                  ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"

  -- Test batch: Various sizes
  let testCases := [
    ([], "empty"),
    ([1], "singleton"),
    ([1, 2], "pair"),
    ([1, 2, 3], "triple (odd)"),
    ([1, 2, 3, 4], "N=4"),
    ([1, 2, 3, 4, 5], "N=5 (odd)"),
    (List.range 8, "N=8"),
    (List.range 16, "N=16"),
    (List.range 32, "N=32"),
    (List.range 64, "N=64")
  ]

  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test: Length Preservation                                    │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  let mut allPassed := true

  for (tc, name) in testCases do
    let l := tc
    let lenEvens := (evens l).length
    let lenOdds := (odds l).length
    let totalLen := l.length
    let passed := lenEvens + lenOdds == totalLen
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ {name}: evens={lenEvens} + odds={lenOdds} = {lenEvens + lenOdds} (expected {totalLen}) {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test: Roundtrip Property                                     │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for (tc, name) in testCases do
    let l := tc
    let reconstructed := interleave (evens l) (odds l)
    let passed := reconstructed == l
    let status := if passed then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ {name}: interleave(evens, odds) == original: {status}"
    if !passed then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Test: Power-of-2 Lengths (NTT-Critical)                      │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for k in [1, 2, 3, 4, 5, 6] do
    let n := 2^k
    let l := List.range n
    let lenEvens := (evens l).length
    let lenOdds := (odds l).length
    let expectedHalf := n / 2
    let passedEvens := lenEvens == expectedHalf
    let passedOdds := lenOdds == expectedHalf
    let status := if passedEvens && passedOdds then "✓ PASS" else "✗ FAIL"
    IO.println s!"│ N=2^{k}={n}: evens.len={lenEvens}, odds.len={lenOdds} (expected {expectedHalf} each) {status}"
    if !passedEvens || !passedOdds then allPassed := false

  IO.println "└─────────────────────────────────────────────────────────────┘"

  IO.println "\n══════════════════════════════════════════════════════════════"
  if allPassed then
    IO.println "   RESULT: ALL LISTUTILS TESTS PASSED ✓"
  else
    IO.println "   RESULT: SOME TESTS FAILED ✗"
  IO.println "══════════════════════════════════════════════════════════════"

  return allPassed

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 6: STRESS TEST
    Larger inputs to catch potential stack overflow or performance issues
═══════════════════════════════════════════════════════════════════════════ -/

#eval! do
  IO.println "\n┌─────────────────────────────────────────────────────────────┐"
  IO.println "│ Stress Test: Large List Operations                          │"
  IO.println "├─────────────────────────────────────────────────────────────┤"

  for k in [7, 8, 9, 10] do  -- N = 128, 256, 512, 1024
    let n := 2^k
    let l := List.range n
    let e := evens l
    let o := odds l
    let r := interleave e o
    let passed := r == l && e.length + o.length == n
    let status := if passed then "✓" else "✗"
    IO.println s!"│ N=2^{k}={n}: roundtrip={passed} {status}"

  IO.println "└─────────────────────────────────────────────────────────────┘"

end AmoLean.NTT.Tests.ListUtils
