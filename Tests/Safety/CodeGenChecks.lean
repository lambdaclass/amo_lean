/-
  AMO-Lean: Safety Checks for Generated C Code
  Phase 0 Testing Infrastructure

  This module verifies that generated C code complies with design decisions:
  - DD-002: Uses field_add/field_mul instead of native + / *
  - DD-003: Uses restrict keyword and debug assertions
  - DD-006: Compatible with sanitizers

  These are static checks that analyze the generated code text.
-/

import AmoLean.Vector.CodeGen

namespace Tests.Safety.CodeGenChecks

open AmoLean.Vector.CodeGen

/-! ## Part 1: Pattern Checking Infrastructure -/

/-- Result of a safety check -/
structure CheckResult where
  name : String
  passed : Bool
  details : String
  deriving Repr

/-- Check if a string contains a pattern -/
def containsPattern (text : String) (pattern : String) : Bool :=
  (text.splitOn pattern).length > 1

/-- Count occurrences of a pattern -/
def countPattern (text : String) (pattern : String) : Nat :=
  -- Simple implementation: split and count
  let parts := text.splitOn pattern
  parts.length - 1

/-! ## Part 2: DD-002 Checks (Field Arithmetic) -/

/-- Check that field_add is used instead of naked + -/
def checkFieldAdd (code : String) : CheckResult :=
  let hasFieldAdd := containsPattern code "field_add("
  let fieldAddCount := countPattern code "field_add("
  -- Look for dangerous patterns: bare + in arithmetic context
  -- We check for patterns like "= ... + ..." that aren't field_add
  let hasDangerousPlus := containsPattern code "] + " ||
                          containsPattern code ") + " ||
                          -- Allow for loop increments like "i++"
                          false
  {
    name := "DD-002: field_add usage"
    passed := hasFieldAdd && fieldAddCount > 0
    details := s!"Found {fieldAddCount} uses of field_add(). " ++
               if hasDangerousPlus then "WARNING: Potential bare + detected."
               else "No dangerous + patterns detected."
  }

/-- Check that field_mul is used instead of naked * -/
def checkFieldMul (code : String) : CheckResult :=
  let hasFieldMul := containsPattern code "field_mul("
  let fieldMulCount := countPattern code "field_mul("
  {
    name := "DD-002: field_mul usage"
    passed := hasFieldMul && fieldMulCount > 0
    details := s!"Found {fieldMulCount} uses of field_mul()."
  }

/-! ## Part 3: DD-003 Checks (Memory Safety) -/

/-- Check that restrict keyword is present -/
def checkRestrict (code : String) : CheckResult :=
  let hasRestrict := containsPattern code "restrict"
  let restrictCount := countPattern code "restrict"
  {
    name := "DD-003: restrict keyword"
    passed := hasRestrict && restrictCount >= 3  -- At least even, odd, out
    details := s!"Found {restrictCount} uses of 'restrict'."
  }

/-- Check that debug assertions are present -/
def checkDebugAssertions (code : String) : CheckResult :=
  let hasIfdefDebug := containsPattern code "#ifdef DEBUG"
  let hasAssert := containsPattern code "assert("
  let assertCount := countPattern code "assert("
  {
    name := "DD-003: Debug assertions"
    passed := hasIfdefDebug && hasAssert && assertCount >= 3
    details := s!"Found #ifdef DEBUG: {hasIfdefDebug}, assert count: {assertCount}."
  }

/-- Check for null pointer assertions -/
def checkNullAssertions (code : String) : CheckResult :=
  let hasNullCheck := containsPattern code "!= NULL"
  let nullCheckCount := countPattern code "!= NULL"
  {
    name := "DD-003: Null pointer checks"
    passed := hasNullCheck && nullCheckCount >= 3
    details := s!"Found {nullCheckCount} null pointer checks."
  }

/-- Check for aliasing assertions -/
def checkAliasingAssertions (code : String) : CheckResult :=
  let hasAliasingCheck := containsPattern code "aliases"
  let aliasingCount := countPattern code "aliases"
  {
    name := "DD-003: Aliasing checks"
    passed := hasAliasingCheck && aliasingCount >= 2
    details := s!"Found {aliasingCount} aliasing checks in assertion messages."
  }

/-! ## Part 4: DD-006 Checks (Sanitizer Compatibility) -/

/-- Check that code doesn't have undefined behavior patterns -/
def checkSanitizerCompatibility (code : String) : CheckResult :=
  -- Check for common UB patterns
  let hasSignedOverflow := containsPattern code "int " && containsPattern code " + " &&
                           !containsPattern code "field_add"
  let hasUnsafePointerArith := containsPattern code "++" && containsPattern code "*"
  {
    name := "DD-006: Sanitizer compatibility"
    passed := !hasSignedOverflow
    details := if hasSignedOverflow
               then "WARNING: Potential signed integer arithmetic detected."
               else "No obvious UB patterns detected."
  }

/-! ## Part 5: Proof Anchor Checks -/

/-- Check that proof anchors are present -/
def checkProofAnchors (code : String) : CheckResult :=
  let hasProofAnchor := containsPattern code "PROOF_ANCHOR"
  let anchorCount := countPattern code "PROOF_ANCHOR"
  let hasPreconditions := containsPattern code "Preconditions:"
  let hasPostconditions := containsPattern code "Postconditions:"
  {
    name := "Proof anchors"
    passed := hasProofAnchor && hasPreconditions && hasPostconditions
    details := s!"Found {anchorCount} PROOF_ANCHOR markers, " ++
               s!"Preconditions: {hasPreconditions}, Postconditions: {hasPostconditions}."
  }

/-! ## Part 6: Run All Checks -/

/-- All safety checks to run -/
def allChecks : List (String → CheckResult) := [
  checkFieldAdd,
  checkFieldMul,
  checkRestrict,
  checkDebugAssertions,
  checkNullAssertions,
  checkAliasingAssertions,
  checkSanitizerCompatibility,
  checkProofAnchors
]

/-- Run all safety checks on generated code -/
def runAllChecks (code : String) : List CheckResult :=
  allChecks.map (· code)

/-- Summarize check results -/
def summarizeResults (results : List CheckResult) : (Nat × Nat × String) :=
  let passed := results.filter (·.passed) |>.length
  let total := results.length
  let details := results.map (fun r =>
    let status := if r.passed then "✅ PASS" else "❌ FAIL"
    s!"  {status}: {r.name}\n         {r.details}"
  ) |>.intersperse "\n" |> String.join
  (passed, total, details)

/-! ## Part 7: Test Execution -/

/-- Run safety checks on fri_fold.h -/
def checkFriFoldHeader : IO Bool := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     SAFETY CHECKS: Generated C Code Verification             ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Read the generated header
  let headerPath := "generated/fri_fold.h"
  let code ← IO.FS.readFile headerPath

  IO.println s!"Analyzing: {headerPath}"
  IO.println s!"Code size: {code.length} bytes"
  IO.println ""

  -- Run all checks
  let results := runAllChecks code
  let (passed, total, details) := summarizeResults results

  IO.println "Check Results:"
  IO.println details
  IO.println ""
  IO.println s!"Summary: {passed}/{total} checks passed"

  if passed == total then
    IO.println ""
    IO.println "══════════════════════════════════════════════════════════════"
    IO.println "ALL SAFETY CHECKS PASSED"
    IO.println "══════════════════════════════════════════════════════════════"
    return true
  else
    IO.println ""
    IO.println "══════════════════════════════════════════════════════════════"
    IO.println "SOME SAFETY CHECKS FAILED"
    IO.println "══════════════════════════════════════════════════════════════"
    return false

/-- Run safety checks on field_ops.h -/
def checkFieldOpsHeader : IO Bool := do
  IO.println ""
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     SAFETY CHECKS: field_ops.h Verification                  ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let headerPath := "generated/field_ops.h"
  let code ← IO.FS.readFile headerPath

  IO.println s!"Analyzing: {headerPath}"
  IO.println s!"Code size: {code.length} bytes"
  IO.println ""

  -- Specific checks for field_ops.h
  let checks : List CheckResult := [
    {
      name := "field_t typedef"
      passed := containsPattern code "typedef uint64_t field_t"
      details := "Field type definition present."
    },
    {
      name := "field_add definition"
      passed := containsPattern code "field_add("
      details := "field_add function/macro defined."
    },
    {
      name := "field_mul definition"
      passed := containsPattern code "field_mul("
      details := "field_mul function/macro defined."
    },
    {
      name := "FIELD_NAME macro"
      passed := containsPattern code "FIELD_NAME"
      details := "Field identification macro present."
    },
    {
      name := "Header guard"
      passed := containsPattern code "#ifndef FIELD_OPS_H" &&
                containsPattern code "#define FIELD_OPS_H"
      details := "Header include guard present."
    }
  ]

  let (passed, total, details) := summarizeResults checks

  IO.println "Check Results:"
  IO.println details
  IO.println ""
  IO.println s!"Summary: {passed}/{total} checks passed"

  return passed == total

/-- Main entry point -/
def main : IO UInt32 := do
  let friFoldOk ← checkFriFoldHeader
  let fieldOpsOk ← checkFieldOpsHeader

  IO.println ""
  if friFoldOk && fieldOpsOk then
    IO.println "════════════════════════════════════════════════════════════════"
    IO.println "OVERALL: ALL SAFETY CHECKS PASSED"
    IO.println "════════════════════════════════════════════════════════════════"
    return 0
  else
    IO.println "════════════════════════════════════════════════════════════════"
    IO.println "OVERALL: SOME SAFETY CHECKS FAILED"
    IO.println "════════════════════════════════════════════════════════════════"
    return 1

/-! ## Part 8: Inline Test -/

#eval! do
  -- Quick inline test using the generated code from CodeGen
  let config : CodeGenConfig := {}
  let code := generateFriHeader config

  IO.println "Quick Safety Check on In-Memory Generated Code:"
  IO.println ""

  let results := runAllChecks code
  let (passed, total, _) := summarizeResults results

  IO.println s!"Results: {passed}/{total} checks passed"

  for r in results do
    let status := if r.passed then "✅" else "❌"
    IO.println s!"  {status} {r.name}"

end Tests.Safety.CodeGenChecks
