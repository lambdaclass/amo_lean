/-
  AMO-Lean: Vector Expression Code Generator
  Phase 0 - Direct VecExpr to C Code Generation

  This module generates C code directly from VecExpr specifications,
  bypassing the E-Graph for the Phase 0 Proof of Concept.

  Design Decisions:
  - DD-002: Uses field_add/field_mul instead of native operators
  - DD-003: Uses restrict and debug assertions for memory safety
  - DD-006: Generated code is compatible with sanitizers

  For future phases, consider integrating VecExpr with the E-Graph
  system for optimization (see P-003 in PROBLEMS.md).

  References:
  - docs/option-a/DESIGN_DECISIONS.md
  - docs/option-a/PROBLEMS.md
-/

import AmoLean.Vector.Basic
import AmoLean.Basic

namespace AmoLean.Vector.CodeGen

open AmoLean.Vector (VecExpr VecVarId)
open AmoLean (Expr VarId)

/-! ## Part 1: Code Generation Configuration -/

/-- Configuration for C code generation -/
structure CodeGenConfig where
  /-- Include debug assertions (buffer checks, aliasing) -/
  debugAssertions : Bool := true
  /-- Use restrict keyword for non-aliasing hints -/
  useRestrict : Bool := true
  /-- Include proof anchors in comments -/
  proofAnchors : Bool := true
  /-- Field type name (for typedef) -/
  fieldType : String := "field_t"
  /-- Size type name -/
  sizeType : String := "size_t"
  deriving Repr, Inhabited

def defaultConfig : CodeGenConfig := {}

/-! ## Part 2: Code Generation State -/

/-- State maintained during code generation -/
structure CodeGenState where
  nextTemp : Nat := 0
  nextLoop : Nat := 0
  indent : Nat := 0
  config : CodeGenConfig := defaultConfig
  deriving Repr, Inhabited

def CodeGenState.freshTemp (s : CodeGenState) (varPrefix : String := "t") : (String × CodeGenState) :=
  (s!"{varPrefix}{s.nextTemp}", { s with nextTemp := s.nextTemp + 1 })

def CodeGenState.freshLoop (s : CodeGenState) : (String × CodeGenState) :=
  (s!"i{s.nextLoop}", { s with nextLoop := s.nextLoop + 1 })

def CodeGenState.increaseIndent (s : CodeGenState) : CodeGenState :=
  { s with indent := s.indent + 1 }

def CodeGenState.decreaseIndent (s : CodeGenState) : CodeGenState :=
  { s with indent := if s.indent > 0 then s.indent - 1 else 0 }

/-! ## Part 3: C Code Primitives -/

def indentStr (n : Nat) : String :=
  String.mk (List.replicate (n * 4) ' ')

def line (state : CodeGenState) (content : String) : String :=
  indentStr state.indent ++ content ++ "\n"

def comment (state : CodeGenState) (content : String) : String :=
  line state s!"// {content}"

def proofAnchor (state : CodeGenState) (name : String)
    (preconditions : List String) (postconditions : List String) : String :=
  if state.config.proofAnchors then
    let pre := preconditions.map (fun p => line state s!"//   - {p}") |> String.join
    let post := postconditions.map (fun p => line state s!"//   - {p}") |> String.join
    line state s!"// PROOF_ANCHOR: {name}" ++
    line state "// Preconditions:" ++ pre ++
    line state "// Postconditions:" ++ post
  else ""

/-! ## Part 4: Scalar Expression Code Generation -/

/-- Generate C code for a scalar expression -/
partial def exprToC : Expr Int → String
  | .const c => s!"{c}"
  | .var v => s!"arg{v}"
  | .add e1 e2 => s!"field_add({exprToC e1}, {exprToC e2})"
  | .mul e1 e2 => s!"field_mul({exprToC e1}, {exprToC e2})"
  | .pow e n =>
    if n == 0 then "1"
    else if n == 1 then exprToC e
    else if n == 2 then s!"field_mul({exprToC e}, {exprToC e})"
    else s!"field_pow({exprToC e}, {n})"

/-! ## Part 5: Vector Expression Code Generation -/

/-- Result of vector code generation -/
structure VecGenResult where
  /-- C code for the operation -/
  code : String
  /-- Name of the output variable/array -/
  outputVar : String
  /-- Updated state -/
  state : CodeGenState
  deriving Repr

/-- Generate variable declarations for vector buffers -/
def declareVecBuffer (state : CodeGenState) (name : String) (size : Nat) : String :=
  let ft := state.config.fieldType
  let restrict := if state.config.useRestrict then "restrict " else ""
  line state s!"{ft}* {restrict}{name};"

/-- Generate parameter declaration for input vector -/
def inputVecParam (config : CodeGenConfig) (name : String) : String :=
  let ft := config.fieldType
  let restrict := if config.useRestrict then "restrict " else ""
  s!"const {ft}* {restrict}{name}"

/-- Generate parameter declaration for output vector -/
def outputVecParam (config : CodeGenConfig) (name : String) : String :=
  let ft := config.fieldType
  let restrict := if config.useRestrict then "restrict " else ""
  s!"{ft}* {restrict}{name}"

/-- Generate debug assertions for buffer safety -/
def bufferAssertions (state : CodeGenState) (inputs : List String) (output : String) : String :=
  if state.config.debugAssertions then
    line state "#ifdef DEBUG" ++
    (inputs.map (fun inp => line state s!"    assert({inp} != NULL && \"{inp} is null\");") |> String.join) ++
    line state s!"    assert({output} != NULL && \"{output} is null\");" ++
    (inputs.map (fun inp => line state s!"    assert({output} != {inp} && \"output aliases {inp}\");") |> String.join) ++
    line state "#endif"
  else ""

/-! ## Part 6: FRI Fold Code Generation -/

/-- Generate C code for FRI fold operation.

    FRI fold computes: out[i] = even[i] + alpha * odd[i]

    This is the key operation in the FRI protocol, where:
    - even contains elements at even indices of the input
    - odd contains elements at odd indices of the input
    - alpha is the random challenge from Fiat-Shamir

    Generated code follows DD-002 (field_add/field_mul) and DD-003 (restrict).
-/
def generateFriFold (config : CodeGenConfig) (n : Nat) : String :=
  let ft := config.fieldType
  let st := config.sizeType
  let restrict := if config.useRestrict then "restrict " else ""

  let anchor := if config.proofAnchors then
    s!"/**
 * FRI fold operation: out[i] = even[i] + alpha * odd[i]
 *
 * PROOF_ANCHOR: fri_fold
 * Preconditions:
 *   - even, odd, out are non-null
 *   - even, odd, out point to arrays of at least n elements
 *   - out does not alias even or odd (required for restrict)
 * Postconditions:
 *   - forall i in [0, n): out[i] == even[i] + alpha * odd[i]
 *   - output array is fully initialized
 * Invariants:
 *   - All arithmetic uses field_add/field_mul (per DD-002)
 */
"
  else ""

  let assertions := if config.debugAssertions then
    s!"#ifdef DEBUG
    assert(even != NULL && \"even is null\");
    assert(odd != NULL && \"odd is null\");
    assert(out != NULL && \"out is null\");
    assert(out != even && \"out aliases even\");
    assert(out != odd && \"out aliases odd\");
#endif
"
  else ""

  s!"{anchor}void fri_fold_{n}(
    const {ft}* {restrict}even,
    const {ft}* {restrict}odd,
    {ft}* {restrict}out,
    {ft} alpha
) \{
{assertions}    for ({st} i = 0; i < {n}; i++) \{
        out[i] = field_add(even[i], field_mul(alpha, odd[i]));
    }
}
"

/-- Generate parametric FRI fold (size as parameter) -/
def generateParametricFriFold (config : CodeGenConfig) : String :=
  let ft := config.fieldType
  let st := config.sizeType
  let restrict := if config.useRestrict then "restrict " else ""

  let anchor := if config.proofAnchors then
    s!"/**
 * Parametric FRI fold operation: out[i] = even[i] + alpha * odd[i]
 *
 * PROOF_ANCHOR: fri_fold_parametric
 * Preconditions:
 *   - n > 0
 *   - even, odd, out are non-null
 *   - even, odd, out point to arrays of at least n elements
 *   - out does not alias even or odd (required for restrict)
 * Postconditions:
 *   - forall i in [0, n): out[i] == even[i] + alpha * odd[i]
 *   - output array is fully initialized
 * Invariants:
 *   - All arithmetic uses field_add/field_mul (per DD-002)
 */
"
  else ""

  let assertions := if config.debugAssertions then
    s!"#ifdef DEBUG
    assert(n > 0 && \"n must be positive\");
    assert(even != NULL && \"even is null\");
    assert(odd != NULL && \"odd is null\");
    assert(out != NULL && \"out is null\");
    assert(out != even && \"out aliases even\");
    assert(out != odd && \"out aliases odd\");
#endif
"
  else ""

  s!"{anchor}void fri_fold(
    {st} n,
    const {ft}* {restrict}even,
    const {ft}* {restrict}odd,
    {ft}* {restrict}out,
    {ft} alpha
) \{
{assertions}    for ({st} i = 0; i < n; i++) \{
        out[i] = field_add(even[i], field_mul(alpha, odd[i]));
    }
}
"

/-! ## Part 7: Full FRI Layer Fold Code Generation -/

/-- Generate C code for folding a full layer.

    This takes an input array of 2n elements and produces
    an output array of n elements, where:
    - even[i] = input[2*i]
    - odd[i] = input[2*i + 1]
    - out[i] = even[i] + alpha * odd[i]
-/
def generateFriFoldLayer (config : CodeGenConfig) : String :=
  let ft := config.fieldType
  let st := config.sizeType
  let restrict := if config.useRestrict then "restrict " else ""

  let anchor := if config.proofAnchors then
    s!"/**
 * FRI layer fold: Fold input[2n] to output[n]
 *
 * PROOF_ANCHOR: fri_fold_layer
 * Preconditions:
 *   - n > 0
 *   - input has 2*n elements
 *   - output has n elements
 *   - output does not alias input
 * Postconditions:
 *   - forall i in [0, n): output[i] == input[2*i] + alpha * input[2*i + 1]
 * Invariants:
 *   - Memory accesses are sequential (cache-friendly)
 *   - All arithmetic uses field_add/field_mul (per DD-002)
 */
"
  else ""

  let assertions := if config.debugAssertions then
    s!"#ifdef DEBUG
    assert(n > 0 && \"n must be positive\");
    assert(input != NULL && \"input is null\");
    assert(output != NULL && \"output is null\");
    assert(output != input && \"output aliases input\");
#endif
"
  else ""

  s!"{anchor}void fri_fold_layer(
    {st} n,
    const {ft}* {restrict}input,
    {ft}* {restrict}output,
    {ft} alpha
) \{
{assertions}    for ({st} i = 0; i < n; i++) \{
        {ft} even = input[2 * i];
        {ft} odd = input[2 * i + 1];
        output[i] = field_add(even, field_mul(alpha, odd));
    }
}
"

/-! ## Part 8: File Generation -/

/-- Generate complete header file for FRI operations -/
def generateFriHeader (config : CodeGenConfig) : String :=
  let ft := config.fieldType
  s!"/**
 * fri_fold.h - FRI Fold Operations for AMO-Lean
 *
 * Generated by AmoLean.Vector.CodeGen
 *
 * This file provides FRI fold operations that:
 * - Use field_add/field_mul for field arithmetic (DD-002)
 * - Use restrict for non-aliasing optimization (DD-003)
 * - Include debug assertions when DEBUG is defined (DD-006)
 *
 * Usage:
 *   #define FIELD_GOLDILOCKS  // or FIELD_NATIVE for testing
 *   #define DEBUG             // optional: enable assertions
 *   #include \"field_ops.h\"
 *   #include \"fri_fold.h\"
 */

#ifndef FRI_FOLD_H
#define FRI_FOLD_H

#include <stddef.h>
#include <assert.h>

/* Assumes field_ops.h is included before this header */
#ifndef FIELD_NAME
#error \"Include field_ops.h before fri_fold.h\"
#endif

{generateParametricFriFold config}

{generateFriFoldLayer config}

/* Size-specific versions for common sizes */
{generateFriFold config 16}
{generateFriFold config 64}
{generateFriFold config 256}
{generateFriFold config 1024}

#endif /* FRI_FOLD_H */
"

/-! ## Part 9: Tests -/

section Tests

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     VECTOR CODEGEN: FRI FOLD GENERATION TEST                 ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  IO.println "=== Parametric FRI Fold ==="
  IO.println (generateParametricFriFold defaultConfig)

  IO.println "=== FRI Fold Layer ==="
  IO.println (generateFriFoldLayer defaultConfig)

  IO.println "=== FRI Fold N=16 ==="
  IO.println (generateFriFold defaultConfig 16)

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     VECTOR CODEGEN: SCALAR EXPRESSION TEST                   ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Test scalar expression generation
  let expr1 : Expr Int := .add (.var 0) (.mul (.var 1) (.const 2))
  IO.println s!"expr: x + y * 2"
  IO.println s!"C:    {exprToC expr1}"
  IO.println ""

  let expr2 : Expr Int := .pow (.var 0) 5
  IO.println s!"expr: x^5"
  IO.println s!"C:    {exprToC expr2}"

end Tests

/-! ## Part 10: Summary -/

#eval! IO.println "
Vector CodeGen Summary (Phase 0):
=================================

1. Generates C code directly from VecExpr specifications
2. Uses field_add/field_mul (not native + *) per DD-002
3. Uses restrict keyword for optimization hints per DD-003
4. Includes debug assertions for sanitizer compatibility per DD-006
5. Generates proof anchors as structured comments

Generated functions:
- fri_fold(n, even, odd, out, alpha): Parametric fold
- fri_fold_layer(n, input, output, alpha): Full layer fold
- fri_fold_N(...): Size-specific versions (N=16,64,256,1024)

Requires: #include \"field_ops.h\" before use

Note: This is a Phase 0 bypass solution. For optimization,
VecExpr should be integrated with the E-Graph system (P-003).
"

end AmoLean.Vector.CodeGen
