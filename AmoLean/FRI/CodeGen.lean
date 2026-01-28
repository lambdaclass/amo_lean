/-
  AMO-Lean: FRI Code Generation
  Phase 7-Alpha - Generate C code from CryptoSigma

  This module generates C code from the CryptoSigma IR, preserving
  cryptographic operation ordering and including proof anchors for
  formal verification in Phase 6.6.

  Key Features:
  - Proof Anchors: Structured comments documenting pre/postconditions
  - Intrinsic Handling: Cryptographic operations as function calls
  - Memory Layout: Proper alignment for AVX operations
  - Security Preservation: Operation order matches IR exactly

  Generated Code Structure:
  ```c
  // PROOF_ANCHOR: function_name
  // Precondition: ...
  // Postcondition: ...
  void function_name(params) {
      // Domain: fri_fold
      transcript_absorb(&ts, root, 1);  // BARRIER
      uint64_t alpha = transcript_squeeze(&ts);  // BARRIER
      fri_fold(n, input, output, alpha);
  }
  ```

  References:
  - FRI Protocol: Ben-Sasson et al. "Fast Reed-Solomon IOP of Proximity"
  - Fiat-Shamir: Canetti et al. "Fiat-Shamir From Public-Key Encryption"
-/

import AmoLean.FRI.Transcript
import AmoLean.FRI.Protocol
import AmoLean.FRI.Kernel
import AmoLean.Sigma.Basic

namespace AmoLean.FRI.CodeGen

open AmoLean.FRI.Transcript (CryptoSigma Intrinsic DomainTag TranscriptState)
open AmoLean.FRI.Protocol (RoundState RoundOutput friRound)
open AmoLean.Sigma (Gather Scatter IdxExpr Kernel LoopVar)

/-! ## Part 1: Code Generation Configuration -/

/-- Configuration for C code generation -/
structure CodeGenConfig where
  /-- Use 64-bit field elements (Goldilocks) -/
  fieldBits : Nat := 64
  /-- Generate AVX2 intrinsics -/
  useAVX2 : Bool := true
  /-- Include proof anchors in comments -/
  proofAnchors : Bool := true
  /-- Alignment for SIMD operations (bytes) -/
  simdAlignment : Nat := 32
  /-- Hash function to use -/
  hashFunction : String := "poseidon2"
  deriving Repr, Inhabited

def defaultConfig : CodeGenConfig := {}

/-! ## Part 2: Code Generation State -/

/-- State maintained during code generation -/
structure CodeGenState where
  indent : Nat := 0
  nextTemp : Nat := 0
  nextLoop : Nat := 0
  currentDomain : List String := []
  config : CodeGenConfig := defaultConfig
  deriving Repr, Inhabited

def CodeGenState.increaseIndent (s : CodeGenState) : CodeGenState :=
  { s with indent := s.indent + 1 }

def CodeGenState.decreaseIndent (s : CodeGenState) : CodeGenState :=
  { s with indent := if s.indent > 0 then s.indent - 1 else 0 }

def CodeGenState.freshTemp (s : CodeGenState) : (String × CodeGenState) :=
  (s!"t{s.nextTemp}", { s with nextTemp := s.nextTemp + 1 })

def CodeGenState.freshLoop (s : CodeGenState) : (String × CodeGenState) :=
  (s!"i{s.nextLoop}", { s with nextLoop := s.nextLoop + 1 })

def CodeGenState.pushDomain (s : CodeGenState) (d : String) : CodeGenState :=
  { s with currentDomain := d :: s.currentDomain }

def CodeGenState.popDomain (s : CodeGenState) : CodeGenState :=
  { s with currentDomain := s.currentDomain.tail }

/-! ## Part 3: C Code Primitives -/

def indentStr (n : Nat) : String :=
  String.mk (List.replicate (n * 4) ' ')

def fieldType (config : CodeGenConfig) : String :=
  if config.fieldBits == 64 then "uint64_t" else "uint32_t"

def hashFuncName (config : CodeGenConfig) : String :=
  match config.hashFunction with
  | "poseidon2" => "poseidon2_hash"
  | "blake3" => "blake3_hash"
  | _ => "hash"

/-! ## Part 4: Proof Anchor Generation -/

/-- Generate a proof anchor comment block -/
def proofAnchor (name : String) (preconditions : List String) (postconditions : List String)
    (invariants : List String := []) : String :=
  let pre := preconditions.map (s!"//   - {·}") |>.intersperse "\n" |> String.join
  let post := postconditions.map (s!"//   - {·}") |>.intersperse "\n" |> String.join
  let inv := if invariants.isEmpty then ""
             else "\n// Invariants:\n" ++ (invariants.map (s!"//   - {·}") |>.intersperse "\n" |> String.join)
  s!"// PROOF_ANCHOR: {name}
// Preconditions:
{pre}
// Postconditions:
{post}{inv}
"

/-- Proof anchor for FRI fold operation -/
def friFoldAnchor (n : Nat) : String :=
  proofAnchor "fri_fold"
    [s!"input != NULL && output != NULL",
     s!"input has {2 * n} elements",
     s!"output has {n} elements",
     "alpha is a valid field element"]
    [s!"forall i in [0, {n}): output[i] == input[2*i] + alpha * input[2*i + 1]",
     "output array is fully initialized"]

/-- Proof anchor for Merkle hash -/
def merkleHashAnchor : String :=
  proofAnchor "merkle_hash"
    ["left and right are valid field elements"]
    ["result == hash(left, right)",
     "hash is collision-resistant"]

/-- Proof anchor for transcript absorb -/
def absorbAnchor (count : Nat) : String :=
  proofAnchor "transcript_absorb"
    [s!"data has {count} elements",
     "transcript state is valid"]
    ["transcript state updated with absorbed data",
     "FIAT-SHAMIR: data incorporated into challenge derivation"]
    ["BARRIER: No code motion across this operation"]

/-- Proof anchor for transcript squeeze -/
def squeezeAnchor : String :=
  proofAnchor "transcript_squeeze"
    ["transcript state is valid",
     "at least one absorb has occurred since last squeeze (Fiat-Shamir)"]
    ["challenge is pseudo-random field element",
     "challenge is deterministic given transcript state",
     "transcript state updated (squeeze count incremented)"]
    ["BARRIER: No code motion across this operation",
     "SECURITY: Challenge depends on ALL previously absorbed data"]

/-! ## Part 5: Index Expression to C -/

/-- Convert IdxExpr to C expression -/
partial def idxExprToC : IdxExpr → String
  | .const n => s!"{n}"
  | .var v => s!"i{v}"
  | .affine base stride v =>
    if base == 0 && stride == 1 then s!"i{v}"
    else if base == 0 then s!"{stride} * i{v}"
    else if stride == 1 then s!"{base} + i{v}"
    else s!"{base} + {stride} * i{v}"
  | .add e1 e2 => s!"({idxExprToC e1} + {idxExprToC e2})"
  | .mul c e => s!"{c} * ({idxExprToC e})"

/-- Generate gather base address -/
def gatherBase (g : Gather) : String := idxExprToC g.baseAddr

/-- Generate scatter base address -/
def scatterBase (s : Scatter) : String := idxExprToC s.baseAddr

/-! ## Part 6: Intrinsic Code Generation -/

/-- Generate C code for an intrinsic operation -/
def intrinsicToC (state : CodeGenState) (intr : Intrinsic) (gather : Gather) (scatter : Scatter) : String :=
  let pad := indentStr state.indent
  let ft := fieldType state.config
  match intr with
  | .absorb count =>
    let anchor := if state.config.proofAnchors then absorbAnchor count else ""
    let gatherAddr := gatherBase gather
    s!"{anchor}{pad}transcript_absorb(&transcript, &data[{gatherAddr}], {count}); // BARRIER"

  | .squeeze =>
    let anchor := if state.config.proofAnchors then squeezeAnchor else ""
    let scatterAddr := scatterBase scatter
    s!"{anchor}{pad}{ft} alpha_{state.nextTemp} = transcript_squeeze(&transcript); // BARRIER"

  | .hash inputCount =>
    let gatherAddr := gatherBase gather
    let scatterAddr := scatterBase scatter
    let hashFunc := hashFuncName state.config
    s!"{pad}{ft} hash_result = {hashFunc}(&data[{gatherAddr}], {inputCount});"

  | .merkleHash =>
    let anchor := if state.config.proofAnchors then merkleHashAnchor else ""
    let gatherAddr := gatherBase gather
    let scatterAddr := scatterBase scatter
    s!"{anchor}{pad}nodes[{scatterAddr}] = merkle_hash(nodes[{gatherAddr}], nodes[{gatherAddr} + 1]);"

  | .domainEnter tag =>
    let tagStr := match tag with
      | .friFold => "FRI_FOLD"
      | .friCommit => "FRI_COMMIT"
      | .friQuery => "FRI_QUERY"
      | .merkleNode => "MERKLE_NODE"
      | .merkleLeaf => "MERKLE_LEAF"
      | .custom s => s
    s!"{pad}// === DOMAIN ENTER: {tagStr} ==="

  | .domainExit =>
    s!"{pad}// === DOMAIN EXIT ==="

  | .barrier =>
    s!"{pad}__asm__ volatile(\"\" ::: \"memory\"); // MEMORY BARRIER"

/-! ## Part 7: Kernel Code Generation -/

/-- Generate C code for a compute kernel -/
def kernelToC (state : CodeGenState) (kernel : Kernel) (gather : Gather) (scatter : Scatter) : String :=
  let pad := indentStr state.indent
  let ft := fieldType state.config
  let gatherAddr := gatherBase gather
  let scatterAddr := scatterBase scatter
  match kernel with
  | .identity n =>
    s!"{pad}// Identity kernel (n={n})\n{pad}memcpy(&out[{scatterAddr}], &in[{gatherAddr}], {n} * sizeof({ft}));"

  | .dft n =>
    if n == 2 then
      s!"{pad}// DFT_2 butterfly
{pad}{ft} t0 = in[{gatherAddr}] + in[{gatherAddr} + 1];
{pad}{ft} t1 = in[{gatherAddr}] - in[{gatherAddr} + 1];
{pad}out[{scatterAddr}] = t0;
{pad}out[{scatterAddr} + 1] = t1;"
    else
      s!"{pad}dft_{n}(&in[{gatherAddr}], &out[{scatterAddr}]);"

  | .ntt n p =>
    s!"{pad}ntt_{n}_{p}(&in[{gatherAddr}], &out[{scatterAddr}]);"

  | .butterfly =>
    s!"{pad}// FRI fold butterfly
{pad}out[{scatterAddr}] = in[{gatherAddr}] + alpha * in[{gatherAddr} + 1];"

  | .twiddle n k =>
    s!"{pad}// Twiddle multiplication (n={n}, k={k})
{pad}out[{scatterAddr}] = in[{gatherAddr}] * twiddle_factor;"

  | .scale =>
    s!"{pad}// Scalar scaling
{pad}out[{scatterAddr}] = in[{gatherAddr}] * scale_factor;"

  -- Poseidon2 kernels (added in Step 3)
  -- .sbox: size, exponent (x^α for all elements)
  | .sbox n alpha =>
    s!"{pad}// S-box x^{alpha} (size={n})
{pad}sbox_{n}_{alpha}(&in[{gatherAddr}], &out[{scatterAddr}]);"

  -- .partialSbox: size, exponent, index (x^α only at index)
  | .partialSbox n alpha idx =>
    s!"{pad}// Partial S-box x^{alpha} at position {idx} (size={n})
{pad}partial_sbox_{n}_{alpha}_{idx}(&in[{gatherAddr}], &out[{scatterAddr}]);"

  -- .mdsApply: name, size
  | .mdsApply name size =>
    s!"{pad}// MDS matrix apply (name={name}, size={size})
{pad}mds_{name}(&in[{gatherAddr}], &out[{scatterAddr}]);"

  -- .mdsInternal: size (Poseidon2 internal MDS optimization)
  | .mdsInternal size =>
    s!"{pad}// Internal MDS (Poseidon2 optimization, size={size})
{pad}mds_internal_{size}(&in[{gatherAddr}], &out[{scatterAddr}]);"

  -- .addRoundConst: round, size
  | .addRoundConst round size =>
    s!"{pad}// Add round constants (round={round}, size={size})
{pad}add_round_const_{round}_{size}(&in[{gatherAddr}], &out[{scatterAddr}], round_constants);"

/-! ## Part 8: CryptoSigma Code Generation -/

/-- Generate C code from CryptoSigma -/
partial def cryptoSigmaToC (state : CodeGenState) (sigma : CryptoSigma) : String × CodeGenState :=
  match sigma with
  | .nop => ("", state)

  | .compute kernel gather scatter =>
    (kernelToC state kernel gather scatter, state)

  | .intrinsic intr gather scatter =>
    (intrinsicToC state intr gather scatter, state)

  | .loop n loopVar body =>
    let pad := indentStr state.indent
    let (loopVarName, state') := state.freshLoop
    let state'' := state'.increaseIndent
    let (bodyCode, state''') := cryptoSigmaToC state'' body
    let code := s!"{pad}for (size_t {loopVarName} = 0; {loopVarName} < {n}; {loopVarName}++) \{
{bodyCode}
{pad}}"
    (code, { state''' with indent := state.indent })

  | .seq s1 s2 =>
    let (code1, state') := cryptoSigmaToC state s1
    let (code2, state'') := cryptoSigmaToC state' s2
    if code1.isEmpty then (code2, state'')
    else if code2.isEmpty then (code1, state'')
    else (code1 ++ "\n" ++ code2, state'')

  | .par s1 s2 =>
    -- For now, generate sequential code (parallel execution is target-dependent)
    let pad := indentStr state.indent
    let (code1, state') := cryptoSigmaToC state s1
    let (code2, state'') := cryptoSigmaToC state' s2
    (s!"{pad}// BEGIN PARALLEL SECTION\n{code1}\n{code2}\n{pad}// END PARALLEL SECTION", state'')

  | .temp size body =>
    let pad := indentStr state.indent
    let ft := fieldType state.config
    let (tempName, state') := state.freshTemp
    let (bodyCode, state'') := cryptoSigmaToC state'.increaseIndent body
    let code := s!"{pad}\{
{pad}    {ft} {tempName}[{size}] __attribute__((aligned({state.config.simdAlignment})));
{bodyCode}
{pad}}"
    (code, { state'' with indent := state.indent })

/-! ## Part 9: FRI Protocol Code Generation -/

/-- Generate C header with type definitions -/
def generateHeader (config : CodeGenConfig) : String :=
  let ft := fieldType config
  s!"/*
 * FRI Protocol Implementation
 * Generated by AMO-Lean Phase 7-Alpha
 *
 * Field: {if config.fieldBits == 64 then "Goldilocks (p = 2^64 - 2^32 + 1)" else "BabyBear (p = 2^31 - 2^27 + 1)"}
 * SIMD: {if config.useAVX2 then "AVX2 enabled" else "Scalar only"}
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>
{if config.useAVX2 then "#include <immintrin.h>" else ""}

// Field element type
typedef {ft} field_t;

// Transcript state for Fiat-Shamir
typedef struct \{
    field_t state[4];      // Sponge state (e.g., Poseidon)
    size_t absorb_count;   // Number of elements absorbed
    size_t squeeze_count;  // Number of challenges squeezed
} transcript_t;

// Forward declarations
void transcript_init(transcript_t* ts);
void transcript_absorb(transcript_t* ts, const field_t* data, size_t count);
field_t transcript_squeeze(transcript_t* ts);
field_t merkle_hash(field_t left, field_t right);
"

/-- Generate FRI fold function -/
def generateFriFold (config : CodeGenConfig) (n : Nat) : String :=
  let ft := fieldType config
  let anchor := if config.proofAnchors then friFoldAnchor n else ""
  if config.useAVX2 && n >= 4 then
    s!"{anchor}void fri_fold_{n}(const {ft}* input, {ft}* output, {ft} alpha) \{
    // AVX2 vectorized implementation
    __m256i v_alpha = _mm256_set1_epi64x((int64_t)alpha);

    for (size_t i = 0; i < {n}; i += 4) \{
        // Load even indices: input[2i], input[2i+2], input[2i+4], input[2i+6]
        __m256i even = _mm256_set_epi64x(
            (int64_t)input[2*(i+3)], (int64_t)input[2*(i+2)],
            (int64_t)input[2*(i+1)], (int64_t)input[2*i]);

        // Load odd indices: input[2i+1], input[2i+3], input[2i+5], input[2i+7]
        __m256i odd = _mm256_set_epi64x(
            (int64_t)input[2*(i+3)+1], (int64_t)input[2*(i+2)+1],
            (int64_t)input[2*(i+1)+1], (int64_t)input[2*i+1]);

        // Compute: even + alpha * odd (simplified, real impl needs modular mul)
        __m256i prod = _mm256_mullo_epi64(v_alpha, odd);
        __m256i result = _mm256_add_epi64(even, prod);

        // Store results
        _mm256_storeu_si256((__m256i*)&output[i], result);
    }}

    // Handle remainder
    for (size_t i = ({n} / 4) * 4; i < {n}; i++) \{
        output[i] = input[2*i] + alpha * input[2*i + 1];
    }}
}}
"
  else
    s!"{anchor}void fri_fold_{n}(const {ft}* input, {ft}* output, {ft} alpha) \{
    for (size_t i = 0; i < {n}; i++) \{
        output[i] = input[2*i] + alpha * input[2*i + 1];
    }}
}}
"

/-- Generate parametric FRI fold function (reusable for any size) -/
def generateParametricFriFold (config : CodeGenConfig) : String :=
  let ft := fieldType config
  let anchor := if config.proofAnchors then
    proofAnchor "fri_fold"
      ["n > 0", "input has 2*n elements", "output has n elements", "input != output (no aliasing)"]
      ["forall i in [0, n): output[i] == input[2*i] + alpha * input[2*i + 1]"]
      ["Memory accesses are contiguous", "Suitable for SIMD vectorization"]
    else ""
  s!"{anchor}void fri_fold(size_t n, const {ft}* input, {ft}* output, {ft} alpha) \{
    for (size_t i = 0; i < n; i++) \{
        output[i] = input[2*i] + alpha * input[2*i + 1];
    }}
}}
"

/-- Generate Merkle tree build function -/
def generateMerkleBuild (config : CodeGenConfig) : String :=
  let ft := fieldType config
  let anchor := if config.proofAnchors then
    proofAnchor "merkle_build"
      ["n is a power of 2", "leaves has n elements", "nodes has 2*n - 1 elements"]
      ["nodes[0..n-1] == leaves[0..n-1]",
       "forall layer k: nodes at layer k are hashes of children at layer k-1",
       "nodes[2*n - 2] is the Merkle root"]
      ["Bottom-up construction", "Layer-by-layer hashing"]
    else ""
  s!"{anchor}void merkle_build(size_t n, const {ft}* leaves, {ft}* nodes) \{
    // Copy leaves to first n positions
    memcpy(nodes, leaves, n * sizeof({ft}));

    // Build tree bottom-up
    size_t layer_start = 0;
    size_t layer_size = n;

    while (layer_size > 1) \{
        size_t next_start = layer_start + layer_size;
        size_t next_size = layer_size / 2;

        for (size_t i = 0; i < next_size; i++) \{
            size_t left_idx = layer_start + 2 * i;
            size_t right_idx = layer_start + 2 * i + 1;
            size_t parent_idx = next_start + i;
            nodes[parent_idx] = merkle_hash(nodes[left_idx], nodes[right_idx]);
        }}

        layer_start = next_start;
        layer_size = next_size;
    }}
}}
"

/-- Generate complete FRI round function -/
def generateFriRound (config : CodeGenConfig) (domainSize : Nat) : String :=
  let ft := fieldType config
  let anchor := if config.proofAnchors then
    proofAnchor "fri_round"
      [s!"domain_size == {domainSize}",
       "poly has domain_size elements",
       "transcript is valid"]
      ["Merkle commitment computed and absorbed",
       "Challenge alpha squeezed from transcript",
       "output_poly has domain_size/2 elements",
       "output_poly[i] == poly[2*i] + alpha * poly[2*i + 1]"]
      ["SECURITY: commit BEFORE squeeze (Fiat-Shamir)",
       "Order: Commit → Absorb → Squeeze → Fold"]
    else ""
  s!"{anchor}{ft} fri_round_{domainSize}(
    const {ft}* poly,
    {ft}* output_poly,
    {ft}* merkle_nodes,
    transcript_t* transcript
) \{
    // === DOMAIN ENTER: FRI_FOLD ===

    // Phase 1: COMMIT - Build Merkle tree
    // === DOMAIN ENTER: MERKLE_NODE ===
    merkle_build({domainSize}, poly, merkle_nodes);
    {ft} root = merkle_nodes[2 * {domainSize} - 2];
    // === DOMAIN EXIT ===

    // Phase 2: ABSORB - Ingest root into transcript
    // PROOF_ANCHOR: absorb_before_squeeze
    // Precondition: root is valid Merkle commitment
    // Postcondition: root incorporated into Fiat-Shamir challenge
    transcript_absorb(transcript, &root, 1); // BARRIER

    // Phase 3: SQUEEZE - Extract challenge
    // PROOF_ANCHOR: squeeze_after_absorb
    // Precondition: absorb completed
    // Postcondition: alpha is pseudo-random, depends on root
    {ft} alpha = transcript_squeeze(transcript); // BARRIER

    // Phase 4: FOLD - Compute next layer
    fri_fold({domainSize / 2}, poly, output_poly, alpha);

    // === DOMAIN EXIT ===

    return alpha;
}}
"

/-! ## Part 10: Complete Protocol Generation -/

/-- Generate complete FRI protocol implementation -/
def generateFriProtocol (config : CodeGenConfig) (initialDomain : Nat) (numRounds : Nat) : String :=
  let header := generateHeader config
  let parametricFold := generateParametricFriFold config
  let merkleBuild := generateMerkleBuild config

  -- Generate round functions for each domain size
  let roundFuncs := List.range numRounds |>.map fun r =>
    let domainSize := initialDomain / (2^r)
    generateFriRound config domainSize

  let roundFuncsStr := roundFuncs.intersperse "\n" |> String.join

  -- Main protocol function
  let ft := fieldType config
  let mainFunc := s!"
/*
 * Complete FRI Commit Phase
 *
 * PROOF_ANCHOR: fri_commit_phase
 * Preconditions:
 *   - initial_poly has {initialDomain} elements
 *   - All allocated buffers are properly aligned
 * Postconditions:
 *   - commitments[] contains {numRounds} Merkle roots
 *   - challenges[] contains {numRounds} alpha values
 *   - final_poly has {initialDomain / (2^numRounds)} elements
 * Security Invariants:
 *   - Each round: commit BEFORE squeeze
 *   - All roots absorbed before any challenge derived
 */
void fri_commit_phase(
    const {ft}* initial_poly,
    {ft}* final_poly,
    {ft}* commitments,
    {ft}* challenges,
    transcript_t* transcript
) \{
    // Allocate working buffers (should be aligned for SIMD)
    {ft}* current = ({ft}*)initial_poly;
    {ft}* next = final_poly;  // Reuse final buffer as intermediate

    // Merkle tree nodes (2N - 1 per round)
    {ft} merkle_nodes[{2 * initialDomain}] __attribute__((aligned(32)));

    // Execute rounds
    size_t domain = {initialDomain};
    for (size_t round = 0; round < {numRounds}; round++) \{
        // Round-specific fold (domain halves each round)
        {ft} alpha = 0;
        switch (domain) \{
{List.range numRounds |>.map (fun r =>
  let d := initialDomain / (2^r)
  s!"            case {d}: alpha = fri_round_{d}(current, next, merkle_nodes, transcript); break;") |>.intersperse "\n" |> String.join}
        }}

        // Store commitment and challenge
        commitments[round] = merkle_nodes[2 * domain - 2];
        challenges[round] = alpha;

        // Swap buffers for next round
        {ft}* temp = current;
        current = next;
        next = temp;
        domain /= 2;
    }}

    // Copy final result if needed
    if (current != final_poly) \{
        memcpy(final_poly, current, domain * sizeof({ft}));
    }}
}}
"

  header ++ "\n" ++ parametricFold ++ "\n" ++ merkleBuild ++ "\n" ++
  roundFuncsStr ++ "\n" ++ mainFunc

/-! ## Part 11: Tests and Examples -/

section Tests

/-- Test: Generate C for single intrinsic -/
def testIntrinsicGen : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI CODEGEN: INTRINSIC GENERATION TEST                 ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let state : CodeGenState := { config := { proofAnchors := true } }
  let gather := Gather.contiguous 1 (.const 0)
  let scatter := Scatter.contiguous 1 (.const 0)

  IO.println "=== Absorb Intrinsic ==="
  IO.println (intrinsicToC state (.absorb 1) gather scatter)
  IO.println ""

  IO.println "=== Squeeze Intrinsic ==="
  IO.println (intrinsicToC state .squeeze gather scatter)
  IO.println ""

  IO.println "=== Merkle Hash Intrinsic ==="
  IO.println (intrinsicToC state .merkleHash gather scatter)
  IO.println ""

  IO.println "=== Domain Enter ==="
  IO.println (intrinsicToC state (.domainEnter .friFold) gather scatter)

#eval! testIntrinsicGen

/-- Test: Generate parametric FRI fold -/
def testFriFoldGen : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI CODEGEN: FRI FOLD GENERATION TEST                  ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  IO.println "=== Parametric FRI Fold (scalar) ==="
  IO.println (generateParametricFriFold { useAVX2 := false, proofAnchors := true })
  IO.println ""

  IO.println "=== FRI Fold N=8 (AVX2) ==="
  IO.println (generateFriFold { useAVX2 := true, proofAnchors := true } 8)

#eval! testFriFoldGen

/-- Test: Generate complete FRI round -/
def testFriRoundGen : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI CODEGEN: ROUND GENERATION TEST                     ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  IO.println "=== FRI Round (N=16) ==="
  IO.println (generateFriRound { proofAnchors := true } 16)

#eval! testFriRoundGen

/-- Test: Generate complete protocol -/
def testProtocolGen : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI CODEGEN: COMPLETE PROTOCOL TEST                    ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  let code := generateFriProtocol { proofAnchors := true, useAVX2 := false } 16 2
  IO.println code

#eval! testProtocolGen

/-- Test: Generate CryptoSigma to C -/
def testCryptoSigmaGen : IO Unit := do
  IO.println "\n╔══════════════════════════════════════════════════════════════╗"
  IO.println "║       FRI CODEGEN: CRYPTOSIGMA TO C TEST                     ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Build a simple CryptoSigma: absorb -> squeeze -> fold loop
  let gather := Gather.contiguous 8 (.const 0)
  let scatter := Scatter.contiguous 4 (.const 0)

  let sigma : CryptoSigma :=
    .seq (.intrinsic (.domainEnter .friFold) gather scatter)
    (.seq (.intrinsic (.absorb 1) gather scatter)
    (.seq (.intrinsic .squeeze gather scatter)
    (.seq (.loop 4 0 (.compute .butterfly (Gather.contiguous 2 (.affine 0 2 0)) (Scatter.contiguous 1 (.var 0))))
    (.intrinsic .domainExit gather scatter))))

  let state : CodeGenState := { config := { proofAnchors := true } }
  let (code, _) := cryptoSigmaToC state sigma

  IO.println "Input CryptoSigma structure:"
  IO.println s!"{sigma}"
  IO.println ""
  IO.println "Generated C code:"
  IO.println code

-- Note: Test skipped due to #eval limitations with partial functions
-- Run manually with: lake env lean --run AmoLean/FRI/CodeGen.lean
-- #eval! testCryptoSigmaGen

end Tests

/-! ## Part 12: Summary -/

def codeGenSummary : String :=
"FRI CodeGen Module Summary (Phase 7-Alpha):
============================================

1. Proof Anchors: Structured comments documenting:
   - Preconditions (valid inputs)
   - Postconditions (guaranteed outputs)
   - Invariants (BARRIER, SECURITY constraints)

2. Intrinsic Handling:
   - transcript_absorb(): Ingest data into Fiat-Shamir
   - transcript_squeeze(): Extract pseudo-random challenge
   - merkle_hash(): Collision-resistant hash for tree nodes
   - Domain enter/exit: Context markers

3. Memory Layout:
   - Field type: uint64_t (Goldilocks) or uint32_t (BabyBear)
   - SIMD alignment: 32 bytes (AVX2)
   - Merkle nodes: 2N - 1 contiguous array

4. Security Preservation:
   - Operation order matches CryptoSigma exactly
   - BARRIER comments mark non-reorderable operations
   - Fiat-Shamir: commit BEFORE squeeze enforced

5. Generated Functions:
   - fri_fold(): Parametric or size-specific
   - merkle_build(): Bottom-up tree construction
   - fri_round_N(): Complete round for domain N
   - fri_commit_phase(): Multi-round protocol

Next: Phase 7-Beta (Differential Fuzzing) will test this
      generated code against Lean evaluation."

#eval! IO.println codeGenSummary

end AmoLean.FRI.CodeGen
