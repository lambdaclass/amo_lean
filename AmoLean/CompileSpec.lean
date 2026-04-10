/-
  AmoLean CompileSpec — Dispatch logic for the trzk compiler.

  Routes Spec values to the appropriate codegen backend:
  - NTT specs → OptimizedNTTPipeline (verified, field-aware)
  - Poseidon2 specs → Poseidon CodeGen (field-specific S-box)
  - Matrix specs → Sigma-SPL pipeline (matExprToC / matExprToRust)
-/

import AmoLean.Spec
import AmoLean.Sigma.CodeGen
import AmoLean.Backends.Rust
import AmoLean.Matrix.Basic
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.Protocols.Poseidon.CodeGen

namespace AmoLean.CompileSpec

open AmoLean.Spec (Spec Field Hardware)
open AmoLean.Matrix (MatExpr)
open AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
  (FieldConfig babybearConfig koalabearConfig mersenne31Config goldilocksConfig emitPlanBasedNTTC)
open AmoLean.EGraph.Verified.Bitwise
  (HardwareCost arm_cortex_a76 arm_neon_simd x86_avx2_simd)
open AmoLean.Protocols.Poseidon.CodeGen
  (CodeGenConfig FieldType genSboxFunction)

-- ═══════════════════════════════════════════════════
-- Field / Hardware mapping
-- ═══════════════════════════════════════════════════

def fieldToConfig : Field → FieldConfig
  | .babybear   => babybearConfig
  | .koalabear  => koalabearConfig
  | .mersenne31 => mersenne31Config
  | .goldilocks => goldilocksConfig

def hwToConfig : Hardware → HardwareCost
  | .scalar => arm_cortex_a76
  | .neon   => arm_neon_simd
  | .avx2   => x86_avx2_simd

def fieldToPoseidon : Field → FieldType
  | .goldilocks => .Goldilocks
  | _           => .Generic

-- ═══════════════════════════════════════════════════
-- Spec → MatExpr conversion via Sigma types
-- ═══════════════════════════════════════════════════

/-- Convert a composable Spec to a MatExpr bundled with its dimensions.
    Uses Sigma types to avoid dependent type issues. -/
partial def specToMatExpr : Spec → Option (Σ (m : Nat) (n : Nat), MatExpr Int m n)
  | .dft n => some ⟨n, n, .dft n⟩
  | .identity n => some ⟨n, n, .identity n⟩
  | .kron a b => do
    let ⟨ma, na, ea⟩ ← specToMatExpr a
    let ⟨mb, nb, eb⟩ ← specToMatExpr b
    some ⟨ma * mb, na * nb, .kron ea eb⟩
  | .compose a b => do
    let ⟨ma, ka, ea⟩ ← specToMatExpr a
    let ⟨kb, nb, eb⟩ ← specToMatExpr b
    if h : ka = kb then
      some ⟨ma, nb, .compose ea (h ▸ eb)⟩
    else none
  | _ => none

-- ═══════════════════════════════════════════════════
-- Matrix spec compilation
-- ═══════════════════════════════════════════════════

def compileMatrixC (s : Spec) (funcName : String) : Option String := do
  let ⟨m, n, expr⟩ ← specToMatExpr s
  some (AmoLean.Sigma.CodeGen.matExprToC funcName m n expr)

def compileMatrixRust (s : Spec) (funcName : String) : Option String := do
  let ⟨m, n, expr⟩ ← specToMatExpr s
  some (AmoLean.Backends.Rust.matExprToRust funcName m n expr)

-- ═══════════════════════════════════════════════════
-- NTT compilation
-- ═══════════════════════════════════════════════════

private def log2 (n : Nat) : Nat :=
  if n ≤ 1 then 0 else 1 + log2 (n / 2)
termination_by n
decreasing_by omega

private def nttPreamble (fc : FieldConfig) : String :=
  let wt := fc.wideType
  let et := fc.elemType
  let rLit := if fc.k > 32 then s!"(({wt})1 << 64)" else s!"(({wt})1 << 32)"
  s!"#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>

{wt} mod_pow({wt} base, {wt} exp, {wt} mod) \{
  {wt} result = 1;
  base %= mod;
  while (exp > 0) \{
    if (exp & 1) result = result * base % mod;
    exp >>= 1;
    base = base * base % mod;
  }
  return result;
}

void compute_twiddles({et}* tw, {et}* tw_mont, size_t n, size_t logn, {wt} p, {wt} gen) \{
  {wt} omega_n = mod_pow(gen, (p - 1) / ({wt})n, p);
  for (size_t st = 0; st < logn; st++) \{
    size_t h = (size_t)1 << (logn - 1 - st);
    for (size_t g = 0; g < ((size_t)1 << st); g++)
      for (size_t pp = 0; pp < h; pp++) \{
        {wt} w = mod_pow(omega_n, ({wt})(pp * ((size_t)1 << st)), p);
        tw[st * (n/2) + g * h + pp] = ({et})w;
        tw_mont[st * (n/2) + g * h + pp] = ({et})((w * {rLit}) % p);
      }
  }
}

"

def compileNTTC (field : Field) (size : Nat) (hw : Hardware) (_funcName : String) : String :=
  let fc := fieldToConfig field
  let hwCost := hwToConfig hw
  let logN := log2 size
  let preamble := nttPreamble fc
  let kernel := emitPlanBasedNTTC fc logN hwCost
  preamble ++ kernel

-- ═══════════════════════════════════════════════════
-- Poseidon2 S-box compilation
-- ═══════════════════════════════════════════════════

def compilePoseidonC (field : Field) (stateSize exp : Nat) (_funcName : String) : String :=
  let config : CodeGenConfig := {
    fieldType := fieldToPoseidon field
    stateSize := stateSize
    sboxExp := exp
    includeProofAnchors := false
  }
  genSboxFunction config

-- ═══════════════════════════════════════════════════
-- Main dispatch
-- ═══════════════════════════════════════════════════

/-- Compile a Spec to C or Rust code. -/
def compileSpec (spec : Spec) (target : String) (hw : Hardware)
    (funcName : String) : Except String String :=
  -- Validate dimensions
  match spec.dims with
  | none => .error "Dimension mismatch: inner dimensions of compose don't match."
  | some _ =>
    match spec with
    | .ntt field size =>
      if target == "rust" then .error "Rust NTT codegen not yet wired (use --target c)"
      else .ok (compileNTTC field size hw funcName)
    | .poseidon2Sbox field stateSize exp =>
      if target == "rust" then .error "Rust Poseidon2 codegen not yet wired (use --target c)"
      else .ok (compilePoseidonC field stateSize exp funcName)
    | s =>
      let result := if target == "rust"
        then compileMatrixRust s funcName
        else compileMatrixC s funcName
      match result with
      | some code => .ok code
      | none => .error "Failed to convert spec to matrix expression."

end AmoLean.CompileSpec
