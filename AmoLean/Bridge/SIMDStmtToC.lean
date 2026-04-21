import TrustLean.Backend.CBackend
import TrustLean.Backend.RustBackend

/-!
# SIMDStmtToC — Type-Safe NEON Intrinsic Emission via Stmt.call

Route NEON butterflies through TrustLean.Stmt IR using existing Stmt.call
constructor. Zero TrustLean modifications.

Key insight (Option D): `Stmt.call result fname args` already exists. We just need:
1. A type-safe ADT for intrinsic names (no string typos)
2. A wrapper that handles void intrinsics (stores) and struct decomposition

Trust boundary: `evalStmt(.call) = none`. NEON intrinsics are trusted external calls,
same as `stmtToC` is trusted for scalar emission.

Node N37.1 in Fase v3.7.0 (Verified SIMD Codegen).
Consumed by: N37.4 VerifiedSIMDButterfly.
-/

set_option autoImplicit false

namespace AmoLean.Bridge.SIMDStmtToC

open _root_.TrustLean (Stmt VarName LowLevelExpr stmtToC stmtToRust indentStr
  varNameToC varNameToStr exprToC exprToRust joinCode)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: NeonIntrinsic ADT
-- ══════════════════════════════════════════════════════════════════

/-- Type-safe NEON intrinsic/helper names. Eliminates string typos.
    Each constructor maps to exactly one C function (ARM NEON intrinsic or
    project helper like neon_deinterleave_load) via `toCName`.
    Grouped by return type for clarity. -/
inductive NeonIntrinsic where
  -- Arithmetic 4-lane (value-returning, int32x4_t → int32x4_t)
  | sqdmulh       -- vqdmulhq_s32: saturating doubling multiply high
  | mul_s32        -- vmulq_s32: multiply
  | hsub           -- vhsubq_s32: halving subtract
  | add_u32        -- vaddq_u32: unsigned add
  | sub_u32        -- vsubq_u32: unsigned subtract
  | add_s32        -- vaddq_s32: signed add
  | sub_s32        -- vsubq_s32: signed subtract (insurance for unsigned-only fallback)
  -- Bitwise/Compare 4-lane (value-returning, uint32x4_t)
  | cmpGe_u32      -- vcgeq_u32: compare ≥ unsigned
  | and_u32        -- vandq_u32: bitwise AND
  | min_u32        -- vminq_u32: minimum unsigned
  | clt_s32        -- vcltq_s32: compare < signed
  -- Multiply-subtract 4-lane (value-returning)
  | mls_u32        -- vmlsq_u32: a - b*c
  -- Memory 4-lane (value-returning)
  | load4_s32      -- vld1q_s32: load 4 × int32
  -- Memory 4-lane (void — no return value)
  | store4_s32     -- vst1q_s32: store 4 × int32
  | store4x2_s32   -- neon_interleave_store: store and interleave (wraps vst2q_s32)
  -- 2-lane ops for hs2 butterfly (int32x2_t)
  | load2_s32      -- vld1_s32: load 2 × int32 (int32x2_t)
  | store2_s32     -- vst1_s32: store 2 × int32 (void)
  | combine_s32    -- vcombine_s32: combine 2×int32x2_t → int32x4_t
  | get_low_s32    -- vget_low_s32: extract lower int32x2_t from int32x4_t
  | get_high_s32   -- vget_high_s32: extract upper int32x2_t from int32x4_t
  -- Struct decomposition (void — calls project helper from N37.2)
  | deinterleaveLoad -- neon_deinterleave_load: vld2q + decompose
  -- 64-bit ops for Goldilocks butterfly (v3.9.0 N39.9)
  | add_u64          -- vaddq_u64: 2-lane add uint64x2_t
  | sub_u64          -- vsubq_u64: 2-lane subtract uint64x2_t
  | load2_u64        -- vld1q_u64: load 2 × uint64 (uint64x2_t)
  | store2_u64       -- vst1q_u64: store 2 × uint64 (void)
  | widening_mul32   -- vmull_u32: 2×32→2×64 widening multiply
  | narrow_high32    -- vshrn_n_u64: narrow high 32 bits (shift right + narrow)
  | narrow_low32     -- vmovn_u64: narrow low 32 bits (truncate)
  -- v3.20.b B2 (§14.13.2 Gap 2): batch interleave load/store + u32 lane extract.
  -- Added for the packed butterfly kernel `emitPackedButterflyNeonDIT_C` (B3):
  -- vld2q_s32/vst2q_s32 handle the interleaved layout MemLayout.transposeForBatch
  -- produces (lane 0 of polys 0..3 at data[0..3], lane 1 at data[4..7], etc.),
  -- and vget_low_u32/vget_high_u32 split a uint32x4_t into halves for the REDC
  -- widening step inside the kernel. Naming mirrors the existing get_low_s32/
  -- get_high_s32 (int32 variants) — same intrinsic, different type class.
  | load2x4_s32      -- vld2q_s32: deinterleave + load 2×4 int32 (int32x4x2_t)
  | store2x4_raw_s32 -- vst2q_s32: interleave + store 2×4 int32 (void; raw,
                     --   distinct from `store4x2_s32` which wraps the project
                     --   helper `neon_interleave_store`)
  | get_low_u32      -- vget_low_u32: extract lower uint32x2_t from uint32x4_t
  | get_high_u32     -- vget_high_u32: extract upper uint32x2_t from uint32x4_t
  deriving BEq, Repr, Inhabited

/-- Map ADT to C intrinsic name. SINGLE SOURCE OF TRUTH for naming.
    This is the only place where NEON string names appear. -/
def NeonIntrinsic.toCName : NeonIntrinsic → String
  | .sqdmulh          => "vqdmulhq_s32"
  | .mul_s32          => "vmulq_s32"
  | .hsub             => "vhsubq_s32"
  | .add_u32          => "vaddq_u32"
  | .sub_u32          => "vsubq_u32"
  | .add_s32          => "vaddq_s32"
  | .sub_s32          => "vsubq_s32"
  | .cmpGe_u32        => "vcgeq_u32"
  | .and_u32          => "vandq_u32"
  | .min_u32          => "vminq_u32"
  | .clt_s32          => "vcltq_s32"
  | .mls_u32          => "vmlsq_u32"
  | .load4_s32        => "vld1q_s32"
  | .store4_s32       => "vst1q_s32"
  | .store4x2_s32     => "neon_interleave_store"
  | .load2_s32        => "vld1_s32"
  | .store2_s32       => "vst1_s32"
  | .combine_s32      => "vcombine_s32"
  | .get_low_s32      => "vget_low_s32"
  | .get_high_s32     => "vget_high_s32"
  | .deinterleaveLoad => "neon_deinterleave_load"
  -- 64-bit Goldilocks (v3.9.0)
  | .add_u64          => "vaddq_u64"
  | .sub_u64          => "vsubq_u64"
  | .load2_u64        => "vld1q_u64"
  | .store2_u64       => "vst1q_u64"
  | .widening_mul32   => "vmull_u32"
  | .narrow_high32    => "vshrn_n_u64"
  | .narrow_low32     => "vmovn_u64"
  -- v3.20.b B2 (§14.13.2)
  | .load2x4_s32      => "vld2q_s32"
  | .store2x4_raw_s32 => "vst2q_s32"
  | .get_low_u32      => "vget_low_u32"
  | .get_high_u32     => "vget_high_u32"

/-- Is this a void-return intrinsic (stores, struct decomposition)? -/
def NeonIntrinsic.isVoid : NeonIntrinsic → Bool
  | .store4_s32 | .store4x2_s32 | .store2_s32 | .store2_u64 | .deinterleaveLoad
  | .store2x4_raw_s32 => true  -- v3.20.b B2: vst2q_s32 is void like its cousins
  | _ => false

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Stmt.call Wrappers
-- ══════════════════════════════════════════════════════════════════

/-- Build a Stmt.call for a value-returning NEON intrinsic.
    Type-safe: `neonCall .sqdmulh nv0 [a, b]` compiles;
    a string typo would be caught at the ADT level. -/
def neonCall (intr : NeonIntrinsic) (result : VarName)
    (args : List LowLevelExpr) : Stmt :=
  Stmt.call result intr.toCName args

/-- Build a void Stmt.call for store intrinsics.
    Uses sentinel VarName "__void" (variable is never used). -/
def neonCallVoid (intr : NeonIntrinsic) (args : List LowLevelExpr) : Stmt :=
  Stmt.call (.user "__void") intr.toCName args

-- ══════════════════════════════════════════════════════════════════
-- Section 3: SIMD-aware C Emission
-- ══════════════════════════════════════════════════════════════════

/-- Reverse map: C function name → NeonIntrinsic. Single source of truth for
    void detection (via `fromCName fname |>.any (·.isVoid)`).
    Replaces the fragile `voidIntrinsicNames` list. -/
def NeonIntrinsic.fromCName : String → Option NeonIntrinsic
  | "vqdmulhq_s32"            => some .sqdmulh
  | "vmulq_s32"               => some .mul_s32
  | "vhsubq_s32"              => some .hsub
  | "vaddq_u32"               => some .add_u32
  | "vsubq_u32"               => some .sub_u32
  | "vaddq_s32"               => some .add_s32
  | "vsubq_s32"               => some .sub_s32
  | "vcgeq_u32"               => some .cmpGe_u32
  | "vandq_u32"               => some .and_u32
  | "vminq_u32"               => some .min_u32
  | "vcltq_s32"               => some .clt_s32
  | "vmlsq_u32"               => some .mls_u32
  | "vld1q_s32"               => some .load4_s32
  | "vst1q_s32"               => some .store4_s32
  | "neon_interleave_store"   => some .store4x2_s32
  | "vld1_s32"                => some .load2_s32
  | "vst1_s32"                => some .store2_s32
  | "vcombine_s32"            => some .combine_s32
  | "vget_low_s32"            => some .get_low_s32
  | "vget_high_s32"           => some .get_high_s32
  | "neon_deinterleave_load"  => some .deinterleaveLoad
  -- 64-bit Goldilocks (v3.9.0)
  | "vaddq_u64"               => some .add_u64
  | "vsubq_u64"               => some .sub_u64
  | "vld1q_u64"               => some .load2_u64
  | "vst1q_u64"               => some .store2_u64
  | "vmull_u32"                => some .widening_mul32
  | "vshrn_n_u64"              => some .narrow_high32
  | "vmovn_u64"                => some .narrow_low32
  -- v3.20.b B2 (§14.13.2)
  | "vld2q_s32"               => some .load2x4_s32
  | "vst2q_s32"               => some .store2x4_raw_s32
  | "vget_low_u32"            => some .get_low_u32
  | "vget_high_u32"           => some .get_high_u32
  | _                         => none

/-- Emit a Stmt to C with NEON intrinsic handling.
    Delegates non-call Stmt to TrustLean.stmtToC (trusted).
    Special handling for:
    - Void intrinsics: emit `fname(args);` without `result =`
    - Value-returning intrinsics: emit `result = fname(args);`
      (variable pre-declared with NEON type at function top by N37.3) -/
def simdStmtToC (level : Nat) : Stmt → String
  | .call result fname args =>
    let argsStr := ", ".intercalate (args.map exprToC)
    let pad := indentStr level
    if (NeonIntrinsic.fromCName fname).any (·.isVoid) then
      pad ++ fname ++ "(" ++ argsStr ++ ");"
    else
      pad ++ varNameToC result ++ " = " ++ fname ++ "(" ++ argsStr ++ ");"
  | .seq s1 s2 => joinCode (simdStmtToC level s1) (simdStmtToC level s2)
  | other => stmtToC level other

-- ══════════════════════════════════════════════════════════════════
-- Section 4: SIMD-aware Rust Emission (v3.8.0)
-- ══════════════════════════════════════════════════════════════════

/-- Determine if a VarName refers to a NEON vector variable (needs transmute). -/
private def isNeonVar : VarName → Bool
  | .user s => s.startsWith "nv" || s.startsWith "nu" || s.startsWith "nh" ||
               s.startsWith "p_vec"
  | _ => false

/-- Emit a LowLevelExpr for Rust NEON context.
    NEON vector variables are wrapped in std::mem::transmute() to handle
    int32x4_t ↔ uint32x4_t conversions that C does implicitly. Zero-cost.
    Pointer arithmetic uses .add() instead of + (Rust raw pointer semantics). -/
private def neonArgToRust : LowLevelExpr → String
  | .varRef v =>
    let name := varNameToStr v
    if isNeonVar v then s!"std::mem::transmute({name})" else name
  | .addrOf v => "&mut " ++ varNameToStr v
  | .binOp .add (.varRef v) (.litInt n) =>
    -- Pointer offset: ptr.add(n) instead of ptr + n (Rust raw pointer semantics)
    s!"unsafe \{ {varNameToStr v}.add({n} as usize) }"
  | other => exprToRust other

/-- Emit a Stmt to Rust with NEON intrinsic handling.
    Gemelo of simdStmtToC. ARM NEON intrinsics have identical names in C and Rust
    (core::arch::aarch64). Differences from C:
    - `unsafe { }` wrapping for each intrinsic call
    - `std::mem::transmute()` for NEON vector args (int32x4_t ↔ uint32x4_t)
    - Non-call Stmt delegated to stmtToRust (not stmtToC) -/
def simdStmtToRust (level : Nat) : Stmt → String
  | .call result fname args =>
    let argsStr := ", ".intercalate (args.map neonArgToRust)
    let pad := indentStr level
    if (NeonIntrinsic.fromCName fname).any (·.isVoid) then
      pad ++ "unsafe { " ++ fname ++ "(" ++ argsStr ++ ") };"
    else
      pad ++ varNameToStr result ++ " = unsafe { " ++ fname ++ "(" ++ argsStr ++ ") };"
  | .seq s1 s2 => joinCode (simdStmtToRust level s1) (simdStmtToRust level s2)
  | other => stmtToRust level other

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- toCName: 4-lane intrinsics. -/
example : NeonIntrinsic.sqdmulh.toCName = "vqdmulhq_s32" := rfl
example : NeonIntrinsic.load4_s32.toCName = "vld1q_s32" := rfl
example : NeonIntrinsic.store4_s32.toCName = "vst1q_s32" := rfl
example : NeonIntrinsic.sub_s32.toCName = "vsubq_s32" := rfl

/-- toCName: 2-lane intrinsics (hs2). -/
example : NeonIntrinsic.load2_s32.toCName = "vld1_s32" := rfl
example : NeonIntrinsic.store2_s32.toCName = "vst1_s32" := rfl
example : NeonIntrinsic.combine_s32.toCName = "vcombine_s32" := rfl
example : NeonIntrinsic.get_low_s32.toCName = "vget_low_s32" := rfl
example : NeonIntrinsic.get_high_s32.toCName = "vget_high_s32" := rfl

/-- toCName: helper. -/
example : NeonIntrinsic.deinterleaveLoad.toCName = "neon_deinterleave_load" := rfl

/-- Void classification. -/
example : NeonIntrinsic.store4_s32.isVoid = true := rfl
example : NeonIntrinsic.store2_s32.isVoid = true := rfl
example : NeonIntrinsic.deinterleaveLoad.isVoid = true := rfl
example : NeonIntrinsic.sqdmulh.isVoid = false := rfl
example : NeonIntrinsic.combine_s32.isVoid = false := rfl

/-- fromCName roundtrips with toCName. -/
example : NeonIntrinsic.fromCName NeonIntrinsic.sqdmulh.toCName = some .sqdmulh := rfl
example : NeonIntrinsic.fromCName NeonIntrinsic.store2_s32.toCName = some .store2_s32 := rfl
example : NeonIntrinsic.fromCName NeonIntrinsic.deinterleaveLoad.toCName = some .deinterleaveLoad := rfl
example : NeonIntrinsic.fromCName "not_a_real_intrinsic" = none := rfl

/-- neonCall produces a Stmt.call with correct fname. -/
example : match neonCall .sqdmulh (.user "nv0") [.varRef (.user "a"), .varRef (.user "b")] with
  | .call _ fname _ => fname == "vqdmulhq_s32"
  | _ => false := rfl

/-- neonCallVoid produces a Stmt.call with sentinel VarName. -/
example : match neonCallVoid .store4_s32 [.varRef (.user "ptr"), .varRef (.user "v")] with
  | .call result fname _ => fname == "vst1q_s32" && result == .user "__void"
  | _ => false := rfl

/-- simdStmtToC emits value-returning intrinsic correctly. -/
example : simdStmtToC 1 (neonCall .sqdmulh (.user "nv0") [.varRef (.user "a"), .varRef (.user "b")])
    = "  nv0 = vqdmulhq_s32(a, b);" := rfl

/-- simdStmtToC emits void 4-lane store. -/
example : simdStmtToC 1 (neonCallVoid .store4_s32 [.varRef (.user "ptr"), .varRef (.user "v")])
    = "  vst1q_s32(ptr, v);" := rfl

/-- simdStmtToC emits void 2-lane store. -/
example : simdStmtToC 1 (neonCallVoid .store2_s32 [.varRef (.user "ptr"), .varRef (.user "v")])
    = "  vst1_s32(ptr, v);" := rfl

/-- simdStmtToC delegates non-call Stmt to stmtToC. -/
example : simdStmtToC 1 (.assign (.user "x") (.litInt 42))
    = stmtToC 1 (.assign (.user "x") (.litInt 42)) := rfl

/-- simdStmtToC handles addrOf for deinterleaveLoad output pointers. -/
example : simdStmtToC 1 (neonCallVoid .deinterleaveLoad
    [.addrOf (.user "a"), .addrOf (.user "b"), .varRef (.user "ptr")])
    = "  neon_deinterleave_load(&a, &b, ptr);" := rfl

-- ── Rust emitter tests (v3.8.0) ──

/-- simdStmtToRust produces non-empty output for NEON calls. -/
example : (simdStmtToRust 1 (neonCall .sqdmulh (.user "nv0")
    [.varRef (.user "nv1"), .varRef (.user "nv2")])).length > 50 := by native_decide

/-- simdStmtToRust: non-NEON vars (pointers) don't get transmuted. -/
example : (simdStmtToRust 1 (neonCallVoid .store4_s32
    [.varRef (.user "a_ptr"), .varRef (.user "nu5")])).length > 20 := by native_decide

/-- simdStmtToRust delegates non-call Stmt to stmtToRust. -/
example : simdStmtToRust 1 (.assign (.user "x") (.litInt 42))
    = stmtToRust 1 (.assign (.user "x") (.litInt 42)) := by native_decide

/-- simdStmtToRust handles addrOf for deinterleaveLoad. -/
example : (simdStmtToRust 1 (neonCallVoid .deinterleaveLoad
    [.addrOf (.user "nv0"), .addrOf (.user "nv1"), .varRef (.user "ptr")])).length > 30 := by native_decide

end SmokeTests

end AmoLean.Bridge.SIMDStmtToC
