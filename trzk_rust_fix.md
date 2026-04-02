# TRZK Rust Codegen Fix: Type System Mismatch in Ultra Pipeline

## Status

**C path**: WORKING. Correctness verified at runtime (element-by-element mod p comparison). Benchmarks pass for BabyBear and KoalaBear at N=2^16, 2^20, 2^22.

**Rust path**: BROKEN. Runtime correctness check detects `MISMATCH at i=0` for KoalaBear. Root cause identified and documented below.

---

## The Problem

The Ultra pipeline generates NTT code via `TrustLean.Stmt`, which uses **signed `Int` arithmetic** internally. The C backend (`stmtToC`) works because C does implicit `int32_t → int64_t` promotion and truncation is well-defined. The Rust backend (`stmtToRust`) fails because Rust requires explicit casts and has different semantics for signed/unsigned truncation.

### Concrete failure

```
$ /tmp/amobench_rs
MISMATCH at i=0: ultra=1297177229 p3=1149235926
```

Generated Rust for a lazy butterfly (no reduction):
```rust
fn koalabear_ntt_ultra_rs(data: &mut [u32], twiddles: &[u32]) {
  let mut t0: u64;
  // ...
  a_val = data[idx as usize] as u64;     // load: u32 → u64 (zero-extend) ✓
  b_val = data[idx as usize] as u64;     // load: u32 → u64 (zero-extend) ✓
  w_val = twiddles[idx as usize] as u64; // load: u32 → u64 (zero-extend) ✓
  t0 = (w_val * b_val);                  // u64 * u64 → u64 (wrapping) ✓
  t1 = (a_val + t0);                     // u64 + u64 → u64 ← CAN EXCEED 2^32
  t2 = ((a_val + 2130706433) - t0);      // u64 arithmetic ← CAN EXCEED 2^32
  t3 = t1;                               // lazy: no reduction
  t4 = t2;                               // lazy: no reduction
  data[idx as usize] = t3 as u32;        // STORE: u64 → u32 TRUNCATES high bits ✗
  data[idx as usize] = t4 as u32;        // STORE: u64 → u32 TRUNCATES high bits ✗
}
```

**The bug**: Lazy stages compute intermediates in `u64` but store back to `u32` arrays. The `as u32` truncation discards the high 32 bits. For KoalaBear (p ≈ 2^31), `w*b` can be up to ~2^62, and `a + w*b` can be ~2^62 — far beyond u32 range. The truncated value is wrong, and all subsequent stages operate on garbage.

### Why C works

In C, `int64_t` intermediaries store to `int32_t` arrays via implicit truncation. But C's signed truncation preserves the low 32 bits, and when re-read as `int64_t`, sign-extension reconstructs a value that is **congruent mod 2^32** to the original. The NTT's modular arithmetic at the end (Solinas/Harvey reduction in final stages) produces the correct result because `fold(x) % p = fold(x mod 2^32) % p` for Solinas primes where `p < 2^31`.

In Rust, `u64 as u32` also preserves low 32 bits. But `u32 as u64` zero-extends (not sign-extends), so the round-trip `u64 → u32 → u64` is NOT the same as in C (`int64_t → int32_t → int64_t`). This breaks the implicit modular arithmetic that C relies on.

---

## Root Cause Analysis

There are **two orthogonal issues**:

### Issue A: TrustLean uses `Int` (signed) but Rust needs `u32/u64` (unsigned)

TrustLean's `LowLevelExpr` and `Stmt` types use `Int` for all arithmetic. This maps naturally to C's `int64_t` (signed, 64-bit, implicit promotion). It does NOT map to Rust's type system where `u32` and `u64` are distinct types requiring explicit casts.

**Location**: `.lake/packages/TrustLean/TrustLean/Backend/RustBackend.lean`
- `stmtToRust` emits `load` as `var = data[idx as usize];` — no cast
- `stmtToRust` emits `store` as `data[idx as usize] = val;` — no cast
- `exprToRust` emits literals as signed (negative values get parens)

### Issue B: Lazy reduction stores wide values into narrow arrays

Lazy stages (`ReductionChoice.lazy`) skip modular reduction. The butterfly computes:
```
sum  = a + w*b       (up to ~2^62 for 32-bit fields)
diff = p + a - w*b   (up to ~2^62)
```

These wide values are stored back to `data[i32/u32]` via truncation. The next stage reads them back as narrow values. In C, this works by accident (signed truncation + sign-extension preserves congruence mod 2^32, and final reduction corrects). In Rust with unsigned types, this does not work.

**Location**: `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean:54-57`
```lean
| .lazy =>
    let (vn, cgs') := cgs.freshVar
    (.assign vn xExpr, vn, cgs')  -- no reduction, value may exceed elem width
```

---

## Files Involved

### Files that MUST be modified

| File | What to change | Risk |
|---|---|---|
| `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean` (lines 217-240) | `emitRustFromPlanVerified`: the Rust emission wrapper. Currently does string post-processing to add `as u64`/`as u32` casts. Needs redesign. | Medium — this is the main fix target |
| `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean` (lines 143-173) | `lowerStageVerified`: generates Stmt per NTT stage. For Rust, lazy stages need to emit a truncation-safe store (either reduce before store, or use a wide scratch buffer). | Medium — affects lowering logic |

### Files that MUST NOT be modified

| File | Why |
|---|---|
| `.lake/packages/TrustLean/` (entire package) | External dependency. Modifying it breaks `lake update`. All fixes must be in the AMO-Lean wrapper layer. |
| `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean` lines 205-214 (`emitCFromPlanVerified`) | **C path is working and verified.** Do not touch. |
| `AmoLean/EGraph/Verified/Bitwise/TrustLeanBridge.lean` (lowering functions: `lowerSolinasFold`, `lowerMontyReduce`, `lowerHarveyReduce`) | These generate `Stmt` (language-agnostic IR). They are correct. The problem is in the Rust emission, not the IR. |
| `AmoLean/EGraph/Verified/Bitwise/UltraPipeline.lean` | Pipeline orchestration. Already correctly returns `(cCode, rustCode, report)`. No changes needed. |
| `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean` lines 433-517 (`optimizedNTTC_ultra`, `genOptimizedBenchC_ultra`) | C benchmark harness. Working. The correctness check in the C harness passes. |

### Files that MAY need minor adjustment

| File | What | Risk |
|---|---|---|
| `AmoLean/EGraph/Verified/Bitwise/OptimizedNTTPipeline.lean` lines 718-810 (`genOptimizedBenchRust_ultra`) | Rust benchmark harness. Currently uses `u32/u64` types for data vectors. May need adjustment depending on which fix approach is chosen. | Low |
| `Bench.lean` lines 759-762 | Dispatch for `--lang rust --pipeline ultra`. Already wired correctly. | None unless function signatures change |

### Reference files (read-only, for understanding)

| File | Contains |
|---|---|
| `.lake/packages/TrustLean/TrustLean/Backend/RustBackend.lean` | `stmtToRust` and `exprToRust` — how Stmt becomes Rust strings. 113 lines. |
| `.lake/packages/TrustLean/TrustLean/Backend/CBackend.lean` | `stmtToC` — the C equivalent that works. Compare to understand differences. |
| `AmoLean/EGraph/Verified/Bitwise/TrustLeanBridge.lean` lines 338-462 | `lowerSolinasFold`, `lowerHarveyReduce`, `lowerMontyReduce` — the verified lowering functions that produce Stmt. |
| `AmoLean/EGraph/Verified/Bitwise/VerifiedPlanCodeGen.lean` lines 42-94 | `lowerReductionChoice`, `lowerDIFButterflyByReduction` — how butterflies are lowered per reduction strategy. |

---

## Existing Resources

### C path (working reference)

`emitCFromPlanVerified` (VerifiedPlanCodeGen.lean:205-214) shows the correct pattern:
- All intermediates are `int64_t` (wide)
- Array elements are `int32_t` (narrow for 32-bit fields)
- C handles promotion/truncation implicitly
- `stmtToC` emits loads/stores without explicit casts — C does it

### Rust backend in TrustLean

`stmtToRust` (RustBackend.lean:76-112):
- `load`: `varName = base[idx as usize];` — no type cast
- `store`: `base[idx as usize] = val;` — no type cast
- `assign`: `varName = expr;` — no type cast

The backend is type-agnostic — it doesn't know whether variables are `i32`, `u32`, `i64`, or `u64`. The caller is responsible for declaring variable types and inserting casts.

### The current (broken) post-processing approach

`emitRustFromPlanVerified` (VerifiedPlanCodeGen.lean:228-239) currently does:
1. Calls `stmtToRust` to get raw Rust code (no casts)
2. String-replaces `as usize];` → `as usize] as u64;` (adds u64 cast on loads)
3. Detects store lines by pattern matching `data[` + `] = ` and appends `as u32`

This fixes the type mismatch errors but NOT the semantic truncation bug. The stores correctly cast `u64 → u32`, but the truncation loses data for lazy stages.

---

## Proposed Fix Approaches

### Approach A: Reduce before every store (simplest, ~20 LOC)

Modify `lowerStageVerified` so that **lazy stages emit a modular fold before storing**, not a true no-op. The "lazy" optimization moves from "skip reduction entirely" to "do a cheap partial reduction that fits in u32".

For Solinas primes (p = 2^k - c), the fold `(x >> k) * c + (x & mask)` always produces a value < 2p < 2^32 for 32-bit fields. So inserting a Solinas fold before store guarantees the value fits in u32.

**Change in `lowerReductionChoice`** (VerifiedPlanCodeGen.lean:42-57):
```lean
| .lazy =>
    -- For Rust safety: apply Solinas fold to guarantee output fits in elem width.
    -- This is still "lazy" from a performance perspective: Solinas fold (4 ops)
    -- vs Montgomery (5 ops) or Harvey (3 ops + branch).
    let (sr, cgs') := lowerSolinasFold xExpr k c cgs
    (sr.stmt, extractVar sr.resultVar, cgs')
```

**Pros**: Minimal change. One line. No new infrastructure. C path unchanged (it shares `lowerNTTFromPlanVerified` but the extra fold is harmless in C — slightly slower but correct).

**Cons**: The C path gets an unnecessary extra fold in lazy stages, making it slightly slower (~5-10%). The "lazy" optimization is weakened — instead of 0 ops, it's 4 ops (Solinas fold). This is still cheaper than Montgomery (5 ops) or Barrett (6 ops), but the whole point of lazy was to skip ALL reduction.

**Impact on C benchmarks**: Would need re-benchmarking. The +77-82% improvement may drop slightly.

### Approach B: Fork the lowering for C vs Rust (~40 LOC)

Create `lowerStageVerifiedRust` that always reduces before store, while keeping `lowerStageVerified` for C (unchanged). Then `emitRustFromPlanVerified` calls the Rust-specific version.

**New function** (VerifiedPlanCodeGen.lean):
```lean
def lowerStageVerifiedRust (stage : NTTStage) (n p k c mu : Nat) : Stmt :=
  -- Same as lowerStageVerified, but lazy stages use Solinas fold
  let effectiveRed := if stage.reduction == .lazy then .solinasFold else stage.reduction
  lowerStageVerified { stage with reduction := effectiveRed } n p k c mu
```

And `emitRustFromPlanVerified` uses `lowerNTTFromPlanVerifiedRust` which maps stages through this function.

**Pros**: C path completely untouched. Rust gets correctness. Clear separation.

**Cons**: Code duplication (two lowering paths). Need to maintain both. Risk of divergence over time.

### Approach C: Wide scratch buffer for lazy stages (~80 LOC)

Use a `Vec<u64>` scratch buffer for stages that accumulate without reduction, and only copy back to `u32` when a reducing stage occurs.

**Conceptually**:
```rust
let mut wide: Vec<u64> = data.iter().map(|&x| x as u64).collect();
// Lazy stages operate on wide[]
// Reducing stages: reduce(wide[i]) → u32 → back to data[i]
```

**Pros**: True lazy reduction. Maximum performance. Semantically clean.

**Cons**: Most complex. Changes the function signature (needs scratch buffer or internal allocation). May require changes in how `lowerStageVerified` generates load/store (two different arrays). Risk of introducing bugs.

### Recommendation: Approach B

Approach B is the right balance: C path untouched (verified, benchmarked), Rust path gets correctness via a simple fork, and the change is small enough to not introduce new bugs. The performance cost is modest (Solinas fold in lazy stages = 4 extra ops per butterfly in stages that would have had 0).

---

## Concrete Tasks

### Task 1: Create `lowerStageVerifiedRust` (VerifiedPlanCodeGen.lean)

Add a new function after `lowerStageVerified` (line 173):

```lean
/-- Rust-safe stage lowering: lazy stages use Solinas fold to ensure output fits u32.
    Necessary because Rust u64→u32 truncation loses high bits, unlike C's int64→int32. -/
def lowerStageVerifiedRust (stage : NTTStage) (n p k c mu : Nat) : Stmt :=
  let safeStage := if stage.reduction == .lazy
    then { stage with reduction := .solinasFold }
    else stage
  lowerStageVerified safeStage n p k c mu
```

Then add:
```lean
def lowerNTTFromPlanVerifiedRust (plan : Plan) (k c mu : Nat) : Stmt :=
  let stmts := plan.stages.toList.map fun stage =>
    lowerStageVerifiedRust stage plan.size plan.field k c mu
  stmts.foldl Stmt.seq Stmt.skip
```

### Task 2: Update `emitRustFromPlanVerified` (VerifiedPlanCodeGen.lean)

Change line 219 from:
```lean
let stmt := lowerNTTFromPlanVerified plan k c mu
```
to:
```lean
let stmt := lowerNTTFromPlanVerifiedRust plan k c mu
```

Keep all the existing `as u64`/`as u32` string post-processing — it's still needed for the load/store casts.

### Task 3: Verify `emitCFromPlanVerified` is UNCHANGED

Run the C benchmarks after the change to confirm they still pass:
```bash
lake env lean --run Bench.lean -- --pipeline ultra --field babybear --size 16 --primitive ntt --lang c
lake env lean --run Bench.lean -- --pipeline ultra --field koalabear --size 16 --primitive ntt --lang c
```

Both must show results (no MISMATCH, no COMPILE ERROR) and performance should be identical to pre-change baselines:
- BabyBear 2^16 C: ~301 us AMO, ~478 us P3
- BabyBear 2^20 C: ~4256 us AMO, ~19119 us P3
- KoalaBear 2^20 C NEON: ~4027 us AMO, ~19139 us P3

### Task 4: Run Rust benchmarks and verify correctness

```bash
lake env lean --run Bench.lean -- --pipeline ultra --field koalabear --size 20,22 --primitive ntt --lang rust --hardware arm-neon
```

Expected: no MISMATCH, benchmark results printed. The correctness check in the Rust harness compares `amo_out[i] % p == p3_out[i] % p` for all N elements.

### Task 5: Run BabyBear Rust as well

```bash
lake env lean --run Bench.lean -- --pipeline ultra --field babybear --size 16,20 --primitive ntt --lang rust --hardware arm-scalar
```

### Task 6: Update `maxTempsInPlan` if needed

`maxTempsInPlan` (VerifiedPlanCodeGen.lean:192-201) counts temp variables by dry-running butterfly lowering. If `lowerStageVerifiedRust` produces more temps than `lowerStageVerified` (because Solinas fold replaces lazy no-op), the count might increase. Check that the generated Rust declares enough `let mut tN: u64;` variables. This is likely fine since Solinas fold uses only 1 temp (same as lazy).

---

## Invariants to Preserve

1. **`emitCFromPlanVerified` produces identical output before and after the fix.** The C path must not be touched.

2. **`lowerStageVerified` (the original) is unchanged.** It's used by both `emitCFromPlanVerified` and `lowerNTTFromPlanVerified`. Only the Rust path gets a new function.

3. **All existing theorems compile.** The theorems in VerifiedPlanCodeGen.lean (lines 246+) reference `lowerReductionChoice`, `lowerDIFButterflyByReduction`, etc. None of these should change.

4. **`ultraPipeline` signature is `String × String × String`.** The triple `(cCode, rustCode, report)` was introduced in this session. Don't change it back to a pair.

5. **The Rust benchmark harness** (`genOptimizedBenchRust_ultra` in OptimizedNTTPipeline.lean) uses `u32`/`u64` types and calls `p3_bf` (which takes `&mut u32`). This is correct. The NTT function signature should be `fn name(data: &mut [u32], twiddles: &[u32])`. The internal `u64` intermediates are declared inside the function.

6. **The C benchmark harness** (`optimizedNTTC_ultra`) has a correctness check that compares AMO vs P3 output mod p before benchmarking. The Rust harness has the same check. Both must pass.

---

## How to Verify the Fix is Complete

```bash
# 1. Build
lake build Bench

# 2. C path still works (MUST pass — regression check)
lake env lean --run Bench.lean -- --pipeline ultra --field babybear,koalabear --size 16 --lang c

# 3. Rust path now works (MUST pass — the fix)
lake env lean --run Bench.lean -- --pipeline ultra --field babybear,koalabear --size 16 --lang rust

# 4. Large sizes (correctness at scale)
lake env lean --run Bench.lean -- --pipeline ultra --field koalabear --size 20 --lang rust --hardware arm-neon

# 5. No regressions in legacy pipeline
lake env lean --run Bench.lean -- --pipeline legacy --field babybear --size 16 --lang c
```

All five commands must produce benchmark results with no MISMATCH, no COMPILE ERROR, and no PARSE ERROR.

---

## Context for the Agent

This document was produced during a session where we:

1. Audited the cost model vs Ultra pipeline connection (found it was disconnected)
2. Planned and another agent implemented cost model integration into Ultra
3. Fixed the Bench.lean parser (C printf emits 6 fields, parser expected 4)
4. Added runtime correctness checks (element-by-element mod p comparison)
5. Created `genOptimizedBenchRust_ultra` to expose the Ultra Rust path
6. Discovered the type mismatch (`i64` vs `u32`) and fixed it to `u64`/`u32`
7. Discovered the deeper semantic bug (lazy truncation loses high bits)

The C benchmarks are validated and show +77-82% improvement over Plonky3 Montgomery. The Rust path is the last piece to close.

**Do NOT use `lake build` and run the compiled binary.** The 193MB binary takes >60s to initialize (3136 module inits). Use `lake env lean --run Bench.lean -- [flags]` instead.
