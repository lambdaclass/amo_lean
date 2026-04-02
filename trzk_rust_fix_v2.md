# TRZK Rust Codegen Fix v2: Lazy Stage Truncation in Ultra Pipeline

## Status

| Path | Pipeline | Status | Evidence |
|---|---|---|---|
| C, scalar | Ultra | **WORKING** | BabyBear 2^16/20/22, KoalaBear 2^20/22 — correctness check PASS |
| C, NEON | Ultra | **WORKING** | KoalaBear 2^20/22 — correctness check PASS |
| Rust, scalar | Ultra | **BROKEN** | `MISMATCH at i=0: ultra=1297177229 p3=1149235926` |
| Rust, NEON | Ultra | **BROKEN** | Same root cause |
| C/Rust | Legacy | **WORKING** | Not affected (legacy uses uniform reduction, no lazy stages) |
| Any, Goldilocks | Ultra | **NOT AFFECTED** | k=64 means elemType=u64=wideType, no truncation |

---

## Scope

This bug affects **32-bit fields only** (BabyBear, KoalaBear, Mersenne31) when:
1. Target language is **Rust** (C is not affected), AND
2. Pipeline is **Ultra** (legacy is not affected), AND
3. The plan contains at least one **lazy stage** (which is the typical case for NTTs with >2 stages)

Goldilocks (64-bit, k=64) is not affected because `elemType = u64` and `wideType = u64` are the same — there is no narrow→wide→narrow round-trip.

---

## The Problem

### What happens

The Ultra pipeline assigns per-stage reduction strategies. Early stages often use `.lazy` (no reduction) because bounds are still safe. The lowered `Stmt` IR computes butterfly outputs in wide arithmetic (`Int`, which maps to `int64_t` in C and `u64` in Rust) but stores results back to array elements that are narrow (`int32_t` in C, `u32` in Rust).

For lazy stages, the butterfly computes:
```
sum  = a + w*b       (up to ~p^2 ≈ 2^62 for 32-bit fields)
diff = p + a - w*b   (up to ~p^2 ≈ 2^62)
```

These values are stored to `data[i]` which is `u32` in Rust, truncating the upper 32 bits.

### Why C works

In C, `int64_t → int32_t` truncation preserves the low 32 bits. When re-read as `int64_t`, sign-extension reconstructs a value `v'` such that `v' ≡ v (mod 2^32)`. The NTT's subsequent reducing stages apply `fold(v') % p`, and for Solinas primes where `p < 2^31`, the modular reduction is correct because the Solinas fold identity `fold(x) % p = x % p` holds for all `x`, including sign-extended truncated values.

This is not accidental — it relies on two properties:
1. `int32_t` truncation + sign-extension preserves congruence mod 2^32
2. Solinas fold correctness is unconditional: `fold(x) % p = x % p` for all `x : Nat`

### Why Rust breaks

In Rust, `u64 as u32` preserves the low 32 bits (same as C). But `u32 as u64` **zero-extends** (not sign-extends). For values where bit 31 is set (common since p ≈ 2^31), the round-trip `u64 → u32 → u64` produces a different value than C's `int64 → int32 → int64`:

```
C:    0xFFFFFFFF_80000001 → (int32_t) 0x80000001 → (int64_t) 0xFFFFFFFF_80000001  ✓ preserved
Rust: 0xFFFFFFFF_80000001 → (u32)     0x80000001 → (u64)     0x00000000_80000001  ✗ different
```

The subsequent reduction stages operate on a completely different value, producing wrong outputs.

### Concrete failure

```
$ /tmp/amobench_rs
MISMATCH at i=0: ultra=1297177229 p3=1149235926
```

Generated code for a lazy stage (KoalaBear):
```rust
// All intermediates are u64, data array is u32
a_val = data[i as usize] as u64;
b_val = data[j as usize] as u64;
w_val = twiddles[tw_idx as usize] as u64;
t0 = (w_val * b_val);           // u64, can be ~2^62
t1 = (a_val + t0);              // u64, can be ~2^62
t2 = ((a_val + 2130706433) - t0);
t3 = t1;                        // lazy: NO reduction
t4 = t2;
data[i as usize] = t3 as u32;  // TRUNCATES to low 32 bits
data[j as usize] = t4 as u32;  // TRUNCATES to low 32 bits
```

---

## Why "Replace Lazy with Solinas Fold" Does NOT Work

The v1 report proposed replacing `.lazy` with `.solinasFold` in the Rust path. This is **mathematically wrong** for fields with large Solinas constant `c`.

For a lazy butterfly with inputs in `[0, p)`, the worst case is `sum = a + w*b < p + p^2`. A single Solinas fold maps `x → (x >> k) * c + (x & mask)`. The output size depends on `c`:

| Field | p | k | c | Worst input | After 1 fold | After N folds to fit u32 |
|---|---|---|---|---|---|---|
| Mersenne31 | 2^31-1 | 31 | 1 | 2^62 | 2^32 (32 bits) | **1 fold** |
| KoalaBear | 2^31-2^24+1 | 31 | 2^24-1 | 2^62 | 2^55 (55 bits) | **5 folds** |
| BabyBear | 2^31-2^27+1 | 31 | 2^27-1 | 2^62 | 2^58 (58 bits) | **8 folds** |

For BabyBear, 8 iterated Solinas folds = ~32 ops per butterfly — far worse than Montgomery (5 ops). The "lazy" optimization would cost more than any named reduction. This approach is unviable for any prime with `c > 1`.

---

## Source File Situation

**Only 3 of 59 Bitwise modules have source `.lean` files.** The other 56 exist only as compiled `.olean` artifacts. This is a constraint on any fix.

### Files with source (CAN inspect and modify)

| File | Lines | Key contents |
|---|---|---|
| `VerifiedPlanCodeGen.lean` | 270 | `lowerReductionChoice`, `lowerDIFButterflyByReduction`, `lowerRadix4ButterflyByReduction`, `lowerStageVerified`, `lowerNTTFromPlanVerified`, `emitCFromPlanVerified`, `emitRustFromPlanVerified`, `maxTempsInPlan` |
| `UltraPipeline.lean` | 282 | `ultraPipeline` (orchestration, returns `(cCode, rustCode, report)`) |
| `OptimizedNTTPipeline.lean` | 930+ | `optimizedNTTC_ultra`, `genOptimizedBenchC_ultra`, `genOptimizedBenchRust_ultra`, P3 reference codegen |

### Files WITHOUT source (olean-only, CANNOT inspect or modify)

| Module | Key contents (from earlier investigation, may be stale) |
|---|---|
| `TrustLeanBridge` | `lowerSolinasFold`, `lowerMontyReduce`, `lowerHarveyReduce` — the verified lowering functions that produce `Stmt` |
| `VerifiedCodeGen` | `lowerDIFButterflyStmt`, `solinasFoldLLE` — original Solinas butterfly |
| `BoundPropagation` | `ReductionChoice`, `BoundRuleFactory`, `stageBoundFactor` |
| `MultiRelMixed` | `saturate`, `Config`, `tieredStep` |
| `MixedSaturation` | `applyRulesF`, `rebuildF` |
| `CostModelDef` | `HardwareCost`, `mixedOpCost`, hardware targets |
| All other 50 modules | Various verified components |

**Consequence**: `lowerSolinasFold`, `lowerMontyReduce`, and `lowerHarveyReduce` cannot be read from source. They can only be called as black boxes. Their behavior was documented in earlier sessions but the documentation references source lines that no longer exist.

**Critical warning**: A `lake clean && lake build` would fail catastrophically — only these 3 source files can be recompiled. The other 56 depend on having their `.olean` files cached. Any fix must preserve the existing `.olean` cache.

---

## Temp Variable Counts Per Reduction Strategy

Measured by dry-running `lowerDIFButterflyByReduction` with each strategy (BabyBear params):

| Strategy | Temps used | Notes |
|---|---|---|
| `.lazy` | 5 | wb, sum, diff, assignSum, assignDiff |
| `.solinasFold` | 3 | Uses separate `lowerDIFButterflyStmt` path (not generic butterfly) |
| `.montgomery` | 11 | Generic butterfly + 4 temps per REDC × 2 (sum+diff) |
| `.harvey` | 5 | Generic butterfly + 1 temp per Harvey × 2 |

This matters for `maxTempsInPlan` which declares `let mut tN: u64;` variables. If the Rust path uses a different reduction for lazy stages, the temp count changes. Currently `maxTempsInPlan` uses the C lowering path. If the Rust path replaces `.lazy` (5 temps) with `.montgomery` (11 temps), it needs its own `maxTempsInPlanRust`.

---

## Proposed Fix: Approach D — Montgomery for Lazy Rust Stages

### Why Montgomery

Montgomery REDC is the only single-pass reduction that:
1. **Handles the full lazy range**: valid for inputs `x ∈ [0, p*R)` where `R = 2^32`. For all 32-bit fields, `p*R ≈ 2^63 > p^2 ≈ 2^62`, so lazy butterfly outputs are within range.
2. **Outputs fit u32**: Montgomery produces `result ∈ [0, p) ⊂ [0, 2^31)`.
3. **Single pass**: 5 ops — constant cost, no iteration needed.
4. **Already implemented**: `lowerMontyReduce` exists as an olean-compiled function.

Verified bounds:

| Field | p*R (Montgomery valid range) | Worst lazy output | p*R > worst? |
|---|---|---|---|
| BabyBear | 8,646,911,288,846,319,616 (63b) | 4,053,239,670,673,244,162 (62b) | **YES** |
| KoalaBear | 9,151,314,447,111,815,168 (63b) | 4,539,909,905,758,289,922 (62b) | **YES** |
| Mersenne31 | 9,223,372,032,559,808,512 (63b) | 4,611,686,016,279,904,256 (62b) | **YES** |

### Design

Create a Rust-specific lowering that replaces `.lazy` with `.montgomery` only for the Rust emission path. The C path remains completely unchanged.

```
C path:    Plan → lowerNTTFromPlanVerified → Stmt → stmtToC    (UNCHANGED)
Rust path: Plan → lowerNTTFromPlanVerifiedRust → Stmt → stmtToRust + casts
                  ↑ lazy stages become montgomery
```

### Performance cost

Montgomery (5 ops) vs lazy (0 ops): +5 ops per butterfly in stages that were lazy. For a typical 20-stage NTT with ~2 lazy stages, this adds ~5 ops × N/2 butterflies × 2 stages. At 1 GHz, for N=2^20: ~5 × 500K × 2 = 5M ops ≈ 5ms extra. The total NTT is ~4000μs, so the overhead is negligible (~0.1%).

---

## Concrete Tasks

### Task 1: Add `lowerNTTFromPlanVerifiedRust` to VerifiedPlanCodeGen.lean

Insert after `lowerNTTFromPlanVerified` (line 185):

```lean
/-- Rust-safe NTT lowering: lazy stages use Montgomery to ensure output fits u32.
    
    Rationale: In C, int64→int32 truncation + sign-extension preserves congruence
    mod 2^32, so lazy stages (no reduction) work correctly. In Rust, u64→u32
    truncation + zero-extension does NOT preserve this — values with bit 31 set
    round-trip to different u64 values. Montgomery REDC maps [0, p*R) → [0, p),
    and p*R > p^2 (the lazy worst case), so it's always valid.
    
    For 64-bit fields (Goldilocks), this function is identical to lowerNTTFromPlanVerified
    because elemType = u64 = wideType (no truncation issue). -/
def lowerNTTFromPlanVerifiedRust (plan : Plan) (k c mu : Nat) : Stmt :=
  let stmts := plan.stages.toList.map fun stage =>
    let rustSafeStage := if stage.reduction == .lazy && k < 64
      then { stage with reduction := .montgomery }
      else stage
    lowerStageVerified rustSafeStage plan.size plan.field k c mu
  stmts.foldl Stmt.seq Stmt.skip
```

**Notes:**
- `ReductionChoice` has a `BEq` instance (verified: `ReductionChoice.lazy == ReductionChoice.solinasFold` evaluates to `false`).
- The `k < 64` guard exempts Goldilocks (which doesn't have the truncation bug).
- `lowerStageVerified` is unchanged — we just pass a modified stage.

### Task 2: Add `maxTempsInPlanRust` to VerifiedPlanCodeGen.lean

Insert after `maxTempsInPlan` (line 201):

```lean
/-- Temp count for Rust path (lazy→montgomery may use more temps). -/
private def maxTempsInPlanRust (plan : Plan) (k c mu : Nat) : Nat :=
  let counts := plan.stages.toList.map fun stage =>
    let rustStage := if stage.reduction == .lazy && k < 64
      then { stage with reduction := .montgomery }
      else stage
    let cgs : CodeGenState := {}
    let aVar := VarName.user "a_val"
    let bVar := VarName.user "b_val"
    let wVar := VarName.user "w_val"
    let (_, _, _, cgs') :=
      lowerDIFButterflyByReduction aVar bVar wVar rustStage.reduction plan.field k c mu cgs
    cgs'.nextVar
  counts.foldl Nat.max 0
```

This is necessary because Montgomery uses **11 temps** vs lazy's **5 temps**. If a plan has any lazy stages, the Rust version needs more `let mut tN: u64;` declarations.

### Task 3: Update `emitRustFromPlanVerified` to use Rust-specific lowering

In `emitRustFromPlanVerified` (currently line 217), change:

```lean
-- BEFORE:
let stmt := lowerNTTFromPlanVerified plan k c mu
...
let numTemps := maxTempsInPlan plan k c mu

-- AFTER:
let stmt := lowerNTTFromPlanVerifiedRust plan k c mu
...
let numTemps := maxTempsInPlanRust plan k c mu
```

Keep the existing `as u64`/`as u32` string post-processing — it is still needed for load/store casts regardless of which lowering function is used. The post-processing handles the `stmtToRust` type-agnostic emission (Issue A in v1), while the new lowering handles the semantic truncation (Issue B in v1).

### Task 4: Verify `emitCFromPlanVerified` is UNCHANGED

After all changes, confirm the C lowering function is untouched:

```lean
-- This MUST remain exactly as-is:
def emitCFromPlanVerified (plan : Plan) (k c mu : Nat) (funcName : String) : String :=
  let stmt := lowerNTTFromPlanVerified plan k c mu  -- NOT the Rust variant
  ...
```

Run C benchmarks:
```bash
lake env lean --run Bench.lean -- --pipeline ultra --field babybear --size 16 --primitive ntt --lang c
lake env lean --run Bench.lean -- --pipeline ultra --field koalabear --size 16 --primitive ntt --lang c
```

Both must pass with same performance as pre-change baselines (BabyBear 2^16: ~301μs AMO / ~478μs P3).

### Task 5: Run Rust benchmarks with correctness check

```bash
# 32-bit fields (the bug)
lake env lean --run Bench.lean -- --pipeline ultra --field babybear --size 16,20 --primitive ntt --lang rust --hardware arm-scalar
lake env lean --run Bench.lean -- --pipeline ultra --field koalabear --size 16,20 --primitive ntt --lang rust --hardware arm-neon
lake env lean --run Bench.lean -- --pipeline ultra --field mersenne31 --size 16 --primitive ntt --lang rust --hardware arm-scalar

# 64-bit field (should be unaffected)
lake env lean --run Bench.lean -- --pipeline ultra --field goldilocks --size 16 --primitive ntt --lang rust --hardware arm-scalar
```

All must: compile, pass correctness check (no MISMATCH), print benchmark results.

### Task 6: Handle radix-4 lazy stages

`lowerRadix4ButterflyByReduction` (VerifiedPlanCodeGen.lean:103-120) delegates to `lowerDIFButterflyByReduction` for non-Solinas strategies. If a radix-4 stage is lazy, the same truncation bug applies. The fix in Task 1 already handles this because `lowerNTTFromPlanVerifiedRust` replaces `.lazy` at the **stage level**, before the stage dispatches to radix-2 or radix-4 butterfly lowering. No additional changes needed, but verify by running a plan that includes radix-4 stages (these are generated by `generateCandidates` for N divisible by 4).

---

## Files Modified (Summary)

| File | Changes | Lines affected |
|---|---|---|
| `VerifiedPlanCodeGen.lean` | Add `lowerNTTFromPlanVerifiedRust`, `maxTempsInPlanRust`. Update `emitRustFromPlanVerified` to call them. | +25 new LOC, ~4 LOC changed |
| `OptimizedNTTPipeline.lean` | None needed (harness is correct) | 0 |
| `UltraPipeline.lean` | None needed (already returns triple) | 0 |
| `Bench.lean` | None needed (dispatch already works) | 0 |

**Total: ~30 LOC in 1 file.** No other files touched.

---

## Files NOT to Modify

| File/Directory | Reason |
|---|---|
| `.lake/packages/TrustLean/` | External package. Modifying breaks `lake update`. |
| `emitCFromPlanVerified` (VerifiedPlanCodeGen.lean:205-214) | C path is working and verified. Must use original `lowerNTTFromPlanVerified`. |
| `lowerStageVerified` (VerifiedPlanCodeGen.lean:143-173) | Shared by C path. Changing it affects C performance/correctness. |
| `lowerReductionChoice` (VerifiedPlanCodeGen.lean:42-57) | Used by both C and Rust. Changing `.lazy` here affects C. |
| `lowerDIFButterflyByReduction` (VerifiedPlanCodeGen.lean:66-94) | Butterfly lowering is correct. The bug is in store truncation, not butterfly math. |
| Any `.olean`-only module | No source to modify. Changing `.olean` files manually would corrupt the build. |

---

## Invariants to Preserve

1. **`emitCFromPlanVerified` calls `lowerNTTFromPlanVerified` (not the Rust variant).** C path must be identical pre- and post-fix.

2. **`lowerStageVerified`, `lowerReductionChoice`, `lowerDIFButterflyByReduction` are unchanged.** They generate correct `Stmt` IR. The fix operates at a higher level (stage strategy selection).

3. **`ultraPipeline` signature is `String × String × String`.** The triple `(cCode, rustCode, report)` was introduced in this session. Don't change it.

4. **All existing theorems compile.** The theorems in VerifiedPlanCodeGen.lean (line 248+) reference the original lowering functions. None should change.

5. **The `.olean` cache is preserved.** Do not run `lake clean`. Do not modify files that don't have `.lean` source.

6. **Correctness checks exist in both C and Rust harnesses.** The C harness (in `optimizedNTTC_ultra`) compares `amo_out[i] % p == p3_out[i] % p` before timing. The Rust harness (in `genOptimizedBenchRust_ultra`) does the same. Both must pass after the fix.

---

## Verification Commands

```bash
# 1. Build (only recompiles VerifiedPlanCodeGen + dependents)
lake build Bench

# 2. C path regression check (MUST match pre-change baselines)
lake env lean --run Bench.lean -- --pipeline ultra --field babybear,koalabear --size 16 --lang c

# 3. Rust path — the fix (MUST pass correctness check)
lake env lean --run Bench.lean -- --pipeline ultra --field babybear,koalabear --size 16 --lang rust

# 4. Rust at scale
lake env lean --run Bench.lean -- --pipeline ultra --field koalabear --size 20 --lang rust --hardware arm-neon

# 5. Legacy pipeline regression (MUST still work)
lake env lean --run Bench.lean -- --pipeline legacy --field babybear --size 16 --lang c
```

**Do NOT use `.lake/build/bin/bench`.** The 193MB binary takes >60s to initialize. Use `lake env lean --run Bench.lean -- [flags]` instead.

---

## Why NOT Other Approaches

| Approach | Problem |
|---|---|
| **Single Solinas fold** (v1 Approach A/B) | Insufficient for c > 1. BabyBear needs 8 folds (32 ops), KoalaBear needs 5 folds (20 ops). Worse than Montgomery (5 ops). |
| **Iterated Solinas fold** | Correct but expensive and variable-cost. Hard to predict temp count. |
| **Harvey reduction** | Valid range is `x < 3p ≈ 2^33`. Lazy butterfly outputs are ~2^62. Harvey cannot handle them. |
| **Wide scratch buffer** (v1 Approach C) | Correct and optimal but complex (~80 LOC). Changes function signatures, needs internal allocation or caller-provided buffer. Overkill for the current situation. Worth revisiting if the ~0.1% Montgomery overhead in lazy stages becomes measurable. |
| **Fix TrustLean's `stmtToRust`** | Would require modifying an external package. Also doesn't solve the semantic issue (truncation is inherent to narrow stores, regardless of cast syntax). |

Montgomery is the sweet spot: single-pass, proven correct for the full lazy range, minimal code change, no iteration, predictable temp count.
