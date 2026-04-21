/-
  AmoLean.EGraph.Verified.Bitwise.MemLayout — v3.20.b B3 (N20.3.1)

  Memory layout transformations for batch NTT codegen. The packed NEON
  butterfly kernel (`emitPackedButterflyNeonDIT_C` in SIMDEmitter.lean)
  requires data interleaved ACROSS polynomials at the same NTT index:

    linear:      [p0_0, p0_1, ..., p0_{N-1}, p1_0, p1_1, ..., pW-1_{N-1}]
    interleaved: [p0_0, p1_0, ..., pW-1_0, p0_1, p1_1, ..., pW-1_1, ...]

  where `W = Plan.batchWidth` (typically 4 for NEON WIDTH=4 BabyBear) and
  `N = Plan.size`. With interleaved layout, a single `vld1q_s32(&data[i*W])`
  loads one element from each of W polynomials into one NEON register,
  enabling cross-polynomial parallelism per butterfly.

  This module provides the Nat-level transpose/untranspose functions plus
  the key invertibility theorem `transposeForBatch_inv` that downstream
  bridge proofs (`lowerNTTFromPlanBatch_correct` in B5) reduce to.

  Per §14.13.2 Gap 2 decision + §14.13.7 R2 mitigation: the invertibility
  theorem is the FORMAL witness that the batch NTT output matches the
  scalar NTT output for each polynomial (since `untranspose ∘ batch_NTT ∘
  transpose = W × scalar_NTT`). Proven fully in B3 (v3.20.b, 2026-04-20)
  via `List.ext_getElem` + `Nat.mul_add_mod_of_lt` / `Nat.add_mul_div_left`
  / `Nat.div_add_mod` cancellation — no remaining `sorry`. Combined with a
  runtime golden test (in B6) this closes §14.13.7 R2.

  Trust boundary note: these are pure Lean (Nat)-level List operations,
  no `Stmt.call`, no NEON intrinsics. The analogous C-level transpose
  preamble (emitted in B4 `emitCFromPlanBatch`) is a SEPARATE piece of
  code; its correctness is asserted by the differential fuzz gate in B6
  (+ the fact that it's mechanically mirrored from this Lean definition).
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD

namespace AmoLean.EGraph.Verified.Bitwise.MemLayout

/-! ## Index manipulation

    Core identity: a linear index `k ∈ [0, N*W)` decomposes uniquely into
    `(poly, pos)` where `poly ∈ [0, W)` and `pos ∈ [0, N)`.

    Linear layout (scalar-friendly):   `k = poly * N + pos`
    Interleaved layout (SIMD-friendly): `k = pos * W + poly`

    `transposeForBatch` maps linear → interleaved by `k_lin → (pos * W + poly)`
    where `(poly, pos)` are the linear decomposition of `k_lin`.

    `untransposeFromBatch` maps interleaved → linear by the inverse.
-/

/-- Read the element at linear index `k` from the linear layout, write it
    at interleaved index `(pos * W + poly)`. Precondition: `data.length ≥ N * W`. -/
def transposeForBatch (data : List Nat) (N W : Nat) : List Nat :=
  (List.range (N * W)).map fun k =>
    -- Interleaved index: the k-th output position holds element from
    -- linear index (k % W) * N + (k / W).
    --   At k = 0:   poly=0, pos=0 → linear (0*N + 0) = 0
    --   At k = 1:   poly=1, pos=0 → linear (1*N + 0) = N
    --   At k = W:   poly=0, pos=1 → linear (0*N + 1) = 1
    --   At k = W*N-1: poly=W-1, pos=N-1 → linear ((W-1)*N + N-1)
    let poly := k % W
    let pos  := k / W
    data.getD (poly * N + pos) 0

/-- Inverse of `transposeForBatch`. Maps interleaved → linear.
    Read interleaved index `(pos * W + poly)` from the input, write it at
    linear index `(poly * N + pos)`. -/
def untransposeFromBatch (data : List Nat) (N W : Nat) : List Nat :=
  (List.range (N * W)).map fun k =>
    -- Linear index: the k-th output position holds element from
    -- interleaved index (k / N) at position (k % N), i.e. (k % N) * W + (k / N).
    let poly := k / N
    let pos  := k % N
    data.getD (pos * W + poly) 0

/-! ## Invertibility

    Core theorem: `untransposeFromBatch ∘ transposeForBatch = id` on
    length-(N*W) lists. This is the lemma that `lowerNTTFromPlanBatch_correct`
    (B5) reduces the "batch output recovers per-poly output" claim to. -/

/-- v3.20.b B3 invertibility theorem (proven 2026-04-20, no `sorry`): the
    composition `untransposeFromBatch ∘ transposeForBatch` is the identity on
    length-(N*W) lists.

    Proof strategy: `List.ext_getElem` reduces to length equality (trivial via
    `simp`) + element-wise equality. Case-split on N and W: if either is 0 the
    range is empty and we're done. In the main case (N, W > 0), for `k < N*W`
    with `poly = k/N` and `pos = k%N`:
    - `poly < W` via `Nat.div_lt_iff_lt_mul`
    - `pos * W + poly < N * W` (bounded-index lemma `idx_bound` below)
    - The inner `transposeForBatch` read returns `data.getD (poly * N + pos) 0`
      because `(pos*W + poly) % W = poly` (via `Nat.mul_add_mod_of_lt`) and
      `(pos*W + poly) / W = pos` (via `Nat.add_mul_div_left` + `Nat.div_eq_of_lt`).
    - `poly * N + pos = (k/N)*N + k%N = k` by `Nat.div_add_mod` + `Nat.mul_comm`.
    - Finally `data.getD k 0 = data[k]` via `List.getD_eq_getElem` since
      `k < data.length = N*W`.

    Downstream (B5 bridge theorem) consumes this as a rewrite lemma. -/
private lemma idx_bound (N W k : Nat) (hN : 0 < N) (h : k < N * W) :
    (k % N) * W + (k / N) < N * W := by
  have hdN : k / N < W :=
    (Nat.div_lt_iff_lt_mul hN).mpr (by rw [Nat.mul_comm]; exact h)
  have hmN : k % N < N := Nat.mod_lt k hN
  have hsucc : k % N + 1 ≤ N := by omega
  have hbound : (k % N + 1) * W ≤ N * W := Nat.mul_le_mul_right W hsucc
  rw [Nat.add_one_mul] at hbound
  omega

theorem transposeForBatch_inv (data : List Nat) (N W : Nat)
    (hlen : data.length = N * W) :
    untransposeFromBatch (transposeForBatch data N W) N W = data := by
  apply List.ext_getElem
  · simp [untransposeFromBatch, transposeForBatch, hlen]
  intro k h1 _
  simp only [untransposeFromBatch, List.getElem_map, List.getElem_range,
             List.length_map, List.length_range] at h1 ⊢
  -- Case N = 0: range is empty, no k possible
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp at h1
  -- Case W = 0: range is empty, no k possible
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp at h1
  -- Main case: N > 0 ∧ W > 0
  have hdN : k / N < W :=
    (Nat.div_lt_iff_lt_mul hN).mpr (by rw [Nat.mul_comm]; exact h1)
  have hidx : (k % N) * W + (k / N) < N * W := idx_bound N W k hN h1
  have htrans_len : (transposeForBatch data N W).length = N * W := by
    simp [transposeForBatch]
  have hidx' : (k % N) * W + (k / N) < (transposeForBatch data N W).length :=
    htrans_len ▸ hidx
  rw [List.getD_eq_getElem _ 0 hidx']
  simp only [transposeForBatch, List.getElem_map, List.getElem_range]
  -- Index algebra: ((k%N)*W + k/N) % W = k/N
  have emod : ((k % N) * W + k / N) % W = k / N :=
    Nat.mul_add_mod_of_lt hdN
  -- Index algebra: ((k%N)*W + k/N) / W = k%N
  have ediv : ((k % N) * W + k / N) / W = k % N := by
    rw [Nat.mul_comm (k % N) W, Nat.add_comm]
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hdN, Nat.zero_add]
  rw [emod, ediv]
  -- Now goal: data.getD ((k/N) * N + k%N) 0 = data[k]
  have ek : (k / N) * N + k % N = k := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod k N
  rw [ek]
  have hk_data : k < data.length := hlen ▸ h1
  exact List.getD_eq_getElem _ _ hk_data

/-! ## Non-vacuity examples

    Two concrete instances demonstrate the invertibility holds (tested at
    runtime via #eval / native_decide), satisfying the CLAUDE.md global hygiene
    rule that theorems with ≥3 hypotheses have `example` witnesses. -/

/-- Non-vacuity W=1: batch of 1 polynomial is the identity transform. -/
example : transposeForBatch [10, 20, 30] 3 1 = [10, 20, 30] := by
  unfold transposeForBatch
  rfl

/-- Non-vacuity W=2, N=2: 4 elements laid out as 2 polys × 2 positions.
    Linear:      [p0_0, p0_1, p1_0, p1_1] = [10, 20, 30, 40]
    Interleaved: [p0_0, p1_0, p0_1, p1_1] = [10, 30, 20, 40]. -/
example : transposeForBatch [10, 20, 30, 40] 2 2 = [10, 30, 20, 40] := by
  unfold transposeForBatch
  rfl

/-- Non-vacuity: composing transpose ∘ untranspose on a concrete 2×2 instance
    recovers the input. This is the runtime witness for `transposeForBatch_inv`
    pending the Phase 2 formal proof. -/
example : untransposeFromBatch (transposeForBatch [10, 20, 30, 40] 2 2) 2 2
    = [10, 20, 30, 40] := by
  unfold transposeForBatch untransposeFromBatch
  rfl

/-! ## Batch-aware bit-reversal (v3.20.b B3.5 N20.35.2)

    `bitrev_strided(data, N, B)` is the stride-`B` bit-reverse permutation
    on data of length `N*B` in interleaved batch layout (`data[i*B+p] =
    poly[p][i]`). Used by the v3.20.b fused-bitrev packed kernel — the C
    implementation via `__builtin_bitreverse32` + stride-`B` swaps is what
    replaces the separate `bit_reverse_permute` preamble call.

    The **B=1 collapse** is the pre-condition for Gate H8 single-vector
    benchmarking: when `B=1`, `bitrev_strided` must reduce EXACTLY to the
    scalar bit-reverse permutation that the existing pipeline uses — so the
    measured speedup comes from FUSION (eliminated memory pass), not from
    an accidentally-different permutation algorithm.
-/

/-- Bit-reversal of `i` as a `logn`-bit number. Fold over the `logn` bit
    positions: at each bit `b`, shift `acc` left by 1 and OR in bit `b` of `i`.

    Spec-level definition: the runtime C code uses `__builtin_bitreverse32`
    (→ ARM64 RBIT) for speed; this Lean version is what correctness proofs
    reduce to. Both produce the same result for `i < 2^logn`. -/
def bitrevIdx (i logn : Nat) : Nat :=
  (List.range logn).foldl (fun acc b => (acc <<< 1) ||| ((i >>> b) &&& 1)) 0

/-- Stride-`B` bit-reverse permutation on interleaved batch data.

    Given `data` of length `N * B` with layout `data[i*B + p] = poly[p][i]`
    (see `transposeForBatch` for how this layout is produced), produce the
    list where each B-chunk at position `i` is moved to position
    `bitrevIdx(i, log2 N)`.

    Equivalently: B independent bitrevs applied to the per-poly views of the
    interleaved data, but executed as a SINGLE pass over the B-chunks (no
    explicit transpose/untranspose).

    **B=1 collapse**: `bitrev_strided data N 1` is the scalar bit-reverse
    permutation (see `bitrev_strided_B1_collapse` below).

    **B≥2**: each B-chunk is a NEON vector worth of data (for B=4, s32 → 16
    bytes = one `vld1q_s32`/`vst1q_s32`). The scatter-swap moves B contiguous
    elements at a time, giving linear scaling in B. -/
def bitrev_strided (data : List Nat) (N B : Nat) : List Nat :=
  let logn := Nat.log2 N
  (List.range (N * B)).map fun k =>
    let i := k / B
    let p := k % B
    let iBr := bitrevIdx i logn
    data.getD (iBr * B + p) 0

/-- Length preservation: the output has length `N * B`, same as input
    (assuming `data.length = N * B`). Trivial from `List.range.map`. -/
theorem bitrev_strided_length (data : List Nat) (N B : Nat) :
    (bitrev_strided data N B).length = N * B := by
  simp [bitrev_strided]

/-- B=1 collapse: when `B=1`, `bitrev_strided` reduces to scalar bit-reversal
    applied to linear indices — exactly the permutation that the existing
    `bit_reverse_permute` preamble computes.

    This is the PRE-CONDITION for Gate H8 single-vector benchmarking: at
    `batchWidth=1` the strided kernel must produce byte-equivalent output to
    the non-batch path, so measured speedup comes from fusion alone. -/
theorem bitrev_strided_B1_collapse (data : List Nat) (N : Nat) :
    bitrev_strided data N 1 =
    (List.range N).map (fun k => data.getD (bitrevIdx k (Nat.log2 N)) 0) := by
  unfold bitrev_strided
  simp only [Nat.mul_one, Nat.div_one, Nat.mod_one, Nat.add_zero]

/-! ### Non-vacuity: bitrev_strided concrete examples -/

/-- Non-vacuity B=1 N=4: scalar bitrev. Indices [0,1,2,3] bitrev → [0,2,1,3].
    So `[10,20,30,40]` becomes `[data[0], data[2], data[1], data[3]] = [10,30,20,40]`. -/
example : bitrev_strided [10, 20, 30, 40] 4 1 = [10, 30, 20, 40] := by
  unfold bitrev_strided bitrevIdx
  rfl

/-- Non-vacuity B=2 N=4: stride-2 bitrev. Input is 8 elements interleaved as
    `[poly[0][0], poly[1][0], poly[0][1], poly[1][1], ...]`. After strided
    bitrev, position 0 (chunk [10,20]) stays, position 1 (chunk [30,40])
    swaps with position 2 (chunk [50,60]), position 3 (chunk [70,80]) stays. -/
example : bitrev_strided [10, 20, 30, 40, 50, 60, 70, 80] 4 2 =
    [10, 20, 50, 60, 30, 40, 70, 80] := by
  unfold bitrev_strided bitrevIdx
  rfl

end AmoLean.EGraph.Verified.Bitwise.MemLayout
