import AmoLean.EGraph.Verified.Bitwise.MixedNodeOp

/-!
# CostModelDef — Parametric hardware cost model for E-graph extraction

Provides a parameterized hardware cost model (`HardwareCost`) that assigns
cycle counts to each `MixedNodeOp`. This enables the E-graph extraction
engine to select the cheapest modular reduction strategy for a given target.

## Key results

- `HardwareCost`: structure with cycle costs per operation
- Concrete instances: ARM Cortex-A76, RISC-V SiFive U74, FPGA Xilinx DSP48E2
- `mixedOpCost`: parametric cost function mapping `MixedNodeOp → Nat`
- Cost functions: `mersenneFoldCost`, `pseudoMersenneFoldCost`, `montgomeryCost`
- `mersenne_le_pseudo_mersenne`: Mersenne fold ≤ pseudo-Mersenne on all targets
- `mersenne_le_montgomery`: Mersenne fold ≤ Montgomery on all targets

## Source

ARM Cortex-A76 Software Optimization Guide (v8.0).
SiFive U74 Core Complex Manual (21G1).
Xilinx UG579 UltraScale DSP48E2 User Guide.
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified (EClassId)

/-! ## Hardware cost model -/

/-- Hardware cost model for modular arithmetic operations.
    Each field represents the latency in cycles for the corresponding
    primitive operation on a specific microarchitecture.
    Used by E-graph extraction to select optimal reduction strategy. -/
structure HardwareCost where
  mul32  : Nat    -- 32-bit multiply (cycles)
  mul64  : Nat    -- 64-bit multiply (cycles)
  add    : Nat    -- addition (cycles)
  sub    : Nat    -- subtraction (cycles)
  shift  : Nat    -- shift left/right (cycles)
  bitAnd : Nat    -- bitwise AND (cycles)
  bitXor : Nat    -- bitwise XOR (cycles)
  bitOr  : Nat    -- bitwise OR (cycles)
  -- v4.0: fused instruction costs
  fusedShiftSub : Nat := 2  -- ARM barrel shifter: SUB rd, xn, xm, LSL #k (1 on ARM, 2 on RISC-V)
  fusedMulAdd : Nat := 4    -- fused multiply-accumulate: MADD (ARM), MUL+ADD (others)
  condSub : Nat := 1        -- conditional subtraction for Harvey butterfly
  modReduce : Nat := 1      -- cost of a modular reduction (conditional sub or mask+shift)
  -- v4.1: SIMD-aware cost model
  -- When isSimd = true, operations that require widening (u32 → u64 intermediates)
  -- are penalized. This makes the e-graph prefer Montgomery (u32 lanes) over
  -- Solinas fold (needs u64) in SIMD contexts, and vice versa for scalar.
  isSimd : Bool := false     -- true when targeting SIMD (NEON/AVX2)
  wideningPenalty : Nat := 0 -- extra cycles for ops that need u32→u64 widening
  simdLanes : Nat := 1       -- 1 = scalar, 4 = NEON, 8 = AVX2
  -- v4.2: vector-length-aware cost model
  -- When processing large arrays, u64 operations cause cache pressure
  -- (8 bytes/elem vs 4 bytes for u32). Operations that stay in u32
  -- (Montgomery) are cheaper at scale than u64 operations (Solinas fold).
  -- cachePenalty is added to u64-needing ops when vectorLength > cacheThreshold.
  vectorLength : Nat := 0       -- 0 = single op, >0 = array of this many elements
  cacheThreshold : Nat := 8192  -- above this, cache effects dominate (~32KB = L1/2)
  cachePenalty : Nat := 0       -- extra cycles per op when array exceeds threshold
  -- v4.3: branch-aware cost for combined mul+add patterns
  -- In serial patterns (FRI fold, dot product), each conditional subtract is
  -- a branch. Extra branches add pipeline stall cost beyond the ALU op.
  -- Solinas output < 2p → 2 cond subs. Montgomery output < p → 1 cond sub.
  branchPenalty : Nat := 0      -- extra cost per branch in serial reduction patterns
  deriving Repr, DecidableEq

/-! ## Concrete hardware targets -/

/-- ARM Cortex-A76 cost model (from optimization guide v8.0).
    ARM has a barrel shifter: SUB rd, xn, xm, LSL #k is 1 instruction/1 cycle. -/
def arm_cortex_a76 : HardwareCost :=
  { mul32 := 3, mul64 := 5, add := 1, sub := 1,
    shift := 1, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 1, fusedMulAdd := 3, condSub := 1, modReduce := 1,
    branchPenalty := 1, cachePenalty := 2 }

/-- RISC-V SiFive U74 cost model (from core complex manual 21G1).
    No barrel shifter — shift+sub = 2 separate instructions. -/
def riscv_sifive_u74 : HardwareCost :=
  { mul32 := 5, mul64 := 5, add := 1, sub := 1,
    shift := 1, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 2, fusedMulAdd := 6, condSub := 1, modReduce := 1 }

/-- FPGA Xilinx DSP48E2 cost model (DSP-based multiply, free shifts). -/
def fpga_dsp48e2 : HardwareCost :=
  { mul32 := 1, mul64 := 3, add := 1, sub := 1,
    shift := 0, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 1, fusedMulAdd := 2, condSub := 1, modReduce := 1 }

/-- x86 Intel Skylake cost model. MULX = 4 cycles, ADD = 1. -/
def x86_skylake : HardwareCost :=
  { mul32 := 3, mul64 := 4, add := 1, sub := 1,
    shift := 1, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 2, fusedMulAdd := 4, condSub := 1, modReduce := 1 }

/-! ## SIMD hardware targets

When `isSimd = true`, the cost model penalizes operations that need
u32→u64 widening. This makes the e-graph automatically prefer:
  - Montgomery REDC for SIMD (stays in u32 lanes → no penalty)
  - Solinas fold for scalar (fewer ops, but needs u64 → penalized in SIMD)

The `wideningPenalty` represents the cost of extracting u64 lanes,
doing scalar operations, and repacking — which we measured as
15-20% overhead in bench_ntt_simd.c. -/

/-- ARM NEON SIMD cost model (4 × u32 lanes).
    Montgomery stays in u32 (vqdmulhq_s32) → no penalty.
    Solinas fold needs u64 intermediate → +8 cycle penalty. -/
def arm_neon_simd : HardwareCost :=
  { mul32 := 3, mul64 := 5, add := 1, sub := 1,
    shift := 1, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 1, fusedMulAdd := 3, condSub := 1, modReduce := 1,
    isSimd := true, wideningPenalty := 8, simdLanes := 4 }

/-- x86 AVX2 SIMD cost model (8 × u32 lanes).
    Same principle: Montgomery (vpmuludq) stays in lanes, Solinas needs widening. -/
def x86_avx2_simd : HardwareCost :=
  { mul32 := 3, mul64 := 4, add := 1, sub := 1,
    shift := 1, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 2, fusedMulAdd := 4, condSub := 1, modReduce := 1,
    isSimd := true, wideningPenalty := 8, simdLanes := 8 }

/-! ## Vector-context cost models

When the e-graph optimizes a primitive that operates on a large array
(FRI fold over N=65536, dot product, NTT), the cache effects of u64 vs u32
dominate. These cost models add a cache penalty for u64-needing operations
when the vector is large enough to exceed L1 cache. -/

/-- ARM scalar for large vectors (N > 8192).
    Same as arm_cortex_a76 but with cache penalty for u64 ops.
    Makes the e-graph prefer Montgomery (u32) over Solinas (u64)
    for large-array primitives like FRI fold and dot product. -/
def arm_scalar_vector (n : Nat) : HardwareCost :=
  { mul32 := 3, mul64 := 5, add := 1, sub := 1,
    shift := 1, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 1, fusedMulAdd := 3, condSub := 1, modReduce := 1,
    vectorLength := n, cacheThreshold := 8192, cachePenalty := 8,
    branchPenalty := 1 }

/-- ARM NEON for large vectors — combines SIMD + cache penalties. -/
def arm_neon_vector (n : Nat) : HardwareCost :=
  { mul32 := 3, mul64 := 5, add := 1, sub := 1,
    shift := 1, bitAnd := 1, bitXor := 1, bitOr := 1,
    fusedShiftSub := 1, fusedMulAdd := 3, condSub := 1, modReduce := 1,
    isSimd := true, wideningPenalty := 8, simdLanes := 4,
    vectorLength := n, cacheThreshold := 8192, cachePenalty := 8 }

/-! ## Parametric cost function -/

/-- Extra cost for operations needing u64 intermediates.
    Combines SIMD widening penalty + cache pressure penalty. -/
private def u64Penalty (hw : HardwareCost) : Nat :=
  let simdPen := if hw.isSimd then hw.wideningPenalty else 0
  let cachePen := if hw.vectorLength > hw.cacheThreshold then hw.cachePenalty else 0
  simdPen + cachePen

/-- Parametric cost function: assigns hardware cycle cost to each `MixedNodeOp`.
    Constants and witnesses are free (no ALU operation).
    Operations needing u64 intermediates (Solinas fold, Barrett, mulGate) are
    penalized when: (1) isSimd=true (widening penalty), or (2) vectorLength
    exceeds cacheThreshold (cache pressure penalty). This makes the e-graph
    prefer Montgomery (u32 only) over Solinas (u64 intermediate) for both
    SIMD contexts and large-array contexts. -/
def mixedOpCost (hw : HardwareCost) : MixedNodeOp → Nat
  | .constGate _    => 0
  | .witness _      => 0
  | .pubInput _     => 0
  | .addGate _ _    => hw.add
  | .mulGate _ _    => hw.mul32 + u64Penalty hw
  | .negGate _      => 0
  | .smulGate _ _   => hw.mul32
  | .shiftLeft _ _  => hw.shift
  | .shiftRight _ _ => hw.shift
  | .bitAnd _ _     => hw.bitAnd
  | .bitXor _ _     => hw.bitXor
  | .bitOr _ _      => hw.bitOr
  | .constMask _    => 0
  | .subGate _ _    => hw.sub
  | .reduceGate _ _   => hw.shift + hw.mul32 + hw.bitAnd + hw.add + u64Penalty hw
      -- Solinas fold actual cost: shift + mul(c) + mask + add + u64 penalty
  | .kronPack _ _ _   => 0
  | .kronUnpackLo _ _ => hw.shift
  | .kronUnpackHi _ _ => hw.shift
  -- Modular reduction alternatives
  | .montyReduce _ _ _   => hw.bitAnd + hw.mul32 + hw.add + hw.shift + hw.sub
      -- Montgomery: 5 ops, all u32 lanes → NO widening penalty
  | .barrettReduce _ _ _ => hw.mul32 + hw.shift + hw.mul32 + hw.sub + hw.sub + hw.add +
      u64Penalty hw
      -- Barrett: 6 ops + u64 penalty (SIMD + cache)
  | .harveyReduce _ _    => hw.sub + hw.sub + hw.add
      -- Harvey: 3 ops, u32 conditional subs → no widening
  | .conditionalSub _ _  => hw.condSub
      -- Conditional subtract: 1 compare + 1 sub (selected when boundK ≤ 2)
  -- v3.20.b B2 (§14.13.2) — SIMD pack ops. packedLoad/Store are single NEON
  -- memory ops (vld1q_s32/vst1q_s32), 1 cycle on M1. Model uniformly as
  -- `hw.add` magnitude (conservative, ALU-comparable; cache pressure lives
  -- in u64Penalty/cacheThreshold, not per-op). packedButterflyNeonDIT amortizes
  -- 4 scalar butterflies into one NEON latency chain: ~1 mul32 + 1 add in
  -- latency terms (throughput is 4×). This keeps extraction preferring packed
  -- over 4-scalar sequences in cache-aware regimes without over-weighting.
  | .packedLoadNeon _              => hw.add
  | .packedStoreNeon _ _           => hw.add
  | .packedButterflyNeonDIT _ _ _  => hw.mul32 + hw.add

/-! ## Combined mul+add cost (branch-aware selection)

For primitives with the pattern `reduce(a + reduce(x * y))` (FRI fold, dot product,
polynomial evaluation), the cost of the add reduction depends on the output bound
of the mul reduction:
  - Solinas fold output ∈ [0, 2p) → add needs 2 conditional subtracts (2 branches)
  - Montgomery output ∈ [0, p)  → add needs 1 conditional subtract (1 branch)

`selectMulAddReduction` consults the cost model to pick the cheapest combination,
accounting for branch penalty in serial patterns. -/

/-- Combined cost of mul-reduce + add-reduce, considering output bounds.
    Returns (mul_reduction_cost, total_combined_cost). -/
def combinedMulAddCost (hw : HardwareCost) (useSolinas : Bool) : Nat :=
  if useSolinas then
    -- Solinas: cheaper mul, but output < 2p → 2 conditional subs for add
    let mulCost := mixedOpCost hw (.reduceGate 0 0)
    let addCost := 2 * (hw.condSub + hw.branchPenalty)
    mulCost + addCost
  else
    -- Montgomery: costlier mul, but output < p → 1 conditional sub for add
    let mulCost := mixedOpCost hw (.montyReduce 0 0 0)
    let addCost := 1 * (hw.condSub + hw.branchPenalty)
    mulCost + addCost

/-- Select the best mul reduction for combined mul+add patterns.
    Returns true if Solinas wins, false if Montgomery wins.
    This is a cost-model query, not a hardcoded decision. -/
def solinasWinsForMulAdd (hw : HardwareCost) : Bool :=
  combinedMulAddCost hw true ≤ combinedMulAddCost hw false

/-- Non-vacuity: ARM scalar, Solinas+2br (10) vs Montgomery+1br (9).
    Montgomery wins by 1 cycle due to branchPenalty. -/
example : combinedMulAddCost arm_cortex_a76 true = 10 := by native_decide
example : combinedMulAddCost arm_cortex_a76 false = 9 := by native_decide
example : solinasWinsForMulAdd arm_cortex_a76 = false := by native_decide

/-! ## Zero-cost theorems -/

/-- Constants are free: no ALU operation needed. -/
theorem mixedOpCost_const_zero (hw : HardwareCost) (n : Nat) :
    mixedOpCost hw (.constGate n) = 0 := rfl

/-- Witnesses are free: no ALU operation needed. -/
theorem mixedOpCost_witness_zero (hw : HardwareCost) (n : Nat) :
    mixedOpCost hw (.witness n) = 0 := rfl

/-- Constant masks are free: materialized as immediates. -/
theorem mixedOpCost_constMask_zero (hw : HardwareCost) (n : Nat) :
    mixedOpCost hw (.constMask n) = 0 := rfl

/-- Shifts are cheaper than or equal to multiplies on all realistic targets.
    This justifies rewriting `x * 2^n` to `x <<< n` during E-graph extraction. -/
theorem mixedOpCost_shift_le_mul (hw : HardwareCost) (h : hw.shift ≤ hw.mul32)
    (a : EClassId) (n : Nat) (b : EClassId) :
    mixedOpCost hw (.shiftLeft a n) ≤ mixedOpCost hw (.mulGate a b) := by
  simp [mixedOpCost]
  omega

/-! ## Reduction strategy cost functions -/

/-- Cost of a Mersenne fold step: shift + AND + add (3 ops, no multiply). -/
def mersenneFoldCost (hw : HardwareCost) : Nat :=
  hw.shift + hw.bitAnd + hw.add

/-- Cost of a pseudo-Mersenne fold step: shift + AND + mul32 + add (4 ops). -/
def pseudoMersenneFoldCost (hw : HardwareCost) : Nat :=
  hw.shift + hw.bitAnd + hw.mul32 + hw.add

/-- Cost of Montgomery reduction (REDC): AND + mul32 + add + shift + sub (5 ops). -/
def montgomeryCost (hw : HardwareCost) : Nat :=
  hw.bitAnd + hw.mul32 + hw.add + hw.shift + hw.sub

/-- Cost of Barrett reduction: mul64 + shift + mul32 + sub + conditional sub + add (6 ops). -/
def barrettCost (hw : HardwareCost) : Nat :=
  hw.mul32 + hw.shift + hw.mul32 + hw.sub + hw.sub + hw.add

/-- Cost of Harvey conditional subtraction: 2 comparisons + 1-2 conditional subs (3 ops). -/
def harveyCost (hw : HardwareCost) : Nat :=
  hw.sub + hw.sub + hw.add

/-! ## Cost comparison theorems -/

/-- Mersenne fold is cheaper than pseudo-Mersenne on all targets.
    Mersenne avoids the multiply by constant c entirely. -/
theorem mersenne_le_pseudo_mersenne (hw : HardwareCost) :
    mersenneFoldCost hw ≤ pseudoMersenneFoldCost hw := by
  unfold mersenneFoldCost pseudoMersenneFoldCost
  omega

/-- Mersenne fold is cheaper than Montgomery on all targets.
    Montgomery requires an extra multiply and subtraction. -/
theorem mersenne_le_montgomery (hw : HardwareCost) :
    mersenneFoldCost hw ≤ montgomeryCost hw := by
  unfold mersenneFoldCost montgomeryCost
  omega

/-- Pseudo-Mersenne fold is cheaper than Montgomery on all targets.
    Montgomery requires an extra subtraction step. -/
theorem pseudo_mersenne_le_montgomery (hw : HardwareCost) :
    pseudoMersenneFoldCost hw ≤ montgomeryCost hw := by
  unfold pseudoMersenneFoldCost montgomeryCost
  omega

/-! ## Non-vacuity examples -/

/-- Non-vacuity: ARM Cortex-A76 Mersenne fold costs 3 cycles. -/
example : mersenneFoldCost arm_cortex_a76 = 3 := by native_decide

/-- Non-vacuity: ARM Cortex-A76 pseudo-Mersenne fold costs 5 cycles. -/
example : pseudoMersenneFoldCost arm_cortex_a76 = 6 := by native_decide

/-- Non-vacuity: ARM Cortex-A76 Montgomery costs 6 cycles. -/
example : montgomeryCost arm_cortex_a76 = 7 := by native_decide

/-- Non-vacuity: FPGA shift is free, so Mersenne fold costs only 2 cycles. -/
example : mersenneFoldCost fpga_dsp48e2 = 2 := by native_decide

/-- Non-vacuity: RISC-V multiply is 3 cycles, making Montgomery cost 7. -/
example : montgomeryCost riscv_sifive_u74 = 9 := by native_decide

/-- Non-vacuity: shift_le_mul hypothesis is satisfiable on all three targets. -/
example : arm_cortex_a76.shift ≤ arm_cortex_a76.mul32 := by native_decide
example : riscv_sifive_u74.shift ≤ riscv_sifive_u74.mul32 := by native_decide

/-! ## SIMD cost model — cross-context strategy selection

The key property: in SIMD mode, Montgomery becomes cheaper than Solinas fold
because Solinas fold needs u64 intermediates (penalized by wideningPenalty).
In scalar mode, Solinas fold is cheaper because it has fewer ops.

This means the e-graph, given the same `reduceGate(x, p)`, will extract:
  - `solinasFold` when hw.isSimd = false (cheaper: 4 ops, no penalty)
  - `montyReduce` when hw.isSimd = true  (cheaper: 5 ops but no penalty vs 4+8 penalty)
-/

/-- In SIMD mode (NEON), reduceGate (Solinas fold) costs more than Montgomery.
    This is because Solinas fold gets penalized for u64 widening.
    The e-graph will therefore prefer montyReduce in SIMD context. -/
example : mixedOpCost arm_neon_simd (.reduceGate 0 0) >
          mixedOpCost arm_neon_simd (.montyReduce 0 0 0) := by native_decide

/-- In scalar mode (ARM), reduceGate (Solinas fold) costs less than Montgomery.
    The e-graph will therefore prefer reduceGate (→ Solinas fold) in scalar context. -/
example : mixedOpCost arm_cortex_a76 (.reduceGate 0 0) <
          mixedOpCost arm_cortex_a76 (.montyReduce 0 0 0) := by native_decide

/-- Harvey is cheapest in both contexts (3 ops, no widening). -/
example : mixedOpCost arm_neon_simd (.harveyReduce 0 0) <
          mixedOpCost arm_neon_simd (.montyReduce 0 0 0) := by native_decide
example : mixedOpCost arm_cortex_a76 (.harveyReduce 0 0) <
          mixedOpCost arm_cortex_a76 (.montyReduce 0 0 0) := by native_decide
example : fpga_dsp48e2.shift ≤ fpga_dsp48e2.mul32 := by native_decide

/-! ## Vector-length-aware cost — cache penalty

For single operations, Solinas fold wins (fewer ops).
For large vectors (N > 8192), Montgomery wins (u32 = half cache footprint).
The e-graph automatically switches strategy based on vector context. -/

/-- Scalar single-op: Solinas fold is cheaper (no cache penalty). -/
example : mixedOpCost arm_cortex_a76 (.reduceGate 0 0) <
          mixedOpCost arm_cortex_a76 (.montyReduce 0 0 0) := by native_decide

/-- Scalar large-vector (N=65536): Montgomery is cheaper (cache penalty on Solinas). -/
example : mixedOpCost (arm_scalar_vector 65536) (.reduceGate 0 0) >
          mixedOpCost (arm_scalar_vector 65536) (.montyReduce 0 0 0) := by native_decide

/-- Scalar small-vector (N=1024): Solinas still wins (below cache threshold). -/
example : mixedOpCost (arm_scalar_vector 1024) (.reduceGate 0 0) <
          mixedOpCost (arm_scalar_vector 1024) (.montyReduce 0 0 0) := by native_decide

/-- Non-vacuity: mixedOpCost produces non-trivial values on ARM. -/
example : mixedOpCost arm_cortex_a76 (.mulGate 0 1) = 3 := by native_decide
example : mixedOpCost arm_cortex_a76 (.addGate 0 1) = 1 := by native_decide
example : mixedOpCost arm_cortex_a76 (.shiftLeft 0 5) = 1 := by native_decide

/-! ## Smoke tests -/

#eval s!"ARM Cortex-A76: Mersenne={mersenneFoldCost arm_cortex_a76}, \
  PseudoMersenne={pseudoMersenneFoldCost arm_cortex_a76}, \
  Montgomery={montgomeryCost arm_cortex_a76}"

#eval s!"RISC-V U74:     Mersenne={mersenneFoldCost riscv_sifive_u74}, \
  PseudoMersenne={pseudoMersenneFoldCost riscv_sifive_u74}, \
  Montgomery={montgomeryCost riscv_sifive_u74}"

#eval s!"FPGA DSP48E2:   Mersenne={mersenneFoldCost fpga_dsp48e2}, \
  PseudoMersenne={pseudoMersenneFoldCost fpga_dsp48e2}, \
  Montgomery={montgomeryCost fpga_dsp48e2}"

#eval s!"Cost savings: ARM mul→shift saves {mixedOpCost arm_cortex_a76 (.mulGate 0 1) - mixedOpCost arm_cortex_a76 (.shiftLeft 0 5)} cycles"

end AmoLean.EGraph.Verified.Bitwise
