import AmoLean.EGraph.Verified.Bitwise.CostModelDef
import AmoLean.EGraph.Verified.Bitwise.MixedExtract

/-!
# EnhancedCostModel — Register pressure and SIMD-aware cost model

Extends `HardwareCost` with register file size, spill costs, and SIMD lane
widths. This enables E-graph extraction to account for register pressure
when selecting optimal expressions for a given microarchitecture.

## Key results

- `EnhancedHardwareCost`: structure extending `HardwareCost` with GPR/SIMD fields
- `tempCount`: max simultaneously live temporaries in a `MixedExpr` tree
- `spillPenalty`: additional cost when register demand exceeds availability
- `enhancedCost`: total cost = operation cost + spill penalty
- `enhanced_ge_basic`: enhanced cost is always ≥ basic operation cost
- `spillPenalty_zero_sufficient_regs`: no spill penalty when registers suffice
- `tempCount_leaf_zero`: leaf nodes require zero temporaries
- `enhanced_cost_monotone_gpr`: more GPRs → lower or equal enhanced cost
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)

/-! ## Enhanced hardware cost model -/

/-- Hardware cost model extended with register pressure and SIMD parameters.
    - `availableGPR`: general-purpose registers (ARM=31, RISC-V=31, x86=16)
    - `spillCost`: cycles per register spill to L1 stack (~4 cycles typical)
    - `simdWidth`: SIMD lanes (AVX2=8, NEON=4, none=1)
    - `simdMulCost`: cost of a packed SIMD multiply -/
structure EnhancedHardwareCost where
  base         : HardwareCost
  availableGPR : Nat
  spillCost    : Nat
  simdWidth    : Nat
  simdMulCost  : Nat
  deriving Repr, DecidableEq

/-! ## Concrete enhanced instances -/

/-- ARM Cortex-A76 with NEON (4-lane SIMD, 31 GPRs). -/
def enhanced_arm_a76 : EnhancedHardwareCost :=
  { base := arm_cortex_a76, availableGPR := 31, spillCost := 4,
    simdWidth := 4, simdMulCost := 2 }

/-- RISC-V SiFive U74 (31 GPRs, no SIMD — simdWidth=1). -/
def enhanced_riscv_u74 : EnhancedHardwareCost :=
  { base := riscv_sifive_u74, availableGPR := 31, spillCost := 3,
    simdWidth := 1, simdMulCost := 3 }

/-- FPGA Xilinx DSP48E2 (64 "registers" via flip-flops, no SIMD). -/
def enhanced_fpga : EnhancedHardwareCost :=
  { base := fpga_dsp48e2, availableGPR := 64, spillCost := 2,
    simdWidth := 1, simdMulCost := 1 }

/-! ## Temporary count (register pressure estimation) -/

/-- Count maximum simultaneously live temporaries in an expression tree.
    Uses post-order traversal: at each binary node, one subtree's result
    must be held while the other is computed. -/
def tempCount : MixedExpr → Nat
  | .constE _    => 0
  | .witnessE _  => 0
  | .pubInputE _ => 0
  | .constMaskE _ => 0
  | .negE a      => tempCount a
  | .smulE _ a   => tempCount a
  | .shiftLeftE a _  => tempCount a
  | .shiftRightE a _ => tempCount a
  | .addE a b    => max (tempCount a + 1) (tempCount b + 1)
  | .mulE a b    => max (tempCount a + 1) (tempCount b + 1)
  | .bitAndE a b => max (tempCount a + 1) (tempCount b + 1)
  | .bitXorE a b => max (tempCount a + 1) (tempCount b + 1)
  | .bitOrE a b  => max (tempCount a + 1) (tempCount b + 1)
  | .subE a b    => max (tempCount a + 1) (tempCount b + 1)
  | .reduceE a _     => tempCount a
  | .kronPackE a b _ => max (tempCount a + 1) (tempCount b + 1)
  | .kronUnpackLoE a _ => tempCount a
  | .kronUnpackHiE a _ => tempCount a
  | .montyReduceE a _ _ => tempCount a
  | .barrettReduceE a _ _ => tempCount a
  | .harveyReduceE a _ => tempCount a

/-! ## Expression-level operation cost (recursive) -/

/-- Recursively sum `mixedOpCost` for every node in a `MixedExpr` tree.
    This gives the total ALU cost of evaluating the expression. -/
def exprOpCost (hw : HardwareCost) : MixedExpr → Nat
  | .constE _    => 0
  | .witnessE _  => 0
  | .pubInputE _ => 0
  | .constMaskE _ => 0
  | .negE a      => 0 + exprOpCost hw a
  | .smulE _ a   => hw.mul32 + exprOpCost hw a
  | .shiftLeftE a _  => hw.shift + exprOpCost hw a
  | .shiftRightE a _ => hw.shift + exprOpCost hw a
  | .addE a b    => hw.add + exprOpCost hw a + exprOpCost hw b
  | .mulE a b    => hw.mul32 + exprOpCost hw a + exprOpCost hw b
  | .bitAndE a b => hw.bitAnd + exprOpCost hw a + exprOpCost hw b
  | .bitXorE a b => hw.bitXor + exprOpCost hw a + exprOpCost hw b
  | .bitOrE a b  => hw.bitOr + exprOpCost hw a + exprOpCost hw b
  | .subE a b    => hw.sub + exprOpCost hw a + exprOpCost hw b
  | .reduceE a _     => hw.bitAnd + exprOpCost hw a
  | .kronPackE a b _ => 0 + exprOpCost hw a + exprOpCost hw b
  | .kronUnpackLoE a _ => hw.shift + exprOpCost hw a
  | .kronUnpackHiE a _ => hw.shift + exprOpCost hw a
  | .montyReduceE a _ _ => montgomeryCost hw + exprOpCost hw a
  | .barrettReduceE a _ _ => barrettCost hw + exprOpCost hw a
  | .harveyReduceE a _ => harveyCost hw + exprOpCost hw a

/-! ## Spill penalty and enhanced cost -/

/-- Additional cost when the expression requires more temporaries than
    available GPRs. Each excess temporary incurs `spillCost` cycles for
    a store/reload pair. -/
def spillPenalty (hw : EnhancedHardwareCost) (e : MixedExpr) : Nat :=
  let temps := tempCount e
  if temps > hw.availableGPR then (temps - hw.availableGPR) * hw.spillCost else 0

/-- Total enhanced cost: operation costs + register spill penalty. -/
def enhancedCost (hw : EnhancedHardwareCost) (e : MixedExpr) : Nat :=
  exprOpCost hw.base e + spillPenalty hw e

/-! ## Theorems -/

/-- Enhanced cost is always at least the basic operation cost (spill ≥ 0). -/
theorem enhanced_ge_basic (hw : EnhancedHardwareCost) (e : MixedExpr) :
    enhancedCost hw e ≥ exprOpCost hw.base e := by
  unfold enhancedCost
  omega

/-- When register demand fits within available GPRs, spill penalty is zero. -/
theorem spillPenalty_zero_sufficient_regs (hw : EnhancedHardwareCost) (e : MixedExpr)
    (h : tempCount e ≤ hw.availableGPR) :
    spillPenalty hw e = 0 := by
  unfold spillPenalty
  have hle : ¬ (tempCount e > hw.availableGPR) := Nat.not_lt.mpr h
  simp [hle]

/-- Leaf nodes (constants, witnesses, public inputs, masks) require zero temporaries. -/
theorem tempCount_leaf_zero (n : Nat) :
    tempCount (.constE n) = 0
    ∧ tempCount (.witnessE n) = 0
    ∧ tempCount (.pubInputE n) = 0
    ∧ tempCount (.constMaskE n) = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Auxiliary: the if-then-else in spillPenalty after unfolding the let. -/
private theorem spillPenalty_eq (hw : EnhancedHardwareCost) (e : MixedExpr) :
    spillPenalty hw e =
      if tempCount e > hw.availableGPR
      then (tempCount e - hw.availableGPR) * hw.spillCost
      else 0 := by
  unfold spillPenalty
  rfl

/-- Spill penalty is monotone: more GPRs and cheaper spills yield lower penalty. -/
private theorem spillPenalty_monotone
    (hw1 hw2 : EnhancedHardwareCost)
    (hgpr : hw1.availableGPR ≤ hw2.availableGPR)
    (hspill : hw2.spillCost ≤ hw1.spillCost)
    (e : MixedExpr) :
    spillPenalty hw2 e ≤ spillPenalty hw1 e := by
  rw [spillPenalty_eq, spillPenalty_eq]
  split
  case isTrue h2 =>
    split
    case isTrue h1 =>
      apply Nat.mul_le_mul
      · omega
      · exact hspill
    case isFalse h1 =>
      -- tempCount e > hw2.availableGPR but ≤ hw1.availableGPR
      -- impossible since hw1.availableGPR ≤ hw2.availableGPR
      omega
  case isFalse h2 =>
    exact Nat.zero_le _

/-- More available GPRs with lower spill cost → lower or equal enhanced cost.

    Note on hypothesis orientation: `hspill : hw2.spillCost ≤ hw1.spillCost` means
    hw1 has HIGHER spill cost than hw2. This is the expected direction: if hw2 has
    more GPRs (hgpr), it typically also has lower spill cost since fewer spills occur.
    The theorem compares two hardware targets where hw2 is "better" (more GPRs, cheaper spills). -/
theorem enhanced_cost_monotone_gpr
    (hw1 hw2 : EnhancedHardwareCost)
    (hbase : hw1.base = hw2.base)
    (hgpr : hw1.availableGPR ≤ hw2.availableGPR)
    (hspill : hw2.spillCost ≤ hw1.spillCost)
    (e : MixedExpr) :
    enhancedCost hw2 e ≤ enhancedCost hw1 e := by
  unfold enhancedCost
  have hsp := spillPenalty_monotone hw1 hw2 hgpr hspill e
  rw [hbase]
  omega

/-! ## Non-vacuity examples -/

/-- Non-vacuity: enhanced_ge_basic hypotheses are trivially satisfiable. -/
example : enhancedCost enhanced_arm_a76 (.constE 42) ≥
    exprOpCost enhanced_arm_a76.base (.constE 42) := by native_decide

/-- Non-vacuity: spillPenalty is zero for a simple expression on ARM. -/
example : spillPenalty enhanced_arm_a76 (.addE (.constE 1) (.constE 2)) = 0 := by
  native_decide

/-- Non-vacuity: tempCount of a binary node is 1 for leaf children. -/
example : tempCount (.addE (.constE 1) (.constE 2)) = 1 := by native_decide

/-- Non-vacuity: enhanced_cost_monotone_gpr — FPGA (64 GPR) ≤ ARM (31 GPR)
    on same base cost model. -/
example : enhancedCost
    { base := arm_cortex_a76, availableGPR := 64, spillCost := 4,
      simdWidth := 4, simdMulCost := 2 }
    (.mulE (.addE (.constE 1) (.witnessE 0)) (.constE 3)) ≤
  enhancedCost enhanced_arm_a76
    (.mulE (.addE (.constE 1) (.witnessE 0)) (.constE 3)) := by native_decide

/-! ## Smoke tests -/

#eval do
  let e := MixedExpr.mulE (.addE (.constE 1) (.witnessE 0)) (.shiftLeftE (.constE 5) 3)
  let armBasic := exprOpCost arm_cortex_a76 e
  let armEnhanced := enhancedCost enhanced_arm_a76 e
  let riscvBasic := exprOpCost riscv_sifive_u74 e
  let riscvEnhanced := enhancedCost enhanced_riscv_u74 e
  let fpgaBasic := exprOpCost fpga_dsp48e2 e
  let fpgaEnhanced := enhancedCost enhanced_fpga e
  IO.println s!"Expression: mul(add(const 1, witness 0), shl(const 5, 3))"
  IO.println s!"  tempCount = {tempCount e}"
  IO.println s!"  ARM  A76:  basic={armBasic}, enhanced={armEnhanced}, spill={spillPenalty enhanced_arm_a76 e}"
  IO.println s!"  RISC-V U74: basic={riscvBasic}, enhanced={riscvEnhanced}, spill={spillPenalty enhanced_riscv_u74 e}"
  IO.println s!"  FPGA DSP:  basic={fpgaBasic}, enhanced={fpgaEnhanced}, spill={spillPenalty enhanced_fpga e}"

#eval do
  -- Deep expression tree to show register pressure
  let deep := MixedExpr.addE
    (MixedExpr.addE
      (MixedExpr.addE (.witnessE 0) (.witnessE 1))
      (MixedExpr.addE (.witnessE 2) (.witnessE 3)))
    (MixedExpr.addE
      (MixedExpr.addE (.witnessE 4) (.witnessE 5))
      (MixedExpr.addE (.witnessE 6) (.witnessE 7)))
  IO.println s!"Deep 8-leaf tree: tempCount={tempCount deep}, exprOpCost(ARM)={exprOpCost arm_cortex_a76 deep}"
  IO.println s!"  enhanced(ARM)={enhancedCost enhanced_arm_a76 deep}"

-- Verify concrete instance fields
#eval s!"ARM GPR={enhanced_arm_a76.availableGPR}, SIMD={enhanced_arm_a76.simdWidth}"
#eval s!"RISC-V GPR={enhanced_riscv_u74.availableGPR}, SIMD={enhanced_riscv_u74.simdWidth}"
#eval s!"FPGA GPR={enhanced_fpga.availableGPR}, SIMD={enhanced_fpga.simdWidth}"

end AmoLean.EGraph.Verified.Bitwise
