/-
  AmoLean.EGraph.Verified.Bitwise.ButterflyCost — Butterfly-level cost functions

  B79 (PARALELO): Cost functions for different butterfly implementations.
  Enables the e-graph extractor to choose between full-reduce, Harvey, and lazy butterflies.
-/
import AmoLean.EGraph.Verified.Bitwise.CostModelDef

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.ButterflyCost

open AmoLean.EGraph.Verified.Bitwise (HardwareCost)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Butterfly cost definitions
-- ══════════════════════════════════════════════════════════════════

/-- Full-reduce butterfly: mul + add + mod_reduce (standard, safe). -/
def butterflyFullReduceCost (hw : HardwareCost) : Nat :=
  hw.mul32 + hw.add + hw.modReduce

/-- Harvey butterfly: mul + add + conditional_sub (no full reduction). -/
def butterflyHarveyCost (hw : HardwareCost) : Nat :=
  hw.mul32 + hw.add + hw.condSub

/-- Lazy butterfly: mul + add only (deferred reduction, cheapest). -/
def butterflyLazyCost (hw : HardwareCost) : Nat :=
  hw.mul32 + hw.add

/-- Fused shift-sub butterfly: for Mersenne-1 constants, mul replaced by shift-sub.
    Uses fusedShiftSub cost for targets with barrel shifter. -/
def butterflyShiftSubCost (hw : HardwareCost) : Nat :=
  hw.fusedShiftSub + hw.add + hw.condSub

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Cost ordering theorems
-- ══════════════════════════════════════════════════════════════════

/-- Lazy is always ≤ Harvey (Harvey adds conditional sub). -/
theorem lazy_le_harvey (hw : HardwareCost) :
    butterflyLazyCost hw ≤ butterflyHarveyCost hw := by
  simp [butterflyLazyCost, butterflyHarveyCost]

/-- Harvey is always ≤ full reduce when condSub ≤ modReduce. -/
theorem harvey_le_fullReduce (hw : HardwareCost) (h : hw.condSub ≤ hw.modReduce) :
    butterflyHarveyCost hw ≤ butterflyFullReduceCost hw := by
  unfold butterflyHarveyCost butterflyFullReduceCost; omega

/-- Shift-sub butterfly is cheaper than mul butterfly when fusedShiftSub < mul32. -/
theorem shiftSub_lt_mul (hw : HardwareCost) (h : hw.fusedShiftSub < hw.mul32)
    (hcs : hw.condSub ≤ hw.modReduce) :
    butterflyShiftSubCost hw < butterflyFullReduceCost hw := by
  unfold butterflyShiftSubCost butterflyFullReduceCost
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Per-target concrete costs
-- ══════════════════════════════════════════════════════════════════

open AmoLean.EGraph.Verified.Bitwise (arm_cortex_a76 riscv_sifive_u74 fpga_dsp48e2 x86_skylake)

/-- ARM: full=5, Harvey=5, lazy=4, shiftSub=3. Shift-sub wins on ARM! -/
example : butterflyFullReduceCost arm_cortex_a76 = 5 := by native_decide
example : butterflyHarveyCost arm_cortex_a76 = 5 := by native_decide
example : butterflyLazyCost arm_cortex_a76 = 4 := by native_decide
example : butterflyShiftSubCost arm_cortex_a76 = 3 := by native_decide

/-- RISC-V: full=7, Harvey=7, lazy=6, shiftSub=4. Shift-sub saves 3 cycles! -/
example : butterflyFullReduceCost riscv_sifive_u74 = 7 := by native_decide
example : butterflyHarveyCost riscv_sifive_u74 = 7 := by native_decide
example : butterflyLazyCost riscv_sifive_u74 = 6 := by native_decide
example : butterflyShiftSubCost riscv_sifive_u74 = 4 := by native_decide

/-- FPGA: full=3, Harvey=3, lazy=2, shiftSub=3. Lazy wins on FPGA! -/
example : butterflyFullReduceCost fpga_dsp48e2 = 3 := by native_decide
example : butterflyLazyCost fpga_dsp48e2 = 2 := by native_decide

/-- x86: full=5, Harvey=5, lazy=4, shiftSub=4. -/
example : butterflyFullReduceCost x86_skylake = 5 := by native_decide
example : butterflyShiftSubCost x86_skylake = 4 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.ButterflyCost
