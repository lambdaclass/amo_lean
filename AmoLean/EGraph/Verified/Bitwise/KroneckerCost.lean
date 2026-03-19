/-
  AmoLean.EGraph.Verified.Bitwise.KroneckerCost — SIMD cost scaling for Kronecker packing

  B80 (HOJA): When 2 field elements are packed in one word, effective cost per element halves.
-/
import AmoLean.EGraph.Verified.Bitwise.CostModelDef

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.KroneckerCost

open AmoLean.EGraph.Verified.Bitwise (HardwareCost arm_cortex_a76 riscv_sifive_u74 fpga_dsp48e2)

/-- Kronecker packing factor: 2 elements per word when width fits. -/
def kroneckerFactor (elemBits wordBits : Nat) : Nat :=
  if 2 * elemBits ≤ wordBits then 2 else 1

/-- Effective cost per element when Kronecker-packed. -/
def kronPackedCost (hw : HardwareCost) (elemBits wordBits : Nat) : Nat :=
  hw.mul32 / kroneckerFactor elemBits wordBits

/-- Packed cost is always ≤ unpacked cost. -/
theorem kronPacked_le_unpacked (hw : HardwareCost) (eb wb : Nat) :
    kronPackedCost hw eb wb ≤ hw.mul32 := by
  simp only [kronPackedCost]
  exact Nat.div_le_self hw.mul32 _

/-- BabyBear (31 bits) in u64: factor = 2. -/
example : kroneckerFactor 31 64 = 2 := by native_decide

/-- BabyBear packed mul cost on ARM = 3/2 = 1 (integer division). -/
example : kronPackedCost arm_cortex_a76 31 64 = 1 := by native_decide

/-- BabyBear packed mul cost on RISC-V = 5/2 = 2. -/
example : kronPackedCost riscv_sifive_u74 31 64 = 2 := by native_decide

/-- Goldilocks (64 bits) in u64: factor = 1 (can't pack). -/
example : kroneckerFactor 64 64 = 1 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.KroneckerCost
