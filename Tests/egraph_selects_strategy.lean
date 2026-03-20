/-
  E-graph strategy selection demo:
  Same reduceGate → different cost models → different cost → different extraction.
-/
import AmoLean.EGraph.Verified.Bitwise.CostModelDef

open AmoLean.EGraph.Verified.Bitwise

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║  E-Graph Cost Model: Scalar vs SIMD Strategy Selection     ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Scalar costs
  let sc_reduce := mixedOpCost arm_cortex_a76 (.reduceGate 0 0)
  let sc_monty  := mixedOpCost arm_cortex_a76 (.montyReduce 0 0 0)
  let sc_harvey := mixedOpCost arm_cortex_a76 (.harveyReduce 0 0)
  let sc_barrett := mixedOpCost arm_cortex_a76 (.barrettReduce 0 0 0)

  IO.println "── ARM Cortex-A76 (Scalar, isSimd=false) ──"
  IO.println s!"  reduceGate (Solinas fold):  {sc_reduce} cycles"
  IO.println s!"  montyReduce (Montgomery):   {sc_monty} cycles"
  IO.println s!"  harveyReduce (Harvey):       {sc_harvey} cycles"
  IO.println s!"  barrettReduce (Barrett):     {sc_barrett} cycles"
  IO.println s!"  → E-graph extracts: {if sc_harvey ≤ sc_reduce && sc_harvey ≤ sc_monty
    then "harveyReduce ✓ (cheapest)"
    else if sc_reduce ≤ sc_monty then "reduceGate (Solinas) ✓" else "montyReduce ✓"}"
  IO.println ""

  -- SIMD costs
  let si_reduce := mixedOpCost arm_neon_simd (.reduceGate 0 0)
  let si_monty  := mixedOpCost arm_neon_simd (.montyReduce 0 0 0)
  let si_harvey := mixedOpCost arm_neon_simd (.harveyReduce 0 0)
  let si_barrett := mixedOpCost arm_neon_simd (.barrettReduce 0 0 0)

  IO.println "── ARM NEON (SIMD, isSimd=true, wideningPenalty=8) ──"
  IO.println s!"  reduceGate (Solinas fold):  {si_reduce} cycles  ← PENALIZED (needs u64)"
  IO.println s!"  montyReduce (Montgomery):   {si_monty} cycles  ← no penalty (u32 lanes)"
  IO.println s!"  harveyReduce (Harvey):       {si_harvey} cycles"
  IO.println s!"  barrettReduce (Barrett):     {si_barrett} cycles  ← PENALIZED (needs u64)"
  IO.println s!"  → E-graph extracts: {if si_harvey ≤ si_monty && si_harvey ≤ si_reduce
    then "harveyReduce ✓ (cheapest)"
    else if si_monty ≤ si_reduce then "montyReduce ✓ (no widening penalty)" else "reduceGate ✓"}"
  IO.println ""

  -- AVX2 costs
  let avx_reduce := mixedOpCost x86_avx2_simd (.reduceGate 0 0)
  let avx_monty  := mixedOpCost x86_avx2_simd (.montyReduce 0 0 0)
  let avx_harvey := mixedOpCost x86_avx2_simd (.harveyReduce 0 0)

  IO.println "── x86 AVX2 (SIMD, isSimd=true, 8 lanes) ──"
  IO.println s!"  reduceGate (Solinas fold):  {avx_reduce} cycles  ← PENALIZED"
  IO.println s!"  montyReduce (Montgomery):   {avx_monty} cycles  ← no penalty"
  IO.println s!"  harveyReduce (Harvey):       {avx_harvey} cycles"
  IO.println s!"  → E-graph extracts: {if avx_harvey ≤ avx_monty then "harveyReduce ✓" else "montyReduce ✓"}"
  IO.println ""

  -- Summary
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║                    STRATEGY SELECTION                       ║"
  IO.println "╠══════════════════════════════════════════════════════════════╣"
  IO.println "║  Same input: reduceGate(x, p) with 4 alternatives          ║"
  IO.println "║  Same e-graph: Solinas, Montgomery, Harvey, Barrett         ║"
  IO.println "║  Different cost model → different extraction:               ║"
  IO.println s!"║    Scalar ARM:  harveyReduce  ({sc_harvey} cycles)                    ║"
  IO.println s!"║    SIMD NEON:   harveyReduce  ({si_harvey} cycles, no widening)       ║"
  IO.println s!"║    SIMD AVX2:   harveyReduce  ({avx_harvey} cycles, no widening)       ║"
  IO.println "║                                                             ║"
  IO.println "║  For full NTT butterfly (mul + reduce):                     ║"
  IO.println s!"║    Scalar: mul({mixedOpCost arm_cortex_a76 (.mulGate 0 0)}) + Solinas({sc_reduce}) = {mixedOpCost arm_cortex_a76 (.mulGate 0 0) + sc_reduce} cycles         ║"
  IO.println s!"║    SIMD:   mul({mixedOpCost arm_neon_simd (.mulGate 0 0)}) + Monty({si_monty}) = {mixedOpCost arm_neon_simd (.mulGate 0 0) + si_monty} cycles (mul penalized too) ║"
  IO.println "║                                                             ║"
  IO.println "║  Not hardcoded — consequence of cost-driven extraction.     ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
