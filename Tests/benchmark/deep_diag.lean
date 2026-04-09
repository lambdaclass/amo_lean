/-
  Deep diagnostic: what does the plan look like?
-/
import AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline

set_option maxHeartbeats 40000000

open AmoLean.EGraph.Verified.Bitwise.OptimizedNTTPipeline
open AmoLean.EGraph.Verified.Bitwise (arm_cortex_a76 arm_neon_simd HardwareCost)
open AmoLean.EGraph.Verified.Bitwise.NTTPlan (Plan NTTStage RadixChoice)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)
open AmoLean.EGraph.Verified.Bitwise.PlanSelection (generateCandidates selectPlan CacheConfig)
open AmoLean.EGraph.Verified.Bitwise.CrossRelNTT (nttStageBoundAnalysis NTTBoundConfig)

def showRed : ReductionChoice → String
  | .solinasFold => "Solinas"
  | .montgomery => "Monty"
  | .lazy => "LAZY"
  | .harvey => "Harvey"

def showR : RadixChoice → String
  | .r2 => "R2"
  | .r4 => "R4"

def main (args : List String) : IO Unit := do
  let field := args.getD 0 "babybear"
  let logN := (args.getD 1 "14").toNat?.getD 14
  let n := 2^logN
  let hw := arm_cortex_a76

  let fc := match field with
    | "koalabear" => koalabearConfig
    | "mersenne31" => mersenne31Config
    | "goldilocks" => goldilocksConfig
    | _ => babybearConfig

  IO.println s!"═══ {fc.name} N=2^{logN} ═══"

  -- 1. Bound analysis
  IO.println "\n── BOUND ANALYSIS ──"
  let analysis := nttStageBoundAnalysis { numStages := logN, prime := fc.pNat }
  let mut lazyN := (0 : Nat)
  for entry in analysis do
    let (idx, red, bk) := entry
    IO.println s!"  st{idx}: {showRed red} bK={bk}"
    if red == .lazy then lazyN := lazyN + 1
  IO.println s!"  → {lazyN}/{analysis.length} lazy stages"

  -- 2. Candidates
  IO.println "\n── CANDIDATES ──"
  let arrayIsLarge := n > hw.cacheThreshold
  let cands := generateCandidates fc.pNat n hw arrayIsLarge
  for h : i in [:cands.size] do
    let c := cands[i]
    let hasR4 := c.stages.toList.any (·.radix == .r4)
    let r := if hasR4 then "R4" else "R2"
    let red0 := if h2 : c.stages.size > 0 then showRed c.stages[0].reduction else "?"
    let cost := c.totalCost hw
    IO.println s!"  [{i}] {r}/{red0} stg={c.numStages} lazy={c.lazyStages} cost={cost}"

  -- 3. Winner (scalar)
  IO.println "\n── WINNER (arm-scalar) ──"
  let winner := match selectPlan cands hw CacheConfig.default with
    | some p => p | none => cands[0]!
  IO.println s!"  stages={winner.numStages} lazy={winner.lazyStages} cost={winner.totalCost hw}"
  for h : i in [:winner.stages.size] do
    let s := winner.stages[i]
    IO.println s!"  [{i}] {showR s.radix} {showRed s.reduction} bK={s.inputBoundK}→{s.outputBoundK}"

  -- 3b. Winner (NEON) — compare plan differences
  IO.println "\n── WINNER (arm-neon) ──"
  let hwNeon := arm_neon_simd
  let candsNeon := generateCandidates fc.pNat n hwNeon arrayIsLarge
  let winnerNeon := match selectPlan candsNeon hwNeon CacheConfig.default with
    | some p => p | none => candsNeon[0]!
  IO.println s!"  stages={winnerNeon.numStages} lazy={winnerNeon.lazyStages} cost={winnerNeon.totalCost hwNeon}"
  for h : i in [:winnerNeon.stages.size] do
    let s := winnerNeon.stages[i]
    IO.println s!"  [{i}] {showR s.radix} {showRed s.reduction} bK={s.inputBoundK}→{s.outputBoundK}"

  -- 4. Generate C code for both paths (ND.1 plan dump + ND.5 diagnosis)
  if args.contains "--emit-c" then
    IO.println "\n── EMITTING C CODE ──"
    let scalarCode := genOptimizedBenchC_ultra fc logN 1 arm_cortex_a76
    IO.FS.writeFile ⟨"/tmp/neon_debug_scalar.c"⟩ scalarCode
    IO.println s!"  Scalar: /tmp/neon_debug_scalar.c ({scalarCode.length} chars)"
    let neonCode := genOptimizedBenchC_ultra fc logN 1 arm_neon_simd
    IO.FS.writeFile ⟨"/tmp/neon_debug_neon.c"⟩ neonCode
    IO.println s!"  NEON:   /tmp/neon_debug_neon.c ({neonCode.length} chars)"
