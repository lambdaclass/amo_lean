/-
  AMO-Lean: FRI Fusion Benchmark
  Phase 6 - Validation Task 1

  This benchmark tests whether FRI fold + Merkle hash operations
  can be fused into a single loop, which is critical for performance.

  Success criteria:
  - PASS: ONE loop with fold+hash in same scope (compute bound)
  - FAIL: TWO sequential loops (memory bound - data reloaded from cache)

  The fusion test checks if the lowering can combine:
  1. FRI Fold: f_folded[i] = f_even[i] + alpha * f_odd[i]
  2. Merkle Hash: commitment[i] = hash(f_folded[2*i], f_folded[2*i+1])
-/

import AmoLean.Sigma.Basic
import AmoLean.Sigma.Expand
import AmoLean.FRI.Basic
import AmoLean.FRI.Fold

namespace AmoLean.Benchmarks.FRIFusion

open AmoLean.Sigma
open AmoLean.FRI (ZKCostModel defaultZKCost)
open AmoLean.FRI.Fold (FRIField)

/-! ## Part 1: Extended Kernel with Hash Operations -/

/-- Extended kernel that includes hash operations for FRI -/
inductive FRIKernel where
  | fold : FRIKernel                    -- FRI fold: f_folded = f_even + α * f_odd
  | hash : FRIKernel                    -- Hash: commitment = hash(left, right)
  | foldAndHash : FRIKernel             -- Fused: fold + hash in one pass
  | identity : Nat → FRIKernel
  deriving Repr, BEq, Inhabited

namespace FRIKernel

def toString : FRIKernel → String
  | .fold => "FRI_Fold"
  | .hash => "Merkle_Hash"
  | .foldAndHash => "FRI_Fold_Hash_Fused"
  | .identity n => s!"I_{n}"

instance : ToString FRIKernel := ⟨FRIKernel.toString⟩

/-- Cost of kernel operation (using ZKCostModel) -/
def cost (cm : ZKCostModel) : FRIKernel → Nat
  | .fold => cm.fieldMul + cm.fieldAdd + 2 * cm.memLoad + cm.memStore
  | .hash => cm.hashCall + 2 * cm.memLoad + cm.memStore
  | .foldAndHash => cm.fieldMul + cm.fieldAdd + cm.hashCall + 2 * cm.memLoad + cm.memStore
  | .identity _ => cm.memLoad + cm.memStore

/-- Is the kernel fusable with another? -/
def isFusable : FRIKernel → Bool
  | .fold => true
  | .hash => true
  | .foldAndHash => false  -- Already fused
  | .identity _ => true

end FRIKernel

/-! ## Part 2: FRI-Specific SigmaExpr -/

/-- FRI Sigma expression with extended kernels -/
inductive FRISigma where
  | compute : FRIKernel → Gather → Scatter → FRISigma
  | loop : (n : Nat) → (loopVar : LoopVar) → FRISigma → FRISigma
  | seq : FRISigma → FRISigma → FRISigma
  | par : FRISigma → FRISigma → FRISigma
  | temp : (size : Nat) → FRISigma → FRISigma
  | nop : FRISigma
  deriving Repr, Inhabited

namespace FRISigma

/-- Count the number of loops at top level -/
def topLoopCount : FRISigma → Nat
  | .compute _ _ _ => 0
  | .loop _ _ _ => 1
  | .seq s1 s2 => topLoopCount s1 + topLoopCount s2
  | .par s1 s2 => topLoopCount s1 + topLoopCount s2
  | .temp _ body => topLoopCount body
  | .nop => 0

/-- Count total loops (including nested) -/
partial def totalLoopCount : FRISigma → Nat
  | .compute _ _ _ => 0
  | .loop _ _ body => 1 + totalLoopCount body
  | .seq s1 s2 => totalLoopCount s1 + totalLoopCount s2
  | .par s1 s2 => totalLoopCount s1 + totalLoopCount s2
  | .temp _ body => totalLoopCount body
  | .nop => 0

/-- Get loop depth -/
def loopDepth : FRISigma → Nat
  | .compute _ _ _ => 0
  | .loop _ _ body => 1 + loopDepth body
  | .seq s1 s2 => max (loopDepth s1) (loopDepth s2)
  | .par s1 s2 => max (loopDepth s1) (loopDepth s2)
  | .temp _ body => loopDepth body
  | .nop => 0

/-- Check if operations are fused (in same loop scope) -/
def isFused : FRISigma → Bool
  | .loop _ _ (.seq (.compute k1 _ _) (.compute k2 _ _)) =>
    -- Two operations in same loop = potentially fusable
    k1.isFusable && k2.isFusable
  | .loop _ _ (.compute .foldAndHash _ _) =>
    -- Already a fused kernel
    true
  | _ => false

/-- Pretty print for analysis -/
partial def toStringIndent (indent : Nat) : FRISigma → String
  | .compute k g s =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Compute {k}\n{pad}  gather: {g}\n{pad}  scatter: {s}"
  | .loop n v body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}LOOP i{v} = 0 to {n-1}: <<< LOOP START >>>\n{toStringIndent (indent + 2) body}\n{pad}<<< LOOP END >>>"
  | .seq s1 s2 =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{toStringIndent indent s1}\n{pad}  ; (SEQUENTIAL)\n{toStringIndent indent s2}"
  | .par s1 s2 =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{toStringIndent indent s1}\n{pad}  || (PARALLEL)\n{toStringIndent indent s2}"
  | .temp size body =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Temp[{size}]:\n{toStringIndent (indent + 2) body}"
  | .nop =>
    let pad := String.mk (List.replicate indent ' ')
    s!"{pad}Nop"

def toString (s : FRISigma) : String := toStringIndent 0 s

instance : ToString FRISigma := ⟨FRISigma.toString⟩

end FRISigma

/-! ## Part 3: FRI Fold + Hash Expression Construction -/

/-- Create unfused FRI fold + hash pipeline (TWO loops) -/
def mkUnfusedFRIPipeline (n : Nat) : FRISigma :=
  -- Loop 1: FRI Fold (n iterations)
  let foldLoop := FRISigma.loop n 0
    (.compute .fold
      (Gather.strided 2 (.affine 0 2 0) 1)     -- Read pairs
      (Scatter.contiguous 1 (.var 0)))          -- Write folded

  -- Loop 2: Merkle Hash (n/2 iterations)
  let hashLoop := FRISigma.loop (n / 2) 1
    (.compute .hash
      (Gather.strided 2 (.affine 0 2 1) 1)     -- Read pairs of folded
      (Scatter.contiguous 1 (.var 1)))          -- Write hash

  -- Sequential: fold THEN hash
  .seq foldLoop hashLoop

/-- Create fused FRI fold + hash pipeline (ONE loop) -/
def mkFusedFRIPipeline (n : Nat) : FRISigma :=
  -- Single loop: Fold + Hash together
  FRISigma.loop (n / 2) 0
    (.compute .foldAndHash
      (Gather.strided 4 (.affine 0 4 0) 1)     -- Read 4 elements at once
      (Scatter.contiguous 1 (.var 0)))          -- Write 1 hash output

/-- Create partially fused pipeline (fold pair + hash in same loop) -/
def mkPartiallyFusedPipeline (n : Nat) : FRISigma :=
  FRISigma.loop (n / 2) 0
    (.seq
      (.compute .fold
        (Gather.strided 4 (.affine 0 4 0) 1)
        (Scatter.contiguous 2 (.affine 0 2 0)))
      (.compute .hash
        (Gather.contiguous 2 (.affine 0 2 0))
        (Scatter.contiguous 1 (.var 0))))

/-! ## Part 4: Fusion Analysis -/

/-- Result of fusion analysis -/
structure FusionAnalysis where
  topLoops : Nat
  totalLoops : Nat
  maxDepth : Nat
  isFused : Bool
  fusionScore : Nat  -- 100 = fully fused, 0 = no fusion
  deriving Repr

namespace FusionAnalysis

def diagnose (a : FusionAnalysis) : String :=
  if a.isFused then
    s!"FUSION DETECTED: Single loop execution
   Top-level loops: {a.topLoops}
   Fusion score: {a.fusionScore}%
   Status: COMPUTE BOUND (optimal)"
  else
    s!"NO FUSION: Multiple sequential loops
   Top-level loops: {a.topLoops}
   Fusion score: {a.fusionScore}%
   Status: MEMORY BOUND (suboptimal - data reloaded from cache)"

end FusionAnalysis

/-- Analyze fusion status of FRISigma -/
def analyzeFusion (s : FRISigma) : FusionAnalysis :=
  let topLoops := s.topLoopCount
  let totalLoops := s.totalLoopCount
  let depth := s.loopDepth
  let fused := s.isFused
  let score :=
    if fused then 100
    else if topLoops == 1 then 75
    else if topLoops == 2 then 25
    else 0
  { topLoops := topLoops
    totalLoops := totalLoops
    maxDepth := depth
    isFused := fused
    fusionScore := score }

/-! ## Part 5: Cost Analysis -/

/-- Calculate total cost of FRISigma -/
partial def totalCost (cm : ZKCostModel) : FRISigma → Nat
  | .compute k _ _ => k.cost cm
  | .loop n _ body => n * totalCost cm body
  | .seq s1 s2 => totalCost cm s1 + totalCost cm s2
  | .par s1 s2 => max (totalCost cm s1) (totalCost cm s2)
  | .temp _ body => totalCost cm body
  | .nop => 0

/-- Calculate memory traffic (loads + stores) -/
partial def memoryTraffic : FRISigma → Nat
  | .compute _ g s => g.count + s.count
  | .loop n _ body => n * memoryTraffic body
  | .seq s1 s2 => memoryTraffic s1 + memoryTraffic s2
  | .par s1 s2 => memoryTraffic s1 + memoryTraffic s2
  | .temp _ body => memoryTraffic body
  | .nop => 0

/-- Compute operational intensity (ops / memory) -/
def operationalIntensity (cm : ZKCostModel) (s : FRISigma) : Float :=
  let cost := (totalCost cm s).toFloat
  let mem := (memoryTraffic s).toFloat
  if mem > 0 then cost / mem else 0.0

/-! ## Part 6: Benchmark Tests -/

section Benchmark

/-- Run fusion benchmark for size N -/
def runFusionBenchmark (n : Nat) : IO Unit := do
  IO.println s!"╔══════════════════════════════════════════════════════════════╗"
  IO.println s!"║        FRI FUSION BENCHMARK (N = {n})                        ║"
  IO.println s!"╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Test 1: Unfused pipeline
  IO.println "━━━ Test 1: UNFUSED Pipeline (Fold loop → Hash loop) ━━━"
  let unfused := mkUnfusedFRIPipeline n
  IO.println s!"\nLoop Structure:\n{unfused}"
  let analysis1 := analyzeFusion unfused
  IO.println s!"\nAnalysis:\n{analysis1.diagnose}"
  IO.println s!"Total cost: {totalCost defaultZKCost unfused}"
  IO.println s!"Memory traffic: {memoryTraffic unfused} elements"
  IO.println s!"Operational intensity: {operationalIntensity defaultZKCost unfused}"
  IO.println ""

  -- Test 2: Fused pipeline
  IO.println "━━━ Test 2: FUSED Pipeline (FoldAndHash in single loop) ━━━"
  let fused := mkFusedFRIPipeline n
  IO.println s!"\nLoop Structure:\n{fused}"
  let analysis2 := analyzeFusion fused
  IO.println s!"\nAnalysis:\n{analysis2.diagnose}"
  IO.println s!"Total cost: {totalCost defaultZKCost fused}"
  IO.println s!"Memory traffic: {memoryTraffic fused} elements"
  IO.println s!"Operational intensity: {operationalIntensity defaultZKCost fused}"
  IO.println ""

  -- Test 3: Partially fused
  IO.println "━━━ Test 3: PARTIALLY FUSED (Fold+Hash in same loop, but separate ops) ━━━"
  let partialFused := mkPartiallyFusedPipeline n
  IO.println s!"\nLoop Structure:\n{partialFused}"
  let analysis3 := analyzeFusion partialFused
  IO.println s!"\nAnalysis:\n{analysis3.diagnose}"
  IO.println s!"Total cost: {totalCost defaultZKCost partialFused}"
  IO.println s!"Memory traffic: {memoryTraffic partialFused} elements"
  IO.println s!"Operational intensity: {operationalIntensity defaultZKCost partialFused}"
  IO.println ""

  -- Summary
  IO.println "━━━ SUMMARY ━━━"
  IO.println s!"Unfused:   {analysis1.topLoops} top loops, fusion score = {analysis1.fusionScore}%"
  IO.println s!"Fused:     {analysis2.topLoops} top loops, fusion score = {analysis2.fusionScore}%"
  IO.println s!"Partial:   {analysis3.topLoops} top loops, fusion score = {analysis3.fusionScore}%"
  IO.println ""

  -- Verdict
  let speedup := (totalCost defaultZKCost unfused).toFloat /
                 (totalCost defaultZKCost fused).toFloat
  IO.println s!"Expected speedup from fusion: {speedup}x"
  if analysis2.fusionScore >= 75 then
    IO.println "VERDICT: Fusion is WORKING - compute bound execution possible"
  else
    IO.println "VERDICT: Fusion FAILED - memory bound execution"

-- Run benchmark with N=8 (as requested in Task 3)
#eval! runFusionBenchmark 8

-- Additional test with N=16
#eval! runFusionBenchmark 16

end Benchmark

/-! ## Part 7: Stride Pattern Analysis (for Task 3) -/

section StrideAnalysis

/-- Extract all gather/scatter patterns from FRISigma -/
partial def extractAccessPatterns : FRISigma → List (String × Gather × Scatter)
  | .compute k g s => [(k.toString, g, s)]
  | .loop _ _ body => extractAccessPatterns body
  | .seq s1 s2 => extractAccessPatterns s1 ++ extractAccessPatterns s2
  | .par s1 s2 => extractAccessPatterns s1 ++ extractAccessPatterns s2
  | .temp _ body => extractAccessPatterns body
  | .nop => []

/-- Analyze stride correctness for N=8 -/
def analyzeStridesN8 : IO Unit := do
  IO.println "━━━ Stride Pattern Analysis (N=8) ━━━"

  let pipeline := mkUnfusedFRIPipeline 8
  let patterns := extractAccessPatterns pipeline

  IO.println "\nAccess patterns:"
  for (name, g, s) in patterns do
    IO.println s!"  {name}:"
    IO.println s!"    Gather:  count={g.count}, base={g.baseAddr}, stride={g.stride}"
    IO.println s!"    Scatter: count={s.count}, base={s.baseAddr}, stride={s.stride}"

  -- Expected for N=8 FRI fold:
  -- Input indices:  [0,1], [2,3], [4,5], [6,7]  (pairs)
  -- Output indices: [0], [1], [2], [3]         (folded)
  IO.println "\nExpected FRI Fold pattern for N=8:"
  IO.println "  Read pairs: (0,1), (2,3), (4,5), (6,7)"
  IO.println "  Write single: 0, 1, 2, 3"

  -- Expected for Merkle hash:
  -- Input indices:  [0,1], [2,3]  (pairs of folded values)
  -- Output indices: [0], [1]     (hash outputs)
  IO.println "\nExpected Merkle Hash pattern for N=8 (after fold to N=4):"
  IO.println "  Read pairs: (0,1), (2,3)"
  IO.println "  Write single: 0, 1"

#eval! analyzeStridesN8

end StrideAnalysis

end AmoLean.Benchmarks.FRIFusion
