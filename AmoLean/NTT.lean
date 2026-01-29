/-
  AMO-Lean: NTT Module
  Phase 5: NTT Core

  Number Theoretic Transform implementation with formal verification.

  Architecture (Trieu's Layer Refinement):
  ┌─────────────────────────────────────────────────────────────────┐
  │ LAYER 4: Generated C/AVX2 Code (via E-Graph)                    │
  ├─────────────────────────────────────────────────────────────────┤
  │ LAYER 3: Implementation with Bounds (LazyGoldilocks)            │
  ├─────────────────────────────────────────────────────────────────┤
  │ LAYER 2: Recursive Algorithm (Cooley-Tukey)                     │
  ├─────────────────────────────────────────────────────────────────┤
  │ LAYER 1: Mathematical Specification                             │
  └─────────────────────────────────────────────────────────────────┘

  Current Status: Layers 1-3 complete (Week 4-5)
-/

-- Layer 1: Mathematical Specification
import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Goldilocks
import AmoLean.NTT.ListUtils
import AmoLean.NTT.Spec
import AmoLean.NTT.Properties

-- Layer 2: Recursive Algorithm (Cooley-Tukey)
import AmoLean.NTT.CooleyTukey
import AmoLean.NTT.Butterfly
import AmoLean.NTT.Correctness

-- Layer 3: Implementation with Bounds
import AmoLean.NTT.Bounds
import AmoLean.NTT.LazyButterfly

-- Documentation
import AmoLean.NTT.Axioms

-- Future imports (Layer 4):
-- import AmoLean.NTT.CodeGen        -- Layer 4: C generation
