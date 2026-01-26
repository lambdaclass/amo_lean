/-
  AMO-Lean Core Module

  This module re-exports the core components of AMO-Lean:
  - EGraph: Equality saturation engine
  - Sigma: MatExpr symbolic algebra (Kronecker products)
  - Matrix/Vector: Linear algebra primitives
  - Meta: Compile-time rule generation

  These components form the "engine" and should be stable.
  Changes to Core should be carefully reviewed.
-/

import AmoLean.EGraph.Basic
import AmoLean.EGraph.Saturate
import AmoLean.EGraph.EMatch
import AmoLean.EGraph.Vector

import AmoLean.Sigma.Basic
import AmoLean.Sigma.Expand
import AmoLean.Sigma.SIMD
import AmoLean.Sigma.ZModSIMD

import AmoLean.Matrix.Basic
import AmoLean.Matrix.Perm

import AmoLean.Vector.Basic

import AmoLean.Meta.CompileRules
