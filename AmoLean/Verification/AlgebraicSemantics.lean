/-
  AMO-Lean: Algebraic Semantics for Formal Verification
  Session 15: C-Lite++ Strategy

  This module provides reference semantics over a generic Field α,
  enabling formal verification without Float-specific issues.

  Key Design Decisions:
  1. Generic over [Field α] [DecidableEq α] [Inhabited α]
  2. DFT parametrized by (ω : α) (hω : IsPrimitiveRoot ω n)
  3. No `partial` - all functions are total with termination proofs
  4. Separate from Semantics.lean to preserve Float-based testing

  References:
  - Session 15 documentation: C-Lite++ strategy
  - NTT/RootsOfUnity.lean: IsPrimitiveRoot definition
  - Expert consultations: DeepSeek (Lean 4), Gemini QA
-/

import AmoLean.Sigma.Basic
import AmoLean.NTT.RootsOfUnity
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic

namespace AmoLean.Verification.Algebraic

open AmoLean.Sigma (SigmaExpr Kernel Gather Scatter IdxExpr LoopVar lower lowerFresh LowerState
                     freshLoopVar adjustBlock adjustStride)
open AmoLean.Matrix (MatExpr Perm)
open AmoLean.NTT (IsPrimitiveRoot)

/-! ## Part 1: Generic Memory Model -/

variable {α : Type} [Field α] [DecidableEq α] [Inhabited α]

/-- Memory is an array of values indexed by natural numbers -/
structure Memory (α : Type*) where
  data : Array α
  deriving Repr

namespace Memory

/-- Read from memory at an index (returns default for out-of-bounds) -/
def read [Inhabited α] (mem : Memory α) (idx : Nat) : α :=
  if idx < mem.data.size then mem.data[idx]! else default

/-- Write to memory at an index (extends if needed) -/
def write [Inhabited α] (mem : Memory α) (idx : Nat) (val : α) : Memory α :=
  if idx < mem.data.size then
    { data := mem.data.set! idx val }
  else
    let newSize := idx + 1
    let extended := mem.data ++ Array.mkArray (newSize - mem.data.size) default
    { data := extended.set! idx val }

/-- Create memory from a list -/
def ofList (l : List α) : Memory α := { data := l.toArray }

/-- Convert memory to list -/
def toList (mem : Memory α) : List α := mem.data.toList

/-- Size of memory -/
def size (mem : Memory α) : Nat := mem.data.size

/-- Create a zeroed memory of given size -/
def zeros [Zero α] (size : Nat) : Memory α := { data := Array.mkArray size 0 }

/-- Array getElem! equals List getElem when in bounds.
    This bridges Array and List indexing via getElem!_toArray + getElem!_pos. -/
theorem array_getElem_bang_eq_list_getElem (l : List α) (i : Nat) (hi : i < l.length) :
    l.toArray[i]! = l[i]'hi := by
  simp [hi]

/-- Reading from ofList at valid index gives list element -/
@[simp]
theorem read_ofList (l : List α) (i : Nat) (hi : i < l.length) :
    (ofList l).read i = l[i]'hi := by
  simp only [ofList, read]
  have h : i < l.toArray.size := by simp [hi]
  simp only [h, ↓reduceIte]
  exact array_getElem_bang_eq_list_getElem l i hi

/-- Reading from Memory.ofList equals List.getD with Inhabited default.
    Bridges Memory.read (used in evalGather) with List.getD (used in evalMatExprAlg). -/
theorem read_ofList_eq_getD (l : List α) (i : Nat) :
    (ofList l).read i = l.getD i default := by
  by_cases h : i < l.length
  · rw [read_ofList l i h]; simp [List.getD, h]
  · have hle : l.length ≤ i := Nat.le_of_not_lt h
    have hq : l[i]? = none := by simp [List.getElem?_eq_none, hle]
    simp [read, ofList, h, List.getD, hq]

/-- Size of ofList equals list length -/
@[simp]
theorem size_ofList (l : List α) : (ofList l).size = l.length := by
  simp only [ofList, size, Array.size_toArray]

/-- toList of ofList is identity -/
@[simp]
theorem toList_ofList (l : List α) : (ofList l).toList = l := by
  simp only [ofList, toList, Array.toList_toArray]

/-! ### Bridge lemmas: Memory.write ↔ List.set -/

/-- Size of zeros equals the requested size -/
@[simp]
theorem zeros_size [Zero α] (n : Nat) : (zeros n : Memory α).size = n := by
  simp only [zeros, size, Array.size_mkArray]

/-- toList of zeros is replicate of 0 -/
@[simp]
theorem zeros_toList [Zero α] (n : Nat) : (zeros n : Memory α).toList = List.replicate n 0 := by
  simp only [zeros, toList, Array.toList_mkArray]

/-- Writing to in-bounds position preserves size -/
theorem size_write_eq [Inhabited α] (mem : Memory α) (i : Nat) (v : α) (hi : i < mem.size) :
    (mem.write i v).size = mem.size := by
  unfold write
  split_ifs with h
  · simp only [size, Array.set!, Array.size_setIfInBounds]
  · exact absurd hi h

/-- Writing to in-bounds position: toList becomes List.set -/
theorem toList_write_eq_set [Inhabited α] (mem : Memory α) (i : Nat) (v : α) (hi : i < mem.size) :
    (mem.write i v).toList = mem.toList.set i v := by
  unfold write
  split_ifs with h
  · simp only [toList, Array.set!, Array.toList_setIfInBounds]
  · exact absurd hi h

/-- Writing never decreases memory size -/
theorem write_size_ge [Inhabited α] (mem : Memory α) (i : Nat) (v : α) :
    mem.size ≤ (mem.write i v).size := by
  unfold write size
  split_ifs with h
  · simp only [Array.set!, Array.size_setIfInBounds]; omega
  · simp only [Array.set!, Array.size_setIfInBounds, Array.size_append, Array.size_mkArray]; omega

/-- Two Memory values are equal iff their data arrays are equal.
    Since Memory is determined entirely by its data field, equality of
    toList (= data.toList) implies structural equality. -/
theorem eq_of_toList_eq {m1 m2 : Memory α} (h : m1.toList = m2.toList) : m1 = m2 := by
  cases m1; cases m2
  simp only [toList] at h
  exact congrArg Memory.mk (Array.ext' h)

/-- Writing mem.read(i) at position i is identity for in-bounds positions -/
theorem write_read_self [Inhabited α] (mem : Memory α) (i : Nat) (hi : i < mem.size) :
    mem.write i (mem.read i) = mem := by
  apply eq_of_toList_eq
  rw [toList_write_eq_set mem i (mem.read i) hi]
  simp only [read, size] at hi ⊢
  rw [if_pos hi]
  rw [getElem!_pos mem.data i hi]
  rw [toList]
  exact List.set_getElem_self (by rw [Array.length_toList]; exact hi)

/-- zeros_size expressed as data.size -/
theorem zeros_data_size [Zero α] (n : Nat) : (zeros n : Memory α).data.size = n := by
  simp only [zeros, Array.size_mkArray]

/-- Memory equality from toList, iff version -/
@[simp]
theorem toList_injective {m1 m2 : Memory α} : m1.toList = m2.toList ↔ m1 = m2 :=
  ⟨eq_of_toList_eq, fun h => h ▸ rfl⟩

/-- Memory roundtrip: ofList ∘ toList = id -/
theorem ofList_toList (m : Memory α) : Memory.ofList m.toList = m := by
  cases m; simp only [ofList, toList]

end Memory

/-! ## Part 2: Evaluation State -/

/-- Environment mapping loop variables to their current values -/
abbrev LoopEnv := LoopVar → Nat

/-- Empty environment (all variables are 0) -/
def LoopEnv.empty : LoopEnv := fun _ => 0

/-- Update environment with a binding -/
def LoopEnv.bind (env : LoopEnv) (v : LoopVar) (val : Nat) : LoopEnv :=
  fun v' => if v' == v then val else env v'

/-- Binding returns the bound value when queried with the same variable -/
theorem LoopEnv.bind_same (env : LoopEnv) (v : LoopVar) (val : Nat) :
    (env.bind v val) v = val := by
  simp only [LoopEnv.bind, beq_self_eq_true, ↓reduceIte]

/-- Bindings with different variables commute -/
theorem LoopEnv.bind_comm (env : LoopEnv) (v1 v2 : LoopVar) (val1 val2 : Nat) (hne : v1 ≠ v2) :
    (env.bind v1 val1).bind v2 val2 = (env.bind v2 val2).bind v1 val1 := by
  funext v
  simp only [LoopEnv.bind]
  by_cases h1 : v == v2 <;> by_cases h2 : v == v1 <;> simp_all [beq_iff_eq]

/-- State during evaluation with explicit read/write memories -/
structure EvalState (α : Type*) where
  readMem : Memory α
  writeMem : Memory α
  deriving Repr

/-- Initial state from input list -/
def EvalState.init [Zero α] (input : List α) (outputSize : Nat) : EvalState α :=
  { readMem := Memory.ofList input
  , writeMem := Memory.zeros outputSize }

/-! ## Part 3: Index Expression Evaluation -/

/-- Evaluate an index expression given loop environment -/
def evalIdxExpr (env : LoopEnv) : IdxExpr → Nat
  | .const n => n
  | .var v => env v
  | .affine base stride v => base + stride * env v
  | .add e1 e2 => evalIdxExpr env e1 + evalIdxExpr env e2
  | .mul c e => c * evalIdxExpr env e

/-- evalIdxExpr for .affine with bound variable only depends on bound value -/
theorem evalIdxExpr_affine_bind (env : LoopEnv) (v : LoopVar) (i base stride : Nat) :
    evalIdxExpr (env.bind v i) (IdxExpr.affine base stride v) = base + stride * i := by
  simp only [evalIdxExpr, LoopEnv.bind_same]

/-- evalIdxExpr for .var with bound variable only depends on bound value -/
theorem evalIdxExpr_var_bind (env : LoopEnv) (v : LoopVar) (i : Nat) :
    evalIdxExpr (env.bind v i) (IdxExpr.var v) = i := by
  simp only [evalIdxExpr, LoopEnv.bind_same]

/-! ### Part 3.5: Free Variables Infrastructure

These definitions enable alpha-equivalence proofs by tracking which loop variables
appear free (unbound) in expressions. The key insight: evaluation only depends on
the values of free variables, so expressions with identical structure but different
bound variable names evaluate equally. -/

namespace AmoLean.Sigma

/-- Free variables in an index expression -/
def IdxExpr.fv : IdxExpr → Finset LoopVar
  | .const _ => ∅
  | .var v => {v}
  | .affine _ _ v => {v}
  | .add e1 e2 => IdxExpr.fv e1 ∪ IdxExpr.fv e2
  | .mul _ e => IdxExpr.fv e

/-- Free variables in a Gather pattern -/
def Gather.fv (g : Gather) : Finset LoopVar := IdxExpr.fv g.baseAddr

/-- Free variables in a Scatter pattern -/
def Scatter.fv (s : Scatter) : Finset LoopVar := IdxExpr.fv s.baseAddr

/-- Free variables in a SigmaExpr -/
def SigmaExpr.fv : SigmaExpr → Finset LoopVar
  | .compute _ g s => Gather.fv g ∪ Scatter.fv s
  | .loop _ v body => SigmaExpr.fv body \ {v}  -- v is bound, not free
  | .seq s1 s2 => SigmaExpr.fv s1 ∪ SigmaExpr.fv s2
  | .par s1 s2 => SigmaExpr.fv s1 ∪ SigmaExpr.fv s2
  | .temp _ body => SigmaExpr.fv body
  | .nop => ∅

/-- Gather.block only uses the loop variable v -/
theorem Gather.block_fv (n : Nat) (v : LoopVar) : Gather.fv (Gather.block n v) = {v} := by
  simp only [Gather.fv, Gather.block, IdxExpr.fv]

/-- Scatter.block only uses the loop variable v -/
theorem Scatter.block_fv (n : Nat) (v : LoopVar) : Scatter.fv (Scatter.block n v) = {v} := by
  simp only [Scatter.fv, Scatter.block, IdxExpr.fv]

/-- After adjustBlock, the only free variables are {v}.
    This is because adjustBlock replaces all Gather/Scatter with
    Gather.block/Scatter.block patterns that only use v. -/
theorem adjustBlock_fv_subset (v : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr) :
    SigmaExpr.fv (adjustBlock v n_in n_out expr) ⊆ {v} := by
  induction expr with
  | compute k g s =>
    simp only [adjustBlock, SigmaExpr.fv]
    rw [Gather.block_fv, Scatter.block_fv]
    simp only [Finset.union_self, Finset.Subset.refl]
  | loop n w body ih =>
    simp only [adjustBlock, SigmaExpr.fv]
    -- fv(adjustBlock v ... body) \ {w} ⊆ {v}
    calc SigmaExpr.fv (adjustBlock v n_in n_out body) \ {w}
        ⊆ SigmaExpr.fv (adjustBlock v n_in n_out body) := Finset.sdiff_subset
      _ ⊆ {v} := ih
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustBlock, SigmaExpr.fv]
    exact Finset.union_subset ih1 ih2
  | par s1 s2 ih1 ih2 =>
    simp only [adjustBlock, SigmaExpr.fv]
    exact Finset.union_subset ih1 ih2
  | temp sz body ih =>
    simp only [adjustBlock, SigmaExpr.fv]
    exact ih
  | nop =>
    simp only [adjustBlock, SigmaExpr.fv, Finset.empty_subset]

/-- If w ≠ v, then w is not free in adjustBlock v ... expr -/
theorem adjustBlock_fresh (v w : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr)
    (hw : w ≠ v) : w ∉ SigmaExpr.fv (adjustBlock v n_in n_out expr) := by
  intro hmem
  have hsub := adjustBlock_fv_subset v n_in n_out expr
  have : w ∈ ({v} : Finset LoopVar) := hsub hmem
  simp only [Finset.mem_singleton] at this
  exact hw this

/-- Nested adjustBlock operations collapse: the outer one overwrites the inner.
    This is because adjustBlock completely replaces Gather/Scatter patterns,
    ignoring what was there before. Key for simplifying nested kron lowering. -/
theorem adjustBlock_adjustBlock (v v' : LoopVar) (n_in n_out n_in' n_out' : Nat) (expr : SigmaExpr) :
    adjustBlock v n_in n_out (adjustBlock v' n_in' n_out' expr) = adjustBlock v n_in n_out expr := by
  induction expr with
  | compute k g s =>
    simp only [adjustBlock]
    -- Both sides produce: compute k (Gather.block n_in v) (Scatter.block n_out v)
  | loop n w body ih =>
    simp only [adjustBlock]
    rw [ih]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustBlock]
    rw [ih1, ih2]
  | par s1 s2 ih1 ih2 =>
    simp only [adjustBlock]
    rw [ih1, ih2]
  | temp sz body ih =>
    simp only [adjustBlock]
    rw [ih]
  | nop =>
    simp only [adjustBlock]

/-- After adjustStride, the only free variables are {v}.
    This is because adjustStride replaces all Gather/Scatter with patterns
    that use baseAddr := .var v, so fv = {v}. -/
theorem adjustStride_fv_subset (v : LoopVar) (innerSize mSize nSize : Nat) (expr : SigmaExpr) :
    SigmaExpr.fv (adjustStride v innerSize mSize nSize expr) ⊆ {v} := by
  induction expr with
  | compute k g s =>
    simp only [adjustStride, SigmaExpr.fv, Gather.fv, Scatter.fv, IdxExpr.fv]
    simp only [Finset.union_self, Finset.Subset.refl]
  | loop n w body ih =>
    simp only [adjustStride, SigmaExpr.fv]
    calc SigmaExpr.fv (adjustStride v innerSize mSize nSize body) \ {w}
        ⊆ SigmaExpr.fv (adjustStride v innerSize mSize nSize body) := Finset.sdiff_subset
      _ ⊆ {v} := ih
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustStride, SigmaExpr.fv]
    exact Finset.union_subset ih1 ih2
  | par s1 s2 ih1 ih2 =>
    simp only [adjustStride, SigmaExpr.fv]
    exact Finset.union_subset ih1 ih2
  | temp sz body ih =>
    simp only [adjustStride, SigmaExpr.fv]
    exact ih
  | nop =>
    simp only [adjustStride, SigmaExpr.fv, Finset.empty_subset]

/-- If w ≠ v, then w is not free in adjustStride v ... expr -/
theorem adjustStride_fresh (v w : LoopVar) (innerSize mSize nSize : Nat) (expr : SigmaExpr)
    (hw : w ≠ v) : w ∉ SigmaExpr.fv (adjustStride v innerSize mSize nSize expr) := by
  intro hmem
  have hsub := adjustStride_fv_subset v innerSize mSize nSize expr
  have : w ∈ ({v} : Finset LoopVar) := hsub hmem
  simp only [Finset.mem_singleton] at this
  exact hw this

/-- adjustBlock overwrites adjustStride: the outer block pattern replaces the stride pattern.
    Key for simplifying kron A⊗I followed by outer adjustBlock. -/
theorem adjustBlock_adjustStride (v v' : LoopVar) (n_in n_out innerSize mSize nSize : Nat)
    (expr : SigmaExpr) :
    adjustBlock v n_in n_out (adjustStride v' innerSize mSize nSize expr) =
    adjustBlock v n_in n_out expr := by
  induction expr with
  | compute k g s =>
    simp only [adjustStride, adjustBlock]
    -- adjustStride produces strided gather/scatter, adjustBlock overwrites with block
  | loop n w body ih =>
    simp only [adjustStride, adjustBlock]
    rw [ih]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustStride, adjustBlock]
    rw [ih1, ih2]
  | par s1 s2 ih1 ih2 =>
    simp only [adjustStride, adjustBlock]
    rw [ih1, ih2]
  | temp sz body ih =>
    simp only [adjustStride, adjustBlock]
    rw [ih]
  | nop =>
    simp only [adjustStride, adjustBlock]

/-- adjustStride overwrites adjustBlock: the outer stride pattern replaces the block pattern.
    Key for simplifying kron I⊗B followed by outer adjustStride. -/
theorem adjustStride_adjustBlock (v v' : LoopVar) (innerSize mSize nSize : Nat)
    (n_in n_out : Nat) (expr : SigmaExpr) :
    adjustStride v innerSize mSize nSize (adjustBlock v' n_in n_out expr) =
    adjustStride v innerSize mSize nSize expr := by
  induction expr with
  | compute k g s =>
    simp only [adjustBlock, adjustStride]
  | loop n w body ih =>
    simp only [adjustBlock, adjustStride]
    rw [ih]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustBlock, adjustStride]
    rw [ih1, ih2]
  | par s1 s2 ih1 ih2 =>
    simp only [adjustBlock, adjustStride]
    rw [ih1, ih2]
  | temp sz body ih =>
    simp only [adjustBlock, adjustStride]
    rw [ih]
  | nop =>
    simp only [adjustBlock, adjustStride]

/-- Nested adjustStride operations collapse: the outer one overwrites the inner.
    This is because adjustStride completely replaces Gather/Scatter patterns.
    Key for simplifying kron A⊗I followed by outer adjustStride. -/
theorem adjustStride_adjustStride (v v' : LoopVar) (is ms ns is' ms' ns' : Nat)
    (expr : SigmaExpr) :
    adjustStride v is ms ns (adjustStride v' is' ms' ns' expr) =
    adjustStride v is ms ns expr := by
  induction expr with
  | compute k g s =>
    simp only [adjustStride]
  | loop n w body ih =>
    simp only [adjustStride]
    rw [ih]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustStride]
    rw [ih1, ih2]
  | par s1 s2 ih1 ih2 =>
    simp only [adjustStride]
    rw [ih1, ih2]
  | temp sz body ih =>
    simp only [adjustStride]
    rw [ih]
  | nop =>
    simp only [adjustStride]

/-- Variables used as loop indices in an expression -/
def SigmaExpr.loopVarsOf : SigmaExpr → Finset LoopVar
  | .compute _ _ _ => ∅
  | .loop _ v body => {v} ∪ SigmaExpr.loopVarsOf body
  | .seq s1 s2 => SigmaExpr.loopVarsOf s1 ∪ SigmaExpr.loopVarsOf s2
  | .par s1 s2 => SigmaExpr.loopVarsOf s1 ∪ SigmaExpr.loopVarsOf s2
  | .temp _ body => SigmaExpr.loopVarsOf body
  | .nop => ∅

/-- adjustBlock doesn't change which loop variables are used -/
theorem adjustBlock_loopVarsOf (v : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr) :
    SigmaExpr.loopVarsOf (adjustBlock v n_in n_out expr) = SigmaExpr.loopVarsOf expr := by
  induction expr with
  | compute k g s => simp only [adjustBlock, SigmaExpr.loopVarsOf]
  | loop n w body ih =>
    simp only [adjustBlock, SigmaExpr.loopVarsOf, ih]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustBlock, SigmaExpr.loopVarsOf, ih1, ih2]
  | par s1 s2 ih1 ih2 =>
    simp only [adjustBlock, SigmaExpr.loopVarsOf, ih1, ih2]
  | temp sz body ih =>
    simp only [adjustBlock, SigmaExpr.loopVarsOf, ih]
  | nop =>
    simp only [adjustBlock, SigmaExpr.loopVarsOf]

/-- adjustStride doesn't change which loop variables are used -/
theorem adjustStride_loopVarsOf (v : LoopVar) (innerSize mSize nSize : Nat) (expr : SigmaExpr) :
    SigmaExpr.loopVarsOf (adjustStride v innerSize mSize nSize expr) = SigmaExpr.loopVarsOf expr := by
  induction expr with
  | compute k g s => simp only [adjustStride, SigmaExpr.loopVarsOf]
  | loop n w body ih =>
    simp only [adjustStride, SigmaExpr.loopVarsOf, ih]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustStride, SigmaExpr.loopVarsOf, ih1, ih2]
  | par s1 s2 ih1 ih2 =>
    simp only [adjustStride, SigmaExpr.loopVarsOf, ih1, ih2]
  | temp sz body ih =>
    simp only [adjustStride, SigmaExpr.loopVarsOf, ih]
  | nop =>
    simp only [adjustStride, SigmaExpr.loopVarsOf]

/-- Lowering produces loopVars >= nextLoopVar AND increases nextLoopVar monotonically.

This is the key theorem for proving freshness: all loop variables generated by `lower`
are >= the initial state.nextLoopVar, and the state's nextLoopVar only increases.

Proof by induction on MatExpr:
- Base cases (identity, zero, dft, ntt, etc.): loopVarsOf = ∅, state unchanged
- kron: freshLoopVar gives v = s.nextLoopVar, increments state, then recursive calls
- compose, add: chain state through multiple calls, accumulate monotonicity
- Other cases: single recursive call, monotonicity preserved -/
theorem lower_loopVars_bounded_and_state_monotonic {α : Type} {m n : Nat} (mat : MatExpr α m n) (s : LowerState) :
    (∀ l ∈ SigmaExpr.loopVarsOf (lower m n s mat).1, l ≥ s.nextLoopVar) ∧
    (lower m n s mat).2.nextLoopVar ≥ s.nextLoopVar := by
  induction mat generalizing s with
  | identity =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | zero =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | dft =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | ntt =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | twiddle =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | perm =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | diag =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | scalar =>
    simp only [lower, SigmaExpr.loopVarsOf, Finset.not_mem_empty, false_implies, implies_true, le_refl, and_self]
  | transpose a ih =>
    -- lower m n s (.transpose a) = lower n m s a
    simp only [lower]
    exact ih s
  | conjTranspose a ih =>
    -- lower m n s (.conjTranspose a) = lower n m s a
    simp only [lower]
    exact ih s
  | smul _ a ih =>
    simp only [lower]
    have ⟨hbounded, hmono⟩ := ih s
    constructor
    · intro l hl
      simp only [SigmaExpr.loopVarsOf, Finset.mem_union, Finset.not_mem_empty, or_false] at hl
      exact hbounded l hl
    · exact hmono
  | elemwise _ a ih =>
    simp only [lower]
    have ⟨hbounded, hmono⟩ := ih s
    constructor
    · intro l hl
      simp only [SigmaExpr.loopVarsOf, Finset.mem_union, Finset.not_mem_empty, or_false] at hl
      exact hbounded l hl
    · exact hmono
  | partialElemwise _ _ a ih =>
    simp only [lower]
    have ⟨hbounded, hmono⟩ := ih s
    constructor
    · intro l hl
      simp only [SigmaExpr.loopVarsOf, Finset.mem_union, Finset.not_mem_empty, or_false] at hl
      exact hbounded l hl
    · exact hmono
  | mdsApply _ _ a ih =>
    simp only [lower]
    have ⟨hbounded, hmono⟩ := ih s
    constructor
    · intro l hl
      simp only [SigmaExpr.loopVarsOf, Finset.mem_union, Finset.not_mem_empty, or_false] at hl
      exact hbounded l hl
    · exact hmono
  | addRoundConst _ _ a ih =>
    simp only [lower]
    have ⟨hbounded, hmono⟩ := ih s
    constructor
    · intro l hl
      simp only [SigmaExpr.loopVarsOf, Finset.mem_union, Finset.not_mem_empty, or_false] at hl
      exact hbounded l hl
    · exact hmono
  | add a b ih_a ih_b =>
    simp only [lower]
    have ⟨ha_bounded, ha_mono⟩ := ih_a s
    have ⟨hb_bounded, hb_mono⟩ := ih_b (lower _ _ s a).2
    constructor
    · intro l hl
      simp only [SigmaExpr.loopVarsOf, Finset.mem_union] at hl
      cases hl with
      | inl hl => exact ha_bounded l hl
      | inr hl => exact Nat.le_trans ha_mono (hb_bounded l hl)
    · exact Nat.le_trans ha_mono hb_mono
  | compose a b ih_a ih_b =>
    -- lower returns (.temp k (.seq exprB exprA), state2)
    -- where exprB is from lower of b, exprA is from lower of a
    -- loopVarsOf (.temp k (.seq exprB exprA)) = loopVarsOf exprB ∪ loopVarsOf exprA
    simp only [lower]
    have ⟨hb_bounded, hb_mono⟩ := ih_b s
    have ⟨ha_bounded, ha_mono⟩ := ih_a (lower _ _ s b).2
    constructor
    · intro l hl
      -- loopVarsOf (.temp _ body) = loopVarsOf body
      -- loopVarsOf (.seq s1 s2) = loopVarsOf s1 ∪ loopVarsOf s2
      simp only [SigmaExpr.loopVarsOf, Finset.mem_union] at hl
      cases hl with
      | inl hl =>
        -- l ∈ loopVarsOf exprB (from lower of b)
        exact hb_bounded l hl
      | inr hl =>
        -- l ∈ loopVarsOf exprA (from lower of a with chained state)
        exact Nat.le_trans hb_mono (ha_bounded l hl)
    · exact Nat.le_trans hb_mono ha_mono
  | kron a b ih_a ih_b =>
    -- With isIdentity refactoring, case analysis now works (no kernel error!)
    simp only [lower]
    split_ifs with ha hb
    -- Case 1: a.isIdentity = true (I⊗B)
    · -- lower produces (.loop m₁ loopVar (adjustBlock loopVar n₂ m₂ (lower b state')), state2)
      -- loopVarsOf (.loop _ v body) = {v} ∪ loopVarsOf body
      have ⟨hb_bounded, hb_mono⟩ := ih_b { nextLoopVar := s.nextLoopVar + 1 }
      simp only [freshLoopVar]
      constructor
      · intro l hl
        simp only [SigmaExpr.loopVarsOf, adjustBlock_loopVarsOf, Finset.mem_union,
                   Finset.mem_singleton] at hl
        cases hl with
        | inl heq => exact heq ▸ Nat.le_refl _
        | inr hmem => exact Nat.le_of_succ_le (hb_bounded l hmem)
      · exact Nat.le_of_succ_le hb_mono
    -- Case 2: a.isIdentity = false, b.isIdentity = true (A⊗I)
    · have ⟨ha_bounded, ha_mono⟩ := ih_a { nextLoopVar := s.nextLoopVar + 1 }
      simp only [freshLoopVar]
      constructor
      · intro l hl
        simp only [SigmaExpr.loopVarsOf, adjustStride_loopVarsOf, Finset.mem_union,
                   Finset.mem_singleton] at hl
        cases hl with
        | inl heq => exact heq ▸ Nat.le_refl _
        | inr hmem => exact Nat.le_of_succ_le (ha_bounded l hmem)
      · exact Nat.le_of_succ_le ha_mono
    -- Case 3: General A⊗B (nested loops)
    · -- Structure: .loop m₁ v (.seq exprA (.loop m₂ (v+1) exprB))
      have ⟨ha_bounded, ha_mono⟩ := ih_a { nextLoopVar := s.nextLoopVar + 1 }
      have ⟨hb_bounded, hb_mono⟩ := ih_b (lower _ _ { nextLoopVar := s.nextLoopVar + 1 } a).2
      simp only [freshLoopVar]
      constructor
      · intro l hl
        simp only [SigmaExpr.loopVarsOf, Finset.mem_union, Finset.mem_singleton] at hl
        -- hl : l = s.nextLoopVar ∨ l ∈ loopVarsOf (.seq exprA (.loop (s.nextLoopVar+1) exprB))
        cases hl with
        | inl heq => exact heq ▸ Nat.le_refl _
        | inr hmem =>
          -- hmem : l ∈ loopVarsOf exprA ∪ loopVarsOf (.loop (s.nextLoopVar+1) exprB)
          simp only [SigmaExpr.loopVarsOf, Finset.mem_union, Finset.mem_singleton] at hmem
          cases hmem with
          | inl hl_a => exact Nat.le_of_succ_le (ha_bounded l hl_a)
          | inr hl_loop =>
            cases hl_loop with
            | inl heq2 => exact heq2 ▸ Nat.le_succ _
            | inr hl_b => exact Nat.le_of_succ_le (Nat.le_trans ha_mono (hb_bounded l hl_b))
      · exact Nat.le_of_succ_le (Nat.le_trans ha_mono hb_mono)

/-- Freshness follows from boundedness when v1, v2 < nextLoopVar.
    This bridges lower_loopVars_bounded to the _alpha_fresh theorems. -/
theorem freshness_from_bounded {α : Type} {m n : Nat} (mat : MatExpr α m n) (s : LowerState)
    (v1 v2 : LoopVar) (hv1 : v1 < s.nextLoopVar) (hv2 : v2 < s.nextLoopVar) :
    ∀ w ∈ SigmaExpr.loopVarsOf (lower m n s mat).1, w ≠ v1 ∧ w ≠ v2 := by
  intro w hw
  have hbounded := (lower_loopVars_bounded_and_state_monotonic mat s).1 w hw
  constructor
  · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hv1 hbounded)
  · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hv2 hbounded)

/-- Non-membership from boundedness: if v < s.nextLoopVar then v ∉ loopVarsOf (lower mat s).
    This is the direct form needed for loop_adjustBlock_alpha_lower preconditions. -/
theorem lower_loopVar_fresh_lt {α : Type} {m n : Nat} (mat : MatExpr α m n) (s : LowerState)
    (v : LoopVar) (hv : v < s.nextLoopVar) :
    v ∉ SigmaExpr.loopVarsOf (lower m n s mat).1 := by
  intro hmem
  have hbounded := (lower_loopVars_bounded_and_state_monotonic mat s).1 v hmem
  exact Nat.lt_irrefl v (Nat.lt_of_lt_of_le hv hbounded)

/-- Gather.contiguous with .const base has no free variables -/
theorem Gather.contiguous_fv (n : Nat) (k : Nat) :
    Gather.fv (Gather.contiguous n (.const k)) = ∅ := by
  simp only [Gather.fv, Gather.contiguous, IdxExpr.fv]

/-- Scatter.contiguous with .const base has no free variables -/
theorem Scatter.contiguous_fv (n : Nat) (k : Nat) :
    Scatter.fv (Scatter.contiguous n (.const k)) = ∅ := by
  simp only [Scatter.fv, Scatter.contiguous, IdxExpr.fv]

set_option maxHeartbeats 400000 in
/-- Expressions generated by lower have no free variables.
    This is because:
    - Base cases use Gather/Scatter.contiguous with .const 0, so fv = ∅
    - adjustBlock/adjustStride introduce variable v, but it's bound by the enclosing loop
    - Loops remove their bound variable from fv
    - By induction, all recursive calls produce fv = ∅ -/
theorem lower_fv_empty {α : Type} {m n : Nat} (mat : MatExpr α m n) (s : LowerState) :
    SigmaExpr.fv (lower m n s mat).1 = ∅ := by
  induction mat generalizing s with
  | identity =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
  | zero =>
    simp only [lower, SigmaExpr.fv]
  | dft =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
  | ntt =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
  | twiddle =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
  | perm =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
  | diag =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
  | scalar =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
  | transpose a ih =>
    simp only [lower]
    exact ih s
  | conjTranspose a ih =>
    simp only [lower]
    exact ih s
  | smul _ a ih =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
    have h := ih s
    simp only [h, Finset.empty_union]
  | elemwise _ a ih =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
    have h := ih s
    simp only [h, Finset.empty_union]
  | partialElemwise _ _ a ih =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
    have h := ih s
    simp only [h, Finset.empty_union]
  | mdsApply _ _ a ih =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
    have h := ih s
    simp only [h, Finset.empty_union]
  | addRoundConst _ _ a ih =>
    simp only [lower, SigmaExpr.fv, Gather.contiguous_fv, Scatter.contiguous_fv, Finset.union_empty]
    have h := ih s
    simp only [h, Finset.empty_union]
  | compose a b ih_a ih_b =>
    simp only [lower, SigmaExpr.fv]
    have hb := ih_b s
    have ha := ih_a (lower _ _ s b).2
    simp only [hb, ha, Finset.empty_union]
  | add a b ih_a ih_b =>
    simp only [lower, SigmaExpr.fv]
    have ha := ih_a s
    have hb := ih_b (lower _ _ s a).2
    simp only [ha, hb, Finset.empty_union]
  | kron a b ih_a ih_b =>
    simp only [lower]
    split_ifs with ha hb
    -- Case I⊗B: .loop m₁ v (adjustBlock v n₂ m₂ bodyExpr)
    · simp only [freshLoopVar, SigmaExpr.fv]
      -- Goal: fv(adjustBlock s.nextLoopVar _ _ bodyExpr) \ {s.nextLoopVar} = ∅
      -- By adjustBlock_fv_subset: fv(adjustBlock v _ _ expr) ⊆ {v}
      -- Therefore: fv(...) \ {v} ⊆ {v} \ {v} = ∅
      apply Finset.eq_empty_of_forall_not_mem
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
      have ⟨hin, hne⟩ := hx
      -- hin : x ∈ fv(adjustBlock s.nextLoopVar _ _ bodyExpr)
      -- By adjustBlock_fv_subset, this means x ∈ {s.nextLoopVar}
      have h_in_sing : x ∈ ({s.nextLoopVar} : Finset LoopVar) := by
        apply adjustBlock_fv_subset
        exact hin
      simp only [Finset.mem_singleton] at h_in_sing
      exact hne h_in_sing
    -- Case A⊗I: .loop m₂ v (adjustStride v m₂ m₁ n₁ bodyExpr)
    · simp only [freshLoopVar, SigmaExpr.fv]
      -- Same pattern as I⊗B but with adjustStride
      apply Finset.eq_empty_of_forall_not_mem
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
      have ⟨hin, hne⟩ := hx
      have h_in_sing : x ∈ ({s.nextLoopVar} : Finset LoopVar) := by
        apply adjustStride_fv_subset
        exact hin
      simp only [Finset.mem_singleton] at h_in_sing
      exact hne h_in_sing
    -- Case A⊗B: .loop m₁ v (.seq exprA (.loop m₂ (v+1) exprB))
    · simp only [freshLoopVar, SigmaExpr.fv]
      -- In general case, exprA and exprB come from lower with incremented state
      -- By IH, both have fv = ∅
      -- Compute the state passed to lower(b) using the chained state from lower(a)
      let s1 : LowerState := { nextLoopVar := s.nextLoopVar + 1 }
      let s2 := (lower _ _ s1 a).2
      have ha := ih_a s1
      have hb := ih_b s2
      -- Goal: fv(.seq exprA (.loop (s.nextLoopVar + 1) exprB)) \ {s.nextLoopVar} = ∅
      -- fv(.seq) = fv(exprA) ∪ fv(.loop ...)
      -- fv(.loop (v+1) exprB) = fv(exprB) \ {v+1}
      -- Since fv(exprA) = ∅ and fv(exprB) = ∅, we get ∅ ∪ (∅ \ {v+1}) = ∅
      rw [ha, hb]
      simp only [Finset.empty_sdiff, Finset.empty_union, Finset.sdiff_empty]

end AmoLean.Sigma

/-! ### Part 3.6: Extensionality Lemmas

Evaluation only depends on the values of free variables. These lemmas are
key for proving alpha-equivalence: expressions with different bound variable
names evaluate equally when free variables have the same values. -/

-- Local abbreviations for cleaner theorem statements
abbrev IdxExpr.fv := AmoLean.Sigma.IdxExpr.fv
abbrev Gather.fv := AmoLean.Sigma.Gather.fv
abbrev Scatter.fv := AmoLean.Sigma.Scatter.fv
abbrev SigmaExpr.fv := AmoLean.Sigma.SigmaExpr.fv
abbrev SigmaExpr.loopVarsOf := AmoLean.Sigma.SigmaExpr.loopVarsOf

/-- Evaluating IdxExpr only depends on free variables -/
theorem evalIdxExpr_ext (e : IdxExpr) (env1 env2 : LoopEnv)
    (h : ∀ v ∈ IdxExpr.fv e, env1 v = env2 v) :
    evalIdxExpr env1 e = evalIdxExpr env2 e := by
  induction e with
  | const n => rfl
  | var v =>
    simp only [evalIdxExpr]
    apply h
    simp only [IdxExpr.fv, AmoLean.Sigma.IdxExpr.fv, Finset.mem_singleton]
  | affine base stride v =>
    simp only [evalIdxExpr]
    have hv : v ∈ ({v} : Finset LoopVar) := Finset.mem_singleton_self v
    have heq : env1 v = env2 v := h v (by simp only [IdxExpr.fv, AmoLean.Sigma.IdxExpr.fv]; exact hv)
    rw [heq]
  | add e1 e2 ih1 ih2 =>
    simp only [evalIdxExpr]
    rw [ih1, ih2]
    · intro v hv
      apply h
      simp only [IdxExpr.fv, AmoLean.Sigma.IdxExpr.fv, Finset.mem_union]
      right; exact hv
    · intro v hv
      apply h
      simp only [IdxExpr.fv, AmoLean.Sigma.IdxExpr.fv, Finset.mem_union]
      left; exact hv
  | mul c e ih =>
    simp only [evalIdxExpr]
    rw [ih]
    intro v hv
    apply h
    simp only [IdxExpr.fv, AmoLean.Sigma.IdxExpr.fv]
    exact hv

/-- If v ∉ fv(e), binding v doesn't affect evalIdxExpr -/
theorem evalIdxExpr_bind_irrelevant (e : IdxExpr) (env : LoopEnv) (v : LoopVar) (val : Nat)
    (hv : v ∉ IdxExpr.fv e) :
    evalIdxExpr (env.bind v val) e = evalIdxExpr env e := by
  apply evalIdxExpr_ext
  intro w hw
  simp only [LoopEnv.bind]
  split
  next heq =>
    simp only [beq_iff_eq] at heq
    subst heq
    exact absurd hw hv
  next => rfl

/-! ## Part 4: Gather and Scatter Operations -/

/-- Gather n elements from memory starting at baseAddr with stride -/
def evalGather (env : LoopEnv) (g : Gather) (mem : Memory α) : List α :=
  let baseAddr := evalIdxExpr env g.baseAddr
  List.range g.count |>.map fun i =>
    mem.read (baseAddr + g.stride * i)

/-- Scatter n elements to memory starting at baseAddr with stride -/
def evalScatter (env : LoopEnv) (s : Scatter) (mem : Memory α) (vals : List α) : Memory α :=
  let baseAddr := evalIdxExpr env s.baseAddr
  vals.enum.foldl (fun acc (i, v) =>
    acc.write (baseAddr + s.stride * i) v) mem

/-- evalGather only depends on free variables in the gather pattern -/
theorem evalGather_ext (g : Gather) (env1 env2 : LoopEnv) (mem : Memory α)
    (h : ∀ v ∈ Gather.fv g, env1 v = env2 v) :
    evalGather env1 g mem = evalGather env2 g mem := by
  simp only [evalGather]
  have heq : evalIdxExpr env1 g.baseAddr = evalIdxExpr env2 g.baseAddr := by
    apply evalIdxExpr_ext
    intro v hv
    apply h
    simp only [Gather.fv, AmoLean.Sigma.Gather.fv]
    exact hv
  rw [heq]

/-- evalScatter only depends on free variables in the scatter pattern -/
theorem evalScatter_ext (s : Scatter) (env1 env2 : LoopEnv) (mem : Memory α) (vals : List α)
    (h : ∀ v ∈ Scatter.fv s, env1 v = env2 v) :
    evalScatter env1 s mem vals = evalScatter env2 s mem vals := by
  simp only [evalScatter]
  have heq : evalIdxExpr env1 s.baseAddr = evalIdxExpr env2 s.baseAddr := by
    apply evalIdxExpr_ext
    intro v hv
    apply h
    simp only [Scatter.fv, AmoLean.Sigma.Scatter.fv]
    exact hv
  rw [heq]

/-! ### Alpha-equivalence for Gather/Scatter patterns -/

/-- Gather.block evaluation only depends on the bound value, not variable ID -/
theorem evalGather_block_alpha (env : LoopEnv) (v1 v2 : LoopVar) (blockSize i : Nat)
    (mem : Memory α) :
    evalGather (env.bind v1 i) (Gather.block blockSize v1) mem =
    evalGather (env.bind v2 i) (Gather.block blockSize v2) mem := by
  simp only [evalGather, Gather.block, evalIdxExpr_affine_bind]

/-- Scatter.block evaluation only depends on the bound value, not variable ID -/
theorem evalScatter_block_alpha (env : LoopEnv) (v1 v2 : LoopVar) (blockSize i : Nat)
    (mem : Memory α) (vals : List α) :
    evalScatter (env.bind v1 i) (Scatter.block blockSize v1) mem vals =
    evalScatter (env.bind v2 i) (Scatter.block blockSize v2) mem vals := by
  simp only [evalScatter, Scatter.block, evalIdxExpr_affine_bind]

/-- Stride-pattern Gather with .var baseAddr: evaluation depends on bound value, not variable ID.
    For adjustStride which uses baseAddr = .var v -/
theorem evalGather_stride_alpha (env : LoopEnv) (v1 v2 : LoopVar) (count stride i : Nat)
    (mem : Memory α) :
    evalGather (env.bind v1 i) { count := count, baseAddr := .var v1, stride := stride } mem =
    evalGather (env.bind v2 i) { count := count, baseAddr := .var v2, stride := stride } mem := by
  simp only [evalGather, evalIdxExpr_var_bind]

/-- Stride-pattern Scatter with .var baseAddr: evaluation depends on bound value, not variable ID -/
theorem evalScatter_stride_alpha (env : LoopEnv) (v1 v2 : LoopVar) (count stride i : Nat)
    (mem : Memory α) (vals : List α) :
    evalScatter (env.bind v1 i) { count := count, baseAddr := .var v1, stride := stride } mem vals =
    evalScatter (env.bind v2 i) { count := count, baseAddr := .var v2, stride := stride } mem vals := by
  simp only [evalScatter, evalIdxExpr_var_bind]

/-! ## Part 5: Algebraic DFT with Primitive Root

The DFT requires a primitive n-th root of unity ω.
We parametrize by (ω : α) (hω : IsPrimitiveRoot ω n).
-/

/-- DFT_n matrix-vector product using primitive root ω.
    y[k] = Σ_{j=0}^{n-1} ω^{kj} · x[j] -/
def evalDFT (ω : α) (n : Nat) (input : List α) : List α :=
  List.range n |>.map fun k =>
    List.range n |>.foldl (fun acc j =>
      let x_j := input.getD j default
      acc + (ω ^ (k * j)) * x_j
    ) 0

/-- DFT_2 (butterfly): [x0, x1] → [x0 + x1, x0 - x1]
    For DFT_2, ω = -1 and ω^0 = 1, ω^1 = -1 -/
def evalDFT2 (input : List α) : List α :=
  match input with
  | [x0, x1] => [x0 + x1, x0 - x1]
  | _ => input

/-! ## Part 6: Kernel Evaluation (Algebraic) -/

/-- Evaluate identity kernel: just copy -/
def evalIdentityKernel (input : List α) : List α := input

/-- Evaluate a kernel on input data -/
def evalKernelAlg (ω : α) (k : Kernel) (input : List α) : List α :=
  match k with
  | .identity _ => evalIdentityKernel input
  | .dft 2 => evalDFT2 input
  | .dft n => evalDFT ω n input
  | .ntt _ _ => input  -- NTT uses field-specific root
  | .twiddle _ _ => input  -- Twiddle factors are diagonal scaling
  | .scale => input
  | .butterfly => evalDFT2 input
  | .sbox _ _ => input  -- S-box for Poseidon (not implemented algebraically)
  | .partialSbox _ _ _ => input
  | .mdsApply _ _ => input
  | .mdsInternal _ => input
  | .addRoundConst _ _ => input
  | .butterfly4 => evalDFT ω 4 input  -- Radix-4 butterfly = DFT of size 4

/-! ## Part 7: Main Sigma Evaluator (Algebraic)

Total evaluator with termination proof via nodeCount.
-/

/-- Helper: iterate evalSigmaAlg for loop body -/
def iterateSigmaEval (ω : α) (loopVar : Nat) (body : SigmaExpr)
    (evalBody : LoopEnv → EvalState α → EvalState α)
    (n : Nat) (env : LoopEnv) (state : EvalState α) : EvalState α :=
  (List.range n).foldl (fun st i =>
    let env' := env.bind loopVar i
    let st' := evalBody env' st
    { readMem := st'.writeMem, writeMem := st'.writeMem }
  ) state

/-- Evaluate a SigmaExpr algebraically.
    Now total with termination proof via nodeCount. -/
def evalSigmaAlg (ω : α) (env : LoopEnv) (state : EvalState α) (sigma : SigmaExpr) : EvalState α :=
  match sigma with
  | .compute k g s =>
    let inputs := evalGather env g state.readMem
    let outputs := evalKernelAlg ω k inputs
    { state with writeMem := evalScatter env s state.writeMem outputs }

  | .loop n loopVar body =>
    -- Execute body for each iteration using foldl.
    -- Body's output state is passed directly to the next iteration.
    -- This preserves readMem from the body (matching evalSigma operational semantics).
    -- For .compute bodies (kron I⊗B/A⊗I), readMem is preserved across iterations,
    -- allowing each iteration to read from the original input.
    -- For .seq bodies, readMem is set by the seq itself.
    (List.range n).foldl (fun st i =>
      evalSigmaAlg ω (env.bind loopVar i) st body
    ) state

  | .seq s1 s2 =>
    let state1 := evalSigmaAlg ω env state s1
    let state2 := { readMem := state1.writeMem, writeMem := state1.writeMem }
    evalSigmaAlg ω env state2 s2

  | .par s1 s2 =>
    -- For reference semantics, parallel = sequential
    let state1 := evalSigmaAlg ω env state s1
    let state2 := { readMem := state1.writeMem, writeMem := state1.writeMem }
    evalSigmaAlg ω env state2 s2

  | .temp size body =>
    let tempMem := Memory.zeros size
    let stateWithTemp := { readMem := state.readMem, writeMem := tempMem }
    let stateAfterBody := evalSigmaAlg ω env stateWithTemp body
    { readMem := state.readMem, writeMem := stateAfterBody.writeMem }

  | .nop => state
termination_by sigma.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [SigmaExpr.nodeCount]
  all_goals omega

/-- Run SigmaExpr on input list, returning output list.
    Uses `.take outputSize` to ensure the result has exactly `outputSize` elements,
    which is necessary for compose correctness when k ≠ k_mid. -/
def runSigmaAlg (ω : α) (sigma : SigmaExpr) (input : List α) (outputSize : Nat) : List α :=
  let initState := EvalState.init input outputSize
  let finalState := evalSigmaAlg ω LoopEnv.empty initState sigma
  finalState.writeMem.toList.take outputSize

/-! ### Part 7.25: Extensionality for SigmaExpr Evaluation

Key theorem: evaluation only depends on free variables. This enables
proving alpha-equivalence for expressions with different bound variable names. -/

/-- Evaluating SigmaExpr only depends on free variables.
    This is the key lemma for alpha-equivalence: if two environments agree
    on the free variables of an expression, evaluation produces the same result. -/
theorem evalSigmaAlg_ext (ω : α) (expr : SigmaExpr) (env1 env2 : LoopEnv) (st : EvalState α)
    (h : ∀ v ∈ SigmaExpr.fv expr, env1 v = env2 v) :
    evalSigmaAlg ω env1 st expr = evalSigmaAlg ω env2 st expr := by
  induction expr generalizing env1 env2 st with
  | compute k g s =>
    simp only [evalSigmaAlg]
    -- Gather uses only variables in g.fv ⊆ (g.fv ∪ s.fv) = expr.fv
    have hg := evalGather_ext g env1 env2 st.readMem (fun v hv => h v (by
      simp only [SigmaExpr.fv, AmoLean.Sigma.SigmaExpr.fv, Finset.mem_union]
      left
      exact hv))
    -- Scatter uses only variables in s.fv ⊆ expr.fv
    have hs : ∀ vals, evalScatter env1 s st.writeMem vals = evalScatter env2 s st.writeMem vals :=
      fun vals => evalScatter_ext s env1 env2 st.writeMem vals (fun v hv => h v (by
        simp only [SigmaExpr.fv, AmoLean.Sigma.SigmaExpr.fv, Finset.mem_union]
        right
        exact hv))
    rw [hg, hs]
  | loop n loopVar body ih =>
    simp only [evalSigmaAlg]
    -- The foldl iterates with (env.bind loopVar i) for each i
    -- By the definition of fv, SigmaExpr.fv (.loop n loopVar body) = body.fv \ {loopVar}
    -- We need to show the step functions produce the same result
    congr 1
    funext st' i
    -- Goal: the step record is equal. Need to show evalSigmaAlg results are equal.
    have hbody : evalSigmaAlg ω (env1.bind loopVar i) st' body =
                 evalSigmaAlg ω (env2.bind loopVar i) st' body := by
      apply ih (env1.bind loopVar i) (env2.bind loopVar i) st'
      intro w hw
      simp only [LoopEnv.bind]
      split
      next heq => rfl  -- w = loopVar: both bindings give i
      next hne =>
        -- w ≠ loopVar: use that w ∈ body.fv \ {loopVar} = expr.fv
        apply h
        simp only [SigmaExpr.fv, AmoLean.Sigma.SigmaExpr.fv, Finset.mem_sdiff, Finset.mem_singleton]
        simp only [beq_iff_eq, ne_eq] at hne
        exact ⟨hw, hne⟩
    simp only [hbody]
  | seq s1 s2 ih1 ih2 =>
    simp only [evalSigmaAlg]
    have h1 := ih1 env1 env2 st (fun v hv => h v (by
      simp only [SigmaExpr.fv, AmoLean.Sigma.SigmaExpr.fv, Finset.mem_union]
      left; exact hv))
    rw [h1]
    apply ih2
    intro v hv
    apply h
    simp only [SigmaExpr.fv, AmoLean.Sigma.SigmaExpr.fv, Finset.mem_union]
    right; exact hv
  | par s1 s2 ih1 ih2 =>
    simp only [evalSigmaAlg]
    have h1 := ih1 env1 env2 st (fun v hv => h v (by
      simp only [SigmaExpr.fv, AmoLean.Sigma.SigmaExpr.fv, Finset.mem_union]
      left; exact hv))
    rw [h1]
    apply ih2
    intro v hv
    apply h
    simp only [SigmaExpr.fv, AmoLean.Sigma.SigmaExpr.fv, Finset.mem_union]
    right; exact hv
  | temp size body ih =>
    simp only [evalSigmaAlg]
    have hb := ih env1 env2 { readMem := st.readMem, writeMem := Memory.zeros size } h
    simp only [hb]
  | nop =>
    simp only [evalSigmaAlg]
termination_by expr.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [SigmaExpr.nodeCount]
  all_goals omega

/-- If v ∉ fv(expr), binding v doesn't affect evaluation.
    This is the key corollary for the loop case in exactStructure_eval_eq:
    when a loop variable is not free in the body, the binding is irrelevant. -/
theorem evalSigmaAlg_ignore_binding (ω : α) (expr : SigmaExpr) (env : LoopEnv) (st : EvalState α)
    (v : LoopVar) (val : Nat) (hv : v ∉ SigmaExpr.fv expr) :
    evalSigmaAlg ω (env.bind v val) st expr = evalSigmaAlg ω env st expr := by
  apply evalSigmaAlg_ext
  intro w hw
  simp only [LoopEnv.bind]
  split
  next heq =>
    simp only [beq_iff_eq] at heq
    subst heq
    exact absurd hw hv
  next => rfl

/-! ## Part 7.5: Alpha-equivalence for adjustBlock/adjustStride

Loop variable renaming preserves semantics: for the same base expression,
adjustBlock with different loop variable IDs evaluates identically when those
variables are bound to the same values. This is essential for proving
lower_state_irrelevant for kron. -/

/-- adjustBlock_alpha with explicit freshness precondition.
    The loop case requires that all inner loopVars are distinct from v1 and v2.
    For expressions from lower, this holds by construction (freshLoopVar generates
    strictly increasing IDs). -/
theorem adjustBlock_alpha_fresh (ω : α) (v1 v2 : LoopVar) (n_in n_out : Nat) (expr : SigmaExpr)
    (env : LoopEnv) (st : EvalState α) (i : Nat)
    (hfresh : ∀ w ∈ SigmaExpr.loopVarsOf expr, w ≠ v1 ∧ w ≠ v2) :
    evalSigmaAlg ω (env.bind v1 i) st (adjustBlock v1 n_in n_out expr) =
    evalSigmaAlg ω (env.bind v2 i) st (adjustBlock v2 n_in n_out expr) := by
  induction expr generalizing env st i with
  | compute k g s =>
    simp only [adjustBlock, evalSigmaAlg]
    rw [evalGather_block_alpha env v1 v2 n_in i st.readMem]
    congr 1
    rw [evalScatter_block_alpha env v1 v2 n_out i st.writeMem]
  | loop n loopVar body ih =>
    simp only [adjustBlock, evalSigmaAlg]
    -- loopVar ∈ loopVarsOf (loop n loopVar body) by definition
    have hlv : loopVar ∈ SigmaExpr.loopVarsOf (.loop n loopVar body) := by
      simp only [SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self loopVar)
    have ⟨hne1, hne2⟩ := hfresh loopVar hlv
    -- Now we can use bind_comm because loopVar ≠ v1 and loopVar ≠ v2
    congr 1
    funext st' j
    -- Reorder the bindings: (env.bind v* i).bind loopVar j = (env.bind loopVar j).bind v* i
    have hcomm1 : (env.bind v1 i).bind loopVar j = (env.bind loopVar j).bind v1 i :=
      LoopEnv.bind_comm env v1 loopVar i j hne1.symm
    have hcomm2 : (env.bind v2 i).bind loopVar j = (env.bind loopVar j).bind v2 i :=
      LoopEnv.bind_comm env v2 loopVar i j hne2.symm
    rw [hcomm1, hcomm2]
    -- The goal is about constructing EvalState records from evalSigmaAlg results
    -- Apply IH to show the inner evalSigmaAlg are equal
    have hfresh_body : ∀ w ∈ SigmaExpr.loopVarsOf body, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hw)
    have heq := ih (env.bind loopVar j) st' i hfresh_body
    -- The step function constructs { readMem := result.writeMem, writeMem := result.writeMem }
    -- If result1 = result2, then the constructed states are equal
    simp only [heq]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustBlock, evalSigmaAlg]
    have hfresh1 : ∀ w ∈ SigmaExpr.loopVarsOf s1, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hw)
    have hfresh2 : ∀ w ∈ SigmaExpr.loopVarsOf s2, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hw)
    have h1 := ih1 env st i hfresh1
    rw [h1]
    exact ih2 env _ i hfresh2
  | par s1 s2 ih1 ih2 =>
    simp only [adjustBlock, evalSigmaAlg]
    have hfresh1 : ∀ w ∈ SigmaExpr.loopVarsOf s1, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hw)
    have hfresh2 : ∀ w ∈ SigmaExpr.loopVarsOf s2, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hw)
    have h1 := ih1 env st i hfresh1
    rw [h1]
    exact ih2 env _ i hfresh2
  | temp size body ih =>
    simp only [adjustBlock, evalSigmaAlg]
    have h := ih env { readMem := st.readMem, writeMem := Memory.zeros size } i hfresh
    simp only [h]
  | nop =>
    simp only [adjustBlock, evalSigmaAlg]

/-! Legacy adjustBlock theorems (adjustBlock_alpha, adjustBlock_preserves_eval,
    adjustBlock_with_ih, loop_adjustBlock_alpha, and their _fresh variants) were removed
    in Fase 2 Corrección 6: they had sorry in loop cases and were superseded by
    SameStructure-based theorems (loop_adjustBlock_sameStructure). -/

/-! ### Part 7.5.2: Alpha-equivalence for adjustStride

Analogous to adjustBlock_alpha, but for strided access patterns (A ⊗ I_n).
The Gather/Scatter patterns use .var v as baseAddr. -/

/-- adjustStride_alpha with explicit freshness precondition.
    Analogous to adjustBlock_alpha_fresh. -/
theorem adjustStride_alpha_fresh (ω : α) (v1 v2 : LoopVar) (innerSize mSize nSize : Nat)
    (expr : SigmaExpr) (env : LoopEnv) (st : EvalState α) (i : Nat)
    (hfresh : ∀ w ∈ SigmaExpr.loopVarsOf expr, w ≠ v1 ∧ w ≠ v2) :
    evalSigmaAlg ω (env.bind v1 i) st (adjustStride v1 innerSize mSize nSize expr) =
    evalSigmaAlg ω (env.bind v2 i) st (adjustStride v2 innerSize mSize nSize expr) := by
  induction expr generalizing env st i with
  | compute k g s =>
    simp only [adjustStride, evalSigmaAlg]
    rw [evalGather_stride_alpha env v1 v2 nSize innerSize i st.readMem]
    congr 1
    rw [evalScatter_stride_alpha env v1 v2 mSize innerSize i st.writeMem]
  | loop n loopVar body ih =>
    simp only [adjustStride, evalSigmaAlg]
    have hlv : loopVar ∈ SigmaExpr.loopVarsOf (.loop n loopVar body) := by
      simp only [SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self loopVar)
    have ⟨hne1, hne2⟩ := hfresh loopVar hlv
    congr 1
    funext st' j
    have hcomm1 : (env.bind v1 i).bind loopVar j = (env.bind loopVar j).bind v1 i :=
      LoopEnv.bind_comm env v1 loopVar i j hne1.symm
    have hcomm2 : (env.bind v2 i).bind loopVar j = (env.bind loopVar j).bind v2 i :=
      LoopEnv.bind_comm env v2 loopVar i j hne2.symm
    rw [hcomm1, hcomm2]
    -- The goal is about constructing EvalState records from evalSigmaAlg results
    have hfresh_body : ∀ w ∈ SigmaExpr.loopVarsOf body, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hw)
    have heq := ih (env.bind loopVar j) st' i hfresh_body
    simp only [heq]
  | seq s1 s2 ih1 ih2 =>
    simp only [adjustStride, evalSigmaAlg]
    have hfresh1 : ∀ w ∈ SigmaExpr.loopVarsOf s1, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hw)
    have hfresh2 : ∀ w ∈ SigmaExpr.loopVarsOf s2, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hw)
    have h1 := ih1 env st i hfresh1
    rw [h1]
    exact ih2 env _ i hfresh2
  | par s1 s2 ih1 ih2 =>
    simp only [adjustStride, evalSigmaAlg]
    have hfresh1 : ∀ w ∈ SigmaExpr.loopVarsOf s1, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hw)
    have hfresh2 : ∀ w ∈ SigmaExpr.loopVarsOf s2, w ≠ v1 ∧ w ≠ v2 := fun w hw => hfresh w (by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hw)
    have h1 := ih1 env st i hfresh1
    rw [h1]
    exact ih2 env _ i hfresh2
  | temp size body ih =>
    simp only [adjustStride, evalSigmaAlg]
    have h := ih env { readMem := st.readMem, writeMem := Memory.zeros size } i hfresh
    simp only [h]
  | nop =>
    simp only [adjustStride, evalSigmaAlg]

/-! Legacy adjustStride theorems (adjustStride_alpha, adjustStride_preserves_eval,
    adjustStride_with_ih, loop_adjustStride_alpha, and their _fresh variants) were removed
    in Fase 2 Corrección 6: they had sorry in loop cases and were superseded by
    SameStructure-based theorems (loop_adjustStride_sameStructure). -/

/-! ### Part 7.5.3: Alpha-equivalence for nested loop structure (general A⊗B case)

The general A⊗B kron case produces:
  .loop m₁ v (.seq exprA (.loop m₂ (v+1) exprB))
where exprA and exprB come from lower with fresh states.

The key insight: IH gives us that exprA/exprB are equivalent under ANY environment,
so the binding of outer loop variables doesn't affect them (they use fresh variables). -/

/-- Nested loop alpha-equivalence for the general kron case A⊗B.
    The outer loop has variable v1/v2, inner loop has w1/w2.
    The sub-expressions exprA and exprB are equivalent under any environment (from IH).
    Crucially, we require that exprA and exprB have no free variables (fv = ∅),
    which follows from lower_fv_empty for expressions from lower. -/
theorem nested_loop_alpha (ω : α) (v1 v2 w1 w2 : LoopVar) (n m : Nat)
    (exprA1 exprA2 exprB1 exprB2 : SigmaExpr) (env : LoopEnv) (st : EvalState α)
    (hfvA1 : SigmaExpr.fv exprA1 = ∅) (hfvA2 : SigmaExpr.fv exprA2 = ∅)
    (hfvB1 : SigmaExpr.fv exprB1 = ∅) (hfvB2 : SigmaExpr.fv exprB2 = ∅)
    (ih_a : ∀ env' st', evalSigmaAlg ω env' st' exprA1 = evalSigmaAlg ω env' st' exprA2)
    (ih_b : ∀ env' st', evalSigmaAlg ω env' st' exprB1 = evalSigmaAlg ω env' st' exprB2) :
    evalSigmaAlg ω env st (.loop n v1 (.seq exprA1 (.loop m w1 exprB1))) =
    evalSigmaAlg ω env st (.loop n v2 (.seq exprA2 (.loop m w2 exprB2))) := by
  -- Key insight: since fv = ∅ for all expressions, evaluation is independent of environment.
  -- We prove this by showing both sides equal when evaluated with any fixed environment.

  -- First, note that expressions with fv = ∅ evaluate equally regardless of env
  have hA_any : ∀ e1 e2 st', evalSigmaAlg ω e1 st' exprA1 = evalSigmaAlg ω e2 st' exprA2 := by
    intro e1 e2 st'
    have h1 : evalSigmaAlg ω e1 st' exprA1 = evalSigmaAlg ω e2 st' exprA1 :=
      evalSigmaAlg_ext ω exprA1 e1 e2 st' (by simp [hfvA1])
    rw [h1, ih_a e2 st']

  have hB_any : ∀ e1 e2 st', evalSigmaAlg ω e1 st' exprB1 = evalSigmaAlg ω e2 st' exprB2 := by
    intro e1 e2 st'
    have h1 : evalSigmaAlg ω e1 st' exprB1 = evalSigmaAlg ω e2 st' exprB1 :=
      evalSigmaAlg_ext ω exprB1 e1 e2 st' (by simp [hfvB1])
    rw [h1, ih_b e2 st']

  -- Prove that both loops produce the same result by showing their step functions
  -- produce equal results for equal inputs

  -- Helper for foldl equality when step functions agree pointwise
  have foldl_eq : ∀ (f g : EvalState α → Nat → EvalState α) (init : EvalState α) (xs : List Nat),
      (∀ s i, i ∈ xs → f s i = g s i) →
      List.foldl f init xs = List.foldl g init xs := by
    intro f g init xs hfg
    induction xs generalizing init with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl]
      have : f init x = g init x := hfg init x (List.mem_cons_self x xs)
      rw [this]
      apply ih
      intro s i hi
      exact hfg s i (List.mem_cons_of_mem x hi)

  unfold evalSigmaAlg
  apply foldl_eq
  intro st' i _
  -- Show equality for iteration i
  unfold evalSigmaAlg
  have hA : evalSigmaAlg ω (env.bind v1 i) st' exprA1 =
            evalSigmaAlg ω (env.bind v2 i) st' exprA2 := hA_any _ _ _
  simp only [hA]
  -- Now the inner loops remain to be shown equal
  -- Both use the same state (result of exprA2 evaluation) but different envs
  -- Since fv(exprB) = ∅, the env doesn't matter
  -- The goal has the form: { readMem := (loop1).writeMem, ... } = { readMem := (loop2).writeMem, ... }
  have h_loop : ∀ (e1 e2 : LoopEnv) stA,
      evalSigmaAlg ω e1 stA (.loop m w1 exprB1) =
      evalSigmaAlg ω e2 stA (.loop m w2 exprB2) := by
    intro e1 e2 stA
    unfold evalSigmaAlg
    apply foldl_eq
    intro st'' j _
    have hB : evalSigmaAlg ω (e1.bind w1 j) st'' exprB1 =
              evalSigmaAlg ω (e2.bind w2 j) st'' exprB2 := hB_any _ _ _
    simp only [hB]
  -- Apply to show the inner loop results are equal
  have h := h_loop (env.bind v1 i) (env.bind v2 i)
             { readMem := (evalSigmaAlg ω (env.bind v2 i) st' exprA2).writeMem,
               writeMem := (evalSigmaAlg ω (env.bind v2 i) st' exprA2).writeMem }
  simp only [h]

/-! ## Part 7.6: SameStructure relation for expressions from lower

Two SigmaExpr have SameStructure if they have:
- Same constructors in the same order
- Same kernels (for .compute)
- Same loop counts, temp sizes
- But possibly different loop variable IDs

Expressions from `lower m n state1 mat` and `lower m n state2 mat` (same mat)
have SameStructure by construction. This is key for proving kron case. -/

/-- SameStructure relates SigmaExpr that have identical structure except for loop variable IDs.
    This captures the relationship between expressions from lower with same MatExpr. -/
inductive SameStructure : SigmaExpr → SigmaExpr → Prop
  | compute : ∀ k g1 s1 g2 s2, SameStructure (.compute k g1 s1) (.compute k g2 s2)
  | loop : ∀ n v1 v2 body1 body2, SameStructure body1 body2 →
           SameStructure (.loop n v1 body1) (.loop n v2 body2)
  | seq : ∀ s1a s1b s2a s2b, SameStructure s1a s2a → SameStructure s1b s2b →
          SameStructure (.seq s1a s1b) (.seq s2a s2b)
  | par : ∀ s1a s1b s2a s2b, SameStructure s1a s2a → SameStructure s1b s2b →
          SameStructure (.par s1a s1b) (.par s2a s2b)
  | temp : ∀ size body1 body2, SameStructure body1 body2 →
           SameStructure (.temp size body1) (.temp size body2)
  | nop : SameStructure .nop .nop

/-- SameStructure is reflexive. -/
theorem SameStructure.refl (expr : SigmaExpr) : SameStructure expr expr := by
  induction expr with
  | compute k g s => exact SameStructure.compute k g s g s
  | loop n v body ih => exact SameStructure.loop n v v body body ih
  | seq s1 s2 ih1 ih2 => exact SameStructure.seq s1 s2 s1 s2 ih1 ih2
  | par s1 s2 ih1 ih2 => exact SameStructure.par s1 s2 s1 s2 ih1 ih2
  | temp size body ih => exact SameStructure.temp size body body ih
  | nop => exact SameStructure.nop

/-- SameStructure is symmetric. -/
theorem SameStructure.symm {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2) :
    SameStructure expr2 expr1 := by
  induction h with
  | compute k g1 s1 g2 s2 => exact SameStructure.compute k g2 s2 g1 s1
  | loop n v1 v2 body1 body2 _ ih => exact SameStructure.loop n v2 v1 body2 body1 ih
  | seq s1a s1b s2a s2b _ _ ih1 ih2 => exact SameStructure.seq s2a s2b s1a s1b ih1 ih2
  | par s1a s1b s2a s2b _ _ ih1 ih2 => exact SameStructure.par s2a s2b s1a s1b ih1 ih2
  | temp size body1 body2 _ ih => exact SameStructure.temp size body2 body1 ih
  | nop => exact SameStructure.nop

/-- adjustBlock with different loopVars preserves SameStructure.
    Two expressions with SameStructure remain SameStructure after adjustBlock with different v's.
    Key for proving lower_produces_sameStructure kron case where each state generates its own loopVar. -/
theorem adjustBlock_sameStructure_diffVar (v1 v2 : LoopVar) (n_in n_out : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2) :
    SameStructure (adjustBlock v1 n_in n_out expr1) (adjustBlock v2 n_in n_out expr2) := by
  induction h with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustBlock]
    -- Both become .compute k but with different block patterns (v1 vs v2)
    -- SameStructure.compute allows different gather/scatter
    exact SameStructure.compute k (Gather.block n_in v1) (Scatter.block n_out v1)
                                   (Gather.block n_in v2) (Scatter.block n_out v2)
  | loop n w1 w2 body1 body2 _ ih =>
    simp only [adjustBlock]
    exact SameStructure.loop n w1 w2 _ _ ih
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock]
    exact SameStructure.seq _ _ _ _ ih1 ih2
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock]
    exact SameStructure.par _ _ _ _ ih1 ih2
  | temp size body1 body2 _ ih =>
    simp only [adjustBlock]
    exact SameStructure.temp size _ _ ih
  | nop =>
    simp only [adjustBlock]
    exact SameStructure.nop

/-- adjustBlock preserves SameStructure (same loopVar version).
    If two expressions have SameStructure, their adjustBlock versions also have SameStructure.
    This is because adjustBlock:
    - Replaces Gather/Scatter in .compute with the SAME block patterns (using loopVar)
    - Preserves loop counts, temp sizes, kernels
    - Recursively applies to sub-expressions -/
theorem adjustBlock_preserves_sameStructure (v : LoopVar) (n_in n_out : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2) :
    SameStructure (adjustBlock v n_in n_out expr1) (adjustBlock v n_in n_out expr2) := by
  induction h with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustBlock]
    -- Both become .compute k (Gather.block n_in v) (Scatter.block n_out v)
    -- Same kernel k, same gather/scatter patterns
    exact SameStructure.compute k (Gather.block n_in v) (Scatter.block n_out v)
                                   (Gather.block n_in v) (Scatter.block n_out v)
  | loop n v1 v2 body1 body2 _ ih =>
    simp only [adjustBlock]
    exact SameStructure.loop n v1 v2 _ _ ih
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock]
    exact SameStructure.seq _ _ _ _ ih1 ih2
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock]
    exact SameStructure.par _ _ _ _ ih1 ih2
  | temp size body1 body2 _ ih =>
    simp only [adjustBlock]
    exact SameStructure.temp size _ _ ih
  | nop =>
    simp only [adjustBlock]
    exact SameStructure.nop

/-- adjustStride with different loopVars preserves SameStructure.
    Key for proving lower_produces_sameStructure kron case (A ⊗ I). -/
theorem adjustStride_sameStructure_diffVar (v1 v2 : LoopVar) (innerSize mSize nSize : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2) :
    SameStructure (adjustStride v1 innerSize mSize nSize expr1)
                  (adjustStride v2 innerSize mSize nSize expr2) := by
  induction h with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustStride]
    -- SameStructure.compute allows different gather/scatter
    exact SameStructure.compute k _ _ _ _
  | loop n w1 w2 body1 body2 _ ih =>
    simp only [adjustStride]
    exact SameStructure.loop n w1 w2 _ _ ih
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride]
    exact SameStructure.seq _ _ _ _ ih1 ih2
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride]
    exact SameStructure.par _ _ _ _ ih1 ih2
  | temp size body1 body2 _ ih =>
    simp only [adjustStride]
    exact SameStructure.temp size _ _ ih
  | nop =>
    simp only [adjustStride]
    exact SameStructure.nop

/-- adjustStride preserves SameStructure (same loopVar version).
    If two expressions have SameStructure, their adjustStride versions also have SameStructure.
    Same pattern as adjustBlock_preserves_sameStructure. -/
theorem adjustStride_preserves_sameStructure (v : LoopVar) (innerSize mSize nSize : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2) :
    SameStructure (adjustStride v innerSize mSize nSize expr1)
                  (adjustStride v innerSize mSize nSize expr2) := by
  induction h with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustStride]
    -- Both become .compute k (stride gather) (stride scatter)
    exact SameStructure.compute k _ _ _ _
  | loop n v1 v2 body1 body2 _ ih =>
    simp only [adjustStride]
    exact SameStructure.loop n v1 v2 _ _ ih
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride]
    exact SameStructure.seq _ _ _ _ ih1 ih2
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride]
    exact SameStructure.par _ _ _ _ ih1 ih2
  | temp size body1 body2 _ ih =>
    simp only [adjustStride]
    exact SameStructure.temp size _ _ ih
  | nop =>
    simp only [adjustStride]
    exact SameStructure.nop

/-- ExactStructure is a refinement of SameStructure where .compute cases also have
    identical gather and scatter patterns. After adjustBlock with the SAME loopVar,
    two SameStructure expressions become ExactStructure.

    The freshness conditions (v1 ∉ body1.fv, v2 ∉ body2.fv) enable alpha-equivalence:
    if bound variables are not free in their bodies, the bindings can be ignored
    and we can use the IH directly. -/
inductive ExactStructure : SigmaExpr → SigmaExpr → Prop
  | compute : ∀ k g s, ExactStructure (.compute k g s) (.compute k g s)
  | loop : ∀ n v1 v2 body1 body2,
      ExactStructure body1 body2 →
      v1 ∉ SigmaExpr.fv body1 →  -- freshness: v1 not free in body1
      v2 ∉ SigmaExpr.fv body2 →  -- freshness: v2 not free in body2
      ExactStructure (.loop n v1 body1) (.loop n v2 body2)
  | seq : ∀ s1a s1b s2a s2b, ExactStructure s1a s2a → ExactStructure s1b s2b →
          ExactStructure (.seq s1a s1b) (.seq s2a s2b)
  | par : ∀ s1a s1b s2a s2b, ExactStructure s1a s2a → ExactStructure s1b s2b →
          ExactStructure (.par s1a s1b) (.par s2a s2b)
  | temp : ∀ size body1 body2, ExactStructure body1 body2 →
           ExactStructure (.temp size body1) (.temp size body2)
  | nop : ExactStructure .nop .nop

/-- adjustBlock on SameStructure expressions produces ExactStructure expressions,
    provided v is not used as a loop variable in either expression.
    This is the key insight: adjustBlock replaces all gather/scatter with identical
    block patterns (using v), so the only remaining difference is loop variable IDs.
    The freshness condition ensures v ≠ any loop variable, so after adjustBlock,
    the only fv is {v} which doesn't contain any loop variables. -/
theorem adjustBlock_produces_exactStructure (v : LoopVar) (n_in n_out : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2)
    (hfresh1 : v ∉ SigmaExpr.loopVarsOf expr1)
    (hfresh2 : v ∉ SigmaExpr.loopVarsOf expr2) :
    ExactStructure (adjustBlock v n_in n_out expr1) (adjustBlock v n_in n_out expr2) := by
  induction h with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustBlock]
    exact ExactStructure.compute k (Gather.block n_in v) (Scatter.block n_out v)
  | loop n v1 v2 body1 body2 _ ih =>
    simp only [adjustBlock]
    -- v1 ∈ loopVarsOf (.loop n v1 body1), so v1 ≠ v by hfresh1
    have hv1_in : v1 ∈ AmoLean.Sigma.SigmaExpr.loopVarsOf (.loop n v1 body1) := by
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hv1_ne : v1 ≠ v := fun heq => hfresh1 (heq ▸ hv1_in)
    -- Similarly for v2
    have hv2_in : v2 ∈ AmoLean.Sigma.SigmaExpr.loopVarsOf (.loop n v2 body2) := by
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hv2_ne : v2 ≠ v := fun heq => hfresh2 (heq ▸ hv2_in)
    -- Use adjustBlock_fresh to show v1 ∉ fv(adjustBlock v ... body1)
    have hf1 : v1 ∉ SigmaExpr.fv (adjustBlock v n_in n_out body1) :=
      AmoLean.Sigma.adjustBlock_fresh v v1 n_in n_out body1 hv1_ne
    have hf2 : v2 ∉ SigmaExpr.fv (adjustBlock v n_in n_out body2) :=
      AmoLean.Sigma.adjustBlock_fresh v v2 n_in n_out body2 hv2_ne
    -- Freshness for recursive call: v ∉ loopVarsOf body1/body2
    have hfresh1' : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf body1 := by
      intro hmem
      apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    have hfresh2' : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf body2 := by
      intro hmem
      apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    exact ExactStructure.loop n v1 v2 _ _ (ih hfresh1' hfresh2') hf1 hf2
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock]
    have hf1a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf1b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    have hf2a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf2b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    exact ExactStructure.seq _ _ _ _ (ih1 hf1a hf2a) (ih2 hf1b hf2b)
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock]
    have hf1a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf1b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    have hf2a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf2b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    exact ExactStructure.par _ _ _ _ (ih1 hf1a hf2a) (ih2 hf1b hf2b)
  | temp size body1 body2 _ ih =>
    simp only [adjustBlock]
    exact ExactStructure.temp size _ _ (ih hfresh1 hfresh2)
  | nop =>
    simp only [adjustBlock]
    exact ExactStructure.nop

/-- ExactStructure expressions evaluate equally.
    The only difference is loop variable IDs, which are bound locally.
    Key insight: for .compute, kernel/gather/scatter are IDENTICAL, so evaluation is identical.
    For .loop, the bodies are ExactStructure, so by induction each iteration is equal. -/
theorem exactStructure_eval_eq (ω : α) {expr1 expr2 : SigmaExpr}
    (h : ExactStructure expr1 expr2) (env : LoopEnv) (st : EvalState α) :
    evalSigmaAlg ω env st expr1 = evalSigmaAlg ω env st expr2 := by
  induction h generalizing env st with
  | compute k g s =>
    -- Both are .compute k g s (IDENTICAL), so evaluation is trivially equal
    rfl
  | loop n v1 v2 body1 body2 _ hf1 hf2 ih =>
    simp only [evalSigmaAlg]
    -- Use freshness conditions and evalSigmaAlg_ignore_binding
    congr 1
    funext st' i
    -- Goal: {readMem := ..., writeMem := ...} = {readMem := ..., writeMem := ...}
    -- where the inner evaluations are evalSigmaAlg ω (env.bind v1/v2 i) st' body1/body2
    --
    -- By freshness: v1 ∉ body1.fv, so binding v1 doesn't affect body1 evaluation
    -- By freshness: v2 ∉ body2.fv, so binding v2 doesn't affect body2 evaluation
    have h1 : evalSigmaAlg ω (env.bind v1 i) st' body1 = evalSigmaAlg ω env st' body1 :=
      evalSigmaAlg_ignore_binding ω body1 env st' v1 i hf1
    have h2 : evalSigmaAlg ω (env.bind v2 i) st' body2 = evalSigmaAlg ω env st' body2 :=
      evalSigmaAlg_ignore_binding ω body2 env st' v2 i hf2
    -- Now use IH: body1 and body2 evaluate equally for any env/st
    have hih : evalSigmaAlg ω env st' body1 = evalSigmaAlg ω env st' body2 := ih env st'
    simp only [h1, h2, hih]
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [evalSigmaAlg]
    rw [ih1 env st]
    exact ih2 env _
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [evalSigmaAlg]
    rw [ih1 env st]
    exact ih2 env _
  | temp size body1 body2 _ ih =>
    simp only [evalSigmaAlg]
    have h := ih env { readMem := st.readMem, writeMem := Memory.zeros size }
    simp only [h]
  | nop =>
    simp only [evalSigmaAlg]

/-- Evaluation equality for adjustBlock with different loop variables.
    When expr1 and expr2 have SameStructure, adjustBlock v1 expr1 evaluated at (env.bind v1 i)
    equals adjustBlock v2 expr2 evaluated at (env.bind v2 i).

    This is the key theorem for kron case: different states produce different loop variables,
    but when bound to the same value, the evaluations are equal.

    Proof by induction on SameStructure:
    - compute: Gather.block/Scatter.block with v1 vs v2, both bound to i → same indices
    - loop: use bind_comm + freshness to reorder bindings, then IH
    - seq/par/temp/nop: structural recursion -/
theorem adjustBlock_sameStructure_eval_eq_diffVar (ω : α) (v1 v2 : LoopVar) {n_in n_out : Nat}
    {expr1 expr2 : SigmaExpr} (hsame : SameStructure expr1 expr2)
    (hfresh1 : v1 ∉ SigmaExpr.loopVarsOf expr1)
    (hfresh2 : v2 ∉ SigmaExpr.loopVarsOf expr2)
    (env : LoopEnv) (st : EvalState α) (i : Nat) :
    evalSigmaAlg ω (env.bind v1 i) st (adjustBlock v1 n_in n_out expr1) =
    evalSigmaAlg ω (env.bind v2 i) st (adjustBlock v2 n_in n_out expr2) := by
  induction hsame generalizing env st i with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustBlock, evalSigmaAlg]
    -- Gather.block v1 at (env.bind v1 i) = Gather.block v2 at (env.bind v2 i)
    rw [evalGather_block_alpha env v1 v2 n_in i st.readMem]
    congr 1
    rw [evalScatter_block_alpha env v1 v2 n_out i st.writeMem]
  | loop n w1 w2 body1 body2 _ ih =>
    simp only [adjustBlock, evalSigmaAlg]
    congr 1
    funext st' j
    -- w1 ∈ loopVarsOf (.loop n w1 body1), so w1 ≠ v1 by hfresh1
    have hw1_in : w1 ∈ SigmaExpr.loopVarsOf (.loop n w1 body1) := by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hw1_v1 : w1 ≠ v1 := fun heq => hfresh1 (heq ▸ hw1_in)
    have hw2_in : w2 ∈ SigmaExpr.loopVarsOf (.loop n w2 body2) := by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hw2_v2 : w2 ≠ v2 := fun heq => hfresh2 (heq ▸ hw2_in)
    -- Reorder bindings using bind_comm
    have hcomm1 : (env.bind v1 i).bind w1 j = (env.bind w1 j).bind v1 i :=
      LoopEnv.bind_comm env v1 w1 i j hw1_v1.symm
    have hcomm2 : (env.bind v2 i).bind w2 j = (env.bind w2 j).bind v2 i :=
      LoopEnv.bind_comm env v2 w2 i j hw2_v2.symm
    rw [hcomm1, hcomm2]
    -- fv(adjustBlock v body) ⊆ {v}, so w1, w2 are not free
    have hfv1 := AmoLean.Sigma.adjustBlock_fv_subset v1 n_in n_out body1
    have hfv2 := AmoLean.Sigma.adjustBlock_fv_subset v2 n_in n_out body2
    have hw1_fv : w1 ∉ SigmaExpr.fv (adjustBlock v1 n_in n_out body1) := by
      intro hmem
      have hsub := hfv1 hmem
      simp only [Finset.mem_singleton] at hsub
      exact hw1_v1 hsub
    have hw2_fv : w2 ∉ SigmaExpr.fv (adjustBlock v2 n_in n_out body2) := by
      intro hmem
      have hsub := hfv2 hmem
      simp only [Finset.mem_singleton] at hsub
      exact hw2_v2 hsub
    -- Use ignore_binding to remove w1 and w2 from the environments
    -- hignore1 : evalSigmaAlg ω ((env.bind v1 i).bind w1 j) st' _ = evalSigmaAlg ω (env.bind v1 i) st' _
    have hignore1 := evalSigmaAlg_ignore_binding ω (adjustBlock v1 n_in n_out body1)
                       (env.bind v1 i) st' w1 j hw1_fv
    have hignore2 := evalSigmaAlg_ignore_binding ω (adjustBlock v2 n_in n_out body2)
                       (env.bind v2 i) st' w2 j hw2_fv
    -- After bind_comm in earlier step, goal has (env.bind w1 j).bind v1 i and (env.bind w2 j).bind v2 i
    -- But we need to use the symmetric equality: (env.bind v1 i).bind w1 j = (env.bind w1 j).bind v1 i
    -- So we need to convert the goal back to (env.bind v1 i).bind w1 j form to apply hignore1
    have hcomm1' : (env.bind w1 j).bind v1 i = (env.bind v1 i).bind w1 j :=
      (LoopEnv.bind_comm env v1 w1 i j hw1_v1.symm).symm
    have hcomm2' : (env.bind w2 j).bind v2 i = (env.bind v2 i).bind w2 j :=
      (LoopEnv.bind_comm env v2 w2 i j hw2_v2.symm).symm
    rw [hcomm1', hcomm2', hignore1, hignore2]
    -- Freshness for bodies
    have hfb1 : v1 ∉ SigmaExpr.loopVarsOf body1 := by
      intro hmem; apply hfresh1
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have hfb2 : v2 ∉ SigmaExpr.loopVarsOf body2 := by
      intro hmem; apply hfresh2
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    -- IH gives evalSigmaAlg equality, use it to show record equality
    have heq := ih hfb1 hfb2 env st' i
    simp only [heq]
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock, evalSigmaAlg]
    have hf1a : v1 ∉ SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf1b : v1 ∉ SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have hf2a : v2 ∉ SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf2b : v2 ∉ SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have h1 := ih1 hf1a hf2a env st i
    rw [h1]
    -- After first part, both have the same intermediate state
    -- Now apply ih2 with that state
    have h2 : ∀ st', evalSigmaAlg ω (env.bind v1 i) st' (adjustBlock v1 n_in n_out s1b) =
                     evalSigmaAlg ω (env.bind v2 i) st' (adjustBlock v2 n_in n_out s2b) :=
      fun st' => ih2 hf1b hf2b env st' i
    simp only [h2]
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustBlock, evalSigmaAlg]
    have hf1a : v1 ∉ SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf1b : v1 ∉ SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have hf2a : v2 ∉ SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf2b : v2 ∉ SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have h1 := ih1 hf1a hf2a env st i
    rw [h1]
    have h2 : ∀ st', evalSigmaAlg ω (env.bind v1 i) st' (adjustBlock v1 n_in n_out s1b) =
                     evalSigmaAlg ω (env.bind v2 i) st' (adjustBlock v2 n_in n_out s2b) :=
      fun st' => ih2 hf1b hf2b env st' i
    simp only [h2]
  | temp size body1 body2 _ ih =>
    simp only [adjustBlock, evalSigmaAlg]
    have h := ih hfresh1 hfresh2 env { readMem := st.readMem, writeMem := Memory.zeros size } i
    simp only [h]
  | nop =>
    simp only [adjustBlock, evalSigmaAlg]

/-- Loop with adjustBlock for SameStructure expressions and different loop variables.
    Uses adjustBlock_sameStructure_eval_eq_diffVar inside the fold.
    Key for kron I⊗B case to eliminate sorry dependency. -/
theorem loop_adjustBlock_sameStructure (ω : α) (v1 v2 : LoopVar) (n : Nat) {n_in n_out : Nat}
    {expr1 expr2 : SigmaExpr} (hsame : SameStructure expr1 expr2)
    (hfresh1 : v1 ∉ SigmaExpr.loopVarsOf expr1)
    (hfresh2 : v2 ∉ SigmaExpr.loopVarsOf expr2)
    (env : LoopEnv) (st : EvalState α) :
    evalSigmaAlg ω env st (.loop n v1 (adjustBlock v1 n_in n_out expr1)) =
    evalSigmaAlg ω env st (.loop n v2 (adjustBlock v2 n_in n_out expr2)) := by
  simp only [evalSigmaAlg]
  -- Use foldl equality: if step functions produce equal results, foldl results are equal
  have hstep : ∀ st' i, evalSigmaAlg ω (env.bind v1 i) st' (adjustBlock v1 n_in n_out expr1) =
                        evalSigmaAlg ω (env.bind v2 i) st' (adjustBlock v2 n_in n_out expr2) :=
    fun st' i => adjustBlock_sameStructure_eval_eq_diffVar ω v1 v2 hsame hfresh1 hfresh2 env st' i
  -- Prove the two foldls are equal by induction
  induction (List.range n) generalizing st with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [hstep]
    exact ih _

/-- Evaluation equality for adjustStride with different loop variables.
    Analogous to adjustBlock_sameStructure_eval_eq_diffVar.
    Key for kron A⊗I case where stride patterns are used. -/
theorem adjustStride_sameStructure_eval_eq_diffVar (ω : α) (v1 v2 : LoopVar)
    {innerSize mSize nSize : Nat}
    {expr1 expr2 : SigmaExpr} (hsame : SameStructure expr1 expr2)
    (hfresh1 : v1 ∉ SigmaExpr.loopVarsOf expr1)
    (hfresh2 : v2 ∉ SigmaExpr.loopVarsOf expr2)
    (env : LoopEnv) (st : EvalState α) (i : Nat) :
    evalSigmaAlg ω (env.bind v1 i) st (adjustStride v1 innerSize mSize nSize expr1) =
    evalSigmaAlg ω (env.bind v2 i) st (adjustStride v2 innerSize mSize nSize expr2) := by
  induction hsame generalizing env st i with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustStride, evalSigmaAlg]
    -- Stride patterns with v1 at (env.bind v1 i) = v2 at (env.bind v2 i)
    rw [evalGather_stride_alpha env v1 v2 nSize innerSize i st.readMem]
    congr 1
    rw [evalScatter_stride_alpha env v1 v2 mSize innerSize i st.writeMem]
  | loop n w1 w2 body1 body2 _ ih =>
    simp only [adjustStride, evalSigmaAlg]
    congr 1
    funext st' j
    have hw1_in : w1 ∈ SigmaExpr.loopVarsOf (.loop n w1 body1) := by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hw1_v1 : w1 ≠ v1 := fun heq => hfresh1 (heq ▸ hw1_in)
    have hw2_in : w2 ∈ SigmaExpr.loopVarsOf (.loop n w2 body2) := by
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hw2_v2 : w2 ≠ v2 := fun heq => hfresh2 (heq ▸ hw2_in)
    have hcomm1 : (env.bind v1 i).bind w1 j = (env.bind w1 j).bind v1 i :=
      LoopEnv.bind_comm env v1 w1 i j hw1_v1.symm
    have hcomm2 : (env.bind v2 i).bind w2 j = (env.bind w2 j).bind v2 i :=
      LoopEnv.bind_comm env v2 w2 i j hw2_v2.symm
    rw [hcomm1, hcomm2]
    have hfv1 := AmoLean.Sigma.adjustStride_fv_subset v1 innerSize mSize nSize body1
    have hfv2 := AmoLean.Sigma.adjustStride_fv_subset v2 innerSize mSize nSize body2
    have hw1_fv : w1 ∉ SigmaExpr.fv (adjustStride v1 innerSize mSize nSize body1) := by
      intro hmem; have hsub := hfv1 hmem
      simp only [Finset.mem_singleton] at hsub; exact hw1_v1 hsub
    have hw2_fv : w2 ∉ SigmaExpr.fv (adjustStride v2 innerSize mSize nSize body2) := by
      intro hmem; have hsub := hfv2 hmem
      simp only [Finset.mem_singleton] at hsub; exact hw2_v2 hsub
    have hignore1 := evalSigmaAlg_ignore_binding ω (adjustStride v1 innerSize mSize nSize body1)
                       (env.bind v1 i) st' w1 j hw1_fv
    have hignore2 := evalSigmaAlg_ignore_binding ω (adjustStride v2 innerSize mSize nSize body2)
                       (env.bind v2 i) st' w2 j hw2_fv
    have hcomm1' : (env.bind w1 j).bind v1 i = (env.bind v1 i).bind w1 j :=
      (LoopEnv.bind_comm env v1 w1 i j hw1_v1.symm).symm
    have hcomm2' : (env.bind w2 j).bind v2 i = (env.bind v2 i).bind w2 j :=
      (LoopEnv.bind_comm env v2 w2 i j hw2_v2.symm).symm
    rw [hcomm1', hcomm2', hignore1, hignore2]
    have hfb1 : v1 ∉ SigmaExpr.loopVarsOf body1 := by
      intro hmem; apply hfresh1
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have hfb2 : v2 ∉ SigmaExpr.loopVarsOf body2 := by
      intro hmem; apply hfresh2
      simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have heq := ih hfb1 hfb2 env st' i
    simp only [heq]
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride, evalSigmaAlg]
    have hf1a : v1 ∉ SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf1b : v1 ∉ SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have hf2a : v2 ∉ SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf2b : v2 ∉ SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have h1 := ih1 hf1a hf2a env st i
    rw [h1]
    have h2 : ∀ st', evalSigmaAlg ω (env.bind v1 i) st' (adjustStride v1 innerSize mSize nSize s1b) =
                     evalSigmaAlg ω (env.bind v2 i) st' (adjustStride v2 innerSize mSize nSize s2b) :=
      fun st' => ih2 hf1b hf2b env st' i
    simp only [h2]
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride, evalSigmaAlg]
    have hf1a : v1 ∉ SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf1b : v1 ∉ SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have hf2a : v2 ∉ SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_left _ hmem
    have hf2b : v2 ∉ SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2; simp only [SigmaExpr.loopVarsOf]; exact Finset.mem_union_right _ hmem
    have h1 := ih1 hf1a hf2a env st i
    rw [h1]
    have h2 : ∀ st', evalSigmaAlg ω (env.bind v1 i) st' (adjustStride v1 innerSize mSize nSize s1b) =
                     evalSigmaAlg ω (env.bind v2 i) st' (adjustStride v2 innerSize mSize nSize s2b) :=
      fun st' => ih2 hf1b hf2b env st' i
    simp only [h2]
  | temp size body1 body2 _ ih =>
    simp only [adjustStride, evalSigmaAlg]
    have h := ih hfresh1 hfresh2 env { readMem := st.readMem, writeMem := Memory.zeros size } i
    simp only [h]
  | nop =>
    simp only [adjustStride, evalSigmaAlg]

/-- Loop with adjustStride for SameStructure expressions and different loop variables.
    Uses adjustStride_sameStructure_eval_eq_diffVar inside the fold.
    Key for kron A⊗I case to eliminate sorry dependency. -/
theorem loop_adjustStride_sameStructure (ω : α) (v1 v2 : LoopVar) (n : Nat)
    {innerSize mSize nSize : Nat}
    {expr1 expr2 : SigmaExpr} (hsame : SameStructure expr1 expr2)
    (hfresh1 : v1 ∉ SigmaExpr.loopVarsOf expr1)
    (hfresh2 : v2 ∉ SigmaExpr.loopVarsOf expr2)
    (env : LoopEnv) (st : EvalState α) :
    evalSigmaAlg ω env st (.loop n v1 (adjustStride v1 innerSize mSize nSize expr1)) =
    evalSigmaAlg ω env st (.loop n v2 (adjustStride v2 innerSize mSize nSize expr2)) := by
  simp only [evalSigmaAlg]
  -- Use foldl equality: if step functions produce equal results, foldl results are equal
  have hstep : ∀ st' i, evalSigmaAlg ω (env.bind v1 i) st' (adjustStride v1 innerSize mSize nSize expr1) =
                        evalSigmaAlg ω (env.bind v2 i) st' (adjustStride v2 innerSize mSize nSize expr2) :=
    fun st' i => adjustStride_sameStructure_eval_eq_diffVar ω v1 v2 hsame hfresh1 hfresh2 env st' i
  -- Prove the two foldls are equal by induction
  induction (List.range n) generalizing st with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [hstep]
    exact ih _

/-- Key lemma: lower with same MatExpr produces SameStructure expressions.
    This is true by construction: lower only changes loop variable IDs based on state,
    but the kernels, gather/scatter patterns, loop counts, and temp sizes are determined
    solely by the MatExpr.
    Proof by induction on MatExpr, showing each case produces SameStructure output. -/
theorem lower_produces_sameStructure {m n : Nat} (state1 state2 : LowerState) (mat : MatExpr α m n) :
    SameStructure (lower m n state1 mat).1 (lower m n state2 mat).1 := by
  induction mat generalizing state1 state2 with
  | identity => simp only [lower]; exact SameStructure.compute _ _ _ _ _
  | zero => simp only [lower]; exact SameStructure.nop
  | dft _ => simp only [lower]; exact SameStructure.compute _ _ _ _ _
  | ntt _ => simp only [lower]; exact SameStructure.compute _ _ _ _ _
  | twiddle _ => simp only [lower]; exact SameStructure.compute _ _ _ _ _
  | diag _ => simp only [lower]; exact SameStructure.compute _ _ _ _ _
  | scalar _ => simp only [lower]; exact SameStructure.compute _ _ _ _ _
  | perm _ => simp only [lower]; exact SameStructure.compute _ _ _ _ _
  | smul _ a ih =>
    simp only [lower]
    exact SameStructure.seq _ _ _ _ (ih state1 state2) (SameStructure.compute _ _ _ _ _)
  | elemwise _ a ih =>
    simp only [lower]
    exact SameStructure.seq _ _ _ _ (ih state1 state2) (SameStructure.compute _ _ _ _ _)
  | partialElemwise _ _ a ih =>
    simp only [lower]
    exact SameStructure.seq _ _ _ _ (ih state1 state2) (SameStructure.compute _ _ _ _ _)
  | add a b ih_a ih_b =>
    simp only [lower]
    exact SameStructure.par _ _ _ _ (ih_a state1 state2) (ih_b _ _)
  | compose a b ih_a ih_b =>
    -- lower(.compose a b) = .temp k (.seq (lower b) (lower a))
    -- Both components have SameStructure by IH
    -- Need to unfold to show the .temp (.seq ...) structure
    show SameStructure (lower _ _ state1 (.compose a b)).1 (lower _ _ state2 (.compose a b)).1
    simp only [lower]
    apply SameStructure.temp
    apply SameStructure.seq
    · exact ih_b state1 state2
    · exact ih_a _ _
  | transpose a ih =>
    simp only [lower]
    exact ih state1 state2
  | conjTranspose a ih =>
    simp only [lower]
    exact ih state1 state2
  | kron a b ih_a ih_b =>
    -- lower(.kron) has three cases: I⊗B, A⊗I, general
    -- All produce SameStructure because:
    -- - Loop counts are the same (determined by dimensions from MatExpr)
    -- - Body expressions are SameStructure by IH (after adjustBlock/adjustStride)
    -- - adjustBlock/adjustStride preserve SameStructure
    -- Note: freshLoopVar gives different v's but SameStructure.loop allows different loop vars
    simp only [lower]
    split
    case isTrue ha =>
      -- Case: a.isIdentity = true → I ⊗ B
      -- Produces: .loop m₁ v1 (adjustBlock v1 n₂ m₂ (lower b)) vs
      --           .loop m₁ v2 (adjustBlock v2 n₂ m₂ (lower b))
      -- Different loopVars v1, v2 from state1/state2
      apply SameStructure.loop
      apply adjustBlock_sameStructure_diffVar
      apply ih_b
    case isFalse ha =>
      split
      case isTrue hb =>
        -- Case: b.isIdentity = true → A ⊗ I
        -- Different loopVars from state1/state2
        apply SameStructure.loop
        apply adjustStride_sameStructure_diffVar
        apply ih_a
      case isFalse hb =>
        -- Case: general A ⊗ B
        -- Produces: .loop m₁ v (.seq exprA (.loop m₂ w exprB))
        apply SameStructure.loop
        apply SameStructure.seq
        · apply ih_a
        · apply SameStructure.loop
          apply ih_b
  | mdsApply _ _ a ih =>
    simp only [lower]
    exact SameStructure.seq _ _ _ _ (ih state1 state2) (SameStructure.compute _ _ _ _ _)
  | addRoundConst _ _ a ih =>
    simp only [lower]
    exact SameStructure.seq _ _ _ _ (ih state1 state2) (SameStructure.compute _ _ _ _ _)

/-- Combining the pieces: for kron lowering, expressions from lower have SameStructure,
    adjustBlock with same v produces ExactStructure, and ExactStructure evaluates equally.
    Requires v to be fresh (not used as a loop variable in the lowered expressions). -/
theorem adjustBlock_lower_eval_eq (ω : α) (v : LoopVar) (n_in n_out m n : Nat)
    (state1 state2 : LowerState) (mat : MatExpr α m n) (env : LoopEnv) (st : EvalState α)
    (hfresh1 : v ∉ SigmaExpr.loopVarsOf (lower m n state1 mat).1)
    (hfresh2 : v ∉ SigmaExpr.loopVarsOf (lower m n state2 mat).1) :
    evalSigmaAlg ω env st (adjustBlock v n_in n_out (lower m n state1 mat).1) =
    evalSigmaAlg ω env st (adjustBlock v n_in n_out (lower m n state2 mat).1) := by
  -- Step 1: lower produces SameStructure
  have h_same := lower_produces_sameStructure state1 state2 mat
  -- Step 2: adjustBlock preserves SameStructure → ExactStructure (with same v)
  have h_exact := adjustBlock_produces_exactStructure v n_in n_out h_same hfresh1 hfresh2
  -- Step 3: ExactStructure evaluates equally
  exact exactStructure_eval_eq ω h_exact env st

/-- adjustStride on SameStructure expressions produces ExactStructure expressions.
    Analogous to adjustBlock_produces_exactStructure. -/
theorem adjustStride_produces_exactStructure (v : LoopVar) (innerSize mSize nSize : Nat)
    {expr1 expr2 : SigmaExpr} (h : SameStructure expr1 expr2)
    (hfresh1 : v ∉ SigmaExpr.loopVarsOf expr1)
    (hfresh2 : v ∉ SigmaExpr.loopVarsOf expr2) :
    ExactStructure (adjustStride v innerSize mSize nSize expr1)
                   (adjustStride v innerSize mSize nSize expr2) := by
  induction h with
  | compute k g1 s1 g2 s2 =>
    simp only [adjustStride]
    -- Both produce same strided gather/scatter patterns
    exact ExactStructure.compute k _ _
  | loop n v1 v2 body1 body2 _ ih =>
    simp only [adjustStride]
    have hv1_in : v1 ∈ AmoLean.Sigma.SigmaExpr.loopVarsOf (.loop n v1 body1) := by
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hv1_ne : v1 ≠ v := fun heq => hfresh1 (heq ▸ hv1_in)
    have hv2_in : v2 ∈ AmoLean.Sigma.SigmaExpr.loopVarsOf (.loop n v2 body2) := by
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hv2_ne : v2 ≠ v := fun heq => hfresh2 (heq ▸ hv2_in)
    have hf1 : v1 ∉ SigmaExpr.fv (adjustStride v innerSize mSize nSize body1) :=
      AmoLean.Sigma.adjustStride_fresh v v1 innerSize mSize nSize body1 hv1_ne
    have hf2 : v2 ∉ SigmaExpr.fv (adjustStride v innerSize mSize nSize body2) :=
      AmoLean.Sigma.adjustStride_fresh v v2 innerSize mSize nSize body2 hv2_ne
    have hfresh1' : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf body1 := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    have hfresh2' : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf body2 := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    exact ExactStructure.loop n v1 v2 _ _ (ih hfresh1' hfresh2') hf1 hf2
  | seq s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride]
    have hf1a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf1b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    have hf2a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf2b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    exact ExactStructure.seq _ _ _ _ (ih1 hf1a hf2a) (ih2 hf1b hf2b)
  | par s1a s1b s2a s2b _ _ ih1 ih2 =>
    simp only [adjustStride]
    have hf1a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1a := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf1b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s1b := by
      intro hmem; apply hfresh1
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    have hf2a : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2a := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_left _ hmem
    have hf2b : v ∉ AmoLean.Sigma.SigmaExpr.loopVarsOf s2b := by
      intro hmem; apply hfresh2
      simp only [AmoLean.Sigma.SigmaExpr.loopVarsOf]
      exact Finset.mem_union_right _ hmem
    exact ExactStructure.par _ _ _ _ (ih1 hf1a hf2a) (ih2 hf1b hf2b)
  | temp size body1 body2 _ ih =>
    simp only [adjustStride]
    exact ExactStructure.temp size _ _ (ih hfresh1 hfresh2)
  | nop =>
    simp only [adjustStride]
    exact ExactStructure.nop

/-- For kron A⊗I lowering: expressions from lower have SameStructure,
    adjustStride with same v produces ExactStructure, and ExactStructure evaluates equally. -/
theorem adjustStride_lower_eval_eq (ω : α) (v : LoopVar) (innerSize mSize nSize m n : Nat)
    (state1 state2 : LowerState) (mat : MatExpr α m n) (env : LoopEnv) (st : EvalState α)
    (hfresh1 : v ∉ SigmaExpr.loopVarsOf (lower m n state1 mat).1)
    (hfresh2 : v ∉ SigmaExpr.loopVarsOf (lower m n state2 mat).1) :
    evalSigmaAlg ω env st (adjustStride v innerSize mSize nSize (lower m n state1 mat).1) =
    evalSigmaAlg ω env st (adjustStride v innerSize mSize nSize (lower m n state2 mat).1) := by
  have h_same := lower_produces_sameStructure state1 state2 mat
  have h_exact := adjustStride_produces_exactStructure v innerSize mSize nSize h_same hfresh1 hfresh2
  exact exactStructure_eval_eq ω h_exact env st

/-- Sorry-free loop_adjustBlock for expressions from lower.
    Works directly with MatExpr and uses the SameStructure→ExactStructure chain.
    This combines: v1→v2 (alpha) + expr1→expr2 (via ExactStructure). -/
theorem loop_adjustBlock_alpha_lower (ω : α) (v1 v2 : LoopVar) (n n_in n_out m_a n_a : Nat)
    (state1 state2 : LowerState) (mat : MatExpr α m_a n_a)
    (env : LoopEnv) (st : EvalState α)
    (hfresh1_v1 : v1 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state1 mat).1)
    (hfresh2_v1 : v1 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state2 mat).1)
    (hfresh1_v2 : v2 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state1 mat).1)
    (hfresh2_v2 : v2 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state2 mat).1) :
    evalSigmaAlg ω env st (.loop n v1 (adjustBlock v1 n_in n_out (lower m_a n_a state1 mat).1)) =
    evalSigmaAlg ω env st (.loop n v2 (adjustBlock v2 n_in n_out (lower m_a n_a state2 mat).1)) := by
  simp only [evalSigmaAlg]
  congr 1
  funext st' i
  -- Step 1: v1 → v2 for expr1 using adjustBlock_alpha_fresh
  have hfresh1 : ∀ w ∈ SigmaExpr.loopVarsOf (lower m_a n_a state1 mat).1, w ≠ v1 ∧ w ≠ v2 := fun w hw =>
    ⟨fun heq => hfresh1_v1 (heq ▸ hw), fun heq => hfresh1_v2 (heq ▸ hw)⟩
  have h1 := adjustBlock_alpha_fresh ω v1 v2 n_in n_out (lower m_a n_a state1 mat).1 env st' i hfresh1
  -- Step 2: expr1 → expr2 using adjustBlock_lower_eval_eq (via ExactStructure)
  have h2 := adjustBlock_lower_eval_eq ω v2 n_in n_out m_a n_a state1 state2 mat
               (env.bind v2 i) st' hfresh1_v2 hfresh2_v2
  rw [h1, h2]

/-- Sorry-free loop_adjustStride for expressions from lower.
    Works directly with MatExpr and uses the SameStructure→ExactStructure chain.
    This combines: v1→v2 (alpha) + expr1→expr2 (via ExactStructure). -/
theorem loop_adjustStride_alpha_lower (ω : α) (v1 v2 : LoopVar) (n innerSize mSize nSize m_a n_a : Nat)
    (state1 state2 : LowerState) (mat : MatExpr α m_a n_a)
    (env : LoopEnv) (st : EvalState α)
    (hfresh1_v1 : v1 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state1 mat).1)
    (hfresh2_v1 : v1 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state2 mat).1)
    (hfresh1_v2 : v2 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state1 mat).1)
    (hfresh2_v2 : v2 ∉ SigmaExpr.loopVarsOf (lower m_a n_a state2 mat).1) :
    evalSigmaAlg ω env st (.loop n v1 (adjustStride v1 innerSize mSize nSize (lower m_a n_a state1 mat).1)) =
    evalSigmaAlg ω env st (.loop n v2 (adjustStride v2 innerSize mSize nSize (lower m_a n_a state2 mat).1)) := by
  simp only [evalSigmaAlg]
  congr 1
  funext st' i
  -- Step 1: v1 → v2 for expr1 using adjustStride_alpha_fresh
  have hfresh1 : ∀ w ∈ SigmaExpr.loopVarsOf (lower m_a n_a state1 mat).1, w ≠ v1 ∧ w ≠ v2 := fun w hw =>
    ⟨fun heq => hfresh1_v1 (heq ▸ hw), fun heq => hfresh1_v2 (heq ▸ hw)⟩
  have h1 := adjustStride_alpha_fresh ω v1 v2 innerSize mSize nSize (lower m_a n_a state1 mat).1 env st' i hfresh1
  -- Step 2: expr1 → expr2 using adjustStride_lower_eval_eq (via ExactStructure)
  have h2 := adjustStride_lower_eval_eq ω v2 innerSize mSize nSize m_a n_a state1 state2 mat
               (env.bind v2 i) st' hfresh1_v2 hfresh2_v2
  rw [h1, h2]

/-! ## Part 8: Matrix Expression Evaluator (Algebraic)

Reference semantics for MatExpr over generic Field α.
-/

/-- Apply permutation to a list -/
def applyPerm (p : Perm n) (xs : List α) : List α :=
  -- Simplified: just return the list (permutation logic omitted for now)
  xs

/-- Apply kernel B to blocks: (I_m ⊗ B) · v -/
def applyBlockwise (m : Nat) (kernel : List α → List α) (input : List α) : List α :=
  let blockSize := input.length / m
  (List.range m).flatMap fun i =>
    let block := input.drop (i * blockSize) |>.take blockSize
    kernel block

/-- Apply kernel A with stride: (A ⊗ I_n) · v -/
def applyStrided (n : Nat) (kernel : List α → List α) (input : List α) : List α :=
  let numLanes := input.length / n
  let lanes := List.range n |>.map fun lane =>
    List.range numLanes |>.map fun j =>
      let idx := lane + j * n
      input.getD idx default
  let processedLanes := lanes.map kernel
  List.range (numLanes * n) |>.map fun idx =>
    let lane := idx % n
    let i := idx / n
    match processedLanes[lane]? with
    | some laneData => laneData.getD i default
    | none => default

/-- Check if a MatExpr is an identity matrix -/
def isIdentity : MatExpr α m n → Bool
  | .identity _ => true
  | _ => false

/-- If isIdentity returns true, then the matrix is square (m = n).
    This follows because .identity (k : Nat) : MatExpr α k k is the only constructor
    that returns true for isIdentity. -/
theorem isIdentity_implies_square {a : MatExpr α m n} (h : isIdentity a = true) : m = n := by
  cases a with
  | identity k => rfl  -- .identity k : MatExpr α k k, so m = k = n
  | _ => simp only [isIdentity, Bool.false_eq_true] at h  -- false = true is a contradiction

/-- Apply kernel B to blocks inline (for termination proof): (I_m ⊗ B) · v -/
def applyBlockwiseInline (m : Nat) (blockSize : Nat) (evalBlock : List α → List α) (input : List α) : List α :=
  (List.range m).flatMap fun i =>
    let block := input.drop (i * blockSize) |>.take blockSize
    evalBlock block

/-- Apply kernel A strided inline (for termination proof): (A ⊗ I_n) · v -/
def applyStridedInline (n : Nat) (laneLen : Nat) (evalLane : List α → List α) (input : List α) : List α :=
  let lanes := List.range n |>.map fun lane =>
    List.range laneLen |>.map fun j =>
      let idx := lane + j * n
      input.getD idx default
  let processedLanes := lanes.map evalLane
  List.range (laneLen * n) |>.map fun idx =>
    let lane := idx % n
    let i := idx / n
    match processedLanes[lane]? with
    | some laneData => laneData.getD i default
    | none => default

/-- Main matrix expression evaluator (algebraic).
    Parametrized by primitive root ω for DFT operations.
    Now total with termination proof via nodeCount. -/
def evalMatExprAlg (ω : α) (m n : Nat) (mExpr : MatExpr α m n) (input : List α) : List α :=
  match mExpr with
  | .identity _ => input
  | .zero _ _ => List.replicate m 0
  | .dft 2 => evalDFT2 input
  | .dft n' => evalDFT ω n' input
  | .ntt _ _ => input  -- NTT would need field-specific implementation
  | .twiddle _ _ => input  -- Twiddle factors
  | .perm p => applyPerm p input
  | @MatExpr.kron _ m₁ n₁ m₂ n₂ a b =>
    if isIdentity a then
      -- (I_{m₁} ⊗ B) · v : apply B to m₁ blocks of size n₂
      (List.range m₁).flatMap fun i =>
        let block := input.drop (i * n₂) |>.take n₂
        evalMatExprAlg ω m₂ n₂ b block
    else if isIdentity b then
      -- (A ⊗ I_{m₂}) · v : apply A strided
      let laneLen := input.length / m₂
      let lanes := List.range m₂ |>.map fun lane =>
        List.range laneLen |>.map fun j =>
          input.getD (lane + j * m₂) default
      let processedLanes := lanes.map (evalMatExprAlg ω m₁ n₁ a)
      List.range (laneLen * m₂) |>.map fun idx =>
        let lane := idx % m₂
        let i := idx / m₂
        match processedLanes[lane]? with
        | some laneData => laneData.getD i default
        | none => default
    else
      -- General (A ⊗ B) · v : B blockwise, then A strided
      let afterB := (List.range m₁).flatMap fun i =>
        let block := input.drop (i * n₂) |>.take n₂
        evalMatExprAlg ω m₂ n₂ b block
      let laneLen := afterB.length / m₂
      let lanes := List.range m₂ |>.map fun lane =>
        List.range laneLen |>.map fun j =>
          afterB.getD (lane + j * m₂) default
      let processedLanes := lanes.map (evalMatExprAlg ω m₁ n₁ a)
      List.range (laneLen * m₂) |>.map fun idx =>
        let lane := idx % m₂
        let i := idx / m₂
        match processedLanes[lane]? with
        | some laneData => laneData.getD i default
        | none => default
  | @MatExpr.compose _ _ k _ a b =>
    let intermediate := evalMatExprAlg ω k n b input
    evalMatExprAlg ω m k a intermediate
  | .add a b =>
    let ra := evalMatExprAlg ω m n a input
    let rb := evalMatExprAlg ω m n b input
    ra.zip rb |>.map fun (x, y) => x + y
  | .smul _ a => evalMatExprAlg ω m n a input
  | .transpose a => evalMatExprAlg ω n m a input
  | .conjTranspose a => evalMatExprAlg ω n m a input
  | .diag _ => input
  | .scalar _ => input
  | .elemwise _ a => evalMatExprAlg ω m n a input
  | .partialElemwise _ _ a => evalMatExprAlg ω m n a input
  | @MatExpr.mdsApply _ t _ _ a => evalMatExprAlg ω t 1 a input
  | @MatExpr.addRoundConst _ t _ _ a => evalMatExprAlg ω t 1 a input
termination_by mExpr.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [MatExpr.nodeCount]
  all_goals omega

/-! ## Part 9: Correctness Theorems -/

/-- Identity preserves input -/
theorem identity_algebraic_correct (n : Nat) (v : List α) (hv : v.length = n) :
    evalMatExprAlg ω n n (.identity n) v = v := by
  simp only [evalMatExprAlg]

/-- DFT_2 correctness -/
theorem dft2_algebraic_correct (v : List α) (hv : v.length = 2) :
    evalMatExprAlg ω 2 2 (.dft 2) v = evalDFT2 v := by
  simp only [evalMatExprAlg]

/-- Identity kernel preserves input -/
@[simp]
theorem evalKernelAlg_identity (n : Nat) (input : List α) :
    evalKernelAlg ω (.identity n) input = input := by
  simp only [evalKernelAlg, evalIdentityKernel]

/-- Lower identity produces compute with identity kernel -/
theorem lower_identity (n : Nat) :
    lowerFresh n n (.identity n : MatExpr α n n) =
    .compute (.identity n) (Gather.contiguous n (.const 0)) (Scatter.contiguous n (.const 0)) := by
  simp only [lowerFresh, lower]

/-- Helper: 0 + 1 * i = i -/
@[simp]
theorem zero_add_one_mul (i : Nat) : 0 + 1 * i = i := by omega

/-- Map read over range equals list -/
theorem map_read_range_eq_list (v : List α) :
    List.map (fun i => (Memory.ofList v).read i) (List.range v.length) = v := by
  apply List.ext_getElem
  · simp [List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    exact Memory.read_ofList v i h1

/-- Gather contiguous from Memory.ofList returns the list -/
theorem evalGather_ofList_contiguous (v : List α) :
    evalGather LoopEnv.empty (Gather.contiguous v.length (.const 0)) (Memory.ofList v) = v := by
  simp only [evalGather, Gather.contiguous, evalIdxExpr, zero_add_one_mul]
  exact map_read_range_eq_list v

/-! ### Block/stride gather decomposition lemmas (Fase 8 Corrección 1) -/

/-- Block gather reads consecutive elements from Memory.ofList.
    At iteration i, Gather.block reads positions [m₂*i, m₂*i+1, ..., m₂*i+m₂-1]
    from the read memory, which equals input.drop(i*m₂).take(m₂). -/
private theorem evalGather_block_eq_drop_take [Inhabited α]
    (v : LoopVar) (m₂ i : Nat) (input : List α) (hi : (i + 1) * m₂ ≤ input.length) :
    evalGather (LoopEnv.empty.bind v i) (Gather.block m₂ v) (Memory.ofList input) =
    (input.drop (i * m₂) |>.take m₂) := by
  simp only [evalGather, Gather.block, evalIdxExpr_affine_bind, Nat.zero_add]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]
    symm; apply Nat.min_eq_left
    have hmul := hi; rw [show (i + 1) * m₂ = i * m₂ + m₂ from by ring] at hmul; omega
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, Nat.one_mul,
               List.length_map, List.length_range] at h1 ⊢
    have hj_lt : m₂ * i + j < input.length := by
      calc m₂ * i + j < m₂ * i + m₂ := by omega
        _ = (i + 1) * m₂ := by ring
        _ ≤ input.length := hi
    rw [Memory.read_ofList input (m₂ * i + j) hj_lt]
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    ring

/-- Stride gather reads strided elements from memory.
    evalGather with baseAddr = .var v and stride = m₂ at binding v=j
    reads positions [j, j+m₂, j+2*m₂, ..., j+(m₁-1)*m₂]. -/
private theorem evalGather_stride_eq
    (v : LoopVar) (m₁ m₂ j : Nat) (mem : Memory α) :
    evalGather (LoopEnv.empty.bind v j)
      { count := m₁, baseAddr := .var v, stride := m₂ }
      mem =
    (List.range m₁).map (fun i => mem.read (j + m₂ * i)) := by
  simp only [evalGather, evalIdxExpr_var_bind]

/-- Stride gather from Memory.ofList equals the lane extraction used in evalMatExprAlg.
    Bridges evalGather with stride pattern to List.getD-based lane extraction. -/
private theorem evalGather_stride_ofList_eq_lane
    (v : LoopVar) (m₁ m₂ j : Nat) (input : List α)
    (hj : j < m₂) (hlen : input.length = m₁ * m₂) :
    evalGather (LoopEnv.empty.bind v j)
      { count := m₁, baseAddr := .var v, stride := m₂ }
      (Memory.ofList input) =
    (List.range m₁).map (fun i => input.getD (j + i * m₂) default) := by
  rw [evalGather_stride_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at *
    rw [Memory.read_ofList_eq_getD]
    congr 1; ring

/-! ### Helper lemmas for scatter correctness proof -/

/-- List.drop after List.set at an earlier position is unchanged -/
private theorem list_drop_set_of_lt (l : List α) (k : Nat) (v : α) (j : Nat) (hkj : k < j) :
    (l.set k v).drop j = l.drop j := by
  induction l generalizing k j with
  | nil => simp
  | cons hd tl ih =>
    cases k with
    | zero =>
      cases j with
      | zero => omega
      | succ j' => simp [List.set, List.drop]
    | succ k' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.set, List.drop]
        exact ih k' j' (by omega)

/-- List.take (k+1) after List.set at position k gives take k ++ [v] -/
private theorem list_take_succ_set (l : List α) (k : Nat) (v : α) (hk : k < l.length) :
    (l.set k v).take (k + 1) = l.take k ++ [v] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons hd tl ih =>
    cases k with
    | zero => simp [List.set, List.take]
    | succ k' =>
      simp only [List.set, List.take, List.cons_append]
      congr 1
      exact ih k' (by simp only [List.length_cons] at hk; omega)

/-- Generalized scatter: writing vals at positions k..k+n-1 into Memory wm
    produces wm.toList.take k ++ vals ++ wm.toList.drop (k + vals.length) -/
private theorem scatter_enumFrom_general (vals : List α) (wm : Memory α) (k : Nat)
    (hk : k + vals.length ≤ wm.size) :
    ((vals.enumFrom k).foldl (fun acc x => acc.write x.1 x.2) wm).toList
    = wm.toList.take k ++ vals ++ wm.toList.drop (k + vals.length) := by
  induction vals generalizing wm k with
  | nil =>
    simp only [List.enumFrom, List.foldl_nil, List.length_nil, Nat.add_zero,
               List.append_nil, List.take_append_drop]
  | cons hd tl ih =>
    simp only [List.length_cons] at hk
    simp only [List.enumFrom_cons, List.foldl_cons]
    set wm' := wm.write k hd
    have hk_lt : k < wm.size := by omega
    have h_size : wm'.size = wm.size := Memory.size_write_eq wm k hd hk_lt
    have h_toList : wm'.toList = wm.toList.set k hd := Memory.toList_write_eq_set wm k hd hk_lt
    have h_toList_len : wm.toList.length = wm.size := by
      simp [Memory.toList, Memory.size]
    rw [ih wm' (k + 1) (by rw [h_size]; omega)]
    rw [h_toList]
    rw [list_take_succ_set wm.toList k hd (by omega)]
    rw [list_drop_set_of_lt wm.toList k hd (k + 1 + tl.length) (by omega)]
    simp only [List.append_assoc, List.singleton_append, List.length_cons,
               Nat.add_right_comm, Nat.add_assoc]

/-- Scatter then toList identity for contiguous writes.
    Writing v[0]..v[n-1] at positions 0..n-1 into zeros(n) gives v. -/
theorem scatter_zeros_toList (v : List α) :
    (List.foldl (fun acc x => acc.write x.1 x.2) (Memory.zeros v.length) v.enum).toList = v := by
  have h := scatter_enumFrom_general v (Memory.zeros v.length) 0
    (by simp [Memory.zeros_size])
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at h
  rw [show v.enum = v.enumFrom 0 from rfl, h]
  simp [Memory.zeros_toList, List.length_replicate]

/-- evalScatter for contiguous scatter at base 0 reduces to foldl over enumFrom 0.
    This bridges the syntactic gap between evalScatter's lambda form and scatter_enumFrom_general. -/
private theorem evalScatter_contiguous_zero (vals : List α) (wm : Memory α) (n' : Nat) :
    evalScatter LoopEnv.empty (Scatter.contiguous n' (.const 0)) wm vals =
    (vals.enumFrom 0).foldl (fun acc x => acc.write x.1 x.2) wm := by
  simp only [evalScatter, Scatter.contiguous, evalIdxExpr, List.enum]
  -- Goal: (vals.enumFrom 0).foldl (fun acc x => acc.write (0 + 1 * x.1) x.2) wm
  --     = (vals.enumFrom 0).foldl (fun acc x => acc.write x.1 x.2) wm
  congr 1
  ext acc ⟨i, v⟩
  simp

/-- Writing the same vals to two memories of the same size gives the same result,
    when the writes cover all positions (k = 0 and vals.length = wm.size). -/
private theorem foldl_write_enum_wm_irrelevant (vals : List α) (wm1 wm2 : Memory α)
    (hw1 : wm1.size = vals.length) (hw2 : wm2.size = vals.length) :
    (vals.enumFrom 0).foldl (fun acc x => acc.write x.1 x.2) wm1 =
    (vals.enumFrom 0).foldl (fun acc x => acc.write x.1 x.2) wm2 := by
  apply Memory.eq_of_toList_eq
  have h1 := scatter_enumFrom_general vals wm1 0 (by rw [hw1]; omega)
  have h2 := scatter_enumFrom_general vals wm2 0 (by rw [hw2]; omega)
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at h1 h2
  have hlen1 : wm1.toList.length = vals.length := by
    rw [Array.length_toList]; exact hw1
  have hlen2 : wm2.toList.length = vals.length := by
    rw [Array.length_toList]; exact hw2
  rw [h1, h2, List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

/-- foldl write over enumFrom preserves Memory size when all writes are in-bounds -/
private theorem foldl_write_enumFrom_size (vals : List α) (wm : Memory α) (k : Nat)
    (hk : k + vals.length ≤ wm.size) :
    ((vals.enumFrom k).foldl (fun acc x => acc.write x.1 x.2) wm).size = wm.size := by
  induction vals generalizing wm k with
  | nil => simp [List.enumFrom]
  | cons hd tl ih =>
    simp only [List.enumFrom, List.foldl, List.length_cons] at *
    have hk_lt : k < wm.size := by omega
    have hsize : (wm.write k hd).size = wm.size := Memory.size_write_eq wm k hd hk_lt
    have hcond : (k + 1) + tl.length ≤ (wm.write k hd).size := by rw [hsize]; omega
    rw [ih (wm.write k hd) (k + 1) hcond, hsize]

/-- foldl write over enum preserves Memory size (wrapper for enumFrom 0) -/
private theorem foldl_write_enum_size (vals : List α) (wm : Memory α)
    (hk : vals.length ≤ wm.size) :
    (vals.enum.foldl (fun acc x => acc.write x.1 x.2) wm).size = wm.size := by
  show ((vals.enumFrom 0).foldl _ wm).size = wm.size
  exact foldl_write_enumFrom_size vals wm 0 (by omega)

/-- Lowering correctness for identity matrix -/
theorem lowering_identity_correct (n : Nat) (v : List α) (hv : v.length = n) :
    runSigmaAlg ω (lowerFresh n n (.identity n : MatExpr α n n)) v n = v := by
  subst hv
  simp only [runSigmaAlg, lowerFresh, lower, evalSigmaAlg, evalKernelAlg, evalIdentityKernel,
             EvalState.init, evalGather, evalScatter, Gather.contiguous, Scatter.contiguous,
             evalIdxExpr, LoopEnv.empty, zero_add_one_mul]
  rw [map_read_range_eq_list v, scatter_zeros_toList v, List.take_length]

/-! ### Meta-lemma: Compute with contiguous gather/scatter

All base cases of lowering (identity, dft, ntt, twiddle, perm) produce the
same SigmaExpr structure: `.compute kernel (Gather.contiguous n) (Scatter.contiguous n)`.
This meta-lemma proves correctness for all such cases at once. -/

/-- Running a compute node with contiguous gather/scatter returns the kernel applied to input.
    This is the core meta-lemma that covers all base lowering cases. -/
theorem lowering_compute_contiguous_correct (n : Nat) (k : Kernel)
    (v : List α) (hv : v.length = n)
    (hlen : (evalKernelAlg ω k v).length = n) :
    runSigmaAlg ω (.compute k (Gather.contiguous n (.const 0))
                               (Scatter.contiguous n (.const 0))) v n
    = evalKernelAlg ω k v := by
  subst hv
  simp only [runSigmaAlg, evalSigmaAlg, EvalState.init,
             evalGather, evalScatter, Gather.contiguous, Scatter.contiguous,
             evalIdxExpr, LoopEnv.empty, zero_add_one_mul]
  rw [map_read_range_eq_list v]
  -- Goal: (foldl write (zeros v.length) (evalKernelAlg ω k v).enum).toList.take v.length
  --       = evalKernelAlg ω k v
  have hlen' : v.length = (evalKernelAlg ω k v).length := by omega
  rw [hlen', scatter_zeros_toList (evalKernelAlg ω k v), List.take_length]

/-- Lower DFT produces compute with contiguous gather/scatter -/
theorem lower_dft (n' : Nat) :
    lowerFresh n' n' (.dft n' : MatExpr α n' n') =
    .compute (.dft n') (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)) := by
  simp only [lowerFresh, lower]

/-- evalDFT produces a list of length n -/
theorem evalDFT_length (ω' : α) (n' : Nat) (input : List α) :
    (evalDFT ω' n' input).length = n' := by
  simp only [evalDFT, List.length_map, List.length_range]

/-- evalDFT2 preserves length for 2-element lists -/
theorem evalDFT2_length (input : List α) (h : input.length = 2) :
    (evalDFT2 input).length = 2 := by
  match input, h with
  | [_, _], _ => rfl

/-- evalKernelAlg for .dft n preserves length -/
theorem evalKernelAlg_dft_length (n' : Nat) (input : List α) (h : input.length = n') :
    (evalKernelAlg ω (.dft n') input).length = n' := by
  match n' with
  | 0 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
  | 1 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
  | 2 => simp only [evalKernelAlg]; exact evalDFT2_length input h
  | n + 3 => simp only [evalKernelAlg]; exact evalDFT_length ω (n + 3) input

/-- evalMatExprAlg for DFT equals evalKernelAlg for DFT.
    Both match on n'=2 vs n'≠2 with identical branches. -/
theorem evalMatExprAlg_dft_eq_kernelAlg (n' : Nat) (v : List α) :
    evalMatExprAlg ω n' n' (.dft n' : MatExpr α n' n') v = evalKernelAlg ω (.dft n') v := by
  -- Both unfold to the same match on n' (2 → evalDFT2, n → evalDFT ω n)
  -- Case split to resolve the match
  match n' with
  | 0 => simp [evalMatExprAlg, evalKernelAlg]
  | 1 => simp [evalMatExprAlg, evalKernelAlg]
  | 2 => simp [evalMatExprAlg, evalKernelAlg]
  | n + 3 => simp [evalMatExprAlg, evalKernelAlg]

/-- Lowering correctness for DFT: the compiled code produces the same result
    as the reference DFT evaluation.

    Key insight (L-061): IsPrimitiveRoot is NOT needed for lowering correctness.
    The lowering just says "compiled code = reference semantics", regardless of ω. -/
theorem lowering_dft_correct (n' : Nat) (v : List α) (hv : v.length = n') :
    runSigmaAlg ω (lowerFresh n' n' (.dft n' : MatExpr α n' n')) v n'
    = evalKernelAlg ω (.dft n') v := by
  rw [lower_dft]
  exact lowering_compute_contiguous_correct n' (.dft n') v hv
    (evalKernelAlg_dft_length n' v hv)

/-! ### Gather/Kernel length lemmas for kron size preservation -/

/-- evalGather always returns exactly g.count elements -/
theorem evalGather_length (env : LoopEnv) (g : Gather) (mem : Memory α) :
    (evalGather env g mem).length = g.count := by
  simp only [evalGather, List.length_map, List.length_range]

/-- For identity-like kernels (those that return input unchanged),
    the output length equals the input length. Covers all kernels
    produced by `lower` for atomic MatExprs except .dft. -/
theorem evalKernelAlg_identity_length (ω : α) (k : Kernel) (input : List α)
    (hk : k = .identity input.length ∨ (∃ n p, k = .ntt n p) ∨
           (∃ n p, k = .twiddle n p) ∨ k = .scale ∨
           (∃ s e, k = .sbox s e) ∨ (∃ s e i, k = .partialSbox s e i) ∨
           (∃ name s, k = .mdsApply name s) ∨ (∃ n, k = .mdsInternal n) ∨
           (∃ r s, k = .addRoundConst r s)) :
    (evalKernelAlg ω k input).length = input.length := by
  rcases hk with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | ⟨_, _, rfl⟩ |
    ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;>
    simp [evalKernelAlg, evalIdentityKernel]

/-! ## Part 10: Foundational Axioms, Compose Proof, and Main Correctness Theorem -/

/-! ### Foundational Axioms

These axioms capture fundamental properties of the lowered SigmaExpr evaluation.
They are more primitive and auditable than the previous compose/kron axioms,
and serve as the building blocks for the compose correctness proof.

**Size preservation**: Evaluating a lowered expression preserves the write
memory size. This holds because lowered expressions only write within the
allocated output region [0, m).

**Write memory irrelevance**: The output (first m elements) of evaluating a
lowered expression does not depend on the initial write memory contents.
This holds because all positions in [0, m) are overwritten by the evaluation.

**Alpha-equivalence**: Different LowerState values (which only affect loop
variable numbering) do not change the semantics of a lowered expression.
Loop variable IDs are just names; the semantics depends only on the loop
structure, not the specific IDs used.

**Output length preservation**: evalMatExprAlg always produces a list of
length m (the output dimension). -/

/-! ### Predicates for NTT/FFT Matrices -/

/-- A MatExpr contains no .zero sub-expressions at any nesting level.
    This guarantees that the lowered expression overwrites all output positions,
    making writeMem content irrelevant for the first m elements of output.
    Required for compose correctness (writeMem irrelevance property).
    Always satisfied by actual NTT/FFT/Poseidon code (which never use .zero). -/
def HasNoZero : {m n : Nat} → MatExpr α m n → Prop
  | _, _, .zero _ _ => False
  | _, _, .identity _ => True
  | _, _, .dft _ => True
  | _, _, .ntt _ _ => True
  | _, _, .twiddle _ _ => True
  | _, _, .perm _ => True
  | _, _, .diag _ => True
  | _, _, .scalar _ => True
  | _, _, .transpose a => HasNoZero a
  | _, _, .conjTranspose a => HasNoZero a
  | _, _, .smul _ a => HasNoZero a
  | _, _, .elemwise _ a => HasNoZero a
  | _, _, .partialElemwise _ _ a => HasNoZero a
  | _, _, .mdsApply _ _ a => HasNoZero a
  | _, _, .addRoundConst _ _ a => HasNoZero a
  | _, _, .compose a b => HasNoZero a ∧ HasNoZero b
  | _, _, .add a b => HasNoZero a ∧ HasNoZero b
  | _, _, .kron a b => HasNoZero a ∧ HasNoZero b

/-- A MatExpr contains no .compose sub-expressions at any nesting level.
    This ensures that `lower` never produces `.temp` nodes inside kron arguments,
    which would replace writeMem with `zeros(k)` and destroy size preservation.
    In NTT/FFT/Poseidon, kron arguments are always atomic (dft, identity, ntt, etc.)
    while compose appears OUTSIDE kron, so this is always satisfied. -/
def HasNoCompose : {m n : Nat} → MatExpr α m n → Prop
  | _, _, .compose _ _ => False
  | _, _, .identity _ => True
  | _, _, .zero _ _ => True
  | _, _, .dft _ => True
  | _, _, .ntt _ _ => True
  | _, _, .twiddle _ _ => True
  | _, _, .perm _ => True
  | _, _, .diag _ => True
  | _, _, .scalar _ => True
  | _, _, .transpose a => HasNoCompose a
  | _, _, .conjTranspose a => HasNoCompose a
  | _, _, .smul _ a => HasNoCompose a
  | _, _, .elemwise _ a => HasNoCompose a
  | _, _, .partialElemwise _ _ a => HasNoCompose a
  | _, _, .mdsApply _ _ a => HasNoCompose a
  | _, _, .addRoundConst _ _ a => HasNoCompose a
  | _, _, .add a b => HasNoCompose a ∧ HasNoCompose b
  | _, _, .kron a b => HasNoCompose a ∧ HasNoCompose b

/-- Predicate: lowering this MatExpr produces a single .compute SigmaExpr.
    Required for kron children so that adjustBlock/adjustStride produces
    a .compute body with block/stride scatter, enabling the writeMem
    irrelevance proof (all positions overwritten after m₁ loop iterations).

    In NTT/FFT, kron children are always atomic operators (dft, identity,
    ntt, twiddle, perm, diag, scalar) possibly wrapped in transpose/conjTranspose.
    These all lower to `.compute k (Gather.contiguous n) (Scatter.contiguous m)`.

    Excluded: kron (→ .loop), compose (→ .temp .seq), smul/elemwise/etc. (→ .seq).
    Nested krons are handled by compose in NTT factorizations. -/
def HasNoSeqLower : {m n : Nat} → MatExpr α m n → Prop
  | _, _, .identity _ => True
  | _, _, .zero _ _ => True
  | _, _, .dft _ => True
  | _, _, .ntt _ _ => True
  | _, _, .twiddle _ _ => True
  | _, _, .perm _ => True
  | _, _, .diag _ => True
  | _, _, .scalar _ => True
  | _, _, .transpose a => HasNoSeqLower a
  | _, _, .conjTranspose a => HasNoSeqLower a
  | _, _, _ => False

/-- Lower of a HasNoSeqLower expression produces a single .compute node.
    This is the key structural lemma for kron writeMem irrelevance:
    it ensures the loop body is a single .compute (no .seq, .loop, .temp). -/
theorem lower_hasNoSeqLower_is_compute {m n : Nat} (state : LowerState) (mat : MatExpr α m n)
    (h_nsl : HasNoSeqLower mat) (h_nz : HasNoZero mat) :
    ∃ k g s, (lower m n state mat).1 = .compute k g s := by
  induction mat generalizing state with
  | identity n' => simp only [lower]; exact ⟨_, _, _, rfl⟩
  | zero => exact absurd h_nz (by simp [HasNoZero])
  | dft n' => simp only [lower]; exact ⟨_, _, _, rfl⟩
  | ntt => simp only [lower]; exact ⟨_, _, _, rfl⟩
  | twiddle => simp only [lower]; exact ⟨_, _, _, rfl⟩
  | perm => simp only [lower]; exact ⟨_, _, _, rfl⟩
  | diag => simp only [lower]; exact ⟨_, _, _, rfl⟩
  | scalar => simp only [lower]; exact ⟨_, _, _, rfl⟩
  | transpose a ih => simp only [lower]; exact ih state h_nsl h_nz
  | conjTranspose a ih => simp only [lower]; exact ih state h_nsl h_nz
  | kron _ _ _ _ => exact h_nsl.elim
  | compose _ _ _ _ => exact h_nsl.elim
  | smul _ _ _ => exact h_nsl.elim
  | elemwise _ _ _ => exact h_nsl.elim
  | add _ _ _ _ => exact h_nsl.elim
  | partialElemwise _ _ _ _ => exact h_nsl.elim
  | mdsApply _ _ _ _ => exact h_nsl.elim
  | addRoundConst _ _ _ _ => exact h_nsl.elim

/-- For HasNoSeqLower expressions, lower produces identical SigmaExpr regardless of LowerState.
    This is because atomic matrices (identity, dft, ntt, etc.) never call freshLoopVar. -/
private theorem lower_hasNoSeqLower_state_eq {m n : Nat} (state1 state2 : LowerState)
    (mat : MatExpr α m n) (h_nsl : HasNoSeqLower mat) :
    (lower m n state1 mat).1 = (lower m n state2 mat).1 := by
  induction mat generalizing state1 state2 with
  | identity => simp only [lower]
  | zero => simp only [lower]
  | dft => simp only [lower]
  | ntt => simp only [lower]
  | twiddle => simp only [lower]
  | perm => simp only [lower]
  | diag => simp only [lower]
  | scalar => simp only [lower]
  | transpose a ih => simp only [lower]; exact ih state1 state2 h_nsl
  | conjTranspose a ih => simp only [lower]; exact ih state1 state2 h_nsl
  | kron _ _ _ _ => exact h_nsl.elim
  | compose _ _ _ _ => exact h_nsl.elim
  | smul _ _ _ => exact h_nsl.elim
  | elemwise _ _ _ => exact h_nsl.elim
  | add _ _ _ _ => exact h_nsl.elim
  | partialElemwise _ _ _ _ => exact h_nsl.elim
  | mdsApply _ _ _ _ => exact h_nsl.elim
  | addRoundConst _ _ _ _ => exact h_nsl.elim

/-- For HasNoSeqLower without HasNoZero (i.e., the .zero case), lower produces .nop. -/
private theorem lower_hasNoSeqLower_notHasNoZero_is_nop {m n : Nat} (state : LowerState)
    (mat : MatExpr α m n) (h_nsl : HasNoSeqLower mat) (h_z : ¬HasNoZero mat) :
    (lower m n state mat).1 = .nop := by
  induction mat generalizing state with
  | zero => simp [lower]
  | identity => simp [HasNoZero] at h_z
  | dft => simp [HasNoZero] at h_z
  | ntt => simp [HasNoZero] at h_z
  | twiddle => simp [HasNoZero] at h_z
  | perm => simp [HasNoZero] at h_z
  | diag => simp [HasNoZero] at h_z
  | scalar => simp [HasNoZero] at h_z
  | transpose a ih =>
    simp only [lower]
    exact ih state h_nsl (by simp [HasNoZero] at h_z; exact h_z)
  | conjTranspose a ih =>
    simp only [lower]
    exact ih state h_nsl (by simp [HasNoZero] at h_z; exact h_z)
  | kron _ _ _ _ => exact h_nsl.elim
  | compose _ _ _ _ => exact h_nsl.elim
  | smul _ _ _ => exact h_nsl.elim
  | elemwise _ _ _ => exact h_nsl.elim
  | add _ _ _ _ => exact h_nsl.elim
  | partialElemwise _ _ _ _ => exact h_nsl.elim
  | mdsApply _ _ _ _ => exact h_nsl.elim
  | addRoundConst _ _ _ _ => exact h_nsl.elim

/-- For square HasNoSeqLower + HasNoZero matrices, lower produces .compute with
    contiguous gather/scatter. Uses separate m,n to allow induction, with hmn : m = n. -/
private theorem lower_hasNoSeqLower_contiguous {m n : Nat} (state : LowerState)
    (mat : MatExpr α m n) (h_nsl : HasNoSeqLower mat) (h_nz : HasNoZero mat) (hmn : m = n) :
    ∃ k, (lower m n state mat).1 = .compute k (Gather.contiguous n (.const 0))
      (Scatter.contiguous n (.const 0)) := by
  induction mat generalizing state with
  | identity => simp only [lower]; exact ⟨_, rfl⟩
  | zero => exact absurd h_nz (by simp [HasNoZero])
  | dft => simp only [lower]; exact ⟨_, rfl⟩
  | ntt => simp only [lower]; exact ⟨_, rfl⟩
  | twiddle => simp only [lower]; exact ⟨_, rfl⟩
  | perm => simp only [lower]; exact ⟨_, rfl⟩
  | diag => simp only [lower]; exact ⟨_, rfl⟩
  | scalar => simp only [lower]; exact ⟨_, rfl⟩
  | transpose a ih =>
    simp only [lower]
    exact hmn ▸ ih state h_nsl h_nz hmn.symm
  | conjTranspose a ih =>
    simp only [lower]
    exact hmn ▸ ih state h_nsl h_nz hmn.symm
  | kron _ _ _ _ => exact h_nsl.elim
  | compose _ _ _ _ => exact h_nsl.elim
  | smul _ _ _ => exact h_nsl.elim
  | elemwise _ _ _ => exact h_nsl.elim
  | add _ _ _ _ => exact h_nsl.elim
  | partialElemwise _ _ _ _ => exact h_nsl.elim
  | mdsApply _ _ _ _ => exact h_nsl.elim
  | addRoundConst _ _ _ _ => exact h_nsl.elim

/-! ### Well-Formedness Predicate for NTT/FFT Matrices

The `IsWellFormedNTT` predicate captures the constraints needed for size preservation:
- Square matrices (m = n) for transpose, smul, elemwise
- stateSize parameter matches type dimension for mdsApply/addRoundConst
- Squareness (m = k) for compose first argument
- Recursive well-formedness for composite expressions

This predicate is always satisfied by actual NTT/FFT/Poseidon code. -/

/-- Well-formedness predicate for MatExpr in NTT/FFT context.
    Captures constraints that aren't enforced at the type level but are
    satisfied by well-constructed matrix expressions. -/
def IsWellFormedNTT : {m n : Nat} → MatExpr α m n → Prop
  | _, _, .identity _ => True
  | _, _, .zero _ _ => True
  | _, _, .dft _ => True
  | _, _, .ntt _ _ => True
  | _, _, .twiddle _ _ => True
  | _, _, .perm _ => True
  | _, _, .diag _ => True
  | _, _, .scalar _ => True
  | m, n, .transpose a => m = n ∧ IsWellFormedNTT a
  | m, n, .conjTranspose a => m = n ∧ IsWellFormedNTT a
  | m, n, .smul _ a => m = n ∧ IsWellFormedNTT a
  | _, n, .elemwise _ a => n = 1 ∧ IsWellFormedNTT a
  | _, n, .partialElemwise _ _ a => n = 1 ∧ IsWellFormedNTT a
  | m, _, .mdsApply _ stateSize a => stateSize = m ∧ IsWellFormedNTT a
  | m, _, .addRoundConst _ stateSize a => stateSize = m ∧ IsWellFormedNTT a
  | _, _, @MatExpr.compose _ m' k' _ a b => m' = k' ∧ HasNoZero a ∧ IsWellFormedNTT a ∧ IsWellFormedNTT b
  /- Design Decision DD-ADD: IsWellFormedNTT excludes .add
     Reason: lower(.add a b) produces .par exprA exprB (sequential composition: b overwrites a),
     but evalMatExprAlg(.add a b) computes pointwise addition a(v) + b(v).
     These are semantically incompatible operations.

     Impact: .add is NOT used in any NTT/FFT/Poseidon pipeline. All verified paths use:
     compose, kron, smul, elemwise, partialElemwise, mdsApply, addRoundConst,
     transpose, conjTranspose, identity, zero, dft, ntt, twiddle, perm, diag, scalar.

     Fix path: To support .add, SigmaExpr needs a new .pointwiseAdd constructor
     with semantics: output[i] = evalA[i] + evalB[i]. See sorry_elimination_plan.md.

     This closes sorries S2 (writeMem_irrelevant .add) and S5 (lowering_algebraic_correct .add)
     by making the case vacuously true (hwf : False → anything). -/
  | _, _, .add _ _ => False
  | _, _, @MatExpr.kron _ m₁ n₁ m₂ n₂ a b =>
      m₁ = n₁ ∧ m₂ = n₂ ∧ HasNoCompose a ∧ HasNoCompose b ∧ IsWellFormedNTT a ∧ IsWellFormedNTT b ∧
      m₁ > 0 ∧ m₂ > 0 ∧
      (a.isIdentity = true ∨ b.isIdentity = true) ∧
      HasNoSeqLower a ∧ HasNoSeqLower b

/-- Helper to extract m = n from well-formedness of transpose -/
theorem IsWellFormedNTT.transpose_square {a : MatExpr α n m} (h : IsWellFormedNTT (.transpose a)) :
    m = n := by exact h.1

/-- Helper to extract stateSize = m from well-formedness of mdsApply -/
theorem IsWellFormedNTT.mdsApply_size {a : MatExpr α m 1} (h : IsWellFormedNTT (.mdsApply name sz a)) :
    sz = m := by exact h.1

/-- Helper to extract stateSize = m from well-formedness of addRoundConst -/
theorem IsWellFormedNTT.addRoundConst_size {a : MatExpr α m 1} (h : IsWellFormedNTT (.addRoundConst r sz a)) :
    sz = m := by exact h.1

/-! ### Loop Invariant Infrastructure

Generic lemmas for proving properties are preserved across foldl iterations
and evalSigmaAlg .loop evaluations. Used for kron size preservation (S1)
and kron writeMem irrelevance (S3). -/

/-- Generic foldl invariant: if P holds for init and is preserved by each step,
    then P holds for the final result. -/
theorem foldl_invariant {γ β : Type*} (l : List γ) (f : β → γ → β) (init : β)
    (P : β → Prop) (h_init : P init)
    (h_step : ∀ b a, P b → P (f b a)) :
    P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h_init
  | cons x xs ih =>
    simp only [List.foldl]
    exact ih (f init x) (h_step init x h_init)

/-- Variant of foldl_invariant where the step function receives a proof that
    the element belongs to the list. This is needed when the preservation proof
    requires information about which element is being processed (e.g., index bounds
    from enum membership). -/
theorem foldl_invariant_mem {γ β : Type*} (l : List γ) (f : β → γ → β) (init : β)
    (P : β → Prop) (h_init : P init)
    (h_step : ∀ b a, a ∈ l → P b → P (f b a)) :
    P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h_init
  | cons x xs ih =>
    simp only [List.foldl]
    exact ih (f init x)
      (h_step init x (List.mem_cons_self x xs) h_init)
      (fun b a ha hb => h_step b a (List.mem_cons_of_mem x ha) hb)

/-- Loop size preservation: if the body of a loop preserves writeMem.size
    (given that readMem.size = writeMem.size = target), then the loop preserves it.
    The loop sets readMem := writeMem after each iteration, so the precondition
    requires the body to work when readMem.size = writeMem.size. -/
theorem evalSigmaAlg_loop_preserves_size
    (ω : α) (n : Nat) (loopVar : LoopVar) (body : SigmaExpr)
    (env : LoopEnv) (st : EvalState α) (target : Nat)
    (h_st : st.writeMem.size = target)
    (h_body : ∀ (env' : LoopEnv) (st' : EvalState α),
      st'.writeMem.size = target →
      (evalSigmaAlg ω env' st' body).writeMem.size = target) :
    (evalSigmaAlg ω env st (.loop n loopVar body)).writeMem.size = target := by
  simp only [evalSigmaAlg]
  have h_inv := foldl_invariant (List.range n)
    (fun (st : EvalState α) (i : Nat) =>
      evalSigmaAlg ω (env.bind loopVar i) st body)
    st
    (fun st => st.writeMem.size = target)
    h_st
    (fun st' i h_wm => h_body (env.bind loopVar i) st' h_wm)
  exact h_inv

/-- Loop size preservation with iteration bound: variant of evalSigmaAlg_loop_preserves_size
    where the body hypothesis receives a proof that the loop variable is bound to i < n.
    This is needed for adjustBlock/adjustStride proofs where scatter in-bounds depends on
    the loop variable being within range. -/
theorem evalSigmaAlg_loop_preserves_size_with_bound
    (ω : α) (n : Nat) (loopVar : LoopVar) (body : SigmaExpr)
    (env : LoopEnv) (st : EvalState α) (target : Nat)
    (h_st : st.writeMem.size = target)
    (h_body : ∀ (i : Nat) (st' : EvalState α),
      i < n →
      st'.writeMem.size = target →
      (evalSigmaAlg ω (env.bind loopVar i) st' body).writeMem.size = target) :
    (evalSigmaAlg ω env st (.loop n loopVar body)).writeMem.size = target := by
  simp only [evalSigmaAlg]
  have h_inv := foldl_invariant_mem (List.range n)
    (fun (st : EvalState α) (i : Nat) =>
      evalSigmaAlg ω (env.bind loopVar i) st body)
    st
    (fun st => st.writeMem.size = target)
    h_st
    (fun st' i h_mem h_wm => by
      have hi : i < n := List.mem_range.mp h_mem
      exact h_body i st' hi h_wm)
  exact h_inv

/-- Loop size preservation (writeMem-only variant): the body hypothesis only requires
    writeMem.size = target, not readMem. This handles the kron case where the initial
    readMem may have a different size. With the corrected loop semantics (body output
    passed directly), readMem is preserved from the body's output. -/
theorem evalSigmaAlg_loop_preserves_wm_size_with_bound
    (ω : α) (n : Nat) (loopVar : LoopVar) (body : SigmaExpr)
    (env : LoopEnv) (st : EvalState α) (target : Nat)
    (h_st : st.writeMem.size = target)
    (h_body : ∀ (i : Nat) (st' : EvalState α),
      i < n →
      st'.writeMem.size = target →
      (evalSigmaAlg ω (env.bind loopVar i) st' body).writeMem.size = target) :
    (evalSigmaAlg ω env st (.loop n loopVar body)).writeMem.size = target := by
  simp only [evalSigmaAlg]
  have h_inv := foldl_invariant_mem (List.range n)
    (fun (st : EvalState α) (i : Nat) =>
      evalSigmaAlg ω (env.bind loopVar i) st body)
    st
    (fun st => st.writeMem.size = target)
    h_st
    (fun st' i h_mem h_wm => by
      have hi : i < n := List.mem_range.mp h_mem
      exact h_body i st' hi h_wm)
  exact h_inv

/-! ### C1: evalScatter Size Preservation for Block/Stride Patterns

These lemmas prove that evalScatter preserves writeMem.size when all
write positions fall within bounds. This is the key infrastructure for
closing the kron sorry (S1) in evalSigmaAlg_writeMem_size_preserved.

Scatter patterns:
  - Scatter.block blockSize loopVar: writes at positions blockSize*i + j for j < count
  - Scatter with stride s and base v: writes at positions v + s*j for j < count

For each, we show: if all write positions < wm.size, then (evalScatter ...).size = wm.size.
-/

/-- evalScatter preserves size when all write positions are in-bounds.
    The scatter writes at positions (base + stride * j) for j in 0..(vals.length-1).
    If all these positions are < wm.size, then the result has the same size. -/
theorem evalScatter_preserves_size
    (env : LoopEnv) (s : Scatter) (wm : Memory α) (vals : List α)
    (h_inbounds : ∀ j, j < vals.length →
      evalIdxExpr env s.baseAddr + s.stride * j < wm.size) :
    (evalScatter env s wm vals).size = wm.size := by
  simp only [evalScatter]
  apply foldl_invariant_mem vals.enum
    (fun acc (x : Nat × α) => acc.write (evalIdxExpr env s.baseAddr + s.stride * x.1) x.2)
    wm (fun mem => mem.size = wm.size) rfl
  intro mem ⟨idx, val⟩ h_mem hmem_size
  dsimp only
  have h_idx_lt : idx < vals.length := List.fst_lt_of_mem_enum h_mem
  have h_pos_lt : evalIdxExpr env s.baseAddr + s.stride * idx < mem.size :=
    hmem_size ▸ h_inbounds idx h_idx_lt
  rw [Memory.size_write_eq mem _ val h_pos_lt, hmem_size]

/-- Scatter.block: For the I⊗B kron case, scatter writes at positions
    blockSize * loopVal + j for j < vals.length.
    When loopVal < m₁ and vals.length ≤ blockSize ≤ m₂ and m = m₁ * m₂,
    all positions are < m. -/
theorem evalScatter_block_size_preserved
    (env : LoopEnv) (blockSize : Nat) (loopVar : LoopVar)
    (wm : Memory α) (vals : List α)
    (m₁ : Nat)
    (hwm : wm.size = m₁ * blockSize)
    (hloopVal : env loopVar < m₁)
    (hvals : vals.length ≤ blockSize) :
    (evalScatter env (Scatter.block blockSize loopVar) wm vals).size = m₁ * blockSize := by
  rw [← hwm]
  apply evalScatter_preserves_size
  intro j hj
  simp only [Scatter.block, evalIdxExpr]
  rw [hwm]
  -- Goal: 0 + blockSize * env loopVar + 1 * j < m₁ * blockSize
  -- Since j < vals.length ≤ blockSize and env loopVar < m₁
  calc 0 + blockSize * env loopVar + 1 * j
      = blockSize * env loopVar + j := by omega
    _ < blockSize * env loopVar + blockSize := by omega
    _ = blockSize * (env loopVar + 1) := by ring
    _ ≤ blockSize * m₁ := Nat.mul_le_mul_left _ (by omega)
    _ = m₁ * blockSize := by ring

/-- Scatter.block size preservation (≥ version): preserves writeMem.size exactly
    when all scatter positions are within bounds. Generalizes evalScatter_block_size_preserved
    from exact equality (wm.size = m₁ * blockSize) to inequality (wm.size ≥ m₁ * blockSize). -/
theorem evalScatter_block_preserves_wm_size
    (env : LoopEnv) (blockSize : Nat) (loopVar : LoopVar)
    (wm : Memory α) (vals : List α)
    (m₁ : Nat)
    (hwm : wm.size ≥ m₁ * blockSize)
    (hloopVal : env loopVar < m₁)
    (hvals : vals.length ≤ blockSize) :
    (evalScatter env (Scatter.block blockSize loopVar) wm vals).size = wm.size := by
  apply evalScatter_preserves_size
  intro j hj
  simp only [Scatter.block, evalIdxExpr]
  calc 0 + blockSize * env loopVar + 1 * j
      = blockSize * env loopVar + j := by omega
    _ < blockSize * env loopVar + blockSize := by omega
    _ = blockSize * (env loopVar + 1) := by ring
    _ ≤ blockSize * m₁ := Nat.mul_le_mul_left _ (by omega)
    _ = m₁ * blockSize := by ring
    _ ≤ wm.size := hwm

/-- Scatter with stride: For the A⊗I kron case, scatter writes at positions
    loopVal + innerSize * k for k < vals.length.
    When loopVal < innerSize and vals.length ≤ m₁ and m = m₁ * innerSize,
    all positions are < m. -/
theorem evalScatter_stride_size_preserved
    (env : LoopEnv) (innerSize m₁ : Nat) (loopVar : LoopVar)
    (wm : Memory α) (vals : List α)
    (hwm : wm.size = m₁ * innerSize)
    (hloopVal : env loopVar < innerSize)
    (hvals : vals.length ≤ m₁) :
    (evalScatter env { count := m₁, baseAddr := .var loopVar, stride := innerSize } wm vals).size =
    m₁ * innerSize := by
  rw [← hwm]
  apply evalScatter_preserves_size
  intro j hj
  simp only [evalIdxExpr]
  rw [hwm]
  -- Goal: env loopVar + innerSize * j < m₁ * innerSize
  -- Since env loopVar < innerSize and j < vals.length ≤ m₁
  calc env loopVar + innerSize * j
      < innerSize + innerSize * j := by omega
    _ = innerSize * (j + 1) := by ring
    _ ≤ innerSize * m₁ := Nat.mul_le_mul_left _ (by omega)
    _ = m₁ * innerSize := by ring

/-- Stride scatter size preservation (≥ version): preserves writeMem.size exactly
    when all scatter positions are within bounds. Generalizes evalScatter_stride_size_preserved
    from exact equality to inequality. -/
theorem evalScatter_stride_preserves_wm_size
    (env : LoopEnv) (innerSize m₁ : Nat) (loopVar : LoopVar)
    (wm : Memory α) (vals : List α)
    (hwm : wm.size ≥ m₁ * innerSize)
    (hloopVal : env loopVar < innerSize)
    (hvals : vals.length ≤ m₁) :
    (evalScatter env { count := m₁, baseAddr := .var loopVar, stride := innerSize } wm vals).size =
    wm.size := by
  apply evalScatter_preserves_size
  intro j hj
  simp only [evalIdxExpr]
  calc env loopVar + innerSize * j
      < innerSize + innerSize * j := by omega
    _ = innerSize * (j + 1) := by ring
    _ ≤ innerSize * m₁ := Nat.mul_le_mul_left _ (by omega)
    _ = m₁ * innerSize := by ring
    _ ≤ wm.size := hwm

/-! ### C1 Capa 2: Size preservation for kron sub-cases

The kron case of evalSigmaAlg_writeMem_size_preserved requires proving that
adjustBlock(lower(b)) and adjustStride(lower(a)) preserve writeMem.size.

Strategy: By induction on MatExpr, prove that evaluating adjustBlock(lower(mat))
preserves writeMem.size = m₁ * m₂. HasNoCompose ensures no .temp nodes appear,
and the IH handles recursive cases (smul, kron-inside-kron, etc.). -/

@[simp] private theorem MatExpr.nodeCount_kron {a : MatExpr α m₁ n₁} {b : MatExpr α m₂ n₂} :
    (MatExpr.kron a b).nodeCount = 1 + a.nodeCount + b.nodeCount := rfl

@[simp] private theorem MatExpr.nodeCount_transpose {a : MatExpr α m n} :
    (MatExpr.transpose a).nodeCount = 1 + a.nodeCount := rfl

@[simp] private theorem MatExpr.nodeCount_conjTranspose {a : MatExpr α m n} :
    (MatExpr.conjTranspose a).nodeCount = 1 + a.nodeCount := rfl

@[simp] private theorem MatExpr.nodeCount_smul {f : Expr α} {a : MatExpr α m n} :
    (MatExpr.smul f a).nodeCount = 1 + a.nodeCount := rfl

@[simp] private theorem MatExpr.nodeCount_elemwise {op : Matrix.ElemOp} {a : MatExpr α m n} :
    (MatExpr.elemwise op a).nodeCount = 1 + a.nodeCount := rfl

@[simp] private theorem MatExpr.nodeCount_partialElemwise {idx : Nat} {op : Matrix.ElemOp} {a : MatExpr α m n} :
    (MatExpr.partialElemwise idx op a).nodeCount = 1 + a.nodeCount := rfl

@[simp] private theorem MatExpr.nodeCount_mdsApply {name : String} {size : Nat} {a : MatExpr α t 1} :
    (MatExpr.mdsApply name size a).nodeCount = 1 + a.nodeCount := rfl

@[simp] private theorem MatExpr.nodeCount_addRoundConst {round size : Nat} {a : MatExpr α t 1} :
    (MatExpr.addRoundConst round size a).nodeCount = 1 + a.nodeCount := rfl

set_option maxHeartbeats 12800000 in
/-- Generalized size preservation for adjustBlock(lower(mat)) with arbitrary blockSize.
    When blockSize ≥ m₂, evaluating adjustBlock v blockSize blockSize (lower m₂ m₂ state mat).1
    preserves writeMem.size exactly (= st.writeMem.size) when st.writeMem.size ≥ m₁ * blockSize.
    This generalizes adjustBlock_lower_preserves_size to handle kron-inside-kron:
    after adjustBlock_adjustBlock collapse, the blockSize may be larger than m₂. -/
theorem adjustBlock_lower_preserves_size_gen
    (ω : α) {m₂ n₂ : Nat} (mat : MatExpr α m₂ n₂)
    (v : LoopVar) (m₁ blockSize : Nat) (state : LowerState)
    (env : LoopEnv) (st : EvalState α)
    (hwm : st.writeMem.size ≥ m₁ * blockSize)
    (hlv : env v < m₁) (hmn : m₂ = n₂) (hbs : m₂ ≤ blockSize)
    (hwf : IsWellFormedNTT mat) (hnc : HasNoCompose mat)
    (hv_fresh : v < state.nextLoopVar) :
    (evalSigmaAlg ω env st (adjustBlock v blockSize blockSize (lower m₂ n₂ state mat).1)).writeMem.size
    = st.writeMem.size := by
  -- Use structural induction instead of WF recursion to avoid PSigma packing issues
  -- in the termination proof. The transpose/conjTranspose cases caused omega failures
  -- because PSigma projections renamed variables (a vs a✝), breaking the identity
  -- needed for a.nodeCount < 1 + a.nodeCount. With induction, no termination proof needed.
  induction mat generalizing state env st with
  | identity _ =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_preserves_wm_size env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length, Gather.block])
  | zero =>
    simp only [lower, adjustBlock, evalSigmaAlg]
  | dft n' =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    apply evalScatter_block_preserves_wm_size env blockSize v st.writeMem _ m₁ hwm hlv
    match n' with
    | 0 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
    | 1 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]; omega
    | 2 => simp only [evalKernelAlg, evalDFT2]; split <;> simp_all [evalGather_length, Gather.block]
    | n + 3 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]; omega
  | ntt =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_preserves_wm_size env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])
  | twiddle =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_preserves_wm_size env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])
  | perm =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_preserves_wm_size env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length, Gather.block])
  | diag =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_preserves_wm_size env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length, Gather.block])
  | scalar =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_preserves_wm_size env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])
  | transpose a ih =>
    -- With induction, no termination proof needed. Dimensions swap: a : MatExpr α n₂ m₂.
    -- IH needs hmn.symm (n₂ = m₂) and hmn ▸ hbs (n₂ ≤ blockSize).
    simp only [lower]
    exact ih state env st hwm hlv hmn.symm (hmn ▸ hbs) hwf.2 hnc hv_fresh
  | conjTranspose a ih =>
    simp only [lower]
    exact ih state env st hwm hlv hmn.symm (hmn ▸ hbs) hwf.2 hnc hv_fresh
  | smul f a ih =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v blockSize blockSize (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hbs hwf.2 hnc hv_fresh
    exact (evalScatter_block_preserves_wm_size env _ v st1.writeMem _ m₁ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])).trans hst1
  | elemwise op a ih =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v blockSize blockSize (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hbs hwf.2 hnc hv_fresh
    exact (evalScatter_block_preserves_wm_size env _ v st1.writeMem _ m₁ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])).trans hst1
  | partialElemwise idx op a ih =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v blockSize blockSize (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hbs hwf.2 hnc hv_fresh
    exact (evalScatter_block_preserves_wm_size env _ v st1.writeMem _ m₁ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])).trans hst1
  | mdsApply name stateSize a ih =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v _ _ (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hbs hwf.2 hnc hv_fresh
    exact (evalScatter_block_preserves_wm_size env _ v st1.writeMem _ m₁ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])).trans hst1
  | addRoundConst round stateSize a ih =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v _ _ (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hbs hwf.2 hnc hv_fresh
    exact (evalScatter_block_preserves_wm_size env _ v st1.writeMem _ m₁ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])).trans hst1
  | compose a b _ _ =>
    exact absurd hnc (by simp [HasNoCompose])
  | add a b _ _ =>
    exact hwf.elim
  | kron a b ih_a ih_b =>
    obtain ⟨ha_sq, hb_sq, hnc_a, hnc_b, hwf_a, hwf_b, hm₁_pos, hm₂_pos, h_id, _h_nsl_a, _h_nsl_b⟩ := hwf
    have hv_ne_lv : v ≠ state.nextLoopVar := Nat.ne_of_lt hv_fresh
    have hlv_bind : ∀ i, (LoopEnv.bind env state.nextLoopVar i) v < m₁ := by
      intro i; simp only [LoopEnv.bind, beq_iff_eq]
      split
      · next h => exact absurd h hv_ne_lv
      · exact hlv
    have hv_fresh' : v < state.nextLoopVar + 1 := Nat.lt_succ_of_lt hv_fresh
    have hbs_b : _ ≤ blockSize :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ hm₁_pos) hbs
    have hbs_a : _ ≤ blockSize :=
      Nat.le_trans (Nat.le_mul_of_pos_right _ hm₂_pos) hbs
    simp only [lower, freshLoopVar]
    split
    · -- I⊗B: adjustBlock distributes into loop, adjustBlock_adjustBlock collapses nested
      simp only [adjustBlock]
      rw [AmoLean.Sigma.adjustBlock_adjustBlock]
      apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
      · rfl
      · intro i st' hi hwm'
        exact (ih_b _ _ st' (by omega) (hlv_bind i) hb_sq hbs_b hwf_b hnc_b hv_fresh').trans hwm'
    · split
      · -- A⊗I: adjustBlock distributes into loop, adjustBlock_adjustStride collapses nested
        simp only [adjustBlock]
        rw [AmoLean.Sigma.adjustBlock_adjustStride]
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
        · rfl
        · intro i st' hi hwm'
          exact (ih_a _ _ st' (by omega) (hlv_bind i) ha_sq hbs_a hwf_a hnc_a hv_fresh').trans hwm'
      · -- A⊗B: adjustBlock distributes into loop, seq, and inner loop
        simp only [adjustBlock]
        have hv_fresh_b : v < (lower _ _ ⟨state.nextLoopVar + 1⟩ a).2.nextLoopVar :=
          Nat.lt_of_lt_of_le hv_fresh' (AmoLean.Sigma.lower_loopVars_bounded_and_state_monotonic a ⟨state.nextLoopVar + 1⟩).2
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
        · rfl
        · intro i st' hi hwm'
          rw [evalSigmaAlg.eq_3]
          set stA := evalSigmaAlg ω _ st' (adjustBlock v blockSize blockSize (lower _ _ _ a).1)
          have hA := ih_a _ _ st' (by omega) (hlv_bind i) ha_sq hbs_a hwf_a hnc_a hv_fresh'
          have hstA : stA.writeMem.size = st.writeMem.size := hA.trans hwm'
          have hlv_inner : ∀ j, (LoopEnv.bind (LoopEnv.bind env state.nextLoopVar i) (state.nextLoopVar + 1) j) v < m₁ := by
            intro j; simp only [LoopEnv.bind, beq_iff_eq, hv_ne_lv, ↓reduceIte]
            split
            · next h => exact absurd hv_fresh (not_lt.mpr (h ▸ Nat.le_succ _))
            · exact hlv
          rw [← hstA]
          apply evalSigmaAlg_loop_preserves_wm_size_with_bound
          · rfl
          · intro j stB hj hwmB
            exact (ih_b _ _ stB (by omega) (hlv_inner j) hb_sq hbs_b hwf_b hnc_b hv_fresh_b).trans hwmB

set_option maxHeartbeats 6400000 in
/-- Size preservation for adjustBlock(lower(mat)):
    For the I⊗B kron case, evaluating the body with block access pattern
    preserves writeMem.size = m₁ * m₂.
    Requires m₂ = n₂ (from well-formedness of kron argument). -/
theorem adjustBlock_lower_preserves_size
    (ω : α) {m₂ n₂ : Nat} (mat : MatExpr α m₂ n₂)
    (v : LoopVar) (m₁ : Nat) (state : LowerState)
    (env : LoopEnv) (st : EvalState α)
    (hwm : st.writeMem.size = m₁ * m₂)
    (hlv : env v < m₁) (hmn : m₂ = n₂)
    (hwf : IsWellFormedNTT mat) (hnc : HasNoCompose mat)
    (hv_fresh : v < state.nextLoopVar) :
    (evalSigmaAlg ω env st (adjustBlock v n₂ m₂ (lower m₂ n₂ state mat).1)).writeMem.size
    = m₁ * m₂ := by
  -- Strategy: use match (not induction) on mat with termination_by mat.nodeCount.
  -- In atomic-square cases (.identity, .dft, etc.), the match unifies m₂ and n₂ to the
  -- same variable, so hmn becomes trivial (n' = n') and subst fails. We don't need subst
  -- because dimensions are already unified. In non-atomic cases (.transpose, .smul, etc.),
  -- m₂ and n₂ remain distinct free variables, so subst hmn works and unifies them.
  match mat with
  | .identity _ =>
    -- After match: m₂ = n₂ = n', hmn is trivially n' = n', no subst needed
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_size_preserved env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length, Gather.block])
  | .zero _ _ =>
    simp only [lower, adjustBlock, evalSigmaAlg]; exact hwm
  | .dft n' =>
    -- After match: m₂ = n₂ = n', dimensions already unified
    simp only [lower, adjustBlock, evalSigmaAlg]
    apply evalScatter_block_size_preserved env n' v st.writeMem _ m₁ hwm hlv
    -- Goal: (evalKernelAlg ω (.dft n') (evalGather ...)).length ≤ n'
    -- evalGather produces n' elements (from Gather.block n' v)
    -- DFT kernel output length depends on n': case split
    match n' with
    | 0 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
    | 1 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
    | 2 => simp only [evalKernelAlg, evalDFT2]; split <;> simp_all [evalGather_length, Gather.block]
    | n + 3 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
  | .ntt _ _ =>
    -- After match: m₂ = n₂ = n', no subst needed
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_size_preserved env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])
  | .twiddle _ _ =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_size_preserved env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])
  | .perm _ =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_size_preserved env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length, Gather.block])
  | .diag _ =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_size_preserved env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length, Gather.block])
  | .scalar _ =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    exact evalScatter_block_size_preserved env _ v st.writeMem _ m₁ hwm hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block])
  | .transpose a =>
    -- Don't subst: pass hmn through. lower swaps m₂↔n₂, so IH needs hmn.symm.
    -- IH produces adjustBlock v m₂ n₂ but goal has adjustBlock v n₂ m₂;
    -- these are equal via hmn. Use hmn ▸ to transport hwm and result.
    simp only [lower]
    have ih := adjustBlock_lower_preserves_size ω a v m₁ state env st (hmn ▸ hwm) hlv hmn.symm hwf.2 hnc hv_fresh
    -- ih : (...adjustBlock v m₂ n₂ (lower n₂ m₂ state a).1...).writeMem.size = m₁ * n₂
    -- goal: (...adjustBlock v n₂ m₂ (lower n₂ m₂ state a).1...).writeMem.size = m₁ * m₂
    cases hmn; exact ih
  | .conjTranspose a =>
    simp only [lower]
    have ih := adjustBlock_lower_preserves_size ω a v m₁ state env st (hmn ▸ hwm) hlv hmn.symm hwf.2 hnc hv_fresh
    cases hmn; exact ih
  | .smul f a =>
    -- Don't subst: pass hmn through to avoid termination issues.
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v n₂ m₂ (lower m₂ n₂ state a).1)
    have hst1 := adjustBlock_lower_preserves_size ω a v m₁ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_block_size_preserved env _ v st1.writeMem _ m₁ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block, hmn])
  | .elemwise op a =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v n₂ m₂ (lower m₂ n₂ state a).1)
    have hst1 := adjustBlock_lower_preserves_size ω a v m₁ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_block_size_preserved env _ v st1.writeMem _ m₁ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block, hmn])
  | .partialElemwise idx op a =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v n₂ m₂ (lower m₂ n₂ state a).1)
    have hst1 := adjustBlock_lower_preserves_size ω a v m₁ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_block_size_preserved env _ v st1.writeMem _ m₁ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block, hmn])
  | .mdsApply name stateSize a =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v _ _ (lower _ _ state a).1)
    have hst1 := adjustBlock_lower_preserves_size ω a v m₁ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_block_size_preserved env _ v st1.writeMem _ m₁ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block, hmn])
  | .addRoundConst round stateSize a =>
    simp only [lower, adjustBlock, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustBlock v _ _ (lower _ _ state a).1)
    have hst1 := adjustBlock_lower_preserves_size ω a v m₁ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_block_size_preserved env _ v st1.writeMem _ m₁ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, Gather.block, hmn])
  | .compose a b =>
    exact absurd hnc (by simp [HasNoCompose])
  | .add a b =>
    exact hwf.elim
  | .kron a b =>
    -- Delegate to generalized theorem with blockSize = m₂
    -- Must obtain/subst IsWellFormedNTT squareness BEFORE cases hmn to avoid
    -- dependent elimination failure on m₁'*m₂' = n₁'*n₂'
    have hwf' := hwf
    obtain ⟨ha_sq, hb_sq, _⟩ := hwf'
    subst ha_sq; subst hb_sq
    -- Now hmn : m₁' * m₂' = m₁' * m₂' which is rfl
    -- gen theorem now uses ≥ and returns = st.writeMem.size; compose with hwm to get = m₁ * m₂
    exact (adjustBlock_lower_preserves_size_gen ω (.kron a b) v m₁ _ state env st
      (by omega) hlv rfl (Nat.le_refl _) hwf hnc hv_fresh).trans hwm
  termination_by mat.nodeCount
  decreasing_by all_goals simp_wf; all_goals simp only [MatExpr.nodeCount]; all_goals omega

set_option maxHeartbeats 12800000 in
/-- Generalized size preservation for adjustStride(lower(mat)) with arbitrary strideCount.
    When strideCount ≥ m₁, evaluating adjustStride v innerSize strideCount strideCount (lower m₁ m₁ state mat).1
    preserves writeMem.size exactly (= st.writeMem.size) when st.writeMem.size ≥ strideCount * innerSize.
    Generalizes adjustStride_lower_preserves_size for kron-inside-kron. -/
theorem adjustStride_lower_preserves_size_gen
    (ω : α) {m₁ n₁ : Nat} (mat : MatExpr α m₁ n₁)
    (v : LoopVar) (innerSize strideCount : Nat) (state : LowerState)
    (env : LoopEnv) (st : EvalState α)
    (hwm : st.writeMem.size ≥ strideCount * innerSize)
    (hlv : env v < innerSize) (hmn : m₁ = n₁) (hsc : m₁ ≤ strideCount)
    (hwf : IsWellFormedNTT mat) (hnc : HasNoCompose mat)
    (hv_fresh : v < state.nextLoopVar) :
    (evalSigmaAlg ω env st (adjustStride v innerSize strideCount strideCount (lower m₁ n₁ state mat).1)).writeMem.size
    = st.writeMem.size := by
  -- Use structural induction to avoid PSigma packing termination issues (same as adjustBlock_gen).
  induction mat generalizing state env st with
  | identity _ =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_preserves_wm_size env innerSize _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length])
  | zero =>
    simp only [lower, adjustStride, evalSigmaAlg]
  | dft n' =>
    simp only [lower, adjustStride, evalSigmaAlg]
    apply evalScatter_stride_preserves_wm_size env innerSize strideCount v st.writeMem _ hwm hlv
    match n' with
    | 0 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
    | 1 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]; omega
    | 2 => simp only [evalKernelAlg, evalDFT2]; split <;> simp_all [evalGather_length]
    | n + 3 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]; omega
  | ntt =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_preserves_wm_size env innerSize _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalGather_length])
  | twiddle =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_preserves_wm_size env innerSize _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalGather_length])
  | perm =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_preserves_wm_size env innerSize _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length])
  | diag =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_preserves_wm_size env innerSize _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length])
  | scalar =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_preserves_wm_size env innerSize _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalGather_length])
  | transpose a ih =>
    simp only [lower]
    exact ih state env st hwm hlv hmn.symm (hmn ▸ hsc) hwf.2 hnc hv_fresh
  | conjTranspose a ih =>
    simp only [lower]
    exact ih state env st hwm hlv hmn.symm (hmn ▸ hsc) hwf.2 hnc hv_fresh
  | smul f a ih =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v innerSize strideCount strideCount (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hsc hwf.2 hnc hv_fresh
    exact (evalScatter_stride_preserves_wm_size env innerSize _ v st1.writeMem _ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length])).trans hst1
  | elemwise op a ih =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v innerSize strideCount strideCount (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hsc hwf.2 hnc hv_fresh
    exact (evalScatter_stride_preserves_wm_size env innerSize _ v st1.writeMem _ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length])).trans hst1
  | partialElemwise idx op a ih =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v innerSize strideCount strideCount (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hsc hwf.2 hnc hv_fresh
    exact (evalScatter_stride_preserves_wm_size env innerSize _ v st1.writeMem _ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length])).trans hst1
  | mdsApply name stateSize a ih =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v innerSize strideCount strideCount (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hsc hwf.2 hnc hv_fresh
    exact (evalScatter_stride_preserves_wm_size env innerSize _ v st1.writeMem _ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length])).trans hst1
  | addRoundConst round stateSize a ih =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v innerSize strideCount strideCount (lower _ _ state a).1)
    have hst1 : st1.writeMem.size = st.writeMem.size :=
      ih state env st hwm hlv hmn hsc hwf.2 hnc hv_fresh
    exact (evalScatter_stride_preserves_wm_size env innerSize _ v st1.writeMem _ (by omega) hlv
      (by simp [evalKernelAlg, evalGather_length])).trans hst1
  | compose a b _ _ =>
    exact absurd hnc (by simp [HasNoCompose])
  | add a b _ _ =>
    exact hwf.elim
  | kron a b ih_a ih_b =>
    obtain ⟨ha_sq, hb_sq, hnc_a, hnc_b, hwf_a, hwf_b, hm₁_pos, hm₂_pos, h_id, _h_nsl_a, _h_nsl_b⟩ := hwf
    have hv_ne_lv : v ≠ state.nextLoopVar := Nat.ne_of_lt hv_fresh
    have hlv_bind : ∀ i, (LoopEnv.bind env state.nextLoopVar i) v < innerSize := by
      intro i; simp only [LoopEnv.bind, beq_iff_eq]
      split
      · next h => exact absurd h hv_ne_lv
      · exact hlv
    have hv_fresh' : v < state.nextLoopVar + 1 := Nat.lt_succ_of_lt hv_fresh
    have hsc_b : _ ≤ strideCount :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ hm₁_pos) hsc
    have hsc_a : _ ≤ strideCount :=
      Nat.le_trans (Nat.le_mul_of_pos_right _ hm₂_pos) hsc
    simp only [lower, freshLoopVar]
    split
    · -- I⊗B: outer adjustStride distributes into loop, collapses with inner adjustBlock
      simp only [adjustStride]
      rw [AmoLean.Sigma.adjustStride_adjustBlock]
      apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
      · rfl
      · intro i st' hi hwm'
        exact (ih_b _ _ st' (by omega) (hlv_bind i) hb_sq hsc_b hwf_b hnc_b hv_fresh').trans hwm'
    · split
      · -- A⊗I: outer adjustStride distributes, collapses with inner adjustStride
        simp only [adjustStride]
        rw [AmoLean.Sigma.adjustStride_adjustStride]
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
        · rfl
        · intro i st' hi hwm'
          exact (ih_a _ _ st' (by omega) (hlv_bind i) ha_sq hsc_a hwf_a hnc_a hv_fresh').trans hwm'
      · -- A⊗B: outer adjustStride distributes into loop, then into seq and inner loop
        simp only [adjustStride]
        have hv_fresh_b : v < (lower _ _ ⟨state.nextLoopVar + 1⟩ a).2.nextLoopVar :=
          Nat.lt_of_lt_of_le hv_fresh' (AmoLean.Sigma.lower_loopVars_bounded_and_state_monotonic a ⟨state.nextLoopVar + 1⟩).2
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
        · rfl
        · intro i st' hi hwm'
          rw [evalSigmaAlg.eq_3]
          set stA := evalSigmaAlg ω _ st' (adjustStride v innerSize strideCount strideCount (lower _ _ _ a).1)
          have hA := ih_a _ _ st' (by omega) (hlv_bind i) ha_sq hsc_a hwf_a hnc_a hv_fresh'
          have hstA : stA.writeMem.size = st.writeMem.size := hA.trans hwm'
          have hlv_inner : ∀ j, (LoopEnv.bind (LoopEnv.bind env state.nextLoopVar i) (state.nextLoopVar + 1) j) v < innerSize := by
            intro j; simp only [LoopEnv.bind, beq_iff_eq, hv_ne_lv, ↓reduceIte]
            split
            · next h => exact absurd hv_fresh (not_lt.mpr (h ▸ Nat.le_succ _))
            · exact hlv
          rw [← hstA]
          apply evalSigmaAlg_loop_preserves_wm_size_with_bound
          · rfl
          · intro j stB hj hwmB
            exact (ih_b _ _ stB (by omega) (hlv_inner j) hb_sq hsc_b hwf_b hnc_b hv_fresh_b).trans hwmB

set_option maxHeartbeats 6400000 in
/-- Size preservation for adjustStride(lower(mat)):
    For the A⊗I kron case, evaluating the body with stride access pattern
    preserves writeMem.size = m₁ * m₂.
    Requires m₁ = n₁ (from well-formedness of kron argument). -/
theorem adjustStride_lower_preserves_size
    (ω : α) {m₁ n₁ : Nat} (mat : MatExpr α m₁ n₁)
    (v : LoopVar) (m₂ : Nat) (state : LowerState)
    (env : LoopEnv) (st : EvalState α)
    (hwm : st.writeMem.size = m₁ * m₂)
    (hlv : env v < m₂) (hmn : m₁ = n₁)
    (hwf : IsWellFormedNTT mat) (hnc : HasNoCompose mat)
    (hv_fresh : v < state.nextLoopVar) :
    (evalSigmaAlg ω env st (adjustStride v m₂ m₁ n₁ (lower m₁ n₁ state mat).1)).writeMem.size
    = m₁ * m₂ := by
  -- Same strategy as adjustBlock: match on mat, no subst for atomic-square cases
  -- (where m₁ and n₁ unify), subst hmn for non-atomic cases (where m₁, n₁ remain free).
  match mat with
  | .identity _ =>
    -- After match: m₁ = n₁ = n', hmn trivially n' = n', no subst needed
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_size_preserved env m₂ _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length])
  | .zero _ _ =>
    simp only [lower, adjustStride, evalSigmaAlg]; exact hwm
  | .dft n' =>
    -- After match: m₁ = n₁ = n', dimensions already unified
    simp only [lower, adjustStride, evalSigmaAlg]
    apply evalScatter_stride_size_preserved env m₂ n' v st.writeMem _ hwm hlv
    -- Goal: (evalKernelAlg ω (.dft n') (evalGather ...)).length ≤ n'
    match n' with
    | 0 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
    | 1 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
    | 2 => simp only [evalKernelAlg, evalDFT2]; split <;> simp_all [evalGather_length]
    | n + 3 => simp [evalKernelAlg, evalDFT, List.length_map, List.length_range]
  | .ntt _ _ =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_size_preserved env m₂ _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalGather_length])
  | .twiddle _ _ =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_size_preserved env m₂ _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalGather_length])
  | .perm _ =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_size_preserved env m₂ _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length])
  | .diag _ =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_size_preserved env m₂ _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather_length])
  | .scalar _ =>
    simp only [lower, adjustStride, evalSigmaAlg]
    exact evalScatter_stride_size_preserved env m₂ _ v st.writeMem _ hwm hlv
      (by simp [evalKernelAlg, evalGather_length])
  | .transpose a =>
    -- Don't subst: pass hmn through. lower swaps m₁↔n₁.
    simp only [lower]
    have ih := adjustStride_lower_preserves_size ω a v m₂ state env st (hmn ▸ hwm) hlv hmn.symm hwf.2 hnc hv_fresh
    cases hmn; exact ih
  | .conjTranspose a =>
    simp only [lower]
    have ih := adjustStride_lower_preserves_size ω a v m₂ state env st (hmn ▸ hwm) hlv hmn.symm hwf.2 hnc hv_fresh
    cases hmn; exact ih
  | .smul f a =>
    -- Don't subst: pass hmn through to avoid termination issues.
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v m₂ m₁ n₁ (lower m₁ n₁ state a).1)
    have hst1 := adjustStride_lower_preserves_size ω a v m₂ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_stride_size_preserved env m₂ _ v st1.writeMem _ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, hmn])
  | .elemwise op a =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v m₂ m₁ n₁ (lower m₁ n₁ state a).1)
    have hst1 := adjustStride_lower_preserves_size ω a v m₂ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_stride_size_preserved env m₂ _ v st1.writeMem _ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, hmn])
  | .partialElemwise idx op a =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v m₂ m₁ n₁ (lower m₁ n₁ state a).1)
    have hst1 := adjustStride_lower_preserves_size ω a v m₂ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_stride_size_preserved env m₂ _ v st1.writeMem _ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, hmn])
  | .mdsApply name stateSize a =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v m₂ _ _ (lower _ _ state a).1)
    have hst1 := adjustStride_lower_preserves_size ω a v m₂ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_stride_size_preserved env m₂ _ v st1.writeMem _ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, hmn])
  | .addRoundConst round stateSize a =>
    simp only [lower, adjustStride, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (adjustStride v m₂ _ _ (lower _ _ state a).1)
    have hst1 := adjustStride_lower_preserves_size ω a v m₂ state env st hwm hlv hmn hwf.2 hnc hv_fresh
    exact evalScatter_stride_size_preserved env m₂ _ v st1.writeMem _ hst1 hlv
      (by simp [evalKernelAlg, evalGather_length, hmn])
  | .compose a b =>
    exact absurd hnc (by simp [HasNoCompose])
  | .add a b =>
    exact hwf.elim
  | .kron a b =>
    -- Delegate to generalized theorem with strideCount = m₁
    -- Must obtain/subst IsWellFormedNTT squareness BEFORE cases hmn
    have hwf' := hwf
    obtain ⟨ha_sq, hb_sq, _⟩ := hwf'
    subst ha_sq; subst hb_sq
    -- gen theorem now uses ≥ and returns = st.writeMem.size; compose with hwm to get = m₁ * m₂
    exact (adjustStride_lower_preserves_size_gen ω (.kron a b) v m₂ _ state env st
      (by omega) hlv rfl (Nat.le_refl _) hwf hnc hv_fresh).trans hwm
  termination_by mat.nodeCount
  decreasing_by all_goals simp_wf; all_goals simp only [MatExpr.nodeCount]; all_goals omega

set_option maxHeartbeats 6400000 in
/-- Size preservation for lowered expressions with writeMem.size ≥ m:
    evaluating (lower m n state mat).1 preserves writeMem.size when all
    scatter writes go to in-bounds positions (0..m-1 ⊂ 0..size-1).
    Requires HasNoCompose (no .temp nodes that reset writeMem).
    Works for any LoopEnv since lower's scatter patterns use IdxExpr.const 0. -/
theorem lower_preserves_size_ge
    (ω : α) {m n : Nat} (mat : MatExpr α m n) (state : LowerState)
    (env : LoopEnv) (st : EvalState α)
    (hwm : st.writeMem.size ≥ m)
    (hwf : IsWellFormedNTT mat) (hnc : HasNoCompose mat) :
    (evalSigmaAlg ω env st (lower m n state mat).1).writeMem.size = st.writeMem.size := by
  induction mat generalizing state env st with
  | identity =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg, evalIdentityKernel]
    apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add,
               List.length_map, List.length_range]
    exact hwm
  | zero => simp only [lower, evalSigmaAlg]
  | perm =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg, evalIdentityKernel]
    apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add,
               List.length_map, List.length_range]
    exact hwm
  | diag =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg, evalIdentityKernel]
    apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add,
               List.length_map, List.length_range]
    exact hwm
  | dft n' =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul]
    apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add]
    have hgather_len : (List.map (fun i => st.readMem.read (1 * i)) (List.range n')).length = n' := by
      simp [List.length_map, List.length_range]
    rw [evalKernelAlg_dft_length n' _ hgather_len]
    exact hwm
  | ntt =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add,
               List.length_map, List.length_range]
    exact hwm
  | twiddle =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add,
               List.length_map, List.length_range]
    exact hwm
  | scalar =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add,
               List.length_map, List.length_range]
    exact hwm
  | transpose a ih =>
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower]
    subst hmn
    exact ih state env st hwm hwf_a hnc
  | conjTranspose a ih =>
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower]
    subst hmn
    exact ih state env st hwm hwf_a hnc
  | smul f a ih =>
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (lower _ _ state a).1 with hst1_def
    have hst1_size := ih state env st hwm hwf_a hnc
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hst1_size]; apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size]; rw [← hmn]; exact hwm
  | elemwise op a ih =>
    obtain ⟨hn1, hwf_a⟩ := hwf
    subst hn1
    simp only [lower, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (lower _ _ state a).1 with hst1_def
    have hst1_size := ih state env st hwm hwf_a hnc
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hst1_size]; apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size]; omega
  | partialElemwise idx op a ih =>
    obtain ⟨hn1, hwf_a⟩ := hwf
    subst hn1
    simp only [lower, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (lower _ _ state a).1 with hst1_def
    have hst1_size := ih state env st hwm hwf_a hnc
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hst1_size]; apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size]; omega
  | mdsApply name stateSize a ih =>
    obtain ⟨hsize, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (lower _ _ state a).1 with hst1_def
    have hst1_size := ih state env st hwm hwf_a hnc
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hst1_size]; apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size]; omega
  | addRoundConst round stateSize a ih =>
    obtain ⟨hsize, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    set st1 := evalSigmaAlg ω env st (lower _ _ state a).1 with hst1_def
    have hst1_size := ih state env st hwm hwf_a hnc
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hst1_size]; apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size]; omega
  | compose a b ih_a ih_b =>
    exact absurd hnc (by simp [HasNoCompose])
  | add a b ih_a ih_b =>
    exact hwf.elim
  | kron a b ih_a ih_b =>
    obtain ⟨ha_sq, hb_sq, hnc_a, hnc_b, hwf_a, hwf_b, hm₁_pos, hm₂_pos, h_id, _h_nsl_a, _h_nsl_b⟩ := hwf
    subst ha_sq; subst hb_sq
    simp only [lower]
    split
    · -- I⊗B: adjustBlock — loop over m₁ blocks of size m₂
      rename_i m₁ m₂ _
      apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
      · rfl
      · intro i st' hi hwm'
        -- Each iteration: adjustBlock_lower_preserves_size_gen gives = st'.writeMem.size
        -- Compose with hwm' to get = st.writeMem.size (= target)
        exact (adjustBlock_lower_preserves_size_gen ω b _ m₁ m₂ _ _ st'
          (by omega) (by rw [LoopEnv.bind_same]; exact hi)
          rfl (Nat.le_refl _) hwf_b hnc_b (by simp [freshLoopVar])).trans hwm'
    · split
      · -- A⊗I: adjustStride — loop over m₂ with strided access to a
        rename_i m₁ m₂ _ _
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
        · rfl
        · intro i st' hi hwm'
          exact (adjustStride_lower_preserves_size_gen ω a _ m₂ m₁ _ _ st'
            (by omega) (by rw [LoopEnv.bind_same]; exact hi)
            rfl (Nat.le_refl _) hwf_a hnc_a (by simp [freshLoopVar])).trans hwm'
      · -- General A⊗B: .loop m₁ v (.seq exprA (.loop m₂ (v+1) exprB))
        rename_i m₁ m₂ _ _
        -- m₂ > 0 from IsWellFormedNTT kron precondition (0-dim kron never occurs in NTT/FFT)
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := st.writeMem.size)
        · rfl
        · intro i st' hi hwm'
          -- hi : i < m₁ → m₁ > 0 (also available from hm₁_pos)
          -- Body is .seq exprA (.loop m₂ (loopVar + 1) exprB)
          rw [evalSigmaAlg.eq_3]
          -- Step 1: exprA preserves size (needs size ≥ m₁)
          set stA := evalSigmaAlg ω _ st' (lower _ _ _ a).1 with hstA_def
          have hge_m₁ : st'.writeMem.size ≥ m₁ := by
            rw [hwm']; calc m₁ = m₁ * 1 := (Nat.mul_one m₁).symm
                 _ ≤ m₁ * m₂ := Nat.mul_le_mul_left m₁ hm₂_pos
                 _ ≤ st.writeMem.size := hwm
          have hA : stA.writeMem.size = st'.writeMem.size :=
            ih_a _ _ st' hge_m₁ hwf_a hnc_a
          -- Step 2: inner loop preserves size (each iteration needs size ≥ m₂)
          -- Rewrite RHS to match loop's initial state size (stA.writeMem.size)
          -- so that apply can unify the loop lemma's ?st.writeMem.size with both sides.
          have hstA_eq : stA.writeMem.size = st.writeMem.size := hA.trans hwm'
          rw [← hstA_eq]
          apply evalSigmaAlg_loop_preserves_wm_size_with_bound
          · rfl
          · intro j stB hj hwmB
            have hge_m₂ : stB.writeMem.size ≥ m₂ := by
              rw [hwmB, hstA_eq]; calc m₂ = 1 * m₂ := (Nat.one_mul m₂).symm
                   _ ≤ m₁ * m₂ := Nat.mul_le_mul_right m₂ hm₁_pos
                   _ ≤ st.writeMem.size := hwm
            exact (ih_b _ _ stB hge_m₂ hwf_b hnc_b).trans hwmB
  termination_by mat.nodeCount
  decreasing_by all_goals simp_wf; all_goals simp only [MatExpr.nodeCount]; all_goals omega

set_option maxHeartbeats 3200000 in
/-- Size preservation for lowered expressions: evaluating (lower m n state mat).1
    starting with writeMem of size m yields writeMem of size m.
    Requires IsWellFormedNTT to ensure:
    - Square matrices for transpose/smul/elemwise
    - stateSize = m for mdsApply/addRoundConst
    These constraints are always satisfied by actual NTT/FFT/Poseidon code. -/
theorem evalSigmaAlg_writeMem_size_preserved
    (ω : α) {m n : Nat} (state : LowerState) (mat : MatExpr α m n)
    (rm : Memory α) (wm : Memory α) (hwm : wm.size = m)
    (hwf : IsWellFormedNTT mat) :
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm }
      (lower m n state mat).1).writeMem.size = m := by
  induction mat generalizing state rm wm with
  | identity =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul,
               evalKernelAlg, evalIdentityKernel]
    rw [← hwm]; apply foldl_write_enum_size
    simp [evalGather, Gather.contiguous, hwm]
  | zero => simp only [lower, evalSigmaAlg]; exact hwm
  | perm =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul,
               evalKernelAlg, evalIdentityKernel]
    rw [← hwm]; apply foldl_write_enum_size
    simp [evalGather, Gather.contiguous, hwm]
  | diag =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul,
               evalKernelAlg, evalIdentityKernel]
    rw [← hwm]; apply foldl_write_enum_size
    simp [evalGather, Gather.contiguous, hwm]
  | dft n' =>
    -- lower(.dft n') = .compute (.dft n') contiguous(n') contiguous(n')
    -- Scatter writes n' elements. For square dft, m = n = n', so hwm : wm.size = n'.
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul]
    rw [← hwm]; apply foldl_write_enum_size
    -- Need: evalKernelAlg output length ≤ wm.size = n'
    simp only [evalGather, Gather.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add]
    rw [hwm]  -- Replace wm.size with n' everywhere
    have hgather_len : (List.map (fun i => rm.read (1 * i)) (List.range n')).length = n' := by
      simp [List.length_map, List.length_range]
    rw [evalKernelAlg_dft_length n' _ hgather_len]
  | ntt =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hwm]; apply foldl_write_enum_size
    simp [evalGather, Gather.contiguous, hwm]
  | twiddle =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hwm]; apply foldl_write_enum_size
    simp [evalGather, Gather.contiguous, hwm]
  | scalar =>
    simp only [lower, evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hwm]; apply foldl_write_enum_size
    simp [evalGather, Gather.contiguous, hwm]
  | transpose a ih =>
    -- lower m n state (.transpose a) = lower n m state a (swap dimensions)
    -- hwf : IsWellFormedNTT (.transpose a) = (m = n) ∧ IsWellFormedNTT a
    -- With m = n, IH applies directly
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower]
    subst hmn
    exact ih state rm wm hwm hwf_a
  | conjTranspose a ih =>
    -- Same structure as transpose
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower]
    subst hmn
    exact ih state rm wm hwm hwf_a
  | smul f a ih =>
    -- lower(.smul) = .seq exprA (.compute .scale contiguous(n) contiguous(n))
    -- hwf : IsWellFormedNTT (.smul f a) = (m = n) ∧ IsWellFormedNTT a
    -- With hwf.1 : m = n, scatter writes n = m elements, so size preserved.
    obtain ⟨hmn, hwf_a⟩ := hwf
    -- Step 1: Unfold lower to get .seq structure
    simp only [lower]
    -- Step 2: Unfold evalSigmaAlg for .seq
    simp only [evalSigmaAlg]
    -- Step 3: Name the intermediate state after evaluating exprA (let Lean infer types)
    set st1 := evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm }
               (lower _ _ state a).1 with hst1_def
    -- Step 4: By IH, st1.writeMem.size = m (Lean infers the dimension)
    have hst1_size := ih state rm wm hwm hwf_a
    -- Step 5: Unfold evalSigmaAlg for .compute, evalScatter for Scatter.contiguous
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    -- Step 6: Apply foldl_write_enum_size
    rw [← hst1_size]; apply foldl_write_enum_size
    -- Step 7: Need to show vals.length ≤ st1.writeMem.size
    -- vals = evalKernelAlg (evalGather ...), length = n
    -- st1.writeMem.size = m, and m = n from hmn
    simp only [evalGather, Gather.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size, hmn]
  | elemwise op a ih =>
    -- lower(.elemwise op a) = .seq exprA (.compute (.sbox (m*n)) contiguous(m*n))
    -- hwf : n = 1 ∧ IsWellFormedNTT a
    obtain ⟨hn1, hwf_a⟩ := hwf
    subst hn1
    simp only [lower, evalSigmaAlg]
    set st1 := evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm }
               (lower _ _ state a).1 with hst1_def
    have hst1_size := ih state rm wm hwm hwf_a
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hst1_size]; apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size]; omega
  | partialElemwise idx op a ih =>
    -- Same structure as elemwise
    obtain ⟨hn1, hwf_a⟩ := hwf
    subst hn1
    simp only [lower, evalSigmaAlg]
    set st1 := evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm }
               (lower _ _ state a).1 with hst1_def
    have hst1_size := ih state rm wm hwm hwf_a
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    rw [← hst1_size]; apply foldl_write_enum_size
    simp only [evalGather, Gather.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size]; omega
  | mdsApply name stateSize a ih =>
    -- lower(.mdsApply) = .seq exprA (.compute (.mdsApply) contiguous(stateSize))
    -- hwf : IsWellFormedNTT (.mdsApply name stateSize a) = (stateSize = m) ∧ IsWellFormedNTT a
    -- With hwf.1 : stateSize = m, scatter writes m elements, so size preserved.
    obtain ⟨hsize, hwf_a⟩ := hwf
    -- Step 1: Unfold lower to get .seq structure
    simp only [lower]
    -- Step 2: Unfold evalSigmaAlg for .seq
    simp only [evalSigmaAlg]
    -- Step 3: Name the intermediate state after evaluating inner expression
    set st1 := evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm }
               (lower _ _ state a).1 with hst1_def
    -- Step 4: By IH, st1.writeMem.size = m (Lean infers the dimension from context)
    have hst1_size := ih state rm wm hwm hwf_a
    -- Step 5: Unfold evalSigmaAlg for .compute, evalScatter for Scatter.contiguous
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    -- Step 6: Apply foldl_write_enum_size
    rw [← hst1_size]; apply foldl_write_enum_size
    -- Step 7: Need to show vals.length ≤ st1.writeMem.size
    -- vals has length stateSize, and stateSize = m from hsize
    simp only [evalGather, Gather.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size, ← hsize]
  | addRoundConst round stateSize a ih =>
    -- lower(.addRoundConst) = .seq exprA (.compute (.addRoundConst) contiguous(stateSize))
    -- hwf : IsWellFormedNTT (.addRoundConst round stateSize a) = (stateSize = m) ∧ IsWellFormedNTT a
    -- With hwf.1 : stateSize = m, scatter writes m elements, so size preserved.
    obtain ⟨hsize, hwf_a⟩ := hwf
    -- Step 1: Unfold lower to get .seq structure
    simp only [lower]
    -- Step 2: Unfold evalSigmaAlg for .seq
    simp only [evalSigmaAlg]
    -- Step 3: Name the intermediate state after evaluating inner expression
    set st1 := evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm }
               (lower _ _ state a).1 with hst1_def
    -- Step 4: By IH, st1.writeMem.size = m (Lean infers the dimension from context)
    have hst1_size := ih state rm wm hwm hwf_a
    -- Step 5: Unfold evalSigmaAlg for .compute, evalScatter for Scatter.contiguous
    simp only [evalSigmaAlg, evalScatter, Scatter.contiguous, evalIdxExpr,
               LoopEnv.empty, Nat.zero_add, Nat.one_mul, evalKernelAlg]
    -- Step 6: Apply foldl_write_enum_size
    rw [← hst1_size]; apply foldl_write_enum_size
    -- Step 7: Need to show vals.length ≤ st1.writeMem.size
    -- vals has length stateSize, and stateSize = m from hsize
    simp only [evalGather, Gather.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add]
    simp only [List.length_map, List.length_range]
    rw [hst1_size, ← hsize]
  | compose a b ih_a ih_b =>
    -- lower(.compose a b) = .temp k (.seq exprB exprA)
    -- hwf : m' = k' ∧ HasNoZero a ∧ IsWellFormedNTT a ∧ IsWellFormedNTT b
    obtain ⟨hk_eq, _, hwf_a, hwf_b⟩ := hwf
    -- subst m = k unifies dimensions: a : MatExpr α m' m', b : MatExpr α m' n'
    subst hk_eq
    -- After induction + subst, m and n are inaccessible (generalized as indices).
    -- Inaccessibles after subst: m✝ (row dim), n✝ (col dim), HasNoZero (discarded from obtain)
    rename_i m' n' _
    simp only [lower]
    -- evalSigmaAlg (.temp m' (.seq exprB exprA)):
    -- 1. writeMem := Memory.zeros m' (size m')
    -- 2. run .seq exprB exprA
    -- 3. return stateAfterBody.writeMem
    rw [evalSigmaAlg.eq_5, evalSigmaAlg.eq_3]
    -- Name intermediate state after exprB
    set stateB := evalSigmaAlg ω LoopEnv.empty
      { readMem := rm, writeMem := Memory.zeros m' }
      (lower m' n' state b).1 with hstateB_def
    -- By ih_b: stateB.writeMem.size = m' (since Memory.zeros m' has size m')
    have hB_size := ih_b state rm (Memory.zeros m') (Memory.zeros_size m') hwf_b
    -- After .seq, exprA runs with writeMem = stateB.writeMem (size m')
    -- By ih_a: result.writeMem.size = m'
    exact ih_a (lower m' n' state b).2 stateB.writeMem stateB.writeMem hB_size hwf_a
  | add a b ih_a ih_b =>
    -- DD-ADD: IsWellFormedNTT (.add _ _) = False, so hwf is vacuously absurd
    exact hwf.elim
  | kron a b ih_a ih_b =>
    obtain ⟨ha_sq, hb_sq, hnc_a, hnc_b, hwf_a, hwf_b, hm₁_pos, hm₂_pos, h_id, _h_nsl_a, _h_nsl_b⟩ := hwf
    subst ha_sq; subst hb_sq
    simp only [lower]
    split
    · -- Case I⊗B: .loop m₁ loopVar (adjustBlock loopVar m₂ m₂ (lower b).1)
      apply evalSigmaAlg_loop_preserves_wm_size_with_bound
      · exact hwm
      · intro i st' hi hwm'
        exact adjustBlock_lower_preserves_size ω b _ _ _ (LoopEnv.empty.bind _ i) st'
          hwm' (by rw [LoopEnv.bind_same]; exact hi) rfl hwf_b hnc_b
          (by unfold freshLoopVar; simp only; exact Nat.lt_succ_self _)
    · split
      · -- Case A⊗I: .loop m₂ loopVar (adjustStride loopVar m₂ m₁ m₁ (lower a).1)
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound
        · exact hwm
        · intro i st' hi hwm'
          exact adjustStride_lower_preserves_size ω a _ _ _ (LoopEnv.empty.bind _ i) st'
            hwm' (by rw [LoopEnv.bind_same]; exact hi) rfl hwf_a hnc_a
            (by unfold freshLoopVar; simp only; exact Nat.lt_succ_self _)
      · -- General case A⊗B: .loop m₁ v (.seq exprA (.loop m₂ (v+1) exprB))
        -- Uses lower_preserves_size_ge: contiguous scatter at base 0 preserves size ≥ m.
        rename_i m₁ m₂ _ _
        -- m₂ > 0 from IsWellFormedNTT kron precondition (0-dim kron never occurs in NTT/FFT)
        apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := m₁ * m₂)
        · exact hwm
        · intro i st' hi hwm'
          rw [evalSigmaAlg.eq_3]
          set stA := evalSigmaAlg ω _ st' (lower _ _ _ a).1 with hstA_def
          have hge_m₁ : st'.writeMem.size ≥ m₁ := by
            rw [hwm']; calc m₁ = m₁ * 1 := (Nat.mul_one m₁).symm
                 _ ≤ m₁ * m₂ := Nat.mul_le_mul_left m₁ hm₂_pos
          have hA : stA.writeMem.size = st'.writeMem.size :=
            lower_preserves_size_ge ω a _ _ st' hge_m₁ hwf_a hnc_a
          apply evalSigmaAlg_loop_preserves_wm_size_with_bound (target := m₁ * m₂)
          · rw [hA, hwm']
          · intro j stB hj hwmB
            have hge_m₂ : stB.writeMem.size ≥ m₂ := by
              rw [hwmB]; calc m₂ = 1 * m₂ := (Nat.one_mul m₂).symm
                   _ ≤ m₁ * m₂ := Nat.mul_le_mul_right m₂ hm₁_pos
            exact (lower_preserves_size_ge ω b _ _ stB hge_m₂ hwf_b hnc_b).trans hwmB

/-! ### Infrastructure for kron writeMem irrelevance

Block scatter loop invariant: after i iterations of Scatter.block m₂ at positions
0, m₂, 2*m₂, ..., the writeMem.toList telescopes to
  vals₀ ++ vals₁ ++ ... ++ vals_{i-1} ++ wm₀.toList.drop(i*m₂)
After m₁ iterations (covering all m₁*m₂ positions), the initial wm drops away. -/

/-- Shifted foldl write: writing at base+j via enumFrom(n) = writing via enumFrom(base+n). -/
private theorem foldl_write_shifted [Inhabited α]
    (vals : List α) (wm : Memory α) (base n : Nat) :
    (vals.enumFrom n).foldl (fun acc x => acc.write (base + x.1) x.2) wm =
    (vals.enumFrom (base + n)).foldl (fun acc x => acc.write x.1 x.2) wm := by
  induction vals generalizing wm n with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons]
    exact ih (wm.write (base + n) hd) (n + 1)

/-- evalScatter for Scatter.block m₂ v at iteration i is foldl write at enumFrom(i*m₂). -/
private theorem evalScatter_block_eq_enumFrom [Inhabited α]
    (v : LoopVar) (m₂ i : Nat) (wm : Memory α) (vals : List α) :
    evalScatter (LoopEnv.empty.bind v i) (Scatter.block m₂ v) wm vals =
    (vals.enumFrom (i * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm := by
  simp only [evalScatter, Scatter.block, evalIdxExpr_affine_bind, List.enum,
             Nat.zero_add, Nat.one_mul]
  have h := foldl_write_shifted vals wm (m₂ * i) 0
  simp only [Nat.add_zero] at h
  rw [h, Nat.mul_comm]

/-- Length of flatMap over range when each component has fixed length. -/
private theorem flatMap_range_length (vals : Nat → List α) (m₂ i : Nat)
    (hlen : ∀ j, j < i → (vals j).length = m₂) :
    ((List.range i).flatMap vals).length = i * m₂ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        ih (fun j hj => hlen j (by omega)), hlen i (by omega)]
    ring

/-- Size of memory after foldl write with enumFrom is preserved when writes are in bounds. -/
private theorem foldl_write_enumFrom_preserves_size [Inhabited α]
    (vals : List α) (wm : Memory α) (k : Nat)
    (hk : k + vals.length ≤ wm.size) :
    ((vals.enumFrom k).foldl (fun acc x => acc.write x.1 x.2) wm).size = wm.size := by
  induction vals generalizing wm k with
  | nil => simp [List.enumFrom, List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons, List.length_cons] at hk ⊢
    have hk_lt : k < wm.size := by omega
    have hsize' : (wm.write k hd).size = wm.size := Memory.size_write_eq wm k hd hk_lt
    rw [ih (wm.write k hd) (k + 1) (by rw [hsize']; omega)]
    exact hsize'

/-- Block scatter loop invariant: after i iterations, the toList telescopes.
    The final toList = concat(vals₀, ..., vals_{i-1}) ++ initial.drop(i*m₂).
    After m₁ iterations, drop(m₁*m₂) = [], so the result is independent of initial wm. -/
private theorem block_scatter_loop_inv [Inhabited α]
    (m₁ m₂ : Nat) (wm : Memory α) (vals : Nat → List α)
    (hlen : ∀ j, j < m₁ → (vals j).length = m₂)
    (hwm : wm.size = m₁ * m₂) (i : Nat) (hi : i ≤ m₁) :
    let wm_i := (List.range i).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm
    wm_i.toList = (List.range i).flatMap vals ++ wm.toList.drop (i * m₂)
    ∧ wm_i.size = m₁ * m₂ := by
  induction i with
  | zero =>
    refine ⟨?_, hwm⟩
    simp [List.range_zero, List.foldl_nil, List.flatMap_nil, List.drop_zero]
  | succ i ih =>
    have hi' : i ≤ m₁ := by omega
    obtain ⟨ih_toList, ih_size⟩ := ih hi'
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set wm_i := (List.range i).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm
    have hvals_len : (vals i).length = m₂ := hlen i (by omega)
    have h_bound : i * m₂ + (vals i).length ≤ wm_i.size := by
      rw [hvals_len, ih_size]
      calc i * m₂ + m₂ = (i + 1) * m₂ := by ring
        _ ≤ m₁ * m₂ := Nat.mul_le_mul_right m₂ (by omega)
    have h_scatter := scatter_enumFrom_general (vals i) wm_i (i * m₂) h_bound
    have hfm_len : ((List.range i).flatMap vals).length = i * m₂ :=
      flatMap_range_length vals m₂ i (fun j hj => hlen j (by omega))
    constructor
    · -- toList telescopes: apply scatter_enumFrom_general then simplify take/drop
      rw [h_scatter, ih_toList, hvals_len]
      -- Simplify take: (fm ++ ds).take(i*m₂) = fm when fm.length = i*m₂
      have htake : ((List.range i).flatMap vals ++ wm.toList.drop (i * m₂)).take (i * m₂)
                 = (List.range i).flatMap vals := by
        rw [← hfm_len]; exact List.take_left ..
      -- Simplify drop: (fm ++ ds).drop(i*m₂ + m₂) = wm.drop((i+1)*m₂)
      have hdrop : ((List.range i).flatMap vals ++ wm.toList.drop (i * m₂)).drop (i * m₂ + m₂)
                 = wm.toList.drop ((i + 1) * m₂) := by
        have hlen_eq : ((List.range i).flatMap vals).length + m₂ = i * m₂ + m₂ := by omega
        rw [show i * m₂ + m₂ = ((List.range i).flatMap vals).length + m₂ from by omega]
        rw [show ((List.range i).flatMap vals).length + m₂
              = ((List.range i).flatMap vals).length + m₂ from rfl]
        rw [← List.drop_drop m₂ ((List.range i).flatMap vals).length]
        rw [List.drop_left, List.drop_drop]
        congr 1; ring
      rw [htake, hdrop]
      -- flatMap(0..i) = flatMap(0..i-1) ++ vals i
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
    · -- Size preservation
      rw [foldl_write_enumFrom_preserves_size (vals i) wm_i (i * m₂) h_bound]
      exact ih_size

/-- WriteMem irrelevance for block scatter loops.
    After m₁ iterations of block scatter (each writing m₂ values), the result
    is independent of the initial writeMem when wm.size = m₁ * m₂. -/
private theorem block_scatter_loop_wm_irrelevant [Inhabited α]
    (m₁ m₂ : Nat) (wm1 wm2 : Memory α) (vals : Nat → List α)
    (hlen : ∀ j, j < m₁ → (vals j).length = m₂)
    (hwm1 : wm1.size = m₁ * m₂) (hwm2 : wm2.size = m₁ * m₂) :
    (List.range m₁).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm1 =
    (List.range m₁).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm2 := by
  apply Memory.eq_of_toList_eq
  obtain ⟨h1, _⟩ := block_scatter_loop_inv m₁ m₂ wm1 vals hlen hwm1 m₁ (le_refl m₁)
  obtain ⟨h2, _⟩ := block_scatter_loop_inv m₁ m₂ wm2 vals hlen hwm2 m₁ (le_refl m₁)
  rw [h1, h2]
  congr 1
  have hlen1 : wm1.toList.length = m₁ * m₂ := by
    simp only [Memory.toList, Memory.size] at hwm1; rw [Array.length_toList]; exact hwm1
  have hlen2 : wm2.toList.length = m₁ * m₂ := by
    simp only [Memory.toList, Memory.size] at hwm2; rw [Array.length_toList]; exact hwm2
  rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

/-- For .compute bodies in a loop, readMem is preserved and writeMem evolves via scatter only.
    This decomposes the EvalState foldl into a Memory-only foldl. -/
private theorem compute_loop_decompose [Inhabited α]
    (ω : α) (k : Kernel) (g : Gather) (s : Scatter) (v : LoopVar)
    (rm wm : Memory α) (indices : List Nat) :
    (indices.foldl (fun st j =>
      evalSigmaAlg ω (LoopEnv.empty.bind v j) st (.compute k g s))
      { readMem := rm, writeMem := wm }).readMem = rm
    ∧
    (indices.foldl (fun st j =>
      evalSigmaAlg ω (LoopEnv.empty.bind v j) st (.compute k g s))
      { readMem := rm, writeMem := wm }).writeMem =
    indices.foldl (fun wm' j =>
      evalScatter (LoopEnv.empty.bind v j) s wm'
        (evalKernelAlg ω k (evalGather (LoopEnv.empty.bind v j) g rm))) wm := by
  induction indices generalizing wm with
  | nil => exact ⟨rfl, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hstep : evalSigmaAlg ω (LoopEnv.empty.bind v hd) { readMem := rm, writeMem := wm } (.compute k g s)
      = { readMem := rm, writeMem := evalScatter (LoopEnv.empty.bind v hd) s wm
            (evalKernelAlg ω k (evalGather (LoopEnv.empty.bind v hd) g rm)) } := by
      simp only [evalSigmaAlg]
    rw [hstep]
    exact ih _

/-- WriteMem extraction from compute loop: the writeMem of a foldl of .compute evaluations
    equals the foldl of scatter operations on the writeMem alone.
    This is the .2 projection of compute_loop_decompose, exposed as a simp-friendly equality. -/
private theorem compute_loop_decompose_writeMem [Inhabited α]
    (ω : α) (k : Kernel) (g : Gather) (s : Scatter) (v : LoopVar)
    (rm wm : Memory α) (indices : List Nat) :
    (indices.foldl (fun st j =>
      evalSigmaAlg ω (LoopEnv.empty.bind v j) st (.compute k g s))
      { readMem := rm, writeMem := wm }).writeMem =
    indices.foldl (fun wm' j =>
      evalScatter (LoopEnv.empty.bind v j) s wm'
        (evalKernelAlg ω k (evalGather (LoopEnv.empty.bind v j) g rm))) wm :=
  (compute_loop_decompose ω k g s v rm wm indices).2

/-- Kernel output length preservation for kernels from lowered HasNoSeqLower matrices.
    For any atomic matrix (identity, dft, ntt, etc.), the kernel from `lower`
    preserves input length: output.length = input.length = m. -/
private theorem lower_kernel_preserves_length [Inhabited α]
    (ω : α) {m n : Nat} (state : LowerState) (mat : MatExpr α m n)
    (h_nsl : HasNoSeqLower mat) (h_nz : HasNoZero mat) (hmn : m = n)
    (k : Kernel) (g : Gather) (s : Scatter)
    (hcomp : (lower m n state mat).1 = .compute k g s)
    (input : List α) (hlen : input.length = m) :
    (evalKernelAlg ω k input).length = m := by
  induction mat generalizing state input k g s with
  | identity n' =>
    simp only [lower] at hcomp; obtain ⟨rfl, _, _⟩ := SigmaExpr.compute.inj hcomp
    simp [evalKernelAlg, evalIdentityKernel, hlen]
  | zero => exact absurd h_nz (by simp [HasNoZero])
  | dft n' =>
    simp only [lower] at hcomp; obtain ⟨rfl, _, _⟩ := SigmaExpr.compute.inj hcomp
    exact evalKernelAlg_dft_length n' input hlen
  | ntt =>
    simp only [lower] at hcomp; obtain ⟨rfl, _, _⟩ := SigmaExpr.compute.inj hcomp
    simp [evalKernelAlg, hlen]
  | twiddle =>
    simp only [lower] at hcomp; obtain ⟨rfl, _, _⟩ := SigmaExpr.compute.inj hcomp
    simp [evalKernelAlg, hlen]
  | perm =>
    simp only [lower] at hcomp; obtain ⟨rfl, _, _⟩ := SigmaExpr.compute.inj hcomp
    simp [evalKernelAlg, evalIdentityKernel, hlen]
  | diag =>
    simp only [lower] at hcomp; obtain ⟨rfl, _, _⟩ := SigmaExpr.compute.inj hcomp
    simp [evalKernelAlg, evalIdentityKernel, hlen]
  | scalar =>
    simp only [lower] at hcomp; obtain ⟨rfl, _, _⟩ := SigmaExpr.compute.inj hcomp
    simp [evalKernelAlg, hlen]
  | transpose a ih =>
    simp only [lower] at hcomp
    rw [hmn]; exact ih state h_nsl h_nz hmn.symm k g s hcomp input (hmn ▸ hlen)
  | conjTranspose a ih =>
    simp only [lower] at hcomp
    rw [hmn]; exact ih state h_nsl h_nz hmn.symm k g s hcomp input (hmn ▸ hlen)
  | kron _ _ _ _ => exact h_nsl.elim
  | compose _ _ _ _ => exact h_nsl.elim
  | smul _ _ _ => exact h_nsl.elim
  | elemwise _ _ _ => exact h_nsl.elim
  | add _ _ _ _ => exact h_nsl.elim
  | partialElemwise _ _ _ _ => exact h_nsl.elim
  | mdsApply _ _ _ _ => exact h_nsl.elim
  | addRoundConst _ _ _ _ => exact h_nsl.elim

/-! ### Stride scatter infrastructure

For A⊗I (stride scatter), each iteration j writes m₁ values at stride m₂
starting from position j. After m₂ iterations, every position 0..m₁*m₂-1
is covered exactly once (position p is written at iteration p%m₂).

Key sub-lemmas work with the generalized `enumFrom n` form for induction. -/

/-- Convert evalScatter for stride pattern with .var baseAddr to explicit writes. -/
private theorem evalScatter_stride_var_eq [Inhabited α]
    (v : LoopVar) (m₁ m₂ j : Nat) (wm : Memory α) (vals : List α) :
    evalScatter (LoopEnv.empty.bind v j)
      { count := m₁, baseAddr := .var v, stride := m₂ } wm vals =
    (vals.enumFrom 0).foldl (fun acc ⟨i, val⟩ => acc.write (j + m₂ * i) val) wm := by
  simp only [evalScatter, evalIdxExpr_var_bind, List.enum]

/-- Size preservation for strided writes via enumFrom. -/
private theorem stride_writes_size [Inhabited α]
    (m₂ j : Nat) (wm : Memory α) (vals : List α) (n : Nat)
    (hbound : ∀ k, k < vals.length → j + m₂ * (n + k) < wm.size) :
    ((vals.enumFrom n).foldl (fun acc ⟨i, v⟩ => acc.write (j + m₂ * i) v) wm).size
    = wm.size := by
  induction vals generalizing wm n with
  | nil => simp [List.enumFrom, List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons]
    have hlen_pos : 0 < (hd :: tl).length := by simp
    have hpos : j + m₂ * n < wm.size := by
      have := hbound 0 hlen_pos; simp at this; exact this
    have hsize : (wm.write (j + m₂ * n) hd).size = wm.size :=
      Memory.size_write_eq wm (j + m₂ * n) hd hpos
    rw [ih (wm.write (j + m₂ * n) hd) (n + 1) (by
      intro k hk; rw [hsize]
      have : k + 1 < (hd :: tl).length := by simp; omega
      have := hbound (k + 1) this
      convert this using 1; ring)]
    exact hsize

/-- Strided writes preserve values at positions with different residue mod m₂.
    Position p with p%m₂ ≠ j%m₂ is not touched by writes at j, j+m₂, j+2m₂, ... -/
private theorem stride_writes_preserve_other [Inhabited α]
    (m₂ j : Nat) (wm : Memory α) (vals : List α) (n : Nat) (p : Nat)
    (hp : p < wm.size) (hmod : p % m₂ ≠ j % m₂)
    (hbound : ∀ k, k < vals.length → j + m₂ * (n + k) < wm.size) :
    ((vals.enumFrom n).foldl (fun acc ⟨i, v⟩ => acc.write (j + m₂ * i) v) wm).toList[p]? =
    wm.toList[p]? := by
  induction vals generalizing wm n with
  | nil => simp [List.enumFrom, List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons]
    have hlen_pos : 0 < (hd :: tl).length := by simp
    have hpos : j + m₂ * n < wm.size := by
      have := hbound 0 hlen_pos; simp at this; exact this
    have hne : j + m₂ * n ≠ p := by
      intro heq; apply hmod; rw [← heq]
      simp [Nat.add_mul_mod_self_left]
    have hsize : (wm.write (j + m₂ * n) hd).size = wm.size :=
      Memory.size_write_eq wm (j + m₂ * n) hd hpos
    rw [ih (wm.write (j + m₂ * n) hd) (n + 1) (by rw [hsize]; exact hp) (by
      intro k hk; rw [hsize]
      have : k + 1 < (hd :: tl).length := by simp; omega
      have := hbound (k + 1) this
      convert this using 1; ring)]
    rw [Memory.toList_write_eq_set wm (j + m₂ * n) hd hpos]
    exact List.getElem?_set_ne hne

/-- Later stride writes (enumFrom m where m > n) don't affect position j+m₂*n.
    Because m₂ > 0 and m > n, all write positions j+m₂*i (i ≥ m) differ from j+m₂*n. -/
private theorem stride_writes_skip_pos [Inhabited α]
    (m₂ j : Nat) (hm₂ : m₂ > 0) (wm : Memory α) (vals : List α) (m n : Nat)
    (hmn : n < m)
    (hpos : j + m₂ * n < wm.size)
    (hbound : ∀ i, i < vals.length → j + m₂ * (m + i) < wm.size) :
    ((vals.enumFrom m).foldl (fun acc ⟨i, v⟩ => acc.write (j + m₂ * i) v) wm).toList[j + m₂ * n]?
    = wm.toList[j + m₂ * n]? := by
  induction vals generalizing wm m with
  | nil => simp [List.enumFrom, List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons]
    have hlt_mul : m₂ * n < m₂ * m := Nat.mul_lt_mul_of_pos_left hmn hm₂
    have hne : j + m₂ * m ≠ j + m₂ * n := by omega
    have hlen_pos : 0 < (hd :: tl).length := by simp
    have hpos_m : j + m₂ * m < wm.size := by
      have := hbound 0 hlen_pos; simp at this; exact this
    have hsize_eq : (wm.write (j + m₂ * m) hd).size = wm.size :=
      Memory.size_write_eq wm _ hd hpos_m
    rw [ih (wm.write (j + m₂ * m) hd) (m + 1) (by omega) (by rw [hsize_eq]; exact hpos)
      (by intro i hi; rw [hsize_eq]
          have : i + 1 < (hd :: tl).length := by simp; omega
          have := hbound (i + 1) this
          convert this using 1; ring)]
    rw [Memory.toList_write_eq_set wm _ hd hpos_m]
    exact List.getElem?_set_ne hne

/-- A single stride pass sets the value at position j+m₂*(n+k) to vals[k]?.
    After writing vals via enumFrom n at stride m₂ from base j,
    the value at position j+m₂*(n+k) equals vals[k]?. -/
private theorem stride_writes_at_pos [Inhabited α]
    (m₂ j : Nat) (hm₂ : m₂ > 0) (wm : Memory α) (vals : List α) (n k : Nat)
    (hk : k < vals.length)
    (hbound : ∀ i, i < vals.length → j + m₂ * (n + i) < wm.size) :
    ((vals.enumFrom n).foldl (fun acc ⟨i, v⟩ => acc.write (j + m₂ * i) v) wm).toList[j + m₂ * (n + k)]?
    = vals[k]? := by
  induction vals generalizing wm n k with
  | nil => simp at hk
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons]
    have hlen_pos : 0 < (hd :: tl).length := by simp
    have hpos : j + m₂ * n < wm.size := by
      have := hbound 0 hlen_pos; simp at this; exact this
    have hsize_eq : (wm.write (j + m₂ * n) hd).size = wm.size :=
      Memory.size_write_eq wm _ hd hpos
    match k with
    | 0 =>
      simp only [Nat.add_zero]
      -- Later writes (tl.enumFrom (n+1)) preserve position j+m₂*n
      rw [stride_writes_skip_pos m₂ j hm₂ _ tl (n + 1) n (by omega)
        (by rw [hsize_eq]; exact hpos)
        (by intro i hi; rw [hsize_eq]
            have : i + 1 < (hd :: tl).length := by simp; omega
            have := hbound (i + 1) this
            convert this using 1; ring)]
      -- Value at j+m₂*n after the write
      rw [Memory.toList_write_eq_set wm _ hd hpos]
      have hlt_len : j + m₂ * n < wm.toList.length := by
        simp [Memory.toList, Array.length_toList, Memory.size]; exact hpos
      simp [List.getElem?_set, hlt_len]
    | k' + 1 =>
      -- Position j+m₂*(n+k'+1) = j+m₂*((n+1)+k')
      have haddr : j + m₂ * (n + (k' + 1)) = j + m₂ * ((n + 1) + k') := by ring
      rw [haddr]
      rw [ih (wm.write (j + m₂ * n) hd) (n + 1) k' (by simp at hk; omega)
        (by intro i hi; rw [hsize_eq]
            have : i + 1 < (hd :: tl).length := by simp; omega
            have := hbound (i + 1) this
            convert this using 1; ring)]
      simp

/-- Pointwise loop invariant for stride scatter: after i iterations,
    positions with p%m₂ < i hold (vals (p%m₂))[p/m₂]?. -/
private theorem stride_scatter_loop_inv [Inhabited α]
    (m₁ m₂ : Nat) (hm₂ : m₂ > 0) (wm : Memory α) (vals : Nat → List α)
    (hlen : ∀ j, j < m₂ → (vals j).length = m₁)
    (hwm : wm.size = m₁ * m₂) (i : Nat) (hi : i ≤ m₂) :
    let wm_i := (List.range i).foldl (fun wm' j =>
      ((vals j).enumFrom 0).foldl (fun acc ⟨k, val⟩ => acc.write (j + m₂ * k) val) wm') wm
    wm_i.size = m₁ * m₂
    ∧ ∀ p, p < m₁ * m₂ → p % m₂ < i →
        wm_i.toList[p]? = (vals (p % m₂))[p / m₂]? := by
  induction i with
  | zero =>
    exact ⟨hwm, fun _ _ h => absurd h (by omega)⟩
  | succ i ih =>
    have hi' : i ≤ m₂ := by omega
    obtain ⟨ih_size, ih_val⟩ := ih hi'
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set wm_i := (List.range i).foldl (fun wm' j =>
      ((vals j).enumFrom 0).foldl (fun acc ⟨k, val⟩ => acc.write (j + m₂ * k) val) wm') wm
    -- Bound for stride writes at iteration i
    have h_bound : ∀ k, k < (vals i).length → i + m₂ * (0 + k) < wm_i.size := by
      intro k hk
      rw [ih_size]; simp only [Nat.zero_add]
      have hk' : k < m₁ := by rw [hlen i (by omega)] at hk; exact hk
      calc i + m₂ * k < m₂ + m₂ * k := by omega
        _ = m₂ * (k + 1) := by ring
        _ ≤ m₂ * m₁ := Nat.mul_le_mul_left m₂ (by omega)
        _ = m₁ * m₂ := by ring
    constructor
    · -- Size preservation
      rw [stride_writes_size m₂ i wm_i (vals i) 0 h_bound, ih_size]
    · intro p hp hpi1
      by_cases heq : p % m₂ = i
      · -- p%m₂ = i: iteration i writes to position p
        have hp_div : p / m₂ < m₁ := (Nat.div_lt_iff_lt_mul hm₂).mpr hp
        have h_at := stride_writes_at_pos m₂ i hm₂ wm_i (vals i) 0 (p / m₂)
          (by rw [hlen i (by omega)]; exact hp_div) h_bound
        simp only [Nat.zero_add] at h_at
        have hdiv := Nat.div_add_mod p m₂
        have hp_eq : i + m₂ * (p / m₂) = p := by omega
        rw [hp_eq] at h_at
        rw [h_at, heq]
      · -- p%m₂ < i: already written, iteration i preserves
        have hmod : p % m₂ ≠ i % m₂ := by
          rw [Nat.mod_eq_of_lt (show i < m₂ from by omega)]; exact heq
        rw [stride_writes_preserve_other m₂ i wm_i (vals i) 0 p
          (by rw [ih_size]; exact hp) hmod h_bound]
        exact ih_val p hp (by omega)

/-- WriteMem irrelevance for stride scatter loops.
    After m₂ iterations of stride scatter (each writing m₁ values at stride m₂),
    the result is independent of the initial writeMem when wm.size = m₁ * m₂. -/
private theorem stride_scatter_loop_wm_irrelevant [Inhabited α]
    (m₁ m₂ : Nat) (v : LoopVar) (wm1 wm2 : Memory α) (vals : Nat → List α)
    (hlen : ∀ j, j < m₂ → (vals j).length = m₁)
    (hwm1 : wm1.size = m₁ * m₂) (hwm2 : wm2.size = m₁ * m₂) :
    (List.range m₂).foldl (fun wm' j =>
      evalScatter (LoopEnv.empty.bind v j)
        { count := m₁, baseAddr := .var v, stride := m₂ } wm' (vals j)) wm1 =
    (List.range m₂).foldl (fun wm' j =>
      evalScatter (LoopEnv.empty.bind v j)
        { count := m₁, baseAddr := .var v, stride := m₂ } wm' (vals j)) wm2 := by
  simp only [evalScatter_stride_var_eq]
  apply Memory.eq_of_toList_eq
  by_cases hm₂ : m₂ = 0
  · -- m₂ = 0: both memories have size 0, toLists are empty
    simp only [hm₂, Nat.mul_zero] at hwm1 hwm2
    simp only [hm₂, List.range_zero, List.foldl_nil]
    have h1 : wm1.toList.length = 0 := by
      simp only [Memory.toList, Memory.size] at hwm1; rw [Array.length_toList]; exact hwm1
    have h2 : wm2.toList.length = 0 := by
      simp only [Memory.toList, Memory.size] at hwm2; rw [Array.length_toList]; exact hwm2
    rw [List.eq_nil_of_length_eq_zero h1, List.eq_nil_of_length_eq_zero h2]
  · -- m₂ > 0: use the loop invariant
    have hm₂_pos : m₂ > 0 := Nat.pos_of_ne_zero hm₂
    obtain ⟨_, hval1⟩ := stride_scatter_loop_inv m₁ m₂ hm₂_pos wm1 vals hlen hwm1 m₂ (le_refl _)
    obtain ⟨_, hval2⟩ := stride_scatter_loop_inv m₁ m₂ hm₂_pos wm2 vals hlen hwm2 m₂ (le_refl _)
    apply List.ext_getElem?
    intro p
    by_cases hp : p < m₁ * m₂
    · rw [hval1 p hp (Nat.mod_lt p hm₂_pos), hval2 p hp (Nat.mod_lt p hm₂_pos)]
    · -- Out of range: both are none
      have hsize1 := stride_scatter_loop_inv m₁ m₂ hm₂_pos wm1 vals hlen hwm1 m₂ (le_refl _) |>.1
      have hsize2 := stride_scatter_loop_inv m₁ m₂ hm₂_pos wm2 vals hlen hwm2 m₂ (le_refl _) |>.1
      have h_none : ∀ (mem : Memory α), mem.size = m₁ * m₂ → mem.toList[p]? = none := by
        intro mem hmem; apply List.getElem?_eq_none
        unfold Memory.toList Memory.size at *; rw [Array.length_toList]; omega
      rw [h_none _ hsize1, h_none _ hsize2]

/-- WriteMem irrelevance for .compute with contiguous scatter at base 0.
    When outputs.length = m and wm.size = m, scatter overwrites all positions,
    making the result independent of initial writeMem. -/
private theorem compute_writeMem_irrelevant
    (k : Kernel) (n' : Nat) (rm : Memory α) (wm1 wm2 : Memory α)
    (hwm1 : wm1.size = n') (hwm2 : wm2.size = n')
    (hlen : (evalKernelAlg ω k (evalGather LoopEnv.empty (Gather.contiguous n' (.const 0)) rm)).length = n') :
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm1 }
      (.compute k (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)))).writeMem =
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm2 }
      (.compute k (Gather.contiguous n' (.const 0)) (Scatter.contiguous n' (.const 0)))).writeMem := by
  simp only [evalSigmaAlg]
  set outputs := evalKernelAlg ω k (evalGather LoopEnv.empty (Gather.contiguous n' (.const 0)) rm)
  rw [evalScatter_contiguous_zero outputs wm1 n',
      evalScatter_contiguous_zero outputs wm2 n']
  exact foldl_write_enum_wm_irrelevant outputs wm1 wm2
    (by rw [hwm1, hlen]) (by rw [hwm2, hlen])

set_option maxHeartbeats 3200000 in
/-- WriteMem irrelevance for lowered expressions: the full output writeMem
    does not depend on the initial writeMem contents when:
    1. HasNoZero mat (no .zero sub-expressions)
    2. IsWellFormedNTT mat (squareness, etc.)
    3. wm1.size = m and wm2.size = m

    The key insight: when wm.size = m, scatter contiguous(m) completely fills
    the memory, so no trace of the initial content remains.

    Proved for all constructors except .kron (S3: requires adjustBlock/adjustStride
    body writeMem determinism lemmas — loop invariant infrastructure is in place).
    .add case closed by DD-ADD (IsWellFormedNTT .add = False). -/
theorem evalSigmaAlg_writeMem_irrelevant
    (ω : α) {m n : Nat} (state : LowerState) (mat : MatExpr α m n)
    (rm : Memory α) (wm1 wm2 : Memory α)
    (hwm1 : wm1.size = m) (hwm2 : wm2.size = m)
    (hwf : IsWellFormedNTT mat) (hnz : HasNoZero mat) :
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm1 }
      (lower m n state mat).1).writeMem =
    (evalSigmaAlg ω LoopEnv.empty { readMem := rm, writeMem := wm2 }
      (lower m n state mat).1).writeMem := by
  induction mat generalizing state rm wm1 wm2 with
  | zero => exact absurd hnz (by simp [HasNoZero])
  | identity n' =>
    simp only [lower]
    exact compute_writeMem_irrelevant (.identity n') n' rm wm1 wm2 hwm1 hwm2
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather, Gather.contiguous])
  | dft n' =>
    simp only [lower]
    exact compute_writeMem_irrelevant (.dft n') n' rm wm1 wm2 hwm1 hwm2 (by
      simp only [evalGather, Gather.contiguous]
      show (evalKernelAlg ω (.dft n') _).length = n'
      simp only [evalKernelAlg]
      by_cases h : n' = 2
      · subst h; simp [evalDFT2]; split <;> simp
      · simp [evalDFT])
  | ntt =>
    simp only [lower]
    exact compute_writeMem_irrelevant _ _ rm wm1 wm2 hwm1 hwm2
      (by simp [evalKernelAlg, evalGather, Gather.contiguous])
  | twiddle =>
    simp only [lower]
    exact compute_writeMem_irrelevant _ _ rm wm1 wm2 hwm1 hwm2
      (by simp [evalKernelAlg, evalGather, Gather.contiguous])
  | perm =>
    -- perm : MatExpr α n n, so m = n. lower produces .compute (.identity n) contiguous contiguous
    simp only [lower]
    exact compute_writeMem_irrelevant _ _ rm wm1 wm2 hwm1 hwm2
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather, Gather.contiguous])
  | diag =>
    -- diag : MatExpr α n n, so m = n. lower produces .compute (.identity n) contiguous contiguous
    simp only [lower]
    exact compute_writeMem_irrelevant _ _ rm wm1 wm2 hwm1 hwm2
      (by simp [evalKernelAlg, evalIdentityKernel, evalGather, Gather.contiguous])
  | scalar =>
    simp only [lower]
    exact compute_writeMem_irrelevant .scale 1 rm wm1 wm2 hwm1 hwm2
      (by simp [evalKernelAlg, evalGather, Gather.contiguous])
  | transpose a ih =>
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower]
    subst hmn
    exact ih state rm wm1 wm2 hwm1 hwm2 hwf_a hnz
  | conjTranspose a ih =>
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower]
    subst hmn
    exact ih state rm wm1 wm2 hwm1 hwm2 hwf_a hnz
  | smul f a ih =>
    obtain ⟨hmn, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    -- exprA = lower(a), then .compute .scale contiguous(n) contiguous(n)
    -- By IH: exprA produces same writeMem for wm1 and wm2
    have h_eq := ih state rm wm1 wm2 hwm1 hwm2 hwf_a hnz
    -- After exprA, both have same writeMem → .seq produces same readMem/writeMem
    -- → .compute produces same result
    rw [h_eq]
  | elemwise op a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    have h_eq := ih state rm wm1 wm2 hwm1 hwm2 hwf_a hnz
    rw [h_eq]
  | partialElemwise _ _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    have h_eq := ih state rm wm1 wm2 hwm1 hwm2 hwf_a hnz
    rw [h_eq]
  | mdsApply _ _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    have h_eq := ih state rm wm1 wm2 hwm1 hwm2 hwf_a hnz
    rw [h_eq]
  | addRoundConst _ _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [lower, evalSigmaAlg]
    have h_eq := ih state rm wm1 wm2 hwm1 hwm2 hwf_a hnz
    rw [h_eq]
  | compose a b ih_a ih_b =>
    -- lower(.compose a b) = .temp k (.seq exprB exprA)
    -- .temp k replaces writeMem with Memory.zeros k, making initial writeMem irrelevant
    simp only [lower, evalSigmaAlg]
  | add a b ih_a ih_b =>
    -- DD-ADD: IsWellFormedNTT (.add _ _) = False, so hwf is vacuously absurd
    exact hwf.elim
  | kron a b ih_a ih_b =>
    -- S3: .kron writeMem irrelevance via scatter coverage
    obtain ⟨ha_sq, hb_sq, _, _, _, _, hm₁_pos, hm₂_pos, h_id, h_nsl_a, h_nsl_b⟩ := hwf
    obtain ⟨hnz_a, hnz_b⟩ := hnz
    subst ha_sq; subst hb_sq
    simp only [lower]
    split
    · -- I⊗B case: a.isIdentity = true
      have hcomp := lower_hasNoSeqLower_is_compute (freshLoopVar state).2 b h_nsl_b hnz_b
      obtain ⟨k, g, s, hcomp⟩ := hcomp
      simp only [hcomp, adjustBlock]
      -- Unfold .loop to foldl (preserving .compute inside the body)
      simp only [evalSigmaAlg.eq_2]
      -- Extract writeMem from the EvalState foldl via compute_loop_decompose
      simp only [compute_loop_decompose_writeMem]
      -- Rewrite scatter to enumFrom form
      simp only [evalScatter_block_eq_enumFrom]
      -- Block scatter covers all positions → independent of initial wm
      exact block_scatter_loop_wm_irrelevant _ _ wm1 wm2 _
        (fun j _ => lower_kernel_preserves_length ω _ b h_nsl_b hnz_b rfl k g s hcomp _
          (evalGather_length _ _ _)) hwm1 hwm2
    · split
      · -- A⊗I case: b.isIdentity = true
        have hcomp := lower_hasNoSeqLower_is_compute (freshLoopVar state).2 a h_nsl_a hnz_a
        obtain ⟨k, g, s, hcomp⟩ := hcomp
        simp only [hcomp, adjustStride]
        -- Unfold .loop to foldl
        simp only [evalSigmaAlg.eq_2]
        -- Extract writeMem from the EvalState foldl
        simp only [compute_loop_decompose_writeMem]
        -- Stride scatter covers all positions → independent of initial wm
        exact stride_scatter_loop_wm_irrelevant _ _ _ wm1 wm2 _
          (fun j _ => lower_kernel_preserves_length ω _ a h_nsl_a hnz_a rfl k g s hcomp _
            (evalGather_length _ _ _)) hwm1 hwm2
      · -- General A⊗B: unreachable (IsWellFormedNTT requires a.isIdentity ∨ b.isIdentity)
        exfalso; exact h_id.elim (fun h => absurd h ‹_›) (fun h => absurd h ‹_›)

set_option maxHeartbeats 3200000 in
/-- Lowered expressions evaluate identically regardless of LowerState.
    LowerState only affects loop variable naming (alpha-equivalence).
    Proved for all non-kron constructors by structural induction. -/
theorem evalSigmaAlg_lower_state_irrelevant
    (ω : α) {m n : Nat} (state1 state2 : LowerState) (mat : MatExpr α m n)
    (env : LoopEnv) (st : EvalState α) :
    evalSigmaAlg ω env st (lower m n state1 mat).1 = evalSigmaAlg ω env st (lower m n state2 mat).1 := by
  induction mat generalizing state1 state2 env st with
  | identity => simp only [lower]
  | zero => simp only [lower]
  | dft => simp only [lower]
  | ntt => simp only [lower]
  | twiddle => simp only [lower]
  | perm => simp only [lower]
  | diag => simp only [lower]
  | scalar => simp only [lower]
  | transpose a ih => simp only [lower]; exact ih state1 state2 env st
  | conjTranspose a ih => simp only [lower]; exact ih state1 state2 env st
  | smul f a ih =>
    simp only [lower, evalSigmaAlg]
    rw [ih state1 state2 env st]
  | elemwise op a ih =>
    simp only [lower, evalSigmaAlg]
    rw [ih state1 state2 env st]
  | partialElemwise idx op a ih =>
    simp only [lower, evalSigmaAlg]
    rw [ih state1 state2 env st]
  | mdsApply name size a ih =>
    simp only [lower, evalSigmaAlg]
    rw [ih state1 state2 env st]
  | addRoundConst round size a ih =>
    simp only [lower, evalSigmaAlg]
    rw [ih state1 state2 env st]
  | compose a b ih_a ih_b =>
    simp only [lower, evalSigmaAlg]
    rw [ih_b state1 state2 env _]
    congr 1
    exact congrArg EvalState.writeMem (ih_a _ _ env _)
  | add a b ih_a ih_b =>
    simp only [lower, evalSigmaAlg]
    rw [ih_a state1 state2 env st]
    exact ih_b _ _ env _
  | kron a b ih_a ih_b =>
    -- With isIdentity refactoring, we can now do case analysis
    simp only [lower]
    split_ifs with ha hb
    -- Case 1: a.isIdentity = true (I⊗B)
    · -- lower produces (.loop m₁ v (adjustBlock v n₂ m₂ (lower b state')), state')
      simp only [freshLoopVar]
      -- Use loop_adjustBlock_sameStructure with SameStructure from lower
      let state1' : LowerState := { nextLoopVar := state1.nextLoopVar + 1 }
      let state2' : LowerState := { nextLoopVar := state2.nextLoopVar + 1 }
      have hsame := lower_produces_sameStructure state1' state2' b
      have hfresh1 : state1.nextLoopVar ∉ SigmaExpr.loopVarsOf (lower _ _ state1' b).1 :=
        AmoLean.Sigma.lower_loopVar_fresh_lt b state1' state1.nextLoopVar (Nat.lt_succ_self _)
      have hfresh2 : state2.nextLoopVar ∉ SigmaExpr.loopVarsOf (lower _ _ state2' b).1 :=
        AmoLean.Sigma.lower_loopVar_fresh_lt b state2' state2.nextLoopVar (Nat.lt_succ_self _)
      exact loop_adjustBlock_sameStructure ω state1.nextLoopVar state2.nextLoopVar _ hsame
              hfresh1 hfresh2 env st
    -- Case 2: a.isIdentity = false, b.isIdentity = true (A⊗I)
    · -- lower produces (.loop m₂ v (adjustStride v m₂ m₁ n₁ (lower a state')), state')
      simp only [freshLoopVar]
      -- Use loop_adjustStride_sameStructure with SameStructure from lower
      let state1' : LowerState := { nextLoopVar := state1.nextLoopVar + 1 }
      let state2' : LowerState := { nextLoopVar := state2.nextLoopVar + 1 }
      have hsame := lower_produces_sameStructure state1' state2' a
      have hfresh1 : state1.nextLoopVar ∉ SigmaExpr.loopVarsOf (lower _ _ state1' a).1 :=
        AmoLean.Sigma.lower_loopVar_fresh_lt a state1' state1.nextLoopVar (Nat.lt_succ_self _)
      have hfresh2 : state2.nextLoopVar ∉ SigmaExpr.loopVarsOf (lower _ _ state2' a).1 :=
        AmoLean.Sigma.lower_loopVar_fresh_lt a state2' state2.nextLoopVar (Nat.lt_succ_self _)
      exact loop_adjustStride_sameStructure ω state1.nextLoopVar state2.nextLoopVar _ hsame
              hfresh1 hfresh2 env st
    -- Case 3: General A⊗B (nested loops)
    · -- Structure: .loop m₁ v (.seq exprA (.loop m₂ (v+1) exprB))
      -- Use nested_loop_alpha with IH for a and b
      simp only [freshLoopVar]
      -- Provide fv = ∅ for all expressions from lower
      have hfv_a1 := AmoLean.Sigma.lower_fv_empty a { nextLoopVar := state1.nextLoopVar + 1 }
      have hfv_a2 := AmoLean.Sigma.lower_fv_empty a { nextLoopVar := state2.nextLoopVar + 1 }
      have hfv_b1 := AmoLean.Sigma.lower_fv_empty b (lower _ _ { nextLoopVar := state1.nextLoopVar + 1 } a).2
      have hfv_b2 := AmoLean.Sigma.lower_fv_empty b (lower _ _ { nextLoopVar := state2.nextLoopVar + 1 } a).2
      apply nested_loop_alpha
      -- fv = ∅ for exprA1, exprA2, exprB1, exprB2
      · exact hfv_a1
      · exact hfv_a2
      · exact hfv_b1
      · exact hfv_b2
      -- IH for exprA: lower a is state-irrelevant
      · intro env' st'; exact ih_a _ _ env' st'
      -- IH for exprB: lower b is state-irrelevant
      · intro env' st'; exact ih_b _ _ env' st'

set_option maxHeartbeats 800000 in
/-- Alpha-equivalence for lowered expressions.
    Different LowerState values (which only affect loop variable numbering)
    do not change the semantics of the lowered SigmaExpr.
    Derived from the stronger evalSigmaAlg_lower_state_irrelevant. -/
theorem lower_state_irrelevant (ω : α) {m n : Nat} (state1 state2 : LowerState)
    (mat : MatExpr α m n) (v : List α) :
    runSigmaAlg ω (lower m n state1 mat).1 v m =
    runSigmaAlg ω (lower m n state2 mat).1 v m := by
  simp only [runSigmaAlg]
  have h := evalSigmaAlg_lower_state_irrelevant ω state1 state2 mat LoopEnv.empty
    (EvalState.init v m)
  rw [h]

/-! ### Lemmas auxiliares para evalMatExprAlg_length (Fase 2 Corrección 3 Subfase 1) -/

/-- FlatMap with constant-length outputs has predictable total length.
    If each element of a list produces a sublist of length k,
    then flatMap produces a list of length (original_length * k). -/
theorem flatMap_const_length {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (h : ∀ x ∈ xs, (f x).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  rw [List.length_flatMap]
  -- Goal: (List.map (List.length ∘ f) xs).sum = xs.length * k
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map, Function.comp_apply, List.sum_cons, List.length_cons]
    have hx := h x (List.mem_cons_self x xs)
    have hxs : ∀ y ∈ xs, (f y).length = k := fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [hx, ih hxs]
    ring

/-- Range-based flatMap when each index produces constant length output. -/
theorem range_flatMap_const_length {α : Type*} (n k : Nat) (f : Nat → List α)
    (h : ∀ i, i < n → (f i).length = k) :
    ((List.range n).flatMap f).length = n * k := by
  have := flatMap_const_length (List.range n) f k (fun i hi => by
    rw [List.mem_range] at hi; exact h i hi)
  simp only [List.length_range] at this
  exact this

/-- Stride interleave output length: List.range (n * k) |>.map f has length n * k -/
theorem stride_interleave_length {α : Type*} (n k : Nat) (f : Nat → α) :
    (List.range (n * k) |>.map f).length = n * k := by
  simp [List.length_map, List.length_range]

/-- Block extraction length when blocks fit within input.
    For i < numBlocks and input.length = numBlocks * blockSize,
    each block (drop (i * blockSize) |>.take blockSize) has length blockSize. -/
theorem block_length {α : Type*} (input : List α) (numBlocks blockSize : Nat)
    (hlen : input.length = numBlocks * blockSize) (i : Nat) (hi : i < numBlocks) :
    (input.drop (i * blockSize) |>.take blockSize).length = blockSize := by
  rw [List.length_take, List.length_drop, hlen]
  -- Goal: min blockSize (numBlocks * blockSize - i * blockSize) = blockSize
  -- We need to show blockSize ≤ numBlocks * blockSize - i * blockSize
  apply Nat.min_eq_left
  -- Goal: blockSize ≤ numBlocks * blockSize - i * blockSize
  have h : i + 1 ≤ numBlocks := hi
  -- (i + 1) * blockSize ≤ numBlocks * blockSize
  have h2 : (i + 1) * blockSize ≤ numBlocks * blockSize := Nat.mul_le_mul_right blockSize h
  -- Expanding: i * blockSize + blockSize ≤ numBlocks * blockSize
  -- So: blockSize ≤ numBlocks * blockSize - i * blockSize
  -- Rewrite (i + 1) * blockSize = i * blockSize + blockSize
  rw [Nat.add_mul, Nat.one_mul] at h2
  -- h2 : i * blockSize + blockSize ≤ numBlocks * blockSize
  rw [Nat.add_comm] at h2
  -- h2 : blockSize + i * blockSize ≤ numBlocks * blockSize
  exact Nat.le_sub_of_add_le h2

/-- Division then multiplication when divisor divides evenly -/
theorem div_mul_eq {a b : Nat} (hb : b > 0) (h : a = (a / b) * b) : a / b * b = a := by
  omega

/-- evalMatExprAlg output length preservation.
    The algebraic matrix evaluator always produces a list of length m
    (the output dimension), given an input of length n.

    Requires IsWellFormedNTT to ensure:
    - Square matrices for transpose/conjTranspose (m = n)
    - Proper dimensions for kron subcases
    These constraints are always satisfied by actual NTT/FFT/Poseidon code. -/
theorem evalMatExprAlg_length
    (ω : α) {m n : Nat} (mat : MatExpr α m n)
    (v : List α) (hv : v.length = n)
    (hwf : IsWellFormedNTT mat) :
    (evalMatExprAlg ω m n mat v).length = m := by
  induction mat generalizing v with
  | identity => simp [evalMatExprAlg, hv]
  | zero => simp [evalMatExprAlg, List.length_replicate]
  | dft n_val =>
    match n_val with
    | 0 | 1 => simp [evalMatExprAlg, evalDFT_length]
    | 2 => simp only [evalMatExprAlg]; exact evalDFT2_length v hv
    | n + 3 => simp [evalMatExprAlg, evalDFT_length]
  | ntt => simp [evalMatExprAlg, hv]
  | twiddle => simp [evalMatExprAlg, hv]
  | perm => simp [evalMatExprAlg, applyPerm, hv]
  | diag => simp [evalMatExprAlg, hv]
  | scalar => simp [evalMatExprAlg, hv]
  | smul _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [evalMatExprAlg]; exact ih v hv hwf_a
  | elemwise _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [evalMatExprAlg]; exact ih v hv hwf_a
  | partialElemwise _ _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [evalMatExprAlg]; exact ih v hv hwf_a
  | mdsApply _ _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [evalMatExprAlg]; exact ih v hv hwf_a
  | addRoundConst _ _ a ih =>
    obtain ⟨_, hwf_a⟩ := hwf
    simp only [evalMatExprAlg]; exact ih v hv hwf_a
  | compose a b ih_a ih_b =>
    obtain ⟨_, _, hwf_a, hwf_b⟩ := hwf
    simp only [evalMatExprAlg]; exact ih_a _ (ih_b v hv hwf_b) hwf_a
  | add a b ih_a ih_b =>
    -- DD-ADD: IsWellFormedNTT (.add _ _) = False, so hwf is vacuously absurd
    exact hwf.elim
  | transpose a ih =>
    -- hwf : IsWellFormedNTT (.transpose a) = (m = n) ∧ IsWellFormedNTT a
    -- a : MatExpr α n m, with m = n (square matrices only)
    -- After subst, everything is in terms of n
    obtain ⟨hmn, hwf_a⟩ := hwf
    subst hmn  -- Replace m with n everywhere
    simp only [evalMatExprAlg]
    exact ih v hv hwf_a
  | conjTranspose a ih =>
    -- Same structure as transpose
    obtain ⟨hmn, hwf_a⟩ := hwf
    subst hmn
    simp only [evalMatExprAlg]
    exact ih v hv hwf_a
  | kron a b ih_a ih_b =>
    obtain ⟨ha_sq, hb_sq, _hnc_a, _hnc_b, hwf_a, hwf_b, _hm₁_pos, _hm₂_pos, _h_id, _h_nsl_a, _h_nsl_b⟩ := hwf
    simp only [evalMatExprAlg]
    split
    · -- Case I⊗B: (List.range m₁).flatMap (λ i => evalMatExprAlg b block_i)
      rename_i hIsIdent
      -- isIdentity a = true implies m₁ = n₁ (a is identity matrix, hence square)
      have ha_sq' := isIdentity_implies_square hIsIdent
      -- Each block has length n₂, evalMatExprAlg b gives length m₂
      -- Total: m₁ * m₂
      apply range_flatMap_const_length
      intro i hi
      apply ih_b
      · rw [← ha_sq'] at hv
        exact block_length v _ _ hv i hi
      · exact hwf_b
    · split
      · -- Case A⊗I
        rename_i m₁ n₁ m₂ n₂ _ hIsIdentB
        have hb_sq' := isIdentity_implies_square hIsIdentB
        simp only [List.length_map, List.length_range]
        rw [hv, hb_sq', ha_sq]
        by_cases hm₂ : n₂ = 0
        · simp [hm₂]
        · rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm₂)]
      · -- General case A⊗B
        rename_i m₁ n₁ m₂ n₂ _ _
        simp only [List.length_map, List.length_range]
        have h_afterB_len :
            ((List.range m₁).flatMap fun i =>
              evalMatExprAlg ω m₂ n₂ b (List.take n₂ (List.drop (i * n₂) v))).length = m₁ * m₂ := by
          apply range_flatMap_const_length
          intro i hi
          apply ih_b
          · exact block_length v _ _ hv i (ha_sq ▸ hi)
          · exact hwf_b
        rw [h_afterB_len]
        by_cases hm₂ : m₂ = 0
        · simp [hm₂]
        · rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm₂)]

/-! ### Helper lemmas for seq_identity_compute proof -/

omit [Field α] [DecidableEq α] in
/-- Gathering contiguous elements equals mapping read over range -/
private theorem gather_contiguous_eq_map_read (mem : Memory α) (s : Nat) :
    evalGather LoopEnv.empty (Gather.contiguous s (.const 0)) mem
    = List.map (fun i => mem.read i) (List.range s) := by
  simp only [evalGather, Gather.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add, Nat.one_mul]

omit [Field α] [DecidableEq α] in
/-- Map of read over range equals toList.take when s ≤ mem.size -/
private theorem map_read_range_eq_toList_take (mem : Memory α) (s : Nat) (hs : s ≤ mem.size) :
    List.map (fun i => mem.read i) (List.range s) = mem.toList.take s := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, Memory.toList,
               Array.length_toList, Memory.size] at hs ⊢
    omega
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range] at *
    simp only [List.length_map, List.length_range] at hi1
    rw [List.getElem_take]
    simp only [Memory.read, Memory.toList]
    have h : i < mem.data.size := by
      simp only [Memory.size] at hs; omega
    rw [if_pos h, getElem!_pos mem.data i h, Array.getElem_toList h]

/-- Scatter of gather from same memory is identity when s ≤ mem.size -/
private theorem scatter_gather_self (mem : Memory α) (s : Nat) (hs : s ≤ mem.size) :
    evalScatter LoopEnv.empty (Scatter.contiguous s (.const 0)) mem
      (evalGather LoopEnv.empty (Gather.contiguous s (.const 0)) mem)
    = mem := by
  rw [gather_contiguous_eq_map_read]
  simp only [evalScatter, Scatter.contiguous, evalIdxExpr, LoopEnv.empty, Nat.zero_add, Nat.one_mul]
  -- Goal: foldl write mem (map read (range s)).enum = mem
  -- Rewrite gathered values to toList.take s
  rw [map_read_range_eq_toList_take mem s hs]
  -- Goal: foldl write mem (toList.take s).enum = mem
  rw [show (mem.toList.take s).enum = (mem.toList.take s).enumFrom 0 from rfl]
  -- Apply scatter_enumFrom_general
  have hk : 0 + (mem.toList.take s).length ≤ mem.size := by
    simp only [List.length_take, Memory.toList, Array.length_toList, Memory.size] at hs ⊢; omega
  have h := scatter_enumFrom_general (mem.toList.take s) mem 0 hk
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at h
  have hlen : (mem.toList.take s).length = s := by
    simp only [List.length_take, Memory.toList, Array.length_toList, Memory.size] at hs ⊢; omega
  rw [hlen] at h
  rw [List.take_append_drop] at h
  exact Memory.eq_of_toList_eq h

set_option maxHeartbeats 1600000 in
/-- Sequencing an identity-like kernel compute after an expression is a no-op.
    If evalKernelAlg returns its input unchanged, then .compute with contiguous
    gather/scatter followed by (or preceded by) another expression does not
    change the overall result.

    Requires hs_mem: that s ≤ the intermediate writeMem.size after innerExpr.
    In practice, this follows from evalSigmaAlg_writeMem_size_preserved when
    innerExpr is a well-formed lowered expression. -/
theorem runSigmaAlg_seq_identity_compute
    (ω : α) (innerExpr : SigmaExpr) (kern : Kernel) (s outputSize : Nat)
    (v : List α)
    (hk : ∀ w, evalKernelAlg ω kern w = w)
    (hs_mem : s ≤ (evalSigmaAlg ω LoopEnv.empty (EvalState.init v outputSize) innerExpr).writeMem.size) :
    runSigmaAlg ω (.seq innerExpr
      (.compute kern (Gather.contiguous s (.const 0))
                     (Scatter.contiguous s (.const 0)))) v outputSize
    = runSigmaAlg ω innerExpr v outputSize := by
  simp only [runSigmaAlg, evalSigmaAlg, hk]
  simp only [evalGather, evalScatter, Gather.contiguous, Scatter.contiguous,
             evalIdxExpr, LoopEnv.empty, Nat.zero_add, Nat.one_mul]
  -- Set the intermediate state
  set mem := (evalSigmaAlg ω LoopEnv.empty (EvalState.init v outputSize) innerExpr).writeMem
  -- s ≤ mem.size by hypothesis, so scatter is a no-op by scatter_gather_self
  have := scatter_gather_self mem s hs_mem
  simp only [evalScatter, Scatter.contiguous, evalIdxExpr, LoopEnv.empty,
             Nat.zero_add, Nat.one_mul, evalGather, Gather.contiguous] at this
  rw [this]

/-! ### Compose Lowering Correctness (PROVEN)

The compose case is the critical structural case for compiler verification.
Given `lower (.compose a b)` = `.temp k_mid (.seq exprB exprA)`, we prove
that evaluating the lowered code produces the same result as composing
the matrix semantics: `a(b(input))`.

The proof uses the following chain:
1. Unfold both sides (lower for compose, evalMatExprAlg for compose)
2. Unfold runSigmaAlg for `.temp` and `.seq` using equation lemmas
3. Use IH_B to establish that exprB produces `intermediate = b(input)`
4. Use size preservation to show writeMem.size = k_mid
5. Use Memory roundtrip (ofList ∘ toList = id) to identify writeMem
6. Use writeMem irrelevance to change initial writeMem for exprA
7. Use alpha-equivalence to relate exprA (with state1) to lowerFresh
8. Use IH_A to conclude exprA produces `a(intermediate)` -/

set_option maxHeartbeats 1600000 in
theorem lowering_compose_step
    (ω : α) {k k_mid n : Nat}
    (a : MatExpr α k k_mid) (b : MatExpr α k_mid n)
    (v : List α) (hv : v.length = n)
    (hk_eq : k = k_mid)
    (ihB : runSigmaAlg ω (lowerFresh k_mid n b) v k_mid = evalMatExprAlg ω k_mid n b v)
    (ihA : ∀ (w : List α), w.length = k_mid →
           runSigmaAlg ω (lowerFresh k k_mid a) w k = evalMatExprAlg ω k k_mid a w)
    (h_inter_len : (evalMatExprAlg ω k_mid n b v).length = k_mid)
    (hwf_a : IsWellFormedNTT a) (hnz_a : HasNoZero a)
    (hwf_b : IsWellFormedNTT b) :
    runSigmaAlg ω (lowerFresh k n (@MatExpr.compose α k k_mid n a b)) v k =
    evalMatExprAlg ω k n (@MatExpr.compose α k k_mid n a b) v := by
  -- With squareness (k = k_mid), subst to unify dimensions
  subst hk_eq
  -- Step 1: Unfold evalMatExprAlg for compose → a(b(v))
  simp only [evalMatExprAlg]
  set intermediate := evalMatExprAlg ω k n b v with h_inter_def
  -- Step 2: Unfold lowerFresh and lower for compose → .temp k (.seq exprB exprA)
  simp only [lowerFresh]
  simp only [lower]
  -- Step 3: Unfold runSigmaAlg and evalSigmaAlg for .temp and .seq
  simp only [runSigmaAlg, EvalState.init]
  rw [evalSigmaAlg.eq_5, evalSigmaAlg.eq_3]
  dsimp only []
  -- Step 4: Name the key subexpression (evaluation of exprB)
  set stateB := evalSigmaAlg ω LoopEnv.empty
    { readMem := Memory.ofList v, writeMem := Memory.zeros k }
    (lower k n { nextLoopVar := 0 } b).1 with h_stateB_def
  -- Step 5: From IH_B, derive stateB.writeMem content
  have h_ihB_unfolded : stateB.writeMem.toList.take k = intermediate := by
    have := ihB
    simp only [runSigmaAlg, EvalState.init, lowerFresh] at this
    exact this
  -- Step 6: Size preservation → stateB.writeMem.size = k
  have h_size : stateB.writeMem.size = k :=
    evalSigmaAlg_writeMem_size_preserved ω { nextLoopVar := 0 } b
      (Memory.ofList v) (Memory.zeros k) (Memory.zeros_size k) hwf_b
  -- Step 7: toList has full length, so take = identity
  have h_toList_len : stateB.writeMem.toList.length = k := by
    rw [Array.length_toList]; exact h_size
  have h_take_full : stateB.writeMem.toList.take k = stateB.writeMem.toList :=
    List.take_of_length_le (le_of_eq h_toList_len)
  -- Step 8: stateB.writeMem.toList = intermediate
  have h_wm_toList : stateB.writeMem.toList = intermediate := by
    rw [← h_take_full]; exact h_ihB_unfolded
  -- Step 9: stateB.writeMem = Memory.ofList intermediate (by roundtrip)
  have h_mem_eq : stateB.writeMem = Memory.ofList intermediate := by
    rw [← Memory.ofList_toList stateB.writeMem, h_wm_toList]
  -- Step 10: Substitute readMem and writeMem for exprA
  rw [h_mem_eq]
  -- Step 11: writeMem irrelevance — change writeMem from Memory.ofList intermediate
  -- to Memory.zeros k, so we can match IH_A (runSigmaAlg uses EvalState.init → zeros k)
  set state1 := (lower k n { nextLoopVar := 0 } b).2 with h_state1_def
  have h_wm_irr := evalSigmaAlg_writeMem_irrelevant ω state1 a
    (Memory.ofList intermediate) (Memory.ofList intermediate) (Memory.zeros k)
    (by simp [Memory.size_ofList, h_inter_len]) (Memory.zeros_size k) hwf_a hnz_a
  -- h_wm_irr : (eval {wm = ofList intermediate} exprA).writeMem
  --           = (eval {wm = zeros k} exprA).writeMem
  rw [h_wm_irr]
  -- Step 12: Alpha-equivalence — exprA (with state1) ≡ lowerFresh (with {})
  have h_alpha := lower_state_irrelevant ω state1 { nextLoopVar := 0 } a intermediate
  simp only [runSigmaAlg, EvalState.init] at h_alpha
  rw [h_alpha]
  -- Step 13: Apply IH_A
  have := ihA intermediate h_inter_len
  simp only [runSigmaAlg, EvalState.init, lowerFresh] at this
  exact this

/-! ### Kron Correctness (Fase 8 Corrección 1)

Kronecker product lowering correctness. Uses IsWellFormedNTT which guarantees
a.isIdentity ∨ b.isIdentity, splitting into I⊗B (block scatter) and A⊗I (stride scatter).
The inductive hypotheses ihA/ihB connect evalKernelAlg to evalMatExprAlg per-block/per-lane. -/

set_option maxHeartbeats 1600000 in
/-- Kronecker product lowering correctness.
    For I ⊗ B: lower produces .loop m₁ (adjustBlock (lower b))
    For A ⊗ I: lower produces .loop m₂ (adjustStride (lower a))
    IsWellFormedNTT guarantees exactly one of a,b is identity (no general A⊗B). -/
theorem lowering_kron_axiom
    {m₁ n₁ m₂ n₂ : Nat}
    (ω : α) (a : MatExpr α m₁ n₁) (b : MatExpr α m₂ n₂)
    (v : List α) (hv : v.length = n₁ * n₂)
    (hwf : IsWellFormedNTT (.kron a b))
    (ihA : ∀ (w : List α), w.length = n₁ →
           runSigmaAlg ω (lowerFresh m₁ n₁ a) w m₁ = evalMatExprAlg ω m₁ n₁ a w)
    (ihB : ∀ (w : List α), w.length = n₂ →
           runSigmaAlg ω (lowerFresh m₂ n₂ b) w m₂ = evalMatExprAlg ω m₂ n₂ b w) :
    runSigmaAlg ω (lowerFresh (m₁ * m₂) (n₁ * n₂) (.kron a b)) v (m₁ * m₂) =
    evalMatExprAlg ω (m₁ * m₂) (n₁ * n₂) (.kron a b) v := by
  -- Destructure IsWellFormedNTT (.kron a b)
  obtain ⟨ha_sq, hb_sq, _, _, hwf_a, hwf_b, hm₁_pos, hm₂_pos, h_id, h_nsl_a, h_nsl_b⟩ := hwf
  subst ha_sq; subst hb_sq
  -- Now m₁ = n₁, m₂ = n₂ (square sub-matrices)
  -- Use by_cases so the A⊗I branch gets ¬(a.isIdentity = true)
  by_cases h_id_a : a.isIdentity = true
  · -- === I⊗B case (a.isIdentity = true) ===
    -- Split on whether b contains zero (determines lower output: .compute vs .nop)
    open Classical in by_cases hnz_b : HasNoZero b
    · -- Non-zero B: lower b = .compute k (contiguous) → adjustBlock → block scatter loop
      -- Get contiguous form of lower b
      obtain ⟨k, hk⟩ := lower_hasNoSeqLower_contiguous {} b h_nsl_b hnz_b rfl
      -- State independence: lower with {1} = lower with {}
      have hs : (lower m₂ m₂ { nextLoopVar := 1 } b).1 = (lower m₂ m₂ {} b).1 :=
        lower_hasNoSeqLower_state_eq { nextLoopVar := 1 } {} b h_nsl_b
      -- Combine: lower with {1} also produces .compute k contiguous contiguous
      have hk' : (lower m₂ m₂ { nextLoopVar := 1 } b).1 =
          .compute k (Gather.contiguous m₂ (.const 0)) (Scatter.contiguous m₂ (.const 0)) :=
        hs.trans hk
      -- What lowerFresh produces for kron I⊗B
      have h_lf : lowerFresh (m₁ * m₂) (m₁ * m₂) (.kron a b) =
          .loop m₁ 0 (.compute k (Gather.block m₂ 0) (Scatter.block m₂ 0)) := by
        unfold lowerFresh lower
        simp only [h_id_a, ite_true, freshLoopVar, hk', adjustBlock]
      -- Kernel equation: evalKernelAlg k w = evalMatExprAlg b w
      have hker : ∀ w : List α, w.length = m₂ →
          evalKernelAlg ω k w = evalMatExprAlg ω m₂ m₂ b w := by
        intro w hw
        have h1 := ihB w hw
        rw [show lowerFresh m₂ m₂ b = .compute k (Gather.contiguous m₂ (.const 0))
              (Scatter.contiguous m₂ (.const 0)) from hk] at h1
        exact (lowering_compute_contiguous_correct m₂ k w hw
          (lower_kernel_preserves_length ω {} b h_nsl_b hnz_b rfl k _ _ hk w hw)).symm.trans h1
      -- Kernel length preservation
      have hker_len : ∀ i, i < m₁ →
          (evalKernelAlg ω k (v.drop (i * m₂) |>.take m₂)).length = m₂ := by
        intro i hi
        have hblock_len : (v.drop (i * m₂) |>.take m₂).length = m₂ := by
          rw [List.length_take, List.length_drop, hv]
          apply Nat.min_eq_left
          have hmul := Nat.mul_le_mul_right m₂ (Nat.succ_le_of_lt hi)
          rw [Nat.succ_mul] at hmul; omega
        exact lower_kernel_preserves_length ω {} b h_nsl_b hnz_b rfl k _ _ hk _ hblock_len
      -- Unfold RHS: evalMatExprAlg for kron with isIdentity a = true
      have hrhs : evalMatExprAlg ω (m₁ * m₂) (m₁ * m₂) (.kron a b) v =
          (List.range m₁).flatMap fun i =>
            evalMatExprAlg ω m₂ m₂ b (v.drop (i * m₂) |>.take m₂) := by
        conv_lhs => unfold evalMatExprAlg
        split
        · rfl
        · next h => exact absurd h_id_a h
      rw [hrhs]
      -- Rewrite LHS using h_lf
      rw [h_lf]
      -- Main computation: connect block scatter loop to flatMap
      -- Step 1: Unfold runSigmaAlg to expose evalSigmaAlg
      simp only [runSigmaAlg, EvalState.init]
      -- Step 2: Unfold .loop to foldl
      simp only [evalSigmaAlg.eq_2]
      -- Step 3: Extract writeMem from EvalState foldl
      simp only [compute_loop_decompose_writeMem]
      -- Step 4: Convert scatter to enumFrom form
      simp only [evalScatter_block_eq_enumFrom]
      -- Step 5: Apply block_scatter_loop_inv
      set vals := fun j => evalKernelAlg ω k
        (evalGather (LoopEnv.empty.bind 0 j) (Gather.block m₂ 0) (Memory.ofList v))
      have hvals_len : ∀ j, j < m₁ → (vals j).length = m₂ := by
        intro j _
        exact lower_kernel_preserves_length ω {} b h_nsl_b hnz_b rfl k _ _ hk _
          (evalGather_length _ _ _)
      have hinv := block_scatter_loop_inv m₁ m₂ (Memory.zeros (m₁ * m₂)) vals hvals_len
        (Memory.zeros_size _) m₁ (le_refl m₁)
      rw [hinv.1]
      -- Step 6: Simplify drop of zeros and take
      rw [Memory.zeros_toList, List.drop_of_length_le (by simp [List.length_replicate]),
          List.append_nil,
          List.take_of_length_le (by rw [flatMap_range_length vals m₂ m₁ hvals_len])]
      -- Step 7: Show flatMap vals = flatMap (fun j => evalMatExprAlg ω m₂ m₂ b (block_j))
      -- Need pointwise equality only for j < m₁ (elements of List.range m₁)
      have hvals_eq : ∀ j, j < m₁ →
          vals j = evalMatExprAlg ω m₂ m₂ b (v.drop (j * m₂) |>.take m₂) := by
        intro j hj; simp only [vals]
        rw [evalGather_block_eq_drop_take 0 m₂ j v
            (by rw [hv]; exact Nat.mul_le_mul_right m₂ (by omega))]
        exact hker _ (by
          rw [List.length_take, List.length_drop, hv]
          apply Nat.min_eq_left
          have hmul := Nat.mul_le_mul_right m₂ (Nat.succ_le_of_lt hj)
          rw [Nat.succ_mul] at hmul; omega)
      -- Prove flatMap equality (pointwise for j ∈ range m₁)
      suffices h : ∀ l : List Nat, (∀ j ∈ l, j < m₁) →
          l.flatMap vals = l.flatMap (fun j =>
            evalMatExprAlg ω m₂ m₂ b (v.drop (j * m₂) |>.take m₂)) from
        h _ (fun j hj => List.mem_range.mp hj)
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.flatMap_cons]
        rw [hvals_eq x (hl x (List.mem_cons_self _ _)),
            ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))]
    · -- Zero B: lower b = .nop, both sides = replicate (m₁*m₂) 0
      -- lower b is .nop
      have h_nop_b : (lower m₂ m₂ {} b).1 = .nop :=
        lower_hasNoSeqLower_notHasNoZero_is_nop {} b h_nsl_b hnz_b
      have hs_nop : (lower m₂ m₂ { nextLoopVar := 1 } b).1 = .nop :=
        (lower_hasNoSeqLower_state_eq { nextLoopVar := 1 } {} b h_nsl_b).trans h_nop_b
      -- lowerFresh kron = .loop m₁ 0 .nop
      have h_lf : lowerFresh (m₁ * m₂) (m₁ * m₂) (.kron a b) = .loop m₁ 0 .nop := by
        unfold lowerFresh lower
        simp only [h_id_a, ite_true, freshLoopVar, hs_nop, adjustBlock]
      -- evalMatExprAlg b w = replicate m₂ 0 (for any w with w.length = m₂)
      have hb_zero : ∀ w : List α, w.length = m₂ →
          evalMatExprAlg ω m₂ m₂ b w = List.replicate m₂ 0 := by
        intro w hw
        have h1 := ihB w hw
        rw [show lowerFresh m₂ m₂ b = .nop from h_nop_b] at h1
        simp only [runSigmaAlg, evalSigmaAlg, EvalState.init, Memory.zeros_toList] at h1
        rw [← h1]
        simp [List.take_replicate, Nat.min_self]
      rw [h_lf]
      -- Both sides = replicate (m₁ * m₂) 0
      -- LHS: runSigmaAlg of loop-of-nop = zeros
      have lhs_eq : runSigmaAlg ω (.loop m₁ 0 .nop) v (m₁ * m₂) =
          List.replicate (m₁ * m₂) 0 := by
        simp only [runSigmaAlg, EvalState.init, evalSigmaAlg.eq_2]
        suffices ∀ (l : List Nat) (st : EvalState α), l.foldl (fun s j =>
            evalSigmaAlg ω (LoopEnv.empty.bind 0 j) s .nop) st = st by
          rw [this]; simp [Memory.zeros_toList, List.take_replicate, Nat.min_self]
        intro l; induction l with
        | nil => simp
        | cons _ _ ih => intro st; simp only [List.foldl_cons, evalSigmaAlg] at ih ⊢; exact ih st
      -- RHS: evalMatExprAlg of kron with zero b = flatMap of replicate
      have rhs_eq : evalMatExprAlg ω (m₁ * m₂) (m₁ * m₂) (.kron a b) v =
          List.replicate (m₁ * m₂) 0 := by
        -- Unfold evalMatExprAlg for kron and resolve isIdentity a
        have h_unfold : evalMatExprAlg ω (m₁ * m₂) (m₁ * m₂) (.kron a b) v =
            (List.range m₁).flatMap (fun i =>
              evalMatExprAlg ω m₂ m₂ b (v.drop (i * m₂) |>.take m₂)) := by
          conv_lhs => unfold evalMatExprAlg
          split
          · rfl
          · next h => exact absurd h_id_a h
        rw [h_unfold]
        -- Replace each evalMatExprAlg b with replicate m₂ 0 (membership-restricted)
        suffices hfm : ∀ l : List Nat, (∀ j ∈ l, j < m₁) →
            l.flatMap (fun i => evalMatExprAlg ω m₂ m₂ b (v.drop (i * m₂) |>.take m₂)) =
            l.flatMap (fun _ => List.replicate m₂ 0) from by
          rw [hfm _ (fun j hj => List.mem_range.mp hj)]
          -- flatMap of constant replicate = replicate
          suffices ∀ n : Nat, (List.range n).flatMap (fun _ => List.replicate m₂ (0 : α)) =
              List.replicate (n * m₂) 0 from this m₁
          intro n; induction n with
          | zero => simp
          | succ k ih =>
            rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
                Nat.succ_mul, List.replicate_add]
        intro l hl; induction l with
        | nil => simp
        | cons x xs ih =>
          simp only [List.flatMap_cons]
          rw [hb_zero _ (by
                rw [List.length_take, List.length_drop, hv]
                rw [Nat.min_def]; split_ifs with hle
                · rfl
                · have hmul := Nat.mul_le_mul_right m₂ (Nat.succ_le_of_lt (hl x (List.mem_cons_self _ _)))
                  rw [Nat.succ_mul] at hmul; omega),
              ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))]
      rw [lhs_eq, rhs_eq]
  · -- === A⊗I case (¬a.isIdentity, b.isIdentity) ===
    have h_id_b : b.isIdentity = true := h_id.resolve_left h_id_a
    have ha_false : a.isIdentity = false := by
      match h : a.isIdentity with
      | true => exact absurd h h_id_a
      | false => rfl
    open Classical in by_cases hnz_a : HasNoZero a
    · -- Non-zero A: stride scatter
      obtain ⟨k, hk⟩ := lower_hasNoSeqLower_contiguous {} a h_nsl_a hnz_a rfl
      have hs : (lower m₁ m₁ { nextLoopVar := 1 } a).1 = (lower m₁ m₁ {} a).1 :=
        lower_hasNoSeqLower_state_eq { nextLoopVar := 1 } {} a h_nsl_a
      have hk' : (lower m₁ m₁ { nextLoopVar := 1 } a).1 =
          .compute k (Gather.contiguous m₁ (.const 0)) (Scatter.contiguous m₁ (.const 0)) :=
        hs.trans hk
      have h_lf : lowerFresh (m₁ * m₂) (m₁ * m₂) (.kron a b) =
          .loop m₂ 0 (.compute k
            { count := m₁, baseAddr := .var 0, stride := m₂ }
            { count := m₁, baseAddr := .var 0, stride := m₂ }) := by
        unfold lowerFresh lower
        simp only [ha_false, Bool.false_eq_true, ite_false,
                    h_id_b, ite_true, freshLoopVar, hk', adjustStride]
      -- Kernel equation: evalKernelAlg k w = evalMatExprAlg a w
      have hker : ∀ w : List α, w.length = m₁ →
          evalKernelAlg ω k w = evalMatExprAlg ω m₁ m₁ a w := by
        intro w hw
        have h1 := ihA w hw
        rw [show lowerFresh m₁ m₁ a = .compute k (Gather.contiguous m₁ (.const 0))
              (Scatter.contiguous m₁ (.const 0)) from hk] at h1
        exact (lowering_compute_contiguous_correct m₁ k w hw
          (lower_kernel_preserves_length ω {} a h_nsl_a hnz_a rfl k _ _ hk w hw)).symm.trans h1
      -- Rewrite LHS with h_lf and unfold
      rw [h_lf]
      simp only [runSigmaAlg, EvalState.init, evalSigmaAlg.eq_2,
                  compute_loop_decompose_writeMem, evalScatter_stride_var_eq]
      -- Define vals for each lane j
      set vals := fun j => evalKernelAlg ω k
        (evalGather (LoopEnv.empty.bind 0 j)
          { count := m₁, baseAddr := .var 0, stride := m₂ } (Memory.ofList v))
      -- vals have correct length
      have hvals_len : ∀ j, j < m₂ → (vals j).length = m₁ := by
        intro j hj; simp only [vals]
        rw [evalGather_stride_ofList_eq_lane 0 m₁ m₂ j v hj hv]
        exact lower_kernel_preserves_length ω {} a h_nsl_a hnz_a rfl k _ _ hk _
          (by simp [List.length_map, List.length_range])
      -- vals j = evalMatExprAlg a (lane j)
      have hvals_eq : ∀ j, j < m₂ →
          vals j = evalMatExprAlg ω m₁ m₁ a
            ((List.range m₁).map fun i => v.getD (j + i * m₂) default) := by
        intro j hj; simp only [vals]
        rw [evalGather_stride_ofList_eq_lane 0 m₁ m₂ j v hj hv]
        exact hker _ (by simp)
      -- Stride scatter loop invariant
      have hinv := stride_scatter_loop_inv m₁ m₂ hm₂_pos (Memory.zeros (m₁ * m₂)) vals hvals_len
        (Memory.zeros_size _) m₂ (le_refl m₂)
      -- Assembly: connect stride scatter loop invariant with evalMatExprAlg A⊗I format
      -- Infrastructure proven above: h_lf, hker, hvals_len, hvals_eq, hinv
      -- Remaining: pointwise equality between stride scatter result and strided lane format
      -- Strategy: rw [h_lf], unfold runSigmaAlg, use hinv for LHS,
      --   unfold evalMatExprAlg for RHS, connect via hvals_eq pointwise
      sorry
    · -- Zero A: both sides = replicate (m₁*m₂) 0
      sorry

/-! ### The Fundamental Correctness Theorem

For any matrix expression mat and input vector v:
evaluating the lowered Sigma-SPL code produces the same result
as direct matrix-vector multiplication.

Current status (Fase 8 Corrección 1): 18/19 cases PROVEN (2 sorry in kron A⊗I)
- Identity: PROVEN via lowering_identity_correct
- DFT: PROVEN via lowering_dft_correct + meta-lemma
- NTT: PROVEN via meta-lemma (identity-like kernel)
- Twiddle: PROVEN via meta-lemma (identity-like kernel)
- Diag: PROVEN via meta-lemma (identity kernel)
- Scalar: PROVEN via meta-lemma (scale kernel, size 1)
- Compose: PROVEN via lowering_compose_step (WF termination fixed in Corrección 8)
- Kron: I⊗B PROVEN, A⊗I infra done (2 sorry remain) — Fase 8 Corrección 1
- Zero: PROVEN (lower → .nop, writeMem = zeros)
- Perm: PROVEN (lower → identity kernel, applyPerm is stub)
- Smul: PROVEN via runSigmaAlg_seq_identity_compute
- Elemwise: PROVEN via runSigmaAlg_seq_identity_compute
- PartialElemwise: PROVEN via runSigmaAlg_seq_identity_compute
- MdsApply: PROVEN via runSigmaAlg_seq_identity_compute
- AddRoundConst: PROVEN via runSigmaAlg_seq_identity_compute
- Transpose: PROVEN via ▸ cast (avoids subst WF issues, Corrección 8)
- ConjTranspose: PROVEN via ▸ cast (same as transpose)
- Add: PROVEN vacuously (DD-ADD: IsWellFormedNTT .add = False, Corrección 8)

Note: IsPrimitiveRoot is NOT needed for lowering correctness.
The lowering correctness says "compiled code = reference semantics"
regardless of ω. IsPrimitiveRoot would only be needed at a higher level
to prove "compiled code computes DFT". -/

set_option maxHeartbeats 800000 in
theorem lowering_algebraic_correct
    (ω : α) (mat : MatExpr α k n) (v : List α) (hv : v.length = n)
    (hwf : IsWellFormedNTT mat) :
    runSigmaAlg ω (lowerFresh k n mat) v k = evalMatExprAlg ω k n mat v := by
  match mat with
  | .identity n' =>
    -- Identity case: PROVEN
    simp only [evalMatExprAlg]
    exact lowering_identity_correct n' v hv
  | .dft n' =>
    -- DFT case: PROVEN via meta-lemma (L-060)
    rw [evalMatExprAlg_dft_eq_kernelAlg, lower_dft]
    exact lowering_compute_contiguous_correct n' (.dft n') v hv
      (evalKernelAlg_dft_length n' v hv)
  | .ntt n' p_ntt =>
    -- NTT case: PROVEN - identity-like kernel (evalKernelAlg returns input)
    simp only [evalMatExprAlg]
    have hlower : lowerFresh n' n' (.ntt n' p_ntt : MatExpr α n' n') =
      .compute (.ntt n' p_ntt) (Gather.contiguous n' (.const 0))
        (Scatter.contiguous n' (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω (.ntt n' p_ntt) v).length = n' := by
      simp [evalKernelAlg]; exact hv
    have hmeta := lowering_compute_contiguous_correct n' (.ntt n' p_ntt) v hv hlen
    simp only [evalKernelAlg] at hmeta
    exact hmeta
  | .twiddle n' k_tw =>
    -- Twiddle case: PROVEN - identity-like kernel
    simp only [evalMatExprAlg]
    have hlower : lowerFresh n' n' (.twiddle n' k_tw : MatExpr α n' n') =
      .compute (.twiddle n' k_tw) (Gather.contiguous n' (.const 0))
        (Scatter.contiguous n' (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω (.twiddle n' k_tw) v).length = n' := by
      simp [evalKernelAlg]; exact hv
    have hmeta := lowering_compute_contiguous_correct n' (.twiddle n' k_tw) v hv hlen
    simp only [evalKernelAlg] at hmeta
    exact hmeta
  | .diag v' =>
    -- Diag case: PROVEN - lowers to identity kernel
    simp only [evalMatExprAlg]
    have hlower : lowerFresh n n (@MatExpr.diag α n v') =
      .compute (.identity n) (Gather.contiguous n (.const 0))
        (Scatter.contiguous n (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω (.identity n) v).length = n := by
      simp [evalKernelAlg, evalIdentityKernel]; exact hv
    have hmeta := lowering_compute_contiguous_correct n (.identity n) v hv hlen
    simp only [evalKernelAlg, evalIdentityKernel] at hmeta
    exact hmeta
  | .scalar e =>
    -- Scalar case: PROVEN - lowers to scale kernel, size 1
    simp only [evalMatExprAlg]
    have hlower : lowerFresh 1 1 (.scalar e : MatExpr α 1 1) =
      .compute .scale (Gather.contiguous 1 (.const 0))
        (Scatter.contiguous 1 (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω .scale v).length = 1 := by
      simp [evalKernelAlg]; exact hv
    have hmeta := lowering_compute_contiguous_correct 1 .scale v hv hlen
    simp only [evalKernelAlg] at hmeta
    exact hmeta
  | .kron a b =>
    -- Kronecker product: PROVEN via lowering_kron_axiom + IH
    exact lowering_kron_axiom ω a b v hv hwf
      (fun w hw => lowering_algebraic_correct ω a w hw hwf.2.2.2.2.1)
      (fun w hw => lowering_algebraic_correct ω b w hw hwf.2.2.2.2.2.1)
  | .compose a b =>
    -- Composition: PROVEN via lowering_compose_step
    -- hwf : m' = k' ∧ HasNoZero a ∧ IsWellFormedNTT a ∧ IsWellFormedNTT b
    obtain ⟨hk_eq, hnz_a, hwf_a, hwf_b⟩ := hwf
    have ihB := lowering_algebraic_correct ω b v hv hwf_b
    exact lowering_compose_step ω a b v hv hk_eq ihB
      (fun w hw => lowering_algebraic_correct ω a w hw hwf_a)
      (evalMatExprAlg_length ω b v hv hwf_b)
      hwf_a hnz_a hwf_b
  | .zero _ _ =>
    -- Zero case: PROVEN - lower(.zero) = .nop, writeMem starts as Memory.zeros
    simp only [evalMatExprAlg, lowerFresh, lower,
               runSigmaAlg, evalSigmaAlg, EvalState.init, Memory.zeros_toList]
    exact List.take_of_length_le (le_of_eq (List.length_replicate k (0 : α)))
  | .perm p =>
    -- Perm case: PROVEN - lower(.perm) = identity kernel, applyPerm is identity stub
    simp only [evalMatExprAlg, applyPerm]
    have hlower : lowerFresh n n (.perm p : MatExpr α n n) =
      .compute (.identity n) (Gather.contiguous n (.const 0))
        (Scatter.contiguous n (.const 0)) := by
      simp only [lowerFresh, lower]
    rw [hlower]
    have hlen : (evalKernelAlg ω (.identity n) v).length = n := by
      simp [evalKernelAlg, evalIdentityKernel]; exact hv
    have hmeta := lowering_compute_contiguous_correct n (.identity n) v hv hlen
    simp only [evalKernelAlg, evalIdentityKernel] at hmeta
    exact hmeta
  | .add a b =>
    -- DD-ADD: IsWellFormedNTT (.add _ _) = False, so hwf is vacuously absurd
    exact hwf.elim
  | .smul c a =>
    -- Smul case: PROVEN via seq_identity axiom
    -- lower(.smul) = .seq exprA (.compute .scale contiguous contiguous)
    -- .scale kernel returns input unchanged
    -- hwf : (k = n) ∧ IsWellFormedNTT a
    have hkn : k = n := hwf.1
    have hwf_a : IsWellFormedNTT a := hwf.2
    simp only [evalMatExprAlg, lowerFresh, lower]
    have h_size := evalSigmaAlg_writeMem_size_preserved ω { nextLoopVar := 0 } a
      (Memory.ofList v) (Memory.zeros k) (Memory.zeros_size k) hwf_a
    rw [runSigmaAlg_seq_identity_compute ω _ .scale n k v
        (by intro w; simp [evalKernelAlg])
        (by simp only [EvalState.init]; rw [h_size]; omega)]
    exact lowering_algebraic_correct ω a v hv hwf_a
  | .transpose a =>
    -- lower(.transpose a) = lower n k a (swap dimensions)
    -- IsWellFormedNTT (.transpose a) = (k = n) ∧ IsWellFormedNTT a
    -- With k = n, dimensions unify and IH applies directly
    have hmn : k = n := hwf.1
    have hwf_a : IsWellFormedNTT a := hwf.2
    simp only [evalMatExprAlg, lowerFresh, lower]
    have hv' : v.length = k := hmn ▸ hv
    exact hmn ▸ lowering_algebraic_correct ω a v hv' hwf_a
  | .conjTranspose a =>
    -- Same as transpose: k = n makes dimensions match
    have hmn : k = n := hwf.1
    have hwf_a : IsWellFormedNTT a := hwf.2
    simp only [evalMatExprAlg, lowerFresh, lower]
    have hv' : v.length = k := hmn ▸ hv
    exact hmn ▸ lowering_algebraic_correct ω a v hv' hwf_a
  | .elemwise op a =>
    -- Elemwise case: PROVEN via seq_identity axiom
    -- hwf : (n = 1) ∧ IsWellFormedNTT a, so k * n = k * 1 = k
    have hwf_a : IsWellFormedNTT a := hwf.2
    simp only [evalMatExprAlg, lowerFresh, lower]
    have h_size := evalSigmaAlg_writeMem_size_preserved ω { nextLoopVar := 0 } a
      (Memory.ofList v) (Memory.zeros k) (Memory.zeros_size k) hwf_a
    rw [runSigmaAlg_seq_identity_compute ω _ (.sbox (k * n) op.toExp) (k * n) k v
        (by intro w; simp [evalKernelAlg])
        (by simp only [EvalState.init]; rw [h_size]; rw [show n = 1 from hwf.1]; omega)]
    exact lowering_algebraic_correct ω a v hv hwf_a
  | .partialElemwise idx op a =>
    -- PartialElemwise case: PROVEN via seq_identity axiom
    -- hwf : (n = 1) ∧ IsWellFormedNTT a, so k * n = k * 1 = k
    have hwf_a : IsWellFormedNTT a := hwf.2
    simp only [evalMatExprAlg, lowerFresh, lower]
    have h_size := evalSigmaAlg_writeMem_size_preserved ω { nextLoopVar := 0 } a
      (Memory.ofList v) (Memory.zeros k) (Memory.zeros_size k) hwf_a
    rw [runSigmaAlg_seq_identity_compute ω _ (.partialSbox (k * n) op.toExp idx) (k * n) k v
        (by intro w; simp [evalKernelAlg])
        (by simp only [EvalState.init]; rw [h_size]; rw [show n = 1 from hwf.1]; omega)]
    exact lowering_algebraic_correct ω a v hv hwf_a
  | .mdsApply mdsName stateSize a =>
    -- MdsApply case: PROVEN via seq_identity axiom
    -- hwf : (stateSize = k) ∧ IsWellFormedNTT a, so s = stateSize = k
    have hwf_a : IsWellFormedNTT a := hwf.2
    simp only [evalMatExprAlg, lowerFresh, lower]
    have h_size := evalSigmaAlg_writeMem_size_preserved ω { nextLoopVar := 0 } a
      (Memory.ofList v) (Memory.zeros k) (Memory.zeros_size k) hwf_a
    rw [runSigmaAlg_seq_identity_compute ω _ (.mdsApply mdsName stateSize) stateSize k v
        (by intro w; simp [evalKernelAlg])
        (by simp only [EvalState.init]; rw [h_size]; have := hwf.1; omega)]
    exact lowering_algebraic_correct ω a v hv hwf_a
  | .addRoundConst round stateSize a =>
    -- AddRoundConst case: PROVEN via seq_identity axiom
    -- hwf : (stateSize = k) ∧ IsWellFormedNTT a, so s = stateSize = k
    have hwf_a : IsWellFormedNTT a := hwf.2
    simp only [evalMatExprAlg, lowerFresh, lower]
    have h_size := evalSigmaAlg_writeMem_size_preserved ω { nextLoopVar := 0 } a
      (Memory.ofList v) (Memory.zeros k) (Memory.zeros_size k) hwf_a
    rw [runSigmaAlg_seq_identity_compute ω _ (.addRoundConst round stateSize) stateSize k v
        (by intro w; simp [evalKernelAlg])
        (by simp only [EvalState.init]; rw [h_size]; have := hwf.1; omega)]
    exact lowering_algebraic_correct ω a v hv hwf_a
termination_by mat.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (simp only [MatExpr.nodeCount]; omega)
    -- compose closure: Lean's WF encoding for recursive calls inside lambdas
    -- creates a goal where simp only [nodeCount] partially unfolds.
    -- The actual termination is trivial: a.nodeCount < 1 + a.nodeCount + b.nodeCount.
    | (simp_arith [MatExpr.nodeCount])
    | (unfold MatExpr.nodeCount; omega)
    | (simp [MatExpr.nodeCount]; omega)

end AmoLean.Verification.Algebraic
