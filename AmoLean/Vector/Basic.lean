/-
  AMO-Lean: Vector Module
  Phase 5.1 - Length-indexed vectors and vector expressions

  This module implements vectors with length encoded in the type,
  following the approach from Xi & Pfenning's "Dependent Types in
  Practical Programming" (POPL 1999).

  Key design decisions:
  1. Vec α n: Vector with length n in the type (memory safety by construction)
  2. VecExpr α n: Expression AST for vector operations
  3. Explicit length parameters (not inferred) to avoid inference issues with ZMod

  Reference: docs/optimizaciones prefase5/dt practical.pdf
-/

import AmoLean.Basic

namespace AmoLean.Vector

/-! ## Vec α n: Length-indexed Vector

A vector with its length encoded in the type. This guarantees:
- No out-of-bounds access (impossible by construction)
- Length-preserving operations have correct types
- Split/concat operations have precise types

Following DML (Xi & Pfenning):
```
nil <| 'a list(0)
cons <| {n:nat} 'a * 'a list(n) -> 'a list(n+1)
```
-/

/-- Length-indexed vector. The length `n` is part of the type. -/
inductive Vec (α : Type u) : Nat → Type u where
  /-- Empty vector has length 0 -/
  | nil : Vec α 0
  /-- Cons adds one element, incrementing length -/
  | cons : α → Vec α n → Vec α (n + 1)
  deriving Repr

namespace Vec

/-- Get the head of a non-empty vector.
    Note: Only callable on vectors of length n+1, so it's total. -/
def head : Vec α (n + 1) → α
  | cons x _ => x

/-- Get the tail of a non-empty vector. -/
def tail : Vec α (n + 1) → Vec α n
  | cons _ xs => xs

/-- Get element at index i (with proof that i < n) -/
def get (v : Vec α n) (i : Fin n) : α :=
  match n, v, i with
  | _ + 1, cons x _,  ⟨0, _⟩     => x
  | _ + 1, cons _ xs, ⟨i + 1, h⟩ => get xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Append two vectors. Result length is m + n. -/
def append : Vec α m → Vec α n → Vec α (m + n)
  | nil,       ys => by rw [Nat.zero_add]; exact ys
  | cons x xs, ys => by
    rw [Nat.succ_add]
    exact cons x (append xs ys)

/-- Map a function over a vector, preserving length. -/
def map (f : α → β) : Vec α n → Vec β n
  | nil       => nil
  | cons x xs => cons (f x) (map f xs)

/-- Zip two vectors of the same length. -/
def zip : Vec α n → Vec β n → Vec (α × β) n
  | nil,       nil       => nil
  | cons x xs, cons y ys => cons (x, y) (zip xs ys)

/-- ZipWith: combine two vectors element-wise. -/
def zipWith (f : α → β → γ) : Vec α n → Vec β n → Vec γ n
  | nil,       nil       => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)

/-- Replicate: create a vector of n copies of x. -/
def replicate (n : Nat) (x : α) : Vec α n :=
  match n with
  | 0     => nil
  | n + 1 => cons x (replicate n x)

/-- Create vector from function. -/
def ofFn (f : Fin n → α) : Vec α n :=
  match n with
  | 0     => nil
  | n + 1 => cons (f ⟨0, Nat.zero_lt_succ n⟩)
                  (ofFn (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

/-- Convert to List (losing type-level length information). -/
def toList : Vec α n → List α
  | nil       => []
  | cons x xs => x :: toList xs

/-- Create from List (length determined at runtime).
    Returns existential type since length is not known statically. -/
def fromList (l : List α) : (n : Nat) × Vec α n :=
  match l with
  | []     => ⟨0, nil⟩
  | x :: xs =>
    let ⟨n, v⟩ := fromList xs
    ⟨n + 1, cons x v⟩

/-- Reverse a vector. -/
def reverse (v : Vec α n) : Vec α n :=
  have h : 0 + n = n := Nat.zero_add n
  h ▸ go nil v
where
  go {m k : Nat} (acc : Vec α m) (v : Vec α k) : Vec α (m + k) :=
    match k, v with
    | 0, nil => by rw [Nat.add_zero]; exact acc
    | k' + 1, cons x xs =>
      have h : m + (k' + 1) = (m + 1) + k' := by omega
      h ▸ go (cons x acc) xs

/-- Take the first k elements. -/
def take (k : Nat) (h : k ≤ n) : Vec α n → Vec α k :=
  match k with
  | 0     => fun _ => nil
  | k + 1 => fun v =>
    match n, v with
    | _ + 1, cons x xs => cons x (take k (Nat.le_of_succ_le_succ h) xs)

/-- Drop the first k elements. -/
def drop (k : Nat) (h : k ≤ n) : Vec α n → Vec α (n - k) :=
  match k with
  | 0     => fun v => by rw [Nat.sub_zero]; exact v
  | k + 1 => fun v =>
    match n, v with
    | n + 1, cons _ xs =>
      have h' : n + 1 - (k + 1) = n - k := by omega
      h' ▸ drop k (Nat.le_of_succ_le_succ h) xs

/-- Split a vector at position k. -/
def splitAt (k : Nat) (h : k ≤ n) (v : Vec α n) : Vec α k × Vec α (n - k) :=
  (take k h v, drop k h v)

/-- Split into two halves (for even-length vectors). -/
def halve (v : Vec α (2 * n)) : Vec α n × Vec α n :=
  let h : n ≤ 2 * n := by omega
  let h' : 2 * n - n = n := by omega
  let (l, r) := splitAt n h v
  (l, h' ▸ r)

/-- Interleave two vectors: [a₀,a₁,...] [b₀,b₁,...] → [a₀,b₀,a₁,b₁,...] -/
def interleave : Vec α n → Vec α n → Vec α (2 * n)
  | nil, nil => nil
  | @cons _ n' x xs, cons y ys =>
    have h : 2 * (n' + 1) = (2 * n') + 2 := by omega
    h ▸ cons x (cons y (interleave xs ys))

/-- Fold left. -/
def foldl (f : β → α → β) (init : β) : Vec α n → β
  | nil       => init
  | cons x xs => foldl f (f init x) xs

/-- Fold right. -/
def foldr (f : α → β → β) (init : β) : Vec α n → β
  | nil       => init
  | cons x xs => f x (foldr f init xs)

/-- Sum of numeric vector. -/
def sum [Add α] [OfNat α 0] : Vec α n → α :=
  foldl (· + ·) 0

/-- Product of numeric vector. -/
def prod [Mul α] [OfNat α 1] : Vec α n → α :=
  foldl (· * ·) 1

end Vec

/-! ## VecExpr α n: Vector Expression AST

Expressions that denote vectors of a specific length.
This is the "middle level" of our three-level architecture:

  MatExpr (high level, Kronecker) → VecExpr (middle, typed) → Expr (low, scalar)

VecExpr operations preserve or transform lengths in a type-safe way.
-/

-- Re-export Expr and VarId from Basic
open AmoLean (Expr VarId)

/-- Identifier for vector variables -/
abbrev VecVarId := Nat

/-- Expression denoting a vector of length n.

    The type parameter n ensures:
    - split only works on vectors of even length
    - concat produces correct output length
    - zip requires equal-length inputs

    Note: We don't derive Repr because functions can't have Repr instances.
-/
inductive VecExpr (α : Type) : Nat → Type where
  /-- Literal vector -/
  | lit : Vec (Expr α) n → VecExpr α n

  /-- Vector variable (bound by context) -/
  | var : VecVarId → VecExpr α n

  /-- Map scalar function over vector -/
  | map : VecExpr α n → VecExpr α n

  /-- ZipWith: combine two vectors element-wise -/
  | zipWith : VecExpr α n → VecExpr α n → VecExpr α n

  /-- Take first half of a vector (low elements) -/
  | splitLo : VecExpr α (2 * n) → VecExpr α n

  /-- Take second half of a vector (high elements) -/
  | splitHi : VecExpr α (2 * n) → VecExpr α n

  /-- Concatenate two vectors -/
  | concat : VecExpr α m → VecExpr α n → VecExpr α (m + n)

  /-- Interleave two vectors -/
  | interleave : VecExpr α n → VecExpr α n → VecExpr α (2 * n)

  /-- Stride permutation L^{kn}_n
      Rearranges a vector of length k*n using stride-n access pattern.
      This is a key operation for FFT data movement. -/
  | stride : (k : Nat) → VecExpr α (k * n) → VecExpr α (k * n)

  /-- Bit-reversal permutation (for FFT) -/
  | bitRev : VecExpr α (2^k) → VecExpr α (2^k)

  /-- Apply scalar expression element-wise (broadcast) -/
  | broadcast : Expr α → VecExpr α n

namespace VecExpr

/-- Smart constructor: zipWith for addition -/
def add : VecExpr α n → VecExpr α n → VecExpr α n :=
  VecExpr.zipWith

/-- Smart constructor: zipWith for multiplication -/
def mul : VecExpr α n → VecExpr α n → VecExpr α n :=
  VecExpr.zipWith

/-- Smart constructor: scalar multiplication (broadcast + mul) -/
def smul (s : Expr α) (v : VecExpr α n) : VecExpr α n :=
  VecExpr.zipWith (VecExpr.broadcast s) v

/-- Count the number of constructors (for cost estimation) -/
def size : VecExpr α n → Nat
  | lit _           => 1
  | var _           => 1
  | map v           => 1 + size v
  | zipWith v1 v2   => 1 + size v1 + size v2
  | splitLo v       => 1 + size v
  | splitHi v       => 1 + size v
  | concat v1 v2    => 1 + size v1 + size v2
  | interleave v1 v2 => 1 + size v1 + size v2
  | stride _ v      => 1 + size v
  | bitRev v        => 1 + size v
  | broadcast _     => 1

end VecExpr

/-! ## Environment for Vector Evaluation

For denotational semantics, we need an environment that maps
vector variables to actual vectors.
-/

/-- Environment mapping vector variable IDs to vectors.
    Uses a function type for flexibility. -/
def VecEnv (α : Type) (n : Nat) := VecVarId → Vec α n

/-- Empty environment (all variables map to zero vector). -/
def VecEnv.empty [OfNat α 0] : VecEnv α n :=
  fun _ => Vec.replicate n (0 : α)

/-! ## Theorems about Vec operations -/

theorem Vec.map_map (f : β → γ) (g : α → β) (v : Vec α n) :
    Vec.map f (Vec.map g v) = Vec.map (f ∘ g) v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [Vec.map, ih]

theorem Vec.map_id (v : Vec α n) : Vec.map id v = v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [Vec.map, ih]

end AmoLean.Vector
