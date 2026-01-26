/-
  AMO-Lean: Matrix Module
  Phase 5.2 - Matrix expressions with Kronecker products

  This module implements matrix expressions using Kronecker products
  for compact FFT representation, following the SPIRAL approach
  (Franchetti et al.).

  Key design decisions:
  1. MatExpr α m n: Matrix m×n as transformation (not stored explicitly)
  2. Kronecker products (⊗) as first-class constructor
  3. Symbolic DFT, NTT, Twiddle factors (not expanded)
  4. Permutations as separate type for algebraic manipulation

  The key insight from SPIRAL:
    DFT_{mn} = (DFT_m ⊗ I_n) · T^{mn}_n · (I_m ⊗ DFT_n) · L^{mn}_m

  This represents an O(N log N) FFT using O(log N) AST nodes.

  References:
  - docs/optimizaciones prefase5/efficient simd extensions.pdf
  - docs/optimizaciones prefase5/high performance simd.pdf
-/

import AmoLean.Basic
import AmoLean.Vector.Basic

namespace AmoLean.Matrix

open AmoLean (Expr VarId)
open AmoLean.Vector (Vec VecExpr)

/-! ## Perm n: Symbolic Permutations

Permutations are represented symbolically to enable algebraic
manipulation and optimization. Key permutations for FFT:

- Identity: I_n
- Stride (L^{mn}_n): accesses elements with stride n
- Bit-reversal: reverses the bits of indices
- Swap: exchanges two elements

These can be composed and have algebraic identities:
- L^{mn}_n · L^{mn}_m = I_{mn}
- (P ⊗ Q) · (R ⊗ S) = (P·R) ⊗ (Q·S) (when dimensions match)
-/

/-- Symbolic permutation of n elements.
    Stored symbolically, not as explicit mapping. -/
inductive Perm : Nat → Type where
  /-- Identity permutation -/
  | identity : Perm n

  /-- Stride permutation L^{mn}_n
      Maps index i to (i mod m) * n + (i div m)
      This reorders a row-major m×n matrix to column-major -/
  | stride : (m n : Nat) → Perm (m * n)

  /-- Bit-reversal permutation (for radix-2 FFT)
      Maps index i to bit-reverse of i in k bits -/
  | bitRev : (k : Nat) → Perm (2^k)

  /-- Swap: exchange elements 0 and 1 -/
  | swap : Perm 2

  /-- Composition P · Q (apply Q first, then P) -/
  | compose : Perm n → Perm n → Perm n

  /-- Inverse permutation -/
  | inverse : Perm n → Perm n

  /-- Tensor product P ⊗ Q
      Applies P to "outer" indices and Q to "inner" indices -/
  | tensor : Perm m → Perm n → Perm (m * n)

  deriving Repr

namespace Perm

/-- Notation for composition -/
instance : HMul (Perm n) (Perm n) (Perm n) where
  hMul := Perm.compose

/-- Check if permutation is identity (syntactic check) -/
def isIdentity : Perm n → Bool
  | identity => true
  | compose p q => isIdentity p && isIdentity q
  | _ => false

/-- Simplify permutation algebraically.
    Note: Full simplification requires more sophisticated pattern matching
    on dependent types; this is a placeholder for future work. -/
def simplify : Perm n → Perm n
  | identity => identity
  | p => p  -- Placeholder: more rules to be added

end Perm

/-! ## ElemOp: Element-wise Operations

Non-linear operations applied element-wise to matrices.
This is the key extension for Poseidon2 support.

The S-box (x^5) is implemented as `ElemOp.pow 5`.

IMPORTANT: elemwise acts as an "opaque barrier" - linear algebra
E-graph rules must NOT penetrate it. This prevents:
- mul(elemwise(...), ...) from being rewritten
- elemwise being absorbed into Kronecker structure
-/

/-- Element-wise operation type for non-linear functions.
    Used primarily for Poseidon2 S-box (x^α). -/
inductive ElemOp where
  /-- Power operation: x → x^n (S-box for α=5) -/
  | pow : Nat → ElemOp
  /-- Named custom operation (for extensibility) -/
  | custom : String → ElemOp
  deriving Repr, BEq, Hashable

namespace ElemOp

/-- Check if this is the identity operation (pow 1) -/
def isIdentity : ElemOp → Bool
  | pow 1 => true
  | _ => false

/-- S-box for Poseidon2: x^5 -/
def sbox5 : ElemOp := pow 5

/-- S-box for Goldilocks Poseidon2: x^7 -/
def sbox7 : ElemOp := pow 7

end ElemOp

/-! ## MatExpr α m n: Matrix Expression AST

Represents an m×n matrix as a linear transformation.
Matrices are NOT stored explicitly - they are symbolic expressions
that will be lowered to actual operations during code generation.

The Kronecker product (⊗) is the key abstraction:
- (A ⊗ B) has dimensions (m₁·m₂) × (n₁·n₂)
- It represents "applying A to outer structure, B to inner"
- For FFT, this allows O(log N) nodes instead of O(N)
-/

/-- Matrix expression representing an m×n linear transformation.

    Constructors are designed for FFT/NTT representation:
    - Symbolic transforms (DFT, NTT) avoid expansion
    - Kronecker products encode recursive structure
    - Permutations handle data movement -/
inductive MatExpr (α : Type) : Nat → Nat → Type where
  /-- Identity matrix I_n -/
  | identity (n : Nat) : MatExpr α n n

  /-- Zero matrix -/
  | zero (m n : Nat) : MatExpr α m n

  /-- Diagonal matrix from vector -/
  | diag : VecExpr α n → MatExpr α n n

  /-- Scalar as 1×1 matrix -/
  | scalar : Expr α → MatExpr α 1 1

  /-- Symbolic DFT matrix of size n
      DFT_n[i,j] = ω^{ij} where ω = e^{-2πi/n} -/
  | dft (n : Nat) : MatExpr α n n

  /-- Symbolic NTT matrix in Z_p
      NTT uses primitive n-th root of unity in Z_p -/
  | ntt (n p : Nat) : MatExpr α n n

  /-- Twiddle factor matrix T^n_k
      Diagonal matrix with entries ω^{0}, ω^{1}, ..., ω^{n-1}
      where ω is appropriate root of unity -/
  | twiddle (n k : Nat) : MatExpr α n n

  /-- Permutation matrix from symbolic permutation -/
  | perm : Perm n → MatExpr α n n

  /-- Kronecker product A ⊗ B
      Result has dimensions (m₁·m₂) × (n₁·n₂) -/
  | kron : MatExpr α m₁ n₁ → MatExpr α m₂ n₂ → MatExpr α (m₁ * m₂) (n₁ * n₂)

  /-- Matrix composition A · B (apply B first, then A) -/
  | compose : MatExpr α m k → MatExpr α k n → MatExpr α m n

  /-- Matrix addition -/
  | add : MatExpr α m n → MatExpr α m n → MatExpr α m n

  /-- Scalar multiplication c · A -/
  | smul : Expr α → MatExpr α m n → MatExpr α m n

  /-- Transpose -/
  | transpose : MatExpr α m n → MatExpr α n m

  /-- Conjugate transpose (for complex) -/
  | conjTranspose : MatExpr α m n → MatExpr α n m

  /-- Element-wise non-linear operation (OPAQUE BARRIER).
      Applies op to each element independently.
      E-graph rules must NOT penetrate this constructor.
      Used for Poseidon2 full rounds: elemwise (pow 5) state -/
  | elemwise : ElemOp → MatExpr α m n → MatExpr α m n

  /-- Partial element-wise operation (for Poseidon2 partial rounds).
      Applies op only to the element at the specified index.
      Used for partial rounds: partialElemwise 0 (pow 5) state
      Only modifies state[idx], leaves other elements unchanged. -/
  | partialElemwise : (idx : Nat) → ElemOp → MatExpr α m n → MatExpr α m n

  /-- Symbolic MDS matrix application (Poseidon2 Phase 3).
      Represents MDS × state as an OPAQUE operation.
      The matrix is referenced by name, NOT embedded as literals.
      CodeGen translates to a loop or function call.
      @param mdsName: Identifier for the MDS matrix (e.g., "MDS_3")
      @param stateSize: Size of the state vector (t) -/
  | mdsApply : (mdsName : String) → (stateSize : Nat) → MatExpr α t 1 → MatExpr α t 1

  /-- Add round constants (Poseidon2 Phase 3).
      Represents state + RC[round] as a single operation.
      Round constants are referenced by index, NOT embedded.
      @param round: Round index for constant lookup
      @param stateSize: Size of the state vector (t) -/
  | addRoundConst : (round : Nat) → (stateSize : Nat) → MatExpr α t 1 → MatExpr α t 1

namespace MatExpr

/-! ### Smart Constructors -/

/-- Identity that returns existing matrix if it's already identity -/
def smartIdentity (n : Nat) : MatExpr α n n := identity n

/-- Stride permutation as MatExpr -/
def stridePerm (m n : Nat) : MatExpr α (m * n) (m * n) :=
  perm (Perm.stride m n)

/-- Bit-reversal permutation as MatExpr -/
def bitRevPerm (k : Nat) : MatExpr α (2^k) (2^k) :=
  perm (Perm.bitRev k)

/-! ### FFT Building Blocks -/

/-- DFT₂ (butterfly) matrix:
    [[1,  1],
     [1, -1]] -/
def dft2 : MatExpr Int 2 2 := dft 2

/-- Cooley-Tukey FFT decomposition:
    DFT_{mn} = (DFT_m ⊗ I_n) · T^{mn}_n · (I_m ⊗ DFT_n) · L^{mn}_m

    This is THE key formula. It decomposes an FFT of size mn into:
    1. Stride permutation L^{mn}_m (rearrange data)
    2. n parallel DFTs of size m: (I_m ⊗ DFT_n)
    3. Multiply by twiddle factors: T^{mn}_n
    4. m parallel DFTs of size n: (DFT_m ⊗ I_n) -/
def fftCooleyTukey (m n : Nat) : MatExpr α (m * n) (m * n) :=
  compose
    (kron (dft m) (identity n))                    -- (DFT_m ⊗ I_n)
    (compose
      (twiddle (m * n) n)                          -- T^{mn}_n
      (compose
        (kron (identity m) (dft n))                -- (I_m ⊗ DFT_n)
        (perm (Perm.stride m n))))                 -- L^{mn}_m

/-- Radix-2 FFT: DFT_{2n} using Cooley-Tukey with m=2 -/
def fftRadix2 (n : Nat) : MatExpr α (2 * n) (2 * n) :=
  fftCooleyTukey 2 n

/-- Radix-4 FFT: More efficient for some architectures -/
def fftRadix4 (n : Nat) : MatExpr α (4 * n) (4 * n) :=
  fftCooleyTukey 4 n

/-- Recursive FFT for power-of-2 sizes -/
def fftPow2 : (k : Nat) → MatExpr α (2^k) (2^k)
  | 0 => identity 1
  | 1 => dft 2
  | k + 2 =>
    -- DFT_{2^{k+2}} = DFT_{2 · 2^{k+1}} via Cooley-Tukey
    have h : 2^(k + 2) = 2 * 2^(k + 1) := by
      simp [Nat.pow_succ, Nat.mul_comm]
    h ▸ fftRadix2 (2^(k+1))

/-! ### Size and Cost Estimation -/

/-- Count the number of AST nodes (for complexity analysis) -/
def nodeCount : MatExpr α m n → Nat
  | identity _     => 1
  | zero _ _       => 1
  | diag _         => 1
  | scalar _       => 1
  | dft _          => 1
  | ntt _ _        => 1
  | twiddle _ _    => 1
  | perm _         => 1
  | kron A B       => 1 + nodeCount A + nodeCount B
  | compose A B    => 1 + nodeCount A + nodeCount B
  | add A B        => 1 + nodeCount A + nodeCount B
  | smul _ A       => 1 + nodeCount A
  | transpose A    => 1 + nodeCount A
  | conjTranspose A => 1 + nodeCount A
  | elemwise _ A   => 1 + nodeCount A
  | partialElemwise _ _ A => 1 + nodeCount A
  | mdsApply _ _ A => 1 + nodeCount A
  | addRoundConst _ _ A => 1 + nodeCount A

/-- Estimate operation count after expansion (for cost model).
    This gives an upper bound on the number of scalar operations. -/
def opCountEstimate : MatExpr α m n → Nat
  | identity _     => 0           -- No ops needed
  | zero _ _       => 0
  | diag _         => 0
  | scalar _       => 0
  | dft n          => n * n       -- Naive DFT cost (actual FFT is n log n)
  | ntt n _        => n * n
  | twiddle n _    => n           -- n multiplications
  | perm _         => 0           -- Permutations are data movement, not ops
  | kron A B       => opCountEstimate A + opCountEstimate B  -- Rough estimate
  | compose A B    => opCountEstimate A + opCountEstimate B
  | add A B        => opCountEstimate A + opCountEstimate B + m * n
  | smul _ A       => opCountEstimate A + m * n
  | transpose _    => 0
  | conjTranspose _ => 0
  | elemwise op A  =>
    let baseCost := opCountEstimate A
    match op with
    | ElemOp.pow 5 => baseCost + m * n * 3  -- S-box x^5: 3 muls (square chain)
    | ElemOp.pow k => baseCost + m * n * k  -- General power: k muls (naive)
    | ElemOp.custom _ => baseCost + m * n   -- Custom: assume 1 op per element
  | partialElemwise _ op A =>
    let baseCost := opCountEstimate A
    match op with
    | ElemOp.pow 5 => baseCost + 3  -- Single element S-box x^5: 3 muls
    | ElemOp.pow k => baseCost + k  -- General power: k muls (naive)
    | ElemOp.custom _ => baseCost + 1   -- Custom: assume 1 op
  | mdsApply _ t A =>
    let baseCost := opCountEstimate A
    baseCost + t * t  -- Dense matrix: t² multiplications
  | addRoundConst _ t A =>
    let baseCost := opCountEstimate A
    baseCost + t  -- t additions

/-- Full round S-box: apply x^α to all state elements -/
def fullRoundSbox (α : Nat) (state : MatExpr β m n) : MatExpr β m n :=
  MatExpr.elemwise (ElemOp.pow α) state

/-- Partial round S-box: apply x^α only to state[0] -/
def partialRoundSbox (α : Nat) (state : MatExpr β m n) : MatExpr β m n :=
  MatExpr.partialElemwise 0 (ElemOp.pow α) state

end MatExpr

/-! ## Cost Model for Vectorial Operations -/

/-- Cost model for vectorized operations (used by E-graph extraction) -/
structure VectorCostModel where
  /-- SIMD vector width (4 for AVX, 8 for AVX-512) -/
  simdWidth : Nat := 4

  /-- Cost of SIMD add/sub (1 cycle typically) -/
  addCost : Nat := 1

  /-- Cost of SIMD multiply (1 cycle with pipelining) -/
  mulCost : Nat := 1

  /-- Cost of FMA (same as mul with modern CPUs) -/
  fmaCost : Nat := 1

  /-- Cost of shuffle/permute within registers -/
  shuffleCost : Nat := 2

  /-- Cost of cross-lane shuffle (AVX) -/
  crossLaneCost : Nat := 3

  /-- Cost of memory load/store -/
  memoryCost : Nat := 10

  /-- Symbolic Kronecker has zero cost (not expanded) -/
  kronSymbolicCost : Nat := 0

  /-- Symbolic DFT has zero cost (not expanded) -/
  dftSymbolicCost : Nat := 0

  /-- Penalty for scalar fallback (discourages expansion) -/
  scalarPenalty : Nat := 1000

  deriving Repr

/-- Default cost model for AVX2 -/
def defaultCostModel : VectorCostModel := {}

/-- Estimate cost of MatExpr using cost model -/
def estimateCost (cm : VectorCostModel) : MatExpr α m n → Nat
  | MatExpr.identity _ => 0
  | MatExpr.zero _ _ => 0
  | MatExpr.dft _ => cm.dftSymbolicCost
  | MatExpr.ntt _ _ => cm.dftSymbolicCost
  | MatExpr.twiddle n _ => (n / cm.simdWidth) * cm.mulCost
  | MatExpr.perm _ => cm.shuffleCost
  | MatExpr.kron A B => cm.kronSymbolicCost + estimateCost cm A + estimateCost cm B
  | MatExpr.compose A B => estimateCost cm A + estimateCost cm B
  | MatExpr.add A B => estimateCost cm A + estimateCost cm B + m * cm.addCost / cm.simdWidth
  | MatExpr.smul _ A => estimateCost cm A + m * n * cm.mulCost / cm.simdWidth
  | MatExpr.elemwise op A =>
    let baseCost := estimateCost cm A
    -- S-box x^5 uses 3 multiplications per element (square chain)
    let sboxCost := match op with
      | ElemOp.pow 5 => (m * n * 3 * cm.mulCost) / cm.simdWidth
      | ElemOp.pow k => (m * n * k * cm.mulCost) / cm.simdWidth
      | ElemOp.custom _ => (m * n * cm.mulCost) / cm.simdWidth
    baseCost + sboxCost
  | MatExpr.partialElemwise _ op A =>
    let baseCost := estimateCost cm A
    -- Partial S-box: only 1 element, so no SIMD benefit
    let sboxCost := match op with
      | ElemOp.pow 5 => 3 * cm.mulCost  -- 3 muls for x^5
      | ElemOp.pow k => k * cm.mulCost  -- k muls for x^k
      | ElemOp.custom _ => cm.mulCost   -- 1 op for custom
    baseCost + sboxCost
  | MatExpr.mdsApply _ t A =>
    let baseCost := estimateCost cm A
    -- MDS: t² multiplications, potentially SIMD-able for small t
    baseCost + (t * t * cm.mulCost) / cm.simdWidth + (t * t * cm.addCost) / cm.simdWidth
  | MatExpr.addRoundConst _ t A =>
    let baseCost := estimateCost cm A
    -- RC addition: t additions
    baseCost + (t * cm.addCost) / cm.simdWidth
  | _ => 0

end AmoLean.Matrix
