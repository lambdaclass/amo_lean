/-
  AMO-Lean: Permutation Module
  Phase 5.3 - Complete permutation evaluation and algebraic properties

  This module implements the evaluation of symbolic permutations
  and their algebraic properties. Key permutations for FFT:

  - Stride permutation L^{mn}_n: fundamental for Cooley-Tukey FFT
  - Bit-reversal: used in radix-2 FFT output ordering
  - Tensor product of permutations: for parallel operations

  The stride permutation L^{mn}_n maps index i to:
    L(i) = (i mod m) * n + (i div m)

  This corresponds to transposing an m×n matrix stored in row-major order.

  References:
  - SPIRAL: "Efficient SIMD Vectorization for Hashing in OpenSSL"
  - Van Loan: "Computational Frameworks for the Fast Fourier Transform"
-/

import AmoLean.Matrix.Basic

namespace AmoLean.Matrix

open AmoLean.Vector (Vec)

/-! ## Bit Operations for Bit-Reversal -/

/-- Reverse the bits of a natural number, given the number of bits. -/
def bitReverse (numBits : Nat) (x : Nat) : Nat :=
  go numBits x 0
where
  go : Nat → Nat → Nat → Nat
    | 0,     _,  acc => acc
    | b + 1, x', acc => go b (x' / 2) (acc * 2 + x' % 2)

/-- Helper: go preserves a bound that grows with the number of bits processed.
    If acc < 2^n, then after processing b bits, result < 2^(n+b). -/
private theorem go_bound (b x acc : Nat) (n : Nat) (hacc : acc < 2^n) :
    bitReverse.go b x acc < 2^(n + b) := by
  induction b generalizing x acc n with
  | zero =>
    simp only [bitReverse.go, Nat.add_zero]
    exact hacc
  | succ b ih =>
    simp only [bitReverse.go]
    -- Need: acc * 2 + x % 2 < 2^(n + 1)
    have h_mod : x % 2 < 2 := Nat.mod_lt x (by omega)
    have h_acc_bound : acc * 2 < 2^(n + 1) := by
      have h1 : acc * 2 < 2^n * 2 := Nat.mul_lt_mul_of_pos_right hacc (by omega)
      have h2 : 2^n * 2 = 2^(n + 1) := by rw [Nat.pow_succ]
      omega
    have h_new : acc * 2 + x % 2 < 2^(n + 1) := by omega
    -- Apply IH with n+1: result < 2^((n+1)+b) = 2^(n+b+1)
    have := ih (x / 2) (acc * 2 + x % 2) (n + 1) h_new
    -- (n+1)+b = n+(b+1)
    have h_eq : (n + 1) + b = n + (b + 1) := by omega
    rw [h_eq] at this
    exact this

/-- Bit reverse preserves bounds. -/
theorem bitReverse_lt (k : Nat) (x : Nat) (_h : x < 2^k) :
    bitReverse k x < 2^k := by
  simp only [bitReverse]
  have := go_bound k x 0 0 (by simp)
  simp only [Nat.zero_add] at this
  exact this

/-- Helper: go extracts bits in reverse order.
    go b x acc = acc * 2^b + (bits of x reversed with acc=0) -/
private theorem go_spec (b x acc : Nat) :
    bitReverse.go b x acc = acc * 2^b + bitReverse.go b x 0 := by
  induction b generalizing x acc with
  | zero =>
    simp only [bitReverse.go, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  | succ b ih =>
    simp only [bitReverse.go, Nat.zero_mul, Nat.zero_add]
    -- LHS: go b (x/2) (acc*2 + x%2)
    -- RHS: acc * 2^(b+1) + go b (x/2) (x%2)
    rw [ih (x / 2) (acc * 2 + x % 2)]
    rw [ih (x / 2) (x % 2)]
    -- Need: (acc * 2 + x % 2) * 2^b + go = acc * 2^(b+1) + (x % 2) * 2^b + go
    -- Expand 2^(b+1) = 2 * 2^b
    rw [Nat.pow_succ]
    -- (acc * 2 + x % 2) * 2^b = acc * 2 * 2^b + (x % 2) * 2^b
    rw [Nat.add_mul]
    rw [Nat.mul_comm (2^b) 2]
    rw [Nat.mul_assoc acc 2 (2^b)]
    -- Now need: acc * (2 * 2^b) + x % 2 * 2^b + go = acc * (2 * 2^b) + (x % 2 * 2^b + go)
    rw [Nat.add_assoc]

/-- Unfolding lemma: go (b+1) x 0 = (x%2) * 2^b + go b (x/2) 0.
    This is derivable from go_spec. -/
private theorem go_succ_unfold (b x : Nat) :
    bitReverse.go (b + 1) x 0 = (x % 2) * 2^b + bitReverse.go b (x / 2) 0 := by
  simp only [bitReverse.go, Nat.zero_mul, Nat.zero_add]
  exact go_spec b (x / 2) (x % 2)

/-- Helper: x / 2 < 2^b when x < 2^(b+1). -/
private theorem div2_lt_pow (x b : Nat) (hx : x < 2^(b + 1)) : x / 2 < 2^b := by
  rw [Nat.pow_succ, Nat.mul_comm] at hx
  exact Nat.div_lt_of_lt_mul hx

/-- Key identity: (x % 2^(b+1)) / 2 = (x / 2) % 2^b -/
private theorem div2_mod_eq (x b : Nat) : (x % 2^(b + 1)) / 2 = (x / 2) % 2^b := by
  rw [Nat.pow_succ]
  -- Now: (x % (2^b * 2)) / 2 = (x / 2) % 2^b
  -- By Nat.mod_mul_right_div_self: m % (n * k) / n = m / n % k
  -- Need: x % (2 * 2^b) / 2 = x / 2 % 2^b
  rw [Nat.mul_comm]
  exact Nat.mod_mul_right_div_self x 2 (2^b)

/-- LSB of reversed bits equals MSB of original (for go (b+1) x 0).
    (go (b+1) x 0) % 2 = x / 2^b when x < 2^(b+1) -/
private theorem go_lsb (b x : Nat) (hx : x < 2^(b + 1)) :
    bitReverse.go (b + 1) x 0 % 2 = x / 2^b := by
  induction b generalizing x with
  | zero =>
    -- go 1 x 0 = go 0 (x/2) (0*2 + x%2) = go 0 (x/2) (x%2) = x%2 (base case of go)
    -- Goal: (x%2) % 2 = x / 2^0 = x / 1 = x
    have h1 : bitReverse.go 1 x 0 = x % 2 := by
      unfold bitReverse.go bitReverse.go
      simp only [Nat.zero_mul, Nat.zero_add]
    rw [h1]
    -- Now: (x % 2) % 2 = x / 2^0 where x < 2^1
    omega
  | succ b ih =>
    -- go (b+2) x 0 = (x%2) * 2^(b+1) + go (b+1) (x/2) 0
    rw [go_succ_unfold]
    -- Need: ((x%2) * 2^(b+1) + go (b+1) (x/2) 0) % 2 = x / 2^(b+1)
    -- Since 2^(b+1) is even, (x%2) * 2^(b+1) is even
    -- So the result mod 2 equals (go (b+1) (x/2) 0) % 2
    have h_pow_even : 2 ∣ 2^(b + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.dvd_mul_right 2 (2^b)
    have h_term_even : 2 ∣ (x % 2) * 2^(b + 1) :=
      Nat.dvd_trans h_pow_even (Nat.dvd_mul_left (2^(b + 1)) (x % 2))
    rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp h_term_even, Nat.zero_add, Nat.mod_mod]
    -- Now: (go (b+1) (x/2) 0) % 2 = x / 2^(b+1)
    -- By IH: (go (b+1) (x/2) 0) % 2 = (x/2) / 2^b
    have hx' : x / 2 < 2^(b + 1) := div2_lt_pow x (b + 1) (by rw [Nat.add_assoc]; exact hx)
    rw [ih (x / 2) hx']
    -- Need: (x/2) / 2^b = x / 2^(b+1)
    rw [Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]

/-- Upper bits of reversed result equal reversal of lower bits of original.
    (go (b+1) x 0) / 2 = go b (x % 2^b) 0 when x < 2^(b+1) -/
private theorem go_msb (b x : Nat) (hx : x < 2^(b + 1)) :
    bitReverse.go (b + 1) x 0 / 2 = bitReverse.go b (x % 2^b) 0 := by
  induction b generalizing x with
  | zero =>
    -- go 1 x 0 = x % 2, go 0 y 0 = 0
    have h1 : bitReverse.go 1 x 0 = x % 2 := by
      unfold bitReverse.go bitReverse.go
      simp only [Nat.zero_mul, Nat.zero_add]
    have h2 : bitReverse.go 0 (x % 2^0) 0 = 0 := by
      unfold bitReverse.go
      rfl
    rw [h1, h2]
    -- Goal: (x % 2) / 2 = 0 where x < 2^1
    omega
  | succ b ih =>
    -- go (b+2) x 0 = (x%2) * 2^(b+1) + go (b+1) (x/2) 0
    rw [go_succ_unfold]
    -- Need: ((x%2) * 2^(b+1) + go (b+1) (x/2) 0) / 2 = go (b+1) (x % 2^(b+1)) 0
    -- First, compute the division
    have h_go_bound : bitReverse.go (b + 1) (x / 2) 0 < 2^(b + 1) := by
      have := go_bound (b + 1) (x / 2) 0 0 (by simp)
      simp only [Nat.zero_add] at this
      exact this
    -- (a * 2^(b+1) + r) / 2 = a * 2^b + r / 2 for r < 2^(b+1)
    have h_div : ((x % 2) * 2^(b + 1) + bitReverse.go (b + 1) (x / 2) 0) / 2 =
                 (x % 2) * 2^b + bitReverse.go (b + 1) (x / 2) 0 / 2 := by
      -- 2^(b+1) = 2 * 2^b
      have h_pow : 2^(b + 1) = 2 * 2^b := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h_pow]
      -- Goal: ((x % 2) * (2 * 2^b) + go) / 2 = (x % 2) * 2^b + go / 2
      -- Rearrange: (x % 2) * (2 * 2^b) = 2 * ((x % 2) * 2^b)
      have h_rearr : (x % 2) * (2 * 2^b) = 2 * ((x % 2) * 2^b) := by
        rw [Nat.mul_comm (x % 2) (2 * 2^b), Nat.mul_assoc, Nat.mul_comm (2^b) (x % 2)]
      rw [h_rearr]
      -- Now: (2 * ((x % 2) * 2^b) + go) / 2 = (x % 2) * 2^b + go / 2
      exact Nat.mul_add_div (by decide : 2 > 0) ((x % 2) * 2^b) (bitReverse.go (b + 1) (x / 2) 0)
    rw [h_div]
    -- By IH: go (b+1) (x/2) 0 / 2 = go b ((x/2) % 2^b) 0
    have hx'' : x / 2 < 2^(b + 1) := div2_lt_pow x (b + 1) (by rw [Nat.add_assoc]; exact hx)
    rw [ih (x / 2) hx'']
    -- Now need: (x%2) * 2^b + go b ((x/2) % 2^b) 0 = go (b+1) (x % 2^(b+1)) 0
    -- Use go_succ_unfold in reverse: go (b+1) y 0 = (y%2) * 2^b + go b (y/2) 0
    rw [go_succ_unfold]
    -- Need: (x%2) * 2^b + go b ((x/2) % 2^b) 0 = (x % 2^(b+1) % 2) * 2^b + go b (x % 2^(b+1) / 2) 0
    -- Key facts:
    -- 1. x % 2^(b+1) % 2 = x % 2 (since 2 | 2^(b+1))
    -- 2. x % 2^(b+1) / 2 = (x / 2) % 2^b (div2_mod_eq)
    have h1 : x % 2^(b + 1) % 2 = x % 2 := by
      have hdvd : 2 ∣ 2^(b + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
        exact Nat.dvd_mul_right 2 (2^b)
      exact Nat.mod_mod_of_dvd x hdvd
    have h2 : x % 2^(b + 1) / 2 = (x / 2) % 2^b := div2_mod_eq x b
    rw [h1, h2]

/-- go applied twice reverses bits back (involution property).

    Strategy for formal proof (from QA and Lean Expert consultation):
    1. Use go_succ_unfold to expand both inner and outer go applications
    2. Key insight: go reverses bits, so (go b x 0) has bit i = bit (b-1-i) of x
    3. For succ case, show:
       - (go (b+1) x 0) % 2 = x / 2^b (MSB of x becomes LSB of result)
       - (go (b+1) x 0) / 2 = go b (x % 2^b) 0 (remaining bits are reversal of lower bits)
    4. Then: go (b+1) y 0 where y = go (b+1) x 0 gives:
       (y%2) * 2^b + go b (y/2) 0 = (x/2^b) * 2^b + go b (go b (x%2^b) 0) 0
                                  = (x/2^b) * 2^b + (x%2^b)  [by IH]
                                  = x  [by Nat.div_add_mod']

    The proof is computationally verified via #eval bitRevIndices.
    Full formal proof deferred due to complexity of bit-level reasoning. -/
private theorem go_involution (b x : Nat) (hx : x < 2^b) :
    bitReverse.go b (bitReverse.go b x 0) 0 = x := by
  induction b generalizing x with
  | zero =>
    -- x < 2^0 = 1, so x = 0
    -- go 0 0 0 = 0 by definition
    unfold bitReverse.go
    omega
  | succ b ih =>
    -- go (b+1) (go (b+1) x 0) 0 = (y%2) * 2^b + go b (y/2) 0 where y = go (b+1) x 0
    rw [go_succ_unfold]
    -- By go_lsb: (go (b+1) x 0) % 2 = x / 2^b
    have h_lsb : (bitReverse.go (b + 1) x 0) % 2 = x / 2^b := go_lsb b x hx
    -- By go_msb: (go (b+1) x 0) / 2 = go b (x % 2^b) 0
    have h_msb : (bitReverse.go (b + 1) x 0) / 2 = bitReverse.go b (x % 2^b) 0 := go_msb b x hx
    rw [h_lsb, h_msb]
    -- Now: (x / 2^b) * 2^b + go b (go b (x % 2^b) 0) 0 = x
    -- By IH: go b (go b (x % 2^b) 0) 0 = x % 2^b
    have h_mod_bound : x % 2^b < 2^b := Nat.mod_lt x (Nat.two_pow_pos b)
    rw [ih (x % 2^b) h_mod_bound]
    -- Now: (x / 2^b) * 2^b + x % 2^b = x
    rw [Nat.mul_comm]
    exact Nat.div_add_mod x (2^b)

/-- Bit reverse is an involution (applying twice gives identity). -/
theorem bitReverse_involution (k : Nat) (x : Nat) (h : x < 2^k) :
    bitReverse k (bitReverse k x) = x := by
  simp only [bitReverse]
  exact go_involution k x h

/-! ## Stride Permutation Computation -/

/-- Compute the stride permutation L^{mn}_n applied to index i.
    L(i) = (i mod m) * n + (i div m)
    This maps row-major to column-major indexing of an m×n matrix. -/
def strideIndex (m n : Nat) (i : Nat) : Nat :=
  (i % m) * n + (i / m)

/-- The inverse stride: L^{mn}_m applied to index i.
    This is the inverse of strideIndex m n. -/
def strideIndexInv (m n : Nat) (i : Nat) : Nat :=
  (i % n) * m + (i / n)

/-- Stride permutation is its own inverse when swapping m and n. -/
theorem stride_inverse_eq (m n : Nat) (i : Nat) (h : i < m * n) :
    strideIndex n m (strideIndex m n i) = i := by
  simp only [strideIndex]
  -- strideIndex m n i = (i % m) * n + (i / m)
  -- strideIndex n m (above) = ((i % m) * n + (i / m)) % n * m + ((i % m) * n + (i / m)) / n
  have h_n_pos : 0 < n := by
    cases n with
    | zero => simp at h
    | succ n' => exact Nat.succ_pos n'
  have h_m_pos : 0 < m := by
    cases m with
    | zero => simp at h
    | succ m' => exact Nat.succ_pos m'
  have h_mod_bound : i % m < m := Nat.mod_lt i h_m_pos
  have h_div_bound : i / m < n := Nat.div_lt_of_lt_mul h
  -- Simplify the mod part: ((i % m) * n + (i / m)) % n = i / m
  have h_mod_eq : ((i % m) * n + i / m) % n = i / m := by
    -- (a * n + b) % n = b % n, then b % n = b when b < n
    have h1 : (i / m + (i % m) * n) % n = (i / m) % n := Nat.add_mul_mod_self_right (i / m) (i % m) n
    rw [Nat.add_comm] at h1
    rw [h1]
    exact Nat.mod_eq_of_lt h_div_bound
  -- Simplify the div part: ((i % m) * n + (i / m)) / n = i % m
  have h_div_eq : ((i % m) * n + i / m) / n = i % m := by
    -- Rewrite (i % m) * n as n * (i % m) to use mul_add_div
    have h1 : n * (i % m) + i / m = (i % m) * n + i / m := by rw [Nat.mul_comm]
    rw [← h1]
    rw [Nat.mul_add_div h_n_pos]
    rw [Nat.div_eq_of_lt h_div_bound]
    simp only [Nat.add_zero]
  rw [h_mod_eq, h_div_eq]
  -- Now we have: (i / m) * m + (i % m) = i
  -- Use: m % k + k * (m / k) = m (from Nat.mod_add_div)
  have h_div_mod : i % m + m * (i / m) = i := Nat.mod_add_div i m
  -- Rewrite to match: (i / m) * m + (i % m) = (i % m) + m * (i / m)
  rw [Nat.add_comm, Nat.mul_comm]
  exact h_div_mod

/-- Stride index stays within bounds. -/
theorem strideIndex_lt (m n : Nat) (i : Nat) (h : i < m * n) :
    strideIndex m n i < m * n := by
  simp only [strideIndex]
  -- (i % m) * n + (i / m) < m * n
  have h_n_pos : 0 < n := by
    cases n with
    | zero => simp at h
    | succ n' => exact Nat.succ_pos n'
  have h_m_pos : 0 < m := by
    cases m with
    | zero => simp at h
    | succ m' => exact Nat.succ_pos m'
  have h_mod_bound : i % m < m := Nat.mod_lt i h_m_pos
  have h_div_bound : i / m < n := Nat.div_lt_of_lt_mul h
  -- (i % m) * n ≤ (m - 1) * n < m * n - n + n = m * n
  -- i / m < n
  have h_eq : (i % m + 1) * n = (i % m) * n + n := by
    rw [Nat.add_mul, Nat.one_mul]
  calc (i % m) * n + i / m
      < (i % m) * n + n := by omega
    _ = (i % m + 1) * n := by rw [← h_eq]
    _ ≤ m * n := Nat.mul_le_mul_right n h_mod_bound

/-! ## Permutation Application -/

namespace Perm

/-- Apply inverse permutation to an index.
    Extracted as a separate function to avoid nested pattern matching in `applyIndex`,
    which would trigger a splitter generation failure in Lean 4's equation compiler
    for the indexed inductive `Perm n`. The nested patterns `inverse swap`,
    `inverse (stride m n)`, etc. create overlapping index obligations that the
    splitter cannot resolve (e.g., proving `stride m n ≠ swap` when `m * n = 2`
    through heterogeneous equality). -/
def applyInverseIndex : {k : Nat} → Perm k → Fin k → Fin k
  | _, identity, i => i
  | _, swap, ⟨0, _⟩ => ⟨1, by omega⟩
  | _, swap, ⟨1, _⟩ => ⟨0, by omega⟩
  | _, swap, ⟨i + 2, h⟩ => ⟨i + 2, h⟩
  | _, stride m n', i =>
    let newIdx := strideIndexInv m n' i.val
    ⟨newIdx % (m * n'), by
      apply Nat.mod_lt
      match m with
      | 0 => simp at i; exact absurd i.isLt (Nat.not_lt_zero i.val)
      | m' + 1 =>
        match n' with
        | 0 => simp at i; exact absurd i.isLt (Nat.not_lt_zero i.val)
        | n'' + 1 => exact Nat.mul_pos (Nat.succ_pos m') (Nat.succ_pos n'')⟩
  | _, bitRev k, i =>
    let newIdx := bitReverse k i.val
    ⟨newIdx % (2^k), Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  | _, _, i => i  -- Fallback for compose, tensor, inverse

/-- Apply a permutation to an index, returning the new index.
    This is the concrete evaluation of a symbolic permutation.

    The `inverse` case delegates to `applyInverseIndex` to avoid nested pattern
    matching that would prevent equation lemma generation. See `applyInverseIndex`
    for details on the splitter limitation. -/
def applyIndex : {k : Nat} → Perm k → Fin k → Fin k
  -- Identity: return input unchanged
  | _, identity, i => i

  -- Swap: exchange 0 ↔ 1
  | _, swap, ⟨0, _⟩ => ⟨1, by omega⟩
  | _, swap, ⟨1, _⟩ => ⟨0, by omega⟩
  | _, swap, ⟨i + 2, h⟩ => ⟨i + 2, h⟩

  -- Composition: apply right-to-left
  | _, compose p q, i => applyIndex p (applyIndex q i)

  -- Stride: L^{mn}_n maps i to (i mod m) * n + (i div m)
  | _, stride m n', i =>
    let newIdx := strideIndex m n' i.val
    ⟨newIdx % (m * n'), by
      apply Nat.mod_lt
      match m with
      | 0 => simp at i; exact absurd i.isLt (Nat.not_lt_zero i.val)
      | m' + 1 =>
        match n' with
        | 0 => simp at i; exact absurd i.isLt (Nat.not_lt_zero i.val)
        | n'' + 1 => exact Nat.mul_pos (Nat.succ_pos m') (Nat.succ_pos n'')⟩

  -- Bit reversal: reverse k bits
  | _, bitRev k, i =>
    let newIdx := bitReverse k i.val
    ⟨newIdx % (2^k), Nat.mod_lt _ (Nat.two_pow_pos k)⟩

  -- Inverse: delegate to separate function to avoid nested patterns
  | _, inverse p, i => applyInverseIndex p i

  -- Tensor: (P ⊗ Q)(i) where i = outer * n + inner
  -- Apply P to outer index, Q to inner index
  -- Result = P(outer) * n + Q(inner)
  | _, @tensor m_size n_size p q, i =>
    if h_n : n_size = 0 then
      ⟨0, by simp [h_n] at i; exact absurd i.isLt (Nat.not_lt_zero i.val)⟩
    else if h_m : m_size = 0 then
      ⟨0, by simp [h_m] at i; exact absurd i.isLt (Nat.not_lt_zero i.val)⟩
    else
      let outer := i.val / n_size
      let inner := i.val % n_size
      have h_outer_bound : outer < m_size := by
        have h_swap : m_size * n_size = n_size * m_size := Nat.mul_comm m_size n_size
        have h_i_lt : i.val < n_size * m_size := h_swap ▸ i.isLt
        exact Nat.div_lt_of_lt_mul h_i_lt
      have h_inner_bound : inner < n_size := Nat.mod_lt i.val (Nat.pos_of_ne_zero h_n)
      let new_outer := (applyIndex p ⟨outer, h_outer_bound⟩).val
      let new_inner := (applyIndex q ⟨inner, h_inner_bound⟩).val
      let result := new_outer * n_size + new_inner
      have h_result_bound : result < m_size * n_size := by
        have h_no : new_outer < m_size := (applyIndex p ⟨outer, h_outer_bound⟩).isLt
        have h_ni : new_inner < n_size := (applyIndex q ⟨inner, h_inner_bound⟩).isLt
        calc result = new_outer * n_size + new_inner := rfl
          _ < new_outer * n_size + n_size := Nat.add_lt_add_left h_ni _
          _ = (new_outer + 1) * n_size := by simp [Nat.add_mul, Nat.one_mul]
          _ ≤ m_size * n_size := Nat.mul_le_mul_right n_size h_no
      ⟨result, h_result_bound⟩

/-- Apply permutation to a vector, producing a permuted vector. -/
def applyVec (p : Perm n) (v : Vec α n) : Vec α n :=
  Vec.ofFn (fun i => Vec.get v (applyIndex p i))

/-- Apply inverse permutation to a vector. -/
def applyVecInv (p : Perm n) (v : Vec α n) : Vec α n :=
  applyVec (inverse p) v

end Perm

/-! ## Permutation Matrices as Explicit Arrays (for small n) -/

/-- Generate the permutation matrix as a list of target indices.
    permMatrix p = [p(0), p(1), ..., p(n-1)] -/
def Perm.toIndexList (p : Perm n) : List Nat :=
  (List.range n).attach.map (fun ⟨i, hi⟩ =>
    (Perm.applyIndex p ⟨i, List.mem_range.mp hi⟩).val)

/-! ## Algebraic Properties of Permutations -/

/-- Identity is the identity.
    Proven by rfl via signature pattern matching in applyIndex. -/
@[simp]
theorem Perm.apply_identity {n : Nat} (i : Fin n) :
    Perm.applyIndex Perm.identity i = i := rfl

/-- Composition applies right-to-left.
    Proven by rfl via signature pattern matching in applyIndex. -/
@[simp]
theorem Perm.apply_compose {n : Nat} (p q : Perm n) (i : Fin n) :
    Perm.applyIndex (Perm.compose p q) i =
    Perm.applyIndex p (Perm.applyIndex q i) := rfl

/-- Swap is a self-inverse (pointwise).
    Proven by case analysis on Fin 2. -/
theorem Perm.swap_self_inverse_pointwise (i : Fin 2) :
    Perm.applyIndex Perm.swap (Perm.applyIndex Perm.swap i) = i := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Stride and its transpose are inverses (pointwise). -/
theorem Perm.stride_transpose_inverse_pointwise (m n : Nat) (i : Fin (m * n)) :
    let _mn_eq : m * n = n * m := Nat.mul_comm m n
    strideIndex n m (strideIndex m n i.val) = i.val := by
  exact stride_inverse_eq m n i.val i.isLt

/-- applyIndex for bitRev applies bitReverse.
    Proven by rfl via signature pattern matching in applyIndex. -/
@[simp]
theorem Perm.applyIndex_bitRev (k : Nat) (i : Fin (2^k)) :
    Perm.applyIndex (Perm.bitRev k) i =
    ⟨bitReverse k i.val % (2^k), Nat.mod_lt _ (Nat.two_pow_pos k)⟩ := rfl

/-- Bit reversal is self-inverse (pointwise version).
    Note: The structural equality `compose (bitRev k) (bitRev k) = identity`
    is not provable because they are different constructors of an inductive type.
    This pointwise version captures the semantic equivalence. -/
theorem Perm.bitRev_self_inverse_pointwise (k : Nat) (i : Fin (2^k)) :
    Perm.applyIndex (Perm.compose (Perm.bitRev k) (Perm.bitRev k)) i =
    Perm.applyIndex Perm.identity i := by
  rw [Perm.apply_compose, Perm.apply_identity]
  -- applyIndex (bitRev k) (applyIndex (bitRev k) i) = i
  rw [Perm.applyIndex_bitRev, Perm.applyIndex_bitRev]
  -- Now: ⟨bitReverse k (bitReverse k i.val % 2^k) % 2^k, _⟩ = i
  ext
  simp only
  -- bitReverse k i.val < 2^k, so % 2^k is identity
  have h1 : bitReverse k i.val < 2^k := bitReverse_lt k i.val i.isLt
  rw [Nat.mod_eq_of_lt h1]
  -- Now: bitReverse k (bitReverse k i.val) % 2^k = i.val
  have h2 := bitReverse_involution k i.val i.isLt
  rw [h2]
  exact Nat.mod_eq_of_lt i.isLt

/-! ## Stride Permutation Properties (from SPIRAL) -/

/-
  STRIDE FACTORIZATION - COMPOSITIONAL FORM

  The SPIRAL paper establishes stride factorization via tensor products:

    L^{kmn}_{km} = (L^{kn}_k ⊗ I_m) ∘ (I_k ⊗ L^{mn}_m)

  This is NOT a closed-form pointwise formula, but a COMPOSITIONAL relationship.
  With tensor now implemented, this can be expressed as:

    stride (k*m) n ≈ compose (tensor (stride k n) identity) (tensor identity (stride m n))

  The original pointwise formula attempted was INCORRECT (verified by testing):

    strideIndex k (m*n) i ≠ strideIndex k n (strideIndex m n (i % (m*n))) + (i / (m*n)) * (k*n)

  The correct factorization theorem would require:
  1. Type-level arithmetic: (k*m)*n = k*(m*n) = (k*n)*m
  2. Careful handling of index decomposition via tensor semantics
  3. Proof that the compositional form matches pointwise behavior

  See Van Loan "Computational Frameworks for FFT" Chapter 2.
  Left as future work due to type-level arithmetic complexity.
-/

/-! ## Permutation Composition Helpers -/

namespace Perm

/-- Left composition with identity is identity (pointwise). -/
theorem compose_identity_left_pointwise (p : Perm n) (i : Fin n) :
    applyIndex (compose identity p) i = applyIndex p i := by
  rw [Perm.apply_compose, Perm.apply_identity]

/-- Right composition with identity is identity (pointwise). -/
theorem compose_identity_right_pointwise (p : Perm n) (i : Fin n) :
    applyIndex (compose p identity) i = applyIndex p i := by
  rw [Perm.apply_compose, Perm.apply_identity]

/-- Composition is associative (pointwise). -/
theorem compose_assoc_pointwise (p q r : Perm n) (i : Fin n) :
    applyIndex (compose (compose p q) r) i = applyIndex (compose p (compose q r)) i := by
  simp only [Perm.apply_compose]

/-- Inverse of identity is identity (pointwise).
    Proven by rfl via signature pattern matching in applyIndex. -/
@[simp]
theorem apply_inverse_identity {n : Nat} (i : Fin n) :
    applyIndex (inverse (identity : Perm n)) i = i := rfl

theorem inverse_identity_pointwise (i : Fin n) :
    applyIndex (inverse (identity : Perm n)) i = applyIndex identity i := by
  rw [apply_inverse_identity, Perm.apply_identity]

/-
  BLOCKED: Inverse of inverse is the original (pointwise).

  STATUS: Cannot be axiomatized or proved because the current applyIndex
  implementation for `inverse (inverse p)` falls through to the `| _ => i`
  fallback case, making the theorem COMPUTATIONALLY FALSE for most p.

  The theorem would be true mathematically if inverse were fully implemented.
  Current inverse implementation only handles:
  - identity: self-inverse (returns i)
  - swap: self-inverse (applies swap)
  - stride m n: uses strideIndexInv
  - bitRev k: self-inverse (applies bitReverse)
  - Everything else: fallback returns i (WRONG)

  theorem inverse_inverse_pointwise (p : Perm n) (i : Fin n) :
      applyIndex (inverse (inverse p)) i = applyIndex p i := by
    sorry  -- BLOCKED: Current impl falls through to identity for inverse(inverse p)
-/

/-
  BLOCKED: Inverse of composition is reverse composition of inverses.

  STATUS: Cannot be axiomatized because the current implementation makes
  this theorem COMPUTATIONALLY FALSE. The expression `inverse (compose p q)`
  falls through to the `| _ => i` fallback, returning i instead of
  the mathematically correct `compose (inverse q) (inverse p)`.

  To fix this, applyIndex would need to handle:
  | inverse (compose p q) => applyIndex (compose (inverse q) (inverse p)) i

  But this pattern matching is complex for indexed inductives.

  theorem inverse_compose_pointwise (p q : Perm n) (i : Fin n) :
      applyIndex (inverse (compose p q)) i =
      applyIndex (compose (inverse q) (inverse p)) i := by
    sorry  -- Current inverse implementation doesn't handle compose
-/

end Perm

/-! ## Tensor Product Properties -/

-- Auxiliary lemmas for tensor_compose_pointwise
-- Key: For a*n + b with b < n, we have (a*n + b)/n = a and (a*n + b)%n = b

private theorem nat_mul_add_div_eq (a b n : Nat) (hn : n > 0) (hb : b < n) :
    (a * n + b) / n = a := by
  have key : a * n + b < (a + 1) * n := by
    simp only [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left hb _
  rw [Nat.div_eq_of_lt_le (Nat.le_add_right (a * n) b) key]

private theorem nat_mul_add_mod_eq (a b n : Nat) (hn : n > 0) (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_mod]
  have h1 : a * n % n = 0 := Nat.mul_mod_left a n
  have h2 : b % n = b := Nat.mod_eq_of_lt hb
  have h3 : b % n % n = b % n := Nat.mod_eq_of_lt (Nat.mod_lt b hn)
  rw [h1, Nat.zero_add, h3, h2]

namespace Perm

/-- Direct computation of tensor application without using applyIndex pattern matching.
    This avoids the splitter limitation by computing directly. -/
def applyTensorDirect {m n : Nat} (p : Perm m) (q : Perm n)
    (i : Fin (m * n)) (hn : n ≠ 0) (hm : m ≠ 0) : Fin (m * n) :=
  let outer := i.val / n
  let inner := i.val % n
  have h_n_pos : n > 0 := Nat.pos_of_ne_zero hn
  have h_outer_bound : outer < m := by
    have h_swap : m * n = n * m := Nat.mul_comm m n
    have h_i_lt : i.val < n * m := h_swap ▸ i.isLt
    exact Nat.div_lt_of_lt_mul h_i_lt
  have h_inner_bound : inner < n := Nat.mod_lt i.val h_n_pos
  let new_outer := (applyIndex p ⟨outer, h_outer_bound⟩).val
  let new_inner := (applyIndex q ⟨inner, h_inner_bound⟩).val
  ⟨new_outer * n + new_inner, by
    have h_no : new_outer < m := (applyIndex p ⟨outer, h_outer_bound⟩).isLt
    have h_ni : new_inner < n := (applyIndex q ⟨inner, h_inner_bound⟩).isLt
    calc new_outer * n + new_inner
      < new_outer * n + n := Nat.add_lt_add_left h_ni _
      _ = (new_outer + 1) * n := by simp [Nat.add_mul, Nat.one_mul]
      _ ≤ m * n := Nat.mul_le_mul_right n h_no⟩

/-- The key insight: applyIndex (tensor p q) i computes the same as applyTensorDirect.

    Previously stated as an axiom because nested pattern matching on `inverse`
    subcases (e.g., `inverse swap`, `inverse (stride m n)`) in the same match
    as `tensor` triggered a splitter generation failure. The fix: extract inverse
    handling into `applyInverseIndex`, eliminating the nested patterns that caused
    overlapping index obligations the splitter couldn't resolve. -/
theorem applyIndex_tensor_eq {m n : Nat} (p : Perm m) (q : Perm n)
    (i : Fin (m * n)) (hn : n ≠ 0) (hm : m ≠ 0) :
    applyIndex (tensor p q) i = applyTensorDirect p q i hn hm := by
  simp only [applyIndex, dif_neg hn, dif_neg hm, applyTensorDirect]

/-- Tensor distributes over composition (pointwise).
    (p1 ⊗ q1) · (p2 ⊗ q2) = (p1 · p2) ⊗ (q1 · q2)
    This is a fundamental algebraic property of tensor products.

    **Proof Strategy**:
    - Edge cases m=0 or n=0: Handled via Fin.elim0 (empty type)
    - Main case uses `applyIndex_tensor_eq` to rewrite tensor applications
    - With this, we prove both sides compute to p1(p2(i/n)) * n + q1(q2(i%n))
    - Auxiliary lemmas `nat_mul_add_div_eq` and `nat_mul_add_mod_eq` handle the arithmetic -/
theorem tensor_compose_pointwise {m n : Nat} (p1 p2 : Perm m) (q1 q2 : Perm n) (i : Fin (m * n)) :
    applyIndex (compose (tensor p1 q1) (tensor p2 q2)) i =
    applyIndex (tensor (compose p1 p2) (compose q1 q2)) i := by
  -- Expand compose on LHS using the equation lemma
  simp only [Perm.apply_compose]
  -- Handle edge case: n = 0 (Fin (m * 0) is empty)
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.mul_zero] at i
    exact Fin.elim0 i
  -- Handle edge case: m = 0 (Fin (0 * n) is empty)
  by_cases hm : m = 0
  · subst hm
    simp only [Nat.zero_mul] at i
    exact Fin.elim0 i
  -- Main case: m > 0 and n > 0
  -- Setup: positive n for division/modulo bounds
  have h_n_pos : n > 0 := Nat.pos_of_ne_zero hn

  -- Step 1: Get bounds for div/mod of i
  have h_outer_i_bound : i.val / n < m := by
    have h_swap : m * n = n * m := Nat.mul_comm m n
    have h_i_lt : i.val < n * m := h_swap ▸ i.isLt
    exact Nat.div_lt_of_lt_mul h_i_lt
  have h_inner_i_bound : i.val % n < n := Nat.mod_lt i.val h_n_pos

  -- Step 2: Apply applyIndex_tensor_eq to rewrite all tensor applications
  -- j = applyTensorDirect p2 q2 i = ⟨p2(i/n) * n + q2(i%n), ...⟩
  let j := applyTensorDirect p2 q2 i hn hm

  -- Rewrite LHS: applyIndex (tensor p1 q1) (applyIndex (tensor p2 q2) i)
  --           -> applyIndex (tensor p1 q1) j
  --           -> applyTensorDirect p1 q1 j
  have h_lhs_step1 : applyIndex (tensor p2 q2) i = j := applyIndex_tensor_eq p2 q2 i hn hm
  have h_lhs_step2 : applyIndex (tensor p1 q1) j = applyTensorDirect p1 q1 j hn hm :=
    applyIndex_tensor_eq p1 q1 j hn hm

  -- Rewrite RHS: applyIndex (tensor (compose p1 p2) (compose q1 q2)) i
  --           -> applyTensorDirect (compose p1 p2) (compose q1 q2) i
  have h_rhs : applyIndex (tensor (compose p1 p2) (compose q1 q2)) i =
      applyTensorDirect (compose p1 p2) (compose q1 q2) i hn hm :=
    applyIndex_tensor_eq (compose p1 p2) (compose q1 q2) i hn hm

  -- Apply rewrites
  rw [h_lhs_step1, h_lhs_step2, h_rhs]

  -- Step 3: Get the structure of j.val
  have h_new_outer2_bound : (applyIndex p2 ⟨i.val / n, h_outer_i_bound⟩).val < m :=
    (applyIndex p2 ⟨i.val / n, h_outer_i_bound⟩).isLt
  have h_new_inner2_bound : (applyIndex q2 ⟨i.val % n, h_inner_i_bound⟩).val < n :=
    (applyIndex q2 ⟨i.val % n, h_inner_i_bound⟩).isLt

  -- j.val = new_outer2 * n + new_inner2
  have hj_val : j.val = (applyIndex p2 ⟨i.val / n, h_outer_i_bound⟩).val * n +
                         (applyIndex q2 ⟨i.val % n, h_inner_i_bound⟩).val := rfl

  -- Step 4: Use auxiliary lemmas to simplify j.val / n and j.val % n
  have h_j_div : j.val / n = (applyIndex p2 ⟨i.val / n, h_outer_i_bound⟩).val := by
    rw [hj_val]
    exact nat_mul_add_div_eq _ _ n h_n_pos h_new_inner2_bound

  have h_j_mod : j.val % n = (applyIndex q2 ⟨i.val % n, h_inner_i_bound⟩).val := by
    rw [hj_val]
    exact nat_mul_add_mod_eq _ _ n h_n_pos h_new_inner2_bound

  -- Step 5: Prove equality via Fin.ext
  apply Fin.ext
  simp only [applyTensorDirect, Perm.apply_compose]

  -- Now both sides have the form: some_outer * n + some_inner
  -- LHS: applyIndex p1 (j.val / n) * n + applyIndex q1 (j.val % n)
  -- RHS: applyIndex p1 (applyIndex p2 (i/n)) * n + applyIndex q1 (applyIndex q2 (i%n))

  -- Key: use h_j_div and h_j_mod to show they're the same
  -- For the outer part: The bound proof for j.val / n uses different derivation
  -- but the value is the same, so applyIndex gives the same result
  have h_j_outer_bound : j.val / n < m := by
    have h_swap : m * n = n * m := Nat.mul_comm m n
    have h_j_lt : j.val < n * m := h_swap ▸ j.isLt
    exact Nat.div_lt_of_lt_mul h_j_lt
  have h_j_inner_bound : j.val % n < n := Nat.mod_lt j.val h_n_pos

  -- Key insight: The Fin values are equal by h_j_div and h_j_mod
  -- Use Fin.ext to show the outer Fin args are equal, then applyIndex gives same result

  -- For the outer multiplication term:
  -- We need: applyIndex p1 ⟨j.val / n, h_j_outer_bound⟩ = applyIndex p1 (applyIndex p2 ⟨i/n, h_outer_i_bound⟩)
  -- The two Fin m arguments have the same .val by h_j_div
  have h_outer_fin_eq : (⟨j.val / n, h_j_outer_bound⟩ : Fin m) =
      applyIndex p2 ⟨i.val / n, h_outer_i_bound⟩ := by
    apply Fin.ext
    exact h_j_div

  -- For the inner addition term:
  -- We need: applyIndex q1 ⟨j.val % n, h_j_inner_bound⟩ = applyIndex q1 (applyIndex q2 ⟨i%n, h_inner_i_bound⟩)
  have h_inner_fin_eq : (⟨j.val % n, h_j_inner_bound⟩ : Fin n) =
      applyIndex q2 ⟨i.val % n, h_inner_i_bound⟩ := by
    apply Fin.ext
    exact h_j_mod

  -- Now rewrite using these equalities
  simp only [h_outer_fin_eq, h_inner_fin_eq]

/-
  Tensor with I_1 on the left: I_1 ⊗ P ≃ P (pointwise).
  Types: I_1 ⊗ P : Perm (1 * n), P : Perm n.
  Requires type coercion h : 1 * n = n.

  Note: This theorem involves heterogeneous equality due to type coercion.
  The tensor implementation is correct, but proving with type transport
  is complex. Left as future work.

  theorem tensor_identity_left_one (p : Perm n) :
      let h : 1 * n = n := Nat.one_mul n
      ∀ i : Fin n, applyIndex (h ▸ tensor identity p) i = applyIndex p i := by
    sorry  -- Blocked by type coercion complexity
-/

/-
  Tensor with I_1 on the right: P ⊗ I_1 ≃ P (pointwise).
  Types: P ⊗ I_1 : Perm (m * 1), P : Perm m.
  Similar type coercion issues as tensor_identity_left_one.

  theorem tensor_identity_right_one (p : Perm m) :
      let h : m * 1 = m := Nat.mul_one m
      ∀ i : Fin m, applyIndex (h ▸ tensor p identity) i = applyIndex p i := by
    sorry  -- Blocked by type coercion complexity
-/

-- Tensor is associative (up to isomorphism):
-- tensor (tensor p q) r ≃ tensor p (tensor q r)
-- This requires careful handling of the associativity of Nat multiplication
-- Left as future work due to type-level associativity complications

end Perm

/-! ## Concrete Permutation Generation -/

/-- Generate all indices for stride permutation L^{mn}_n. -/
def strideIndices (m n : Nat) : List Nat :=
  List.map (strideIndex m n) (List.range (m * n))

/-- Generate all indices for bit-reversal permutation. -/
def bitRevIndices (k : Nat) : List Nat :=
  List.map (bitReverse k) (List.range (2^k))

/-- Pretty print a permutation (for debugging). -/
def Perm.toString : Perm n → String
  | Perm.identity => s!"I_{n}"
  | Perm.stride m n' => s!"L^{m*n'}_{n'}"
  | Perm.bitRev k => s!"BitRev_{2^k}"
  | Perm.swap => "Swap"
  | Perm.compose p q => s!"({Perm.toString p} · {Perm.toString q})"
  | Perm.inverse p => s!"({Perm.toString p})⁻¹"
  | Perm.tensor p q => s!"({Perm.toString p} ⊗ {Perm.toString q})"

instance : ToString (Perm n) where
  toString := Perm.toString

/-! ## Examples and Tests -/

-- Stride permutation L^{6}_3 on a vector [0,1,2,3,4,5]
-- Treats it as a 2×3 matrix in row-major:
--   [[0,1,2],
--    [3,4,5]]
-- Transposed (column-major read):
--   [0,3,1,4,2,5]
#eval strideIndices 2 3  -- Should be [0, 3, 1, 4, 2, 5]

-- Stride permutation L^{6}_2 (inverse of above)
#eval strideIndices 3 2  -- Should map back

-- Bit reversal for k=3 (size 8)
-- 0=000->000=0, 1=001->100=4, 2=010->010=2, 3=011->110=6,
-- 4=100->001=1, 5=101->101=5, 6=110->011=3, 7=111->111=7
#eval bitRevIndices 3  -- Should be [0, 4, 2, 6, 1, 5, 3, 7]

-- Check bit reverse is self-inverse
#eval (bitRevIndices 3).map (bitReverse 3)  -- Should be [0, 1, 2, 3, 4, 5, 6, 7]

-- Tensor product tests
-- Identity ⊗ Identity should be identity
#eval Perm.toIndexList (Perm.tensor (Perm.identity : Perm 2) (Perm.identity : Perm 3))
-- Expected: [0, 1, 2, 3, 4, 5] (identity on size 6)

-- Swap ⊗ Identity: swaps the two "blocks" of size 3
-- i=0: outer=0 → swap(0)=1, inner=0 → result=1*3+0=3
-- i=1: outer=0 → swap(0)=1, inner=1 → result=1*3+1=4
-- i=2: outer=0 → swap(0)=1, inner=2 → result=1*3+2=5
-- i=3: outer=1 → swap(1)=0, inner=0 → result=0*3+0=0
-- i=4: outer=1 → swap(1)=0, inner=1 → result=0*3+1=1
-- i=5: outer=1 → swap(1)=0, inner=2 → result=0*3+2=2
#eval Perm.toIndexList (Perm.tensor (Perm.swap : Perm 2) (Perm.identity : Perm 3))
-- Expected: [3, 4, 5, 0, 1, 2]

-- Identity ⊗ Swap: swaps pairs within each block
-- Block 0: [0,1] → [1,0] so positions 0,1 become 1,0
-- Block 1: [3,4] → [4,3] so positions 3,4 become 4,3 (but wait, block 1 starts at position 2 for 2x2)
-- Actually for 3⊗2: i = outer*2 + inner
-- i=0: outer=0, inner=0 → id(0)=0, swap(0)=1 → 0*2+1=1
-- i=1: outer=0, inner=1 → id(0)=0, swap(1)=0 → 0*2+0=0
-- i=2: outer=1, inner=0 → id(1)=1, swap(0)=1 → 1*2+1=3
-- i=3: outer=1, inner=1 → id(1)=1, swap(1)=0 → 1*2+0=2
-- i=4: outer=2, inner=0 → id(2)=2, swap(0)=1 → 2*2+1=5
-- i=5: outer=2, inner=1 → id(2)=2, swap(1)=0 → 2*2+0=4
#eval Perm.toIndexList (Perm.tensor (Perm.identity : Perm 3) (Perm.swap : Perm 2))
-- Expected: [1, 0, 3, 2, 5, 4]

-- Test tensor compose: (p1 ⊗ q1) · (p2 ⊗ q2) vs (p1 · p2) ⊗ (q1 · q2)
-- Using swap ⊗ identity composed with identity ⊗ swap
#eval Perm.toIndexList (Perm.compose
  (Perm.tensor (Perm.swap : Perm 2) (Perm.identity : Perm 2))
  (Perm.tensor (Perm.identity : Perm 2) (Perm.swap : Perm 2)))
-- (swap ⊗ id) · (id ⊗ swap):
-- First apply id ⊗ swap: [1,0,3,2]
-- Then apply swap ⊗ id: [0,1]→[2,3], [2,3]→[0,1] so [1,0,3,2]→[3,2,1,0]
-- Expected: [3, 2, 1, 0]

#eval Perm.toIndexList (Perm.tensor
  (Perm.compose (Perm.swap : Perm 2) (Perm.identity : Perm 2))
  (Perm.compose (Perm.identity : Perm 2) (Perm.swap : Perm 2)))
-- (swap · id) ⊗ (id · swap) = swap ⊗ swap
-- swap ⊗ swap: i=outer*2+inner → swap(outer)*2+swap(inner)
-- i=0: outer=0, inner=0 → 1*2+1=3
-- i=1: outer=0, inner=1 → 1*2+0=2
-- i=2: outer=1, inner=0 → 0*2+1=1
-- i=3: outer=1, inner=1 → 0*2+0=0
-- Expected: [3, 2, 1, 0]

end AmoLean.Matrix
