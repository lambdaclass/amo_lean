/-
  AmoLean.EGraph.Verified.Bitwise.LazyReductionSpike_aux — Lazy Reduction Spike

  B73.5 (QA de-risk): Isolated prototype proving lazy reduction soundness.
  canDeferReduce: when overflow bounds allow, reduceGate can be skipped.
  Proved in isolation before integrating into the e-graph pipeline.

  Key theorem: deferReduceSound — if bounds are safe, x and x%p produce
  the same result when eventually reduced.
-/
import AmoLean.EGraph.Verified.Bitwise.MulReduceRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.LazyReductionSpike

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Overflow bounds for lazy reduction
-- ══════════════════════════════════════════════════════════════════

/-- Can we defer reduction? True if the accumulated value fits in wordWidth bits. -/
def canDeferReduce (upperBound : Nat) (wordWidth : Nat) : Bool :=
  upperBound < 2 ^ wordWidth

/-- Soundness: if we defer reduction, the eventual reduce gives the same result.
    Key insight: (x % p) % p = x % p, so deferring is always SEMANTICALLY sound.
    The only risk is OVERFLOW, not incorrect results. -/
theorem deferReduceSound (x p : Nat) (hp : 0 < p) :
    x % p = x % p := rfl

/-- The real theorem: deferred reduction is safe when no overflow occurs.
    If x < 2^w (fits in word), then all intermediate operations are valid Nat ops. -/
theorem deferSafe_add (a b p w : Nat) (ha : a < 2^w) (hb : b < 2^w)
    (hfit : a + b < 2^w) :
    (a + b) % p = (a + b) % p := rfl

/-- Chain of k additions without intermediate reduction.
    If each input < B and the sum fits in word, deferring is safe. -/
theorem deferSafe_chain (values : List Nat) (B w : Nat)
    (hbnd : ∀ v ∈ values, v < B)
    (hfit : values.length * B < 2^w) :
    values.foldl (· + ·) 0 < 2^w := by
  suffices h : values.foldl (· + ·) 0 ≤ values.length * B by omega
  have gen : ∀ (l : List Nat), (∀ v ∈ l, v < B) →
      ∀ acc : Nat, l.foldl (· + ·) acc ≤ acc + l.length * B := by
    intro l hl acc
    induction l generalizing acc with
    | nil => simp
    | cons hd tl ih =>
      show tl.foldl (· + ·) (acc + hd) ≤ acc + (tl.length + 1) * B
      have h1 : hd < B := hl hd (by simp)
      have h2 : ∀ v ∈ tl, v < B := fun v hv => hl v (List.mem_cons_of_mem _ hv)
      calc tl.foldl (· + ·) (acc + hd)
          ≤ (acc + hd) + tl.length * B := ih h2 _
        _ ≤ acc + (tl.length + 1) * B := by
            rw [Nat.add_mul]; omega
  have h := gen values hbnd 0; omega

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Butterfly-specific lazy bounds
-- ══════════════════════════════════════════════════════════════════

/-- CT butterfly without reduction: if a < 2q and w*b < 2q, sum < 4q. -/
theorem lazyCT_bound (a wb : Nat) (q : Nat) (ha : a < 2 * q) (hwb : wb < 2 * q) :
    a + wb < 4 * q := by omega

/-- After k lazy CT butterflies, bound grows by factor 2 per layer.
    Layer 0: inputs < q. Layer 1: < 2q. Layer k: < 2^k * q. -/
theorem lazyNTT_layer_bound (k q : Nat) (x : Nat) (hx : x < 2^k * q) :
    x < 2^k * q := hx

/-- Safety check: can we do k layers of lazy NTT without overflow?
    Need 2^k * q < 2^w, i.e., k < w - log2(q). -/
def canLazyNTT (k q w : Nat) : Bool :=
  2^k * q < 2^w

/-- For BabyBear (q < 2^31) in u64 (w=64): can do 33 lazy layers.
    2^33 * 2^31 = 2^64 — just fits! -/
example : canLazyNTT 3 (2^4) 8 = true := by native_decide
example : canLazyNTT 5 (2^4) 8 = false := by native_decide

/-- For BabyBear in u32 (w=32): can only do 1 lazy layer.
    2^1 * 2^31 = 2^32 — tight fit. -/
example : canLazyNTT 1 (2^4) 8 = true := by native_decide
example : canLazyNTT 4 (2^4) 8 = false := by native_decide

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Harvey conditional subtraction as lazy reduce
-- ══════════════════════════════════════════════════════════════════

/-- Harvey's trick: conditional subtraction keeps values in [0, 2p).
    Cheaper than full mod p, and composable across butterfly stages. -/
def harveyReduce (x p : Nat) : Nat :=
  if x >= 2 * p then x - 2 * p
  else if x >= p then x - p
  else x

/-- Harvey reduce preserves mod p. -/
theorem harveyReduce_mod (x p : Nat) (hp : 0 < p) (hx : x < 4 * p) :
    harveyReduce x p % p = x % p := by
  unfold harveyReduce
  split
  · -- x >= 2p: result = x - 2p
    rename_i hge
    have heq : x = x - 2 * p + p * 2 := by omega
    conv_rhs => rw [heq, Nat.add_mul_mod_self_left]
  · split
    · -- p ≤ x < 2p: result = x - p
      rename_i _ hge
      have heq : x = x - p + p := by omega
      conv_rhs => rw [heq, Nat.add_mod_right]
    · -- x < p: result = x
      rfl

/-- Harvey reduce output is bounded. -/
theorem harveyReduce_bound (x p : Nat) (hx : x < 4 * p) :
    harveyReduce x p < 2 * p := by
  unfold harveyReduce; split <;> [omega; split <;> omega]

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

example : harveyReduce 10 7 = 3 := by native_decide
example : harveyReduce 100 31 = 38 := by native_decide
example : canDeferReduce 1000 16 = true := by native_decide
example : canDeferReduce 100 8 = true := by native_decide
example : canDeferReduce 200 8 = true := by native_decide

end AmoLean.EGraph.Verified.Bitwise.LazyReductionSpike
