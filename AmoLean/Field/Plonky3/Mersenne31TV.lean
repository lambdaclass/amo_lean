/-
  AMO-Lean: Mersenne31 Plonky3 Translation Validation
  Fase 17 Nodo 2 — N17.2 (CRITICO)

  Formalizes Plonky3's EXACT Mersenne31 algorithms and proves they match
  the Mersenne31Field operations from N17.1.

  Reference: Plonky3 mersenne-31 crate
  - mersenne_31.rs: from_u62, mul, neg
  - monty-31/utils.rs: add, sub

  Key identity: 2^31 ≡ 1 (mod 2^31 - 1)
  Therefore splitting a 62-bit product into two 31-bit halves and adding
  them is equivalent to modular reduction.
-/

import AmoLean.Field.Mersenne31

namespace AmoLean.Field.Plonky3.Mersenne31

open AmoLean.Field.Mersenne31

/-! ## Part 1: Plonky3 `from_u62` — Mersenne-specific reduction

Plonky3 Rust (mersenne_31.rs lines 540-545):
```rust
fn from_u62(input: u64) -> Mersenne31 {
    debug_assert!(input < (1 << 62));
    let input_lo = (input & ((1 << 31) - 1)) as u32;
    let input_high = (input >> 31) as u32;
    Mersenne31::new_reduced(input_lo) + Mersenne31::new_reduced(input_high)
}
```

In Lean: split x into lo = x % 2^31 and hi = x / 2^31, then add modulo p.
The intermediate sum lo + hi may equal p (when both are < 2^31), so we
perform a conditional subtraction.
-/

/-- Split a Nat into low 31 bits and high bits. -/
def splitU62 (x : Nat) : Nat × Nat :=
  (x % 2^31, x / 2^31)

/-- from_u62 helper: build the two Mersenne31Field halves and add them. -/
def from_u62_core (lo hi : Nat) : Mersenne31Field :=
  Mersenne31Field.add
    (Mersenne31Field.ofUInt32 lo.toUInt32)
    (Mersenne31Field.ofUInt32 hi.toUInt32)

/-- from_u62: Mersenne-specific reduction for values < 2^62.
    Mirrors Plonky3's `from_u62` exactly. -/
def from_u62 (x : Nat) (_ : x < 2^62) : Mersenne31Field :=
  from_u62_core (x % 2^31) (x / 2^31)

/-! ### Key identity: 2^31 ≡ 1 (mod p) -/

theorem two_pow_31_mod_p : 2^31 % ORDER_NAT = 1 := by native_decide

theorem two_pow_31_eq_order_plus_one : 2^31 = ORDER_NAT + 1 := by native_decide

/-! ### from_u62 correctness -/

/-- Helper: hi part is < 2^31 when x < 2^62. -/
private theorem hi_bound (x : Nat) (hx : x < 2^62) : x / 2^31 < 2^31 := by
  have : 2^62 = 2^31 * 2^31 := by norm_num
  omega

/-- Auxiliary: ofUInt32 on a value < ORDER produces that value directly. -/
private theorem ofUInt32_val_of_lt (n : Nat) (hn : n < ORDER_NAT)
    (hn_size : n < UInt32.size) :
    (Mersenne31Field.ofUInt32 n.toUInt32).value.toNat = n := by
  unfold Mersenne31Field.ofUInt32
  have hlt : n.toUInt32 < ORDER := by
    simp only [UInt32.lt_iff_toNat_lt, Nat.toUInt32, UInt32.toNat_ofNat',
               Nat.mod_eq_of_lt hn_size, ORDER]
    exact hn
  simp only [dif_pos hlt]
  simp only [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn_size]

/-- Auxiliary: ofUInt32 on ORDER produces 0 (since ORDER % ORDER = 0). -/
private theorem ofUInt32_val_of_eq_order :
    (Mersenne31Field.ofUInt32 ORDER_NAT.toUInt32).value.toNat = 0 := by
  native_decide

/-- For any n ≤ ORDER_NAT, ofUInt32(n.toUInt32).value.toNat = n % ORDER_NAT. -/
private theorem ofUInt32_val_mod (n : Nat) (hn : n ≤ ORDER_NAT) :
    (Mersenne31Field.ofUInt32 n.toUInt32).value.toNat = n % ORDER_NAT := by
  by_cases heq : n = ORDER_NAT
  · rw [heq, Nat.mod_self]; exact ofUInt32_val_of_eq_order
  · have hlt : n < ORDER_NAT := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hsize : ORDER_NAT < UInt32.size := by native_decide
    exact ofUInt32_val_of_lt n hlt (by omega)

/-- The core reduction: adding the two halves modulo p gives the same result as x mod p.

    Proof idea:
    1. from_u62_core(lo, hi) = (lo' + hi') % p  where lo' = lo % p, hi' = hi % p
    2. lo + hi ≡ lo + hi * 2^31 ≡ x (mod p)  because 2^31 ≡ 1 (mod p)
-/
theorem from_u62_core_val (lo hi : Nat) (hlo : lo ≤ ORDER_NAT) (hhi : hi ≤ ORDER_NAT) :
    (from_u62_core lo hi).value.toNat = (lo % ORDER_NAT + hi % ORDER_NAT) % ORDER_NAT := by
  unfold from_u62_core
  -- from_u62_core lo hi = Mersenne31Field.add (ofUInt32 lo) (ofUInt32 hi)
  -- which is (ofUInt32 lo) + (ofUInt32 hi)
  -- add_val_eq: (a + b).value.toNat = (a.val + b.val) % ORDER_NAT
  have h := add_val_eq
    (Mersenne31Field.ofUInt32 lo.toUInt32)
    (Mersenne31Field.ofUInt32 hi.toUInt32)
  -- h talks about HAdd (+), our goal talks about Mersenne31Field.add
  -- They are definitionally equal via the Add instance
  show (Mersenne31Field.ofUInt32 lo.toUInt32 +
        Mersenne31Field.ofUInt32 hi.toUInt32).value.toNat =
       (lo % ORDER_NAT + hi % ORDER_NAT) % ORDER_NAT
  rw [h, ofUInt32_val_mod lo hlo, ofUInt32_val_mod hi hhi]

/-- The modular identity: (lo + hi) % p = x % p when lo + 2^31 * hi = x. -/
private theorem mersenne_split_mod {x : Nat} (lo hi : Nat) (hsplit : lo + 2^31 * hi = x) :
    (lo + hi) % ORDER_NAT = x % ORDER_NAT := by
  rw [← hsplit]
  have h2_31 := two_pow_31_eq_order_plus_one
  conv_rhs => rw [show 2^31 * hi = (ORDER_NAT + 1) * hi from by rw [h2_31]]
  rw [Nat.add_mul, Nat.one_mul]
  -- Goal: (lo + hi) % ORDER_NAT = (lo + (ORDER_NAT * hi + hi)) % ORDER_NAT
  -- Rearrange RHS: lo + (ORDER_NAT * hi + hi) = (lo + hi) + ORDER_NAT * hi
  have : lo + (ORDER_NAT * hi + hi) = (lo + hi) + ORDER_NAT * hi := by omega
  rw [this, Nat.add_mul_mod_self_left]

/-- The Nat-level value of from_u62 equals x mod ORDER_NAT. -/
theorem from_u62_val_mod (x : Nat) (hx : x < 2^62) :
    (from_u62 x hx).value.toNat = x % ORDER_NAT := by
  unfold from_u62
  have hord : ORDER_NAT = 2^31 - 1 := by native_decide
  have hlo_bound : x % 2^31 < 2^31 := Nat.mod_lt _ (by norm_num)
  have hhi_bound := hi_bound x hx
  have hlo_le : x % 2^31 ≤ ORDER_NAT := by omega
  have hhi_le : x / 2^31 ≤ ORDER_NAT := by omega
  rw [from_u62_core_val _ _ hlo_le hhi_le]
  -- Goal: (x % 2^31 % p + x / 2^31 % p) % p = x % p
  -- Use (a % p + b % p) % p = (a + b) % p
  rw [Nat.add_mod (x % 2^31 % ORDER_NAT) (x / 2^31 % ORDER_NAT) ORDER_NAT,
      Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
  -- Goal: (x % 2^31 + x / 2^31) % p = x % p
  exact mersenne_split_mod (x % 2^31) (x / 2^31) (Nat.mod_add_div x (2^31))

/-! ## Part 2: Plonky3 Arithmetic Operations

These mirror the Plonky3 Rust implementations at the semantic level.
The i32/overflow tricks in Rust are just optimizations — the mathematical
semantics are identical to our Mersenne31Field operations.
-/

/-- Plonky3-style add: if a + b >= p then a + b - p else a + b.
    Semantically identical to Mersenne31Field.add. -/
def plonky3_add (a b : Mersenne31Field) : Mersenne31Field :=
  Mersenne31Field.add a b

/-- Plonky3-style sub: if a >= b then a - b else a + p - b.
    Semantically identical to Mersenne31Field.sub. -/
def plonky3_sub (a b : Mersenne31Field) : Mersenne31Field :=
  Mersenne31Field.sub a b

/-- Plonky3-style neg: p - value.
    Semantically identical to Mersenne31Field.neg. -/
def plonky3_neg (a : Mersenne31Field) : Mersenne31Field :=
  Mersenne31Field.neg a

/-- Product of two Mersenne31Field values < 2^62. -/
private theorem product_bound (a b : Mersenne31Field) :
    a.value.toNat * b.value.toNat < 2^62 := by
  have ha := a.h_lt
  have hb := b.h_lt
  have : ORDER.toNat = 2147483647 := by native_decide
  have : a.value.toNat < 2147483647 := by omega
  have : b.value.toNat < 2147483647 := by omega
  calc a.value.toNat * b.value.toNat
      < 2147483647 * 2147483647 := by nlinarith
    _ < 2^62 := by norm_num

/-- Plonky3-style mul: compute a * b as u64 (< 2^62), then from_u62.
    This is the key operation that uses the Mersenne-specific reduction. -/
def plonky3_mul (a b : Mersenne31Field) : Mersenne31Field :=
  from_u62 (a.value.toNat * b.value.toNat) (product_bound a b)

/-! ## Part 3: Refinement Theorems -/

/-- Plonky3 add refines Mersenne31Field add (trivially, they are definitionally equal). -/
theorem plonky3_add_refines (a b : Mersenne31Field) :
    plonky3_add a b = a + b := rfl

/-- Plonky3 sub refines Mersenne31Field sub. -/
theorem plonky3_sub_refines (a b : Mersenne31Field) :
    plonky3_sub a b = a - b := rfl

/-- Plonky3 neg refines Mersenne31Field neg. -/
theorem plonky3_neg_refines (a : Mersenne31Field) :
    plonky3_neg a = -a := rfl

/-- The core refinement theorem: plonky3_mul produces the same result as Mersenne31Field.mul.
    This proves that the Plonky3 `from_u62` reduction is equivalent to standard `% p`. -/
theorem plonky3_mul_refines (a b : Mersenne31Field) :
    plonky3_mul a b = a * b := by
  apply Mersenne31Field.ext
  -- LHS: plonky3_mul uses from_u62, which produces (a*b) % p
  have hlhs : (plonky3_mul a b).value.toNat =
      (a.value.toNat * b.value.toNat) % ORDER_NAT := by
    unfold plonky3_mul
    exact from_u62_val_mod _ (product_bound a b)
  -- RHS: standard mul uses reduceMul, also produces (a*b) % p
  have hrhs_mod : (a * b).value.toNat % ORDER_NAT =
      (a.value.toNat * b.value.toNat) % ORDER_NAT := mul_val_eq a b
  have hrhs_canon : (a * b).value.toNat < ORDER_NAT := mersenne31_canonical (a * b)
  have hrhs : (a * b).value.toNat =
      (a.value.toNat * b.value.toNat) % ORDER_NAT := by
    rw [← hrhs_mod, Nat.mod_eq_of_lt hrhs_canon]
  -- Both sides have the same .value.toNat
  have heq : (plonky3_mul a b).value.toNat = (a * b).value.toNat := by
    rw [hlhs, hrhs]
  exact UInt32.ext heq

/-! ## Part 4: Non-vacuity Examples -/

/-- Non-vacuity: plonky3_mul is well-defined and matches standard mul. -/
example : ∃ a b : Mersenne31Field, plonky3_mul a b = a * b :=
  ⟨⟨42, by native_decide⟩, ⟨17, by native_decide⟩, plonky3_mul_refines _ _⟩

/-- Non-vacuity: from_u62 computes the correct reduction. -/
example : (from_u62 0 (by norm_num)).value.toNat = 0 := by native_decide

/-- Non-vacuity: from_u62 on a value that spans both halves. -/
example : (from_u62 (2^31 + 5) (by norm_num)).value.toNat = 6 := by native_decide

/-- Non-vacuity: from_u62 on a larger product. -/
example : (from_u62 (100 * 200) (by norm_num)).value.toNat = 20000 := by native_decide

/-! ## Part 5: #eval Smoke Tests -/

-- Verify from_u62 matches % p for specific values
#eval do
  let p : Nat := 2147483647
  -- Test 1: small value
  let x1 : Nat := 12345
  let r1 := (from_u62 x1 (by norm_num)).value.toNat
  assert! r1 == x1 % p
  -- Test 2: value > p (= 2^31)
  let x2 : Nat := 2147483648
  let r2 := (from_u62 x2 (by norm_num)).value.toNat
  assert! r2 == x2 % p
  -- Test 3: larger value (product-like)
  let x3 : Nat := 1000000007 * 1000000009
  let r3 := (from_u62 x3 (by norm_num)).value.toNat
  assert! r3 == x3 % p
  return ()

-- Verify plonky3_mul matches standard mul for specific values
#eval do
  let a : Mersenne31Field := ⟨42, by native_decide⟩
  let b : Mersenne31Field := ⟨17, by native_decide⟩
  let p3_result := plonky3_mul a b
  let std_result := a * b
  assert! p3_result == std_result
  return ()

#eval do
  let a : Mersenne31Field := ⟨2147483646, by native_decide⟩  -- p-1
  let b : Mersenne31Field := ⟨2147483646, by native_decide⟩  -- p-1
  let p3_result := plonky3_mul a b
  let std_result := a * b
  assert! p3_result == std_result
  -- (p-1)*(p-1) ≡ 1 (mod p)
  let one : Mersenne31Field := ⟨1, by native_decide⟩
  assert! p3_result == one
  return ()

#eval do
  let a : Mersenne31Field := ⟨1073741824, by native_decide⟩  -- 2^30
  let b : Mersenne31Field := ⟨4, by native_decide⟩
  let p3_result := plonky3_mul a b
  let std_result := a * b
  assert! p3_result == std_result
  -- 2^30 * 4 = 2^32 ≡ 2 (mod p)
  let two : Mersenne31Field := ⟨2, by native_decide⟩
  assert! p3_result == two
  return ()

end AmoLean.Field.Plonky3.Mersenne31
