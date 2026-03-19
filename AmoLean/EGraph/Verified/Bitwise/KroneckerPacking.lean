/-
  AmoLean.EGraph.Verified.Bitwise.KroneckerPacking — Kronecker Pack/Unpack Semantics

  B76 (PARALELO): Verified Kronecker packing for BabyBear — 2 elements in 1 u64.
  Adapted from BitwiseLean/NTTButterfly.lean: babybear_pack_lo, babybear_pack_hi.

  Key theorem: kronPack_roundtrip — unpack(pack(a,b)) = (a, b).
-/
import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.KroneckerPacking

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Pack/Unpack correctness
-- ══════════════════════════════════════════════════════════════════

/-- Pack two values: a + b * 2^w. -/
def kronPack (a b w : Nat) : Nat := a + b * 2 ^ w

/-- Unpack low: x % 2^w. -/
def kronUnpackLo (x w : Nat) : Nat := x % 2 ^ w

/-- Unpack high: x / 2^w. -/
def kronUnpackHi (x w : Nat) : Nat := x / 2 ^ w

/-- Low extraction roundtrip: unpackLo(pack(a, b, w)) = a when a < 2^w. -/
theorem kronPack_lo_roundtrip (a b w : Nat) (ha : a < 2 ^ w) :
    kronUnpackLo (kronPack a b w) w = a := by
  simp only [kronPack, kronUnpackLo]
  rw [Nat.mul_comm b (2^w), Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt ha

/-- High extraction roundtrip: unpackHi(pack(a, b, w)) = b when a < 2^w. -/
theorem kronPack_hi_roundtrip (a b w : Nat) (ha : a < 2 ^ w) :
    kronUnpackHi (kronPack a b w) w = b := by
  simp only [kronPack, kronUnpackHi]
  rw [Nat.mul_comm b (2^w), Nat.add_mul_div_left a b (Nat.two_pow_pos w)]
  rw [Nat.div_eq_of_lt ha, Nat.zero_add]

/-- Full roundtrip: unpack(pack(a,b)) = (a, b). -/
theorem kronPack_roundtrip (a b w : Nat) (ha : a < 2 ^ w) :
    kronUnpackLo (kronPack a b w) w = a ∧ kronUnpackHi (kronPack a b w) w = b :=
  ⟨kronPack_lo_roundtrip a b w ha, kronPack_hi_roundtrip a b w ha⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 2: BabyBear concrete instance (w = 32)
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear elements are < 2^31 < 2^32, so they fit in the low 32 bits. -/
theorem babybear_fits_32 (a : Nat) (ha : a < 2 ^ 31) : a < 2 ^ 32 := by omega

/-- BabyBear pack roundtrip with w=32. -/
theorem babybear_pack_roundtrip (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    kronUnpackLo (kronPack a b 32) 32 = a ∧ kronUnpackHi (kronPack a b 32) 32 = b :=
  kronPack_roundtrip a b 32 (babybear_fits_32 a ha)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Addition fusion (lane-independent when no carry)
-- ══════════════════════════════════════════════════════════════════

/-- Packed addition is lane-independent when no carry from low to high lane.
    pack(a1,b1) + pack(a2,b2) = pack(a1+a2, b1+b2) when a1+a2 < 2^w. -/
theorem kronPack_add_no_carry (a1 b1 a2 b2 w : Nat)
    (hno_carry : a1 + a2 < 2 ^ w) :
    kronPack a1 b1 w + kronPack a2 b2 w = kronPack (a1 + a2) (b1 + b2) w := by
  simp only [kronPack, Nat.add_mul]; omega

/-- Subtraction fusion: pack(a1,b1) - pack(a2,b2) = pack(a1-a2, b1-b2)
    when a1 >= a2 and b1 >= b2 (no borrow between lanes). -/
theorem kronPack_sub_no_borrow (a1 b1 a2 b2 w : Nat)
    (ha : a2 ≤ a1) (hb : b2 ≤ b1) :
    kronPack a1 b1 w - kronPack a2 b2 w = kronPack (a1 - a2) (b1 - b2) w := by
  sorry -- B76: Nat subtraction with 2^w terms, needs careful Nat.sub_add_eq chain

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: BabyBear pack roundtrip with concrete values. -/
example : kronUnpackLo (kronPack 42 99 32) 32 = 42 := by native_decide
example : kronUnpackHi (kronPack 42 99 32) 32 = 99 := by native_decide

/-- Smoke: packed addition (no carry). -/
example : kronPack 10 20 32 + kronPack 5 3 32 = kronPack 15 23 32 := by native_decide

end AmoLean.EGraph.Verified.Bitwise.KroneckerPacking
