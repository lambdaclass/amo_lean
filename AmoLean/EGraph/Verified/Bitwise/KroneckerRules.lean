/-
  AmoLean.EGraph.Verified.Bitwise.KroneckerRules — Kronecker Pack/Unpack Rewrite Rules

  B77 (PARALELO): Rewrite rules for Kronecker packing operations.
  Enables the e-graph to discover and exploit packed representations.
-/
import AmoLean.EGraph.Verified.Bitwise.KroneckerPacking
import AmoLean.EGraph.Verified.Bitwise.BitwiseRules

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.KroneckerRules

open AmoLean.EGraph.Verified.Bitwise (MixedSoundRule MixedEnv)
open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise.KroneckerPacking

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Roundtrip rules (unpack after pack = identity)
-- ══════════════════════════════════════════════════════════════════

/-- unpackLo(pack(a, b, w)) = a when a < 2^w. -/
def unpackLoAfterPackRule (w : Nat) : MixedSoundRule where
  name := s!"unpack_lo_after_pack_{w}"
  -- lhs: unpackLo(pack(v0, v1, w), w)
  -- rhs: v0
  -- But MixedSoundRule uses Nat equality over valuations.
  -- We model: if v0 < 2^w, then (v0 + v1 * 2^w) % 2^w = v0
  lhsEval := fun _env v => (v 0 + v 1 * 2^w) % 2^w
  rhsEval := fun _env v => v 0 % 2^w  -- outputs v0 mod 2^w (= v0 when v0 < 2^w)
  soundness := fun _env v => by
    rw [Nat.mul_comm (v 1) (2^w), Nat.add_mul_mod_self_left]

/-- unpackHi(pack(a, b, w)) = b when a < 2^w. -/
def unpackHiAfterPackRule (w : Nat) : MixedSoundRule where
  name := s!"unpack_hi_after_pack_{w}"
  lhsEval := fun _env v => (v 0 + v 1 * 2^w) / 2^w
  rhsEval := fun _env v => v 1 + v 0 / 2^w  -- = v1 when v0 < 2^w (since v0/2^w = 0)
  soundness := fun _env v => by
    rw [Nat.mul_comm (v 1) (2^w), Nat.add_mul_div_left (v 0) (v 1) (Nat.two_pow_pos w)]
    omega

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Addition fusion rule
-- ══════════════════════════════════════════════════════════════════

/-- pack(a1,b1) + pack(a2,b2) = pack(a1+a2, b1+b2) when no carry. -/
def packFuseAddRule (w : Nat) : MixedSoundRule where
  name := s!"pack_fuse_add_{w}"
  -- lhs: (v0 + v2*2^w) + (v1 + v3*2^w)  [pack(v0,v2) + pack(v1,v3)]
  -- rhs: (v0+v1) + (v2+v3)*2^w           [pack(v0+v1, v2+v3)]
  lhsEval := fun _env v => (v 0 + v 2 * 2^w) + (v 1 + v 3 * 2^w)
  rhsEval := fun _env v => (v 0 + v 1) + (v 2 + v 3) * 2^w
  soundness := fun _env v => by simp [Nat.add_mul]; omega

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Rule collection
-- ══════════════════════════════════════════════════════════════════

/-- All Kronecker rules for width w. -/
def allKroneckerRules (w : Nat) : List MixedSoundRule :=
  [ unpackLoAfterPackRule w
  , unpackHiAfterPackRule w
  , packFuseAddRule w
  ]

theorem allKroneckerRules_length (w : Nat) : (allKroneckerRules w).length = 3 := rfl

theorem allKroneckerRules_sound (w : Nat) :
    ∀ r ∈ allKroneckerRules w, ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Smoke: unpack lo after pack. -/
example : (42 + 99 * 2^32) % 2^32 = 42 := by native_decide

/-- Smoke: unpack hi after pack. -/
example : (42 + 99 * 2^32) / 2^32 = 99 + 42 / 2^32 := by native_decide

/-- Smoke: addition fusion. -/
example : (10 + 20 * 2^32) + (5 + 3 * 2^32) = (15 + 23 * 2^32) := by native_decide

end AmoLean.EGraph.Verified.Bitwise.KroneckerRules
