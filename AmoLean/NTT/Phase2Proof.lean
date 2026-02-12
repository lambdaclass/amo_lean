/-
  Phase 2: Lazy Butterfly Simulation Proofs

  S5: lazy_butterfly_fst_simulates
  S6: lazy_butterfly_snd_simulates
  S7: lazy_butterfly_sum
-/

import AmoLean.NTT.Bounds
import Mathlib.Tactic

namespace AmoLean.NTT.Phase2Proof

open LazyGoldilocks

-- Shorthand for the prime
abbrev P := GOLDILOCKS_PRIME

-- Basic facts about P
private theorem p_pos : P > 0 := by native_decide

/-!
## Helper lemmas for modular arithmetic
-/

-- Helper: x % P % P = x % P
lemma mod_mod_self (x : Nat) : (x % P) % P = x % P := Nat.mod_mod x P

-- Helper: (x * y) % P = ((x % P) * y) % P (partial reduction on first arg)
lemma mul_mod_left (x y : Nat) : (x * y) % P = ((x % P) * y) % P := by
  have h := Nat.mul_mod x y P
  -- h: (x * y) % P = ((x % P) * (y % P)) % P
  rw [h]
  -- Goal: (x % P * (y % P)) % P = (x % P * y) % P
  -- Use Nat.mul_mod in reverse on RHS
  rw [Nat.mul_mod (x % P) y P]
  -- Goal: (x % P * (y % P)) % P = (x % P % P * (y % P)) % P
  rw [mod_mod_self]

/-!
## S5: lazy_butterfly_fst_simulates

Goal: (a + (b * tw) % P) % P = ((a % P) + ((b % P) * tw) % P) % P
-/

lemma fst_mod_eq (a b tw : Nat) :
    (a + (b * tw) % P) % P = ((a % P) + ((b % P) * tw) % P) % P := by
  -- Use Nat.add_mod on both sides
  rw [Nat.add_mod a ((b * tw) % P) P]
  rw [Nat.add_mod (a % P) (((b % P) * tw) % P) P]
  -- Simplify nested mods
  rw [mod_mod_self, mod_mod_self, mod_mod_self]
  -- Show (b * tw) % P = ((b % P) * tw) % P
  rw [mul_mod_left]

/-!
## S6: lazy_butterfly_snd_simulates

Goal: (a + 2*P - (b * tw) % P) % P = ((a % P) + P - ((b % P) * tw) % P) % P
-/

-- Helper: (a + 2*P - t) % P = ((a % P) + P - t) % P when t < P
lemma snd_mod_eq_helper (a t : Nat) (ht : t < P) :
    (a + 2 * P - t) % P = ((a % P) + P - t) % P := by
  -- (a + 2P - t) = a + P + (P - t) since t < P ≤ 2P
  have h_split : a + 2 * P - t = a + P + (P - t) := by omega
  rw [h_split]

  -- (a + P + (P - t)) % P = ((a + P) % P + (P - t) % P) % P
  rw [Nat.add_mod (a + P) (P - t) P]

  -- (a + P) % P = a % P
  have h_ap : (a + P) % P = a % P := by
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  rw [h_ap]

  -- Case split on t = 0
  by_cases ht0 : t = 0
  · -- Case t = 0
    subst ht0
    -- Goal: (a % P + (P - 0) % P) % P = ((a % P) + P - 0) % P
    -- Both sides simplify to a % P
    have lhs_simp : (a % P + (P - 0) % P) % P = a % P := by
      rw [Nat.sub_zero, Nat.mod_self, Nat.add_zero, mod_mod_self]
    have rhs_simp : ((a % P) + P - 0) % P = a % P := by
      rw [Nat.sub_zero, Nat.add_mod, mod_mod_self, Nat.mod_self, Nat.add_zero, mod_mod_self]
    rw [lhs_simp, rhs_simp]
  · -- Case t > 0
    have ht_pos : t > 0 := Nat.pos_of_ne_zero ht0
    have h_pt_lt : P - t < P := Nat.sub_lt p_pos ht_pos
    rw [Nat.mod_eq_of_lt h_pt_lt]
    -- Goal: (a % P + (P - t)) % P = ((a % P) + P - t) % P
    -- (a % P) + P - t = (a % P) + (P - t) since t < P and a % P < P
    have ha_lt : a % P < P := Nat.mod_lt a p_pos
    have h_eq : (a % P) + P - t = (a % P) + (P - t) := by omega
    rw [h_eq]

-- Main lemma for S6
lemma snd_mod_eq (a b tw : Nat) :
    (a + 2 * P - (b * tw) % P) % P = ((a % P) + P - ((b % P) * tw) % P) % P := by
  -- (b * tw) % P < P
  have ht : (b * tw) % P < P := Nat.mod_lt (b * tw) p_pos
  -- Apply helper
  have h1 := snd_mod_eq_helper a ((b * tw) % P) ht
  rw [h1]
  -- Use mul_mod_left
  rw [mul_mod_left]

/-!
## S7: lazy_butterfly_sum

Goal: ((a + t) % P + (a + 2*P - t) % P) % P = (2 * (a % P)) % P
where t = (b * twiddle) % P < P
-/

-- Key: (x % P + y % P) % P = (x + y) % P
lemma add_mod_mod (x y : Nat) : (x % P + y % P) % P = (x + y) % P := by
  -- Nat.add_mod: (x + y) % P = (x % P + y % P) % P
  -- We need the symmetric version
  rw [← Nat.add_mod x y P]

-- Key: (2*a) % P = (2 * (a % P)) % P
lemma double_mod (a : Nat) : (2 * a) % P = (2 * (a % P)) % P := by
  rw [Nat.mul_mod 2 a P, Nat.mul_mod 2 (a % P) P, mod_mod_self]

-- The sum: (a + t) + (a + 2*P - t) = 2*a + 2*P when t ≤ a + 2*P
lemma butterfly_sum_nat (a t : Nat) (ht : t ≤ a + 2 * P) :
    (a + t) + (a + 2 * P - t) = 2 * a + 2 * P := by
  omega

-- (2*a + 2*P) % P = (2*a) % P
lemma double_plus_double_p_mod (a : Nat) : (2 * a + 2 * P) % P = (2 * a) % P := by
  -- 2*P = P + P, so 2*a + 2*P = 2*a + P + P
  have h : 2 * P = P + P := by ring
  rw [h]
  -- (2*a + P + P) % P = ((2*a + P) + P) % P
  rw [← Nat.add_assoc]
  -- Use: (x + P) % P = x % P (from Nat.add_mod_right)
  rw [Nat.add_mod_right]
  -- Goal: (2*a + P) % P = (2*a) % P
  rw [Nat.add_mod_right]

-- Main lemma for S7: sum of reduced outputs equals 2a mod P
-- Given t < P (result of mulReduce), we have t ≤ a + 2P trivially
lemma butterfly_sum_mod (a : Nat) (t : Nat) (ht : t < P) :
    ((a + t) % P + (a + 2 * P - t) % P) % P = (2 * (a % P)) % P := by
  -- Step 1: Use add_mod_mod
  rw [add_mod_mod]
  -- Goal: ((a + t) + (a + 2*P - t)) % P = (2 * (a % P)) % P
  -- Step 2: Simplify the sum
  have ht_le : t ≤ a + 2 * P := by
    have hp : P > 0 := p_pos
    omega
  rw [butterfly_sum_nat a t ht_le]
  -- Goal: (2*a + 2*P) % P = (2 * (a % P)) % P
  rw [double_plus_double_p_mod]
  -- Goal: (2*a) % P = (2 * (a % P)) % P
  rw [double_mod]

/-!
## Verification
-/

#check fst_mod_eq
#check snd_mod_eq
#check butterfly_sum_mod

end AmoLean.NTT.Phase2Proof
