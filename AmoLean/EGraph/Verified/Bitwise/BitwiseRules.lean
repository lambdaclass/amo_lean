import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge

/-!
# AmoLean.EGraph.Verified.Bitwise.BitwiseRules

Sound rewrite rules for GENERIC bitwise identities (not field-specific).
Each `MixedSoundRule` bundles an identity name, LHS/RHS evaluation functions
over `MixedEnv` and a valuation, and a soundness proof that LHS = RHS
for all environments and valuations.

## Rules (10 total)

### Shift composition (2)
- `shift_shift_compose_right`: (x >>> a) >>> b = x >>> (a + b)
- `shift_shift_compose_left`:  (x <<< a) <<< b = x <<< (a + b)

### Bitwise identities (5)
- `and_self_eq`:   x &&& x = x
- `and_comm_rule`: x &&& y = y &&& x
- `or_comm_rule`:  x ||| y = y ||| x
- `xor_self_zero`: x ^^^ x = 0
- `xor_comm_rule`: x ^^^ y = y ^^^ x

### Bridge rules (3)
- `mask_mod_bridge_rule`:       x &&& (2^n - 1) = x % 2^n
- `shiftRight_div_bridge_rule`: x >>> n = x / 2^n
- `shiftLeft_mul_bridge_rule`:  x <<< n = x * 2^n

## Design

Parallel to `SoundRewriteRule` (which works with `CircuitNodeOp` + `Expr Int`),
`MixedSoundRule` operates at the `MixedNodeOp` + `Nat` level. The soundness
field is a universally quantified equality over all environments and valuations.
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.Verified (EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: MixedSoundRule structure
-- ══════════════════════════════════════════════════════════════════

/-- A sound rewrite rule for `MixedNodeOp`: LHS and RHS evaluate to the same `Nat`
    for every environment and valuation. This is the bitwise analogue of
    `SoundRewriteRule` from `AmoLean.EGraph.Verified.SoundRewriteRule`. -/
structure MixedSoundRule where
  /-- Human-readable name of the rule. -/
  name : String
  /-- Evaluate the LHS pattern given an environment and e-class valuation. -/
  lhsEval : MixedEnv → (EClassId → Nat) → Nat
  /-- Evaluate the RHS pattern given an environment and e-class valuation. -/
  rhsEval : MixedEnv → (EClassId → Nat) → Nat
  /-- Soundness: LHS and RHS agree on every environment and valuation. -/
  soundness : ∀ (env : MixedEnv) (v : EClassId → Nat), lhsEval env v = rhsEval env v

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Shift composition rules
-- ══════════════════════════════════════════════════════════════════

/-- `(x >>> a) >>> b = x >>> (a + b)` — right shift composition.
    Uses `Nat.shiftRight_add`. -/
def shift_shift_compose_right (a b : Nat) : MixedSoundRule where
  name := "shift_right_compose"
  lhsEval := fun _env v => (v 0 >>> a) >>> b
  rhsEval := fun _env v => v 0 >>> (a + b)
  soundness := fun _env v => (Nat.shiftRight_add (v 0) a b).symm

/-- `(x <<< a) <<< b = x <<< (a + b)` — left shift composition.
    Uses `Nat.shiftLeft_add`. -/
def shift_shift_compose_left (a b : Nat) : MixedSoundRule where
  name := "shift_left_compose"
  lhsEval := fun _env v => (v 0 <<< a) <<< b
  rhsEval := fun _env v => v 0 <<< (a + b)
  soundness := fun _env v => (Nat.shiftLeft_add (v 0) a b).symm

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Pure bitwise identities
-- ══════════════════════════════════════════════════════════════════

/-- `x &&& x = x` — AND is idempotent.
    Uses `Nat.and_self`. -/
def and_self_eq : MixedSoundRule where
  name := "and_self"
  lhsEval := fun _env v => Nat.land (v 0) (v 0)
  rhsEval := fun _env v => v 0
  soundness := fun _env v => Nat.and_self (v 0)

/-- `x &&& y = y &&& x` — AND is commutative.
    Uses `Nat.land_comm`. -/
def and_comm_rule : MixedSoundRule where
  name := "and_comm"
  lhsEval := fun _env v => Nat.land (v 0) (v 1)
  rhsEval := fun _env v => Nat.land (v 1) (v 0)
  soundness := fun _env v => Nat.land_comm (v 0) (v 1)

/-- `x ||| y = y ||| x` — OR is commutative.
    Uses `Nat.lor_comm`. -/
def or_comm_rule : MixedSoundRule where
  name := "or_comm"
  lhsEval := fun _env v => Nat.lor (v 0) (v 1)
  rhsEval := fun _env v => Nat.lor (v 1) (v 0)
  soundness := fun _env v => Nat.lor_comm (v 0) (v 1)

/-- `x ^^^ x = 0` — XOR with self is zero.
    Uses `Nat.xor_self`. -/
def xor_self_zero : MixedSoundRule where
  name := "xor_self_zero"
  lhsEval := fun _env v => Nat.xor (v 0) (v 0)
  rhsEval := fun _env _v => 0
  soundness := fun _env v => Nat.xor_self (v 0)

/-- `x ^^^ y = y ^^^ x` — XOR is commutative.
    Uses `Nat.xor_comm`. -/
def xor_comm_rule : MixedSoundRule where
  name := "xor_comm"
  lhsEval := fun _env v => Nat.xor (v 0) (v 1)
  rhsEval := fun _env v => Nat.xor (v 1) (v 0)
  soundness := fun _env v => Nat.xor_comm (v 0) (v 1)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Bridge rules (bitwise ↔ arithmetic)
-- ══════════════════════════════════════════════════════════════════

/-- `x &&& (2^n - 1) = x % 2^n` — mask equals modular reduction.
    Uses `mask_eq_mod` from BitwiseBridge. -/
def mask_mod_bridge_rule (n : Nat) : MixedSoundRule where
  name := "mask_mod_bridge"
  lhsEval := fun _env v => Nat.land (v 0) (2 ^ n - 1)
  rhsEval := fun _env v => v 0 % 2 ^ n
  soundness := fun _env v => mask_eq_mod (v 0) n

/-- `x >>> n = x / 2^n` — right shift equals division by power of two.
    Uses `shiftRight_eq_div_pow` from BitwiseBridge. -/
def shiftRight_div_bridge_rule (n : Nat) : MixedSoundRule where
  name := "shiftRight_div_bridge"
  lhsEval := fun _env v => v 0 >>> n
  rhsEval := fun _env v => v 0 / 2 ^ n
  soundness := fun _env v => shiftRight_eq_div_pow (v 0) n

/-- `x <<< n = x * 2^n` — left shift equals multiplication by power of two.
    Uses `shiftLeft_eq_mul_pow` from BitwiseBridge. -/
def shiftLeft_mul_bridge_rule (n : Nat) : MixedSoundRule where
  name := "shiftLeft_mul_bridge"
  lhsEval := fun _env v => v 0 <<< n
  rhsEval := fun _env v => v 0 * 2 ^ n
  soundness := fun _env v => shiftLeft_eq_mul_pow (v 0) n

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Rule collection and master soundness
-- ══════════════════════════════════════════════════════════════════

/-- All generic bitwise rewrite rules (parameterized rules use default n=8, a=4, b=4).
    Field-specific rules (e.g., Goldilocks folding) are defined separately. -/
def allBitwiseRules : List MixedSoundRule :=
  [ shift_shift_compose_right 4 4     -- (x >>> 4) >>> 4 = x >>> 8
  , shift_shift_compose_left 4 4      -- (x <<< 4) <<< 4 = x <<< 8
  , and_self_eq                        -- x &&& x = x
  , and_comm_rule                      -- x &&& y = y &&& x
  , or_comm_rule                       -- x ||| y = y ||| x
  , xor_self_zero                      -- x ^^^ x = 0
  , xor_comm_rule                      -- x ^^^ y = y ^^^ x
  , mask_mod_bridge_rule 8             -- x &&& 0xFF = x % 256
  , shiftRight_div_bridge_rule 8       -- x >>> 8 = x / 256
  , shiftLeft_mul_bridge_rule 8        -- x <<< 8 = x * 256
  ]

/-- Length witness for `allBitwiseRules`. -/
theorem allBitwiseRules_length : allBitwiseRules.length = 10 := rfl

/-- **Master soundness**: every rule in the collection preserves evaluation equality.
    Follows directly from each rule's `soundness` field. -/
theorem allBitwiseRules_sound :
    ∀ r ∈ allBitwiseRules, ∀ (env : MixedEnv) (v : EClassId → Nat),
      r.lhsEval env v = r.rhsEval env v :=
  fun r _hmem env v => r.soundness env v

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Individual rule name witnesses
-- ══════════════════════════════════════════════════════════════════

theorem shift_right_compose_name_eq :
    (shift_shift_compose_right 4 4).name = "shift_right_compose" := rfl

theorem shift_left_compose_name_eq :
    (shift_shift_compose_left 4 4).name = "shift_left_compose" := rfl

theorem and_self_name_eq : and_self_eq.name = "and_self" := rfl

theorem and_comm_name_eq : and_comm_rule.name = "and_comm" := rfl

theorem or_comm_name_eq : or_comm_rule.name = "or_comm" := rfl

theorem xor_self_zero_name_eq : xor_self_zero.name = "xor_self_zero" := rfl

theorem xor_comm_name_eq : xor_comm_rule.name = "xor_comm" := rfl

theorem mask_mod_bridge_name_eq :
    (mask_mod_bridge_rule 8).name = "mask_mod_bridge" := rfl

theorem shiftRight_div_bridge_name_eq :
    (shiftRight_div_bridge_rule 8).name = "shiftRight_div_bridge" := rfl

theorem shiftLeft_mul_bridge_name_eq :
    (shiftLeft_mul_bridge_rule 8).name = "shiftLeft_mul_bridge" := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke tests — non-vacuity witnesses
-- ══════════════════════════════════════════════════════════════════

/-- Smoke test: right shift composition on concrete values. -/
example : (256 >>> 4) >>> 4 = 256 >>> 8 := rfl

/-- Smoke test: left shift composition on concrete values. -/
example : (1 <<< 4) <<< 4 = 1 <<< 8 := rfl

/-- Smoke test: AND idempotence. -/
example : Nat.land 42 42 = 42 := by native_decide

/-- Smoke test: XOR self = 0. -/
example : Nat.xor 12345 12345 = 0 := by native_decide

/-- Smoke test: mask bridge (8-bit). -/
example : Nat.land 0x1FF 0xFF = 0x1FF % 256 := by native_decide

/-- Smoke test: shift-right bridge. -/
example : 1024 >>> 8 = 1024 / 256 := by native_decide

/-- Smoke test: shift-left bridge. -/
example : 3 <<< 8 = 3 * 256 := by native_decide

/-- Smoke test: allBitwiseRules collection is non-empty. -/
example : allBitwiseRules.length > 0 := by native_decide

end AmoLean.EGraph.Verified.Bitwise
