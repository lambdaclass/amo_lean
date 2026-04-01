import AmoLean.EGraph.Verified.Bitwise.BitwiseRules
import AmoLean.EGraph.Verified.Bitwise.BitwiseBridge

/-!
# AmoLean.EGraph.Verified.Bitwise.Discovery.BitwiseVocabulary

Parametric bitwise rule TEMPLATES for the spec-driven reduction discovery
pipeline (Fase 26, N26.2). Each template takes parameters (prime, word width,
constants) and produces a `MixedSoundRule` with proven soundness on Nat.

## Templates (8 total)

### Shift / mask (2)
- `shiftDecompTemplate k`: x = (x >>> k) * 2^k + (x &&& (2^k - 1))
- `maskModTemplate w`:     x &&& (2^w - 1) = x % 2^w

### Reduction equivalences (3)
- `harveyEquivTemplate p`:      harveyReduce semantics = reduceGate semantics
- `barrettEquivTemplate p m`:   barrettReduce semantics = reduceGate semantics
- `montgomeryEquivTemplate p mu`: montyReduce semantics = reduceGate semantics

### Modular arithmetic (3)
- `addModTemplate p`:          (a + b) % p = ((a % p) + (b % p)) % p
- `mulModTemplate p`:          (a * b) % p = ((a % p) * (b % p)) % p
- `modIdempotentTemplate p`:   (x % p) % p = x % p

## Design

Templates are parametric: `generateVocabulary` instantiates them for a given
prime/width, producing the full vocabulary for the discovery saturation engine.
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Discovery

open AmoLean.EGraph.Verified.Bitwise (MixedSoundRule MixedEnv mask_eq_mod
  shiftRight_eq_div_pow shiftLeft_eq_mul_pow)
open AmoLean.EGraph.Verified (EClassId)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Shift and mask templates
-- ══════════════════════════════════════════════════════════════════

/-- **Shift decomposition**: `x = (x >>> k) * 2^k + (x &&& (2^k - 1))`.
    Fundamental identity underlying all modular reduction algorithms.
    Proof chain: shiftRight_eq_div_pow → mask_eq_mod → Nat.div_add_mod'. -/
def shiftDecompTemplate (k : Nat) : MixedSoundRule where
  name := s!"shift_decomp_{k}"
  lhsEval := fun _env v => v 0
  rhsEval := fun _env v => (v 0 >>> k) * 2 ^ k + Nat.land (v 0) (2 ^ k - 1)
  soundness := fun _env v => by
    show v 0 = (v 0 >>> k) * 2 ^ k + (v 0 &&& (2 ^ k - 1))
    rw [shiftRight_eq_div_pow, mask_eq_mod]
    exact (Nat.div_add_mod' (v 0) (2 ^ k)).symm

/-- **Mask modulo**: `x &&& (2^w - 1) = x % 2^w`.
    Wrapper around `mask_eq_mod` from BitwiseBridge. -/
def maskModTemplate (w : Nat) : MixedSoundRule where
  name := s!"mask_mod_{w}"
  lhsEval := fun _env v => Nat.land (v 0) (2 ^ w - 1)
  rhsEval := fun _env v => v 0 % 2 ^ w
  soundness := fun _env v => mask_eq_mod (v 0) w

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Reduction equivalence templates
-- ══════════════════════════════════════════════════════════════════

/-- **Harvey equivalence**: `harveyReduce(x, p)` semantically equals
    `reduceGate(x, p)` — both evaluate to `v 0 % p` at the Nat level.
    The MixedNodeOp semantics defines harveyReduce to evaluate to `v a % p`. -/
def harveyEquivTemplate (p : Nat) : MixedSoundRule where
  name := s!"harvey_equiv_{p}"
  lhsEval := fun _env v => v 0 % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env _v => rfl

/-- **Barrett equivalence**: `barrettReduce(x, p, m)` semantically equals
    `reduceGate(x, p)` — both evaluate to `v 0 % p` at the Nat level. -/
def barrettEquivTemplate (p m : Nat) : MixedSoundRule where
  name := s!"barrett_equiv_{p}_{m}"
  lhsEval := fun _env v => v 0 % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env _v => rfl

/-- **Montgomery equivalence**: `montyReduce(x, p, mu)` semantically equals
    `reduceGate(x, p)` — both evaluate to `v 0 % p` at the Nat level. -/
def montgomeryEquivTemplate (p mu : Nat) : MixedSoundRule where
  name := s!"montgomery_equiv_{p}_{mu}"
  lhsEval := fun _env v => v 0 % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env _v => rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Modular arithmetic templates
-- ══════════════════════════════════════════════════════════════════

/-- **Modular addition**: `(a + b) % p = ((a % p) + (b % p)) % p`.
    Uses `Nat.add_mod` from Lean core. -/
def addModTemplate (p : Nat) : MixedSoundRule where
  name := s!"add_mod_{p}"
  lhsEval := fun _env v => (v 0 + v 1) % p
  rhsEval := fun _env v => (v 0 % p + v 1 % p) % p
  soundness := fun _env v => Nat.add_mod (v 0) (v 1) p

/-- **Modular multiplication**: `(a * b) % p = ((a % p) * (b % p)) % p`.
    Uses `Nat.mul_mod` from Lean core. -/
def mulModTemplate (p : Nat) : MixedSoundRule where
  name := s!"mul_mod_{p}"
  lhsEval := fun _env v => (v 0 * v 1) % p
  rhsEval := fun _env v => (v 0 % p * (v 1 % p)) % p
  soundness := fun _env v => Nat.mul_mod (v 0) (v 1) p

/-- **Mod idempotence**: `(x % p) % p = x % p`.
    Uses `Nat.mod_mod` from Lean core. -/
def modIdempotentTemplate (p : Nat) : MixedSoundRule where
  name := s!"mod_idempotent_{p}"
  lhsEval := fun _env v => (v 0 % p) % p
  rhsEval := fun _env v => v 0 % p
  soundness := fun _env v => Nat.mod_mod (v 0) p

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Vocabulary builder
-- ══════════════════════════════════════════════════════════════════

/-- Generate all vocabulary rules for a given prime and word width.
    Includes shift decompositions at key widths, mask-mod bridges,
    reduction equivalences, and modular arithmetic identities. -/
def generateVocabulary (p w : Nat) (barrettM montyMu : Nat) : List MixedSoundRule :=
  [ shiftDecompTemplate 1
  , shiftDecompTemplate w
  , shiftDecompTemplate (w / 2)
  , maskModTemplate w
  , maskModTemplate (w / 2)
  , harveyEquivTemplate p
  , barrettEquivTemplate p barrettM
  , montgomeryEquivTemplate p montyMu
  , addModTemplate p
  , mulModTemplate p
  , modIdempotentTemplate p
  ]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Master soundness
-- ══════════════════════════════════════════════════════════════════

/-- Length witness for `generateVocabulary`. -/
theorem generateVocabulary_length (p w barrettM montyMu : Nat) :
    (generateVocabulary p w barrettM montyMu).length = 11 := rfl

/-- **Master soundness**: every rule in the vocabulary preserves evaluation
    equality. Follows directly from each rule's `soundness` field. -/
theorem generateVocabulary_all_sound (p w barrettM montyMu : Nat) :
    ∀ r ∈ generateVocabulary p w barrettM montyMu,
      ∀ env v, r.lhsEval env v = r.rhsEval env v :=
  fun r _ env v => r.soundness env v

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

private def vocabTestEnv : MixedEnv :=
  { constVal := fun _ => 0, witnessVal := fun _ => 0, pubInputVal := fun _ => 0 }

-- Shift decomposition for k=8: x = (x >> 8) * 256 + (x & 255)
-- 1000 = (1000 >>> 8) * 256 + (1000 &&& 255) = 3 * 256 + 232 = 1000
example : (shiftDecompTemplate 8).lhsEval vocabTestEnv (fun _ => 1000) = 1000 := by native_decide

example : (shiftDecompTemplate 8).rhsEval vocabTestEnv (fun _ => 1000) = 1000 := by native_decide

-- Mask mod for w=8: 1000 &&& 255 = 1000 % 256 = 232
example : (maskModTemplate 8).lhsEval vocabTestEnv (fun _ => 1000) = 232 := by native_decide

example : (maskModTemplate 8).rhsEval vocabTestEnv (fun _ => 1000) = 232 := by native_decide

-- Modular addition: (100 + 200) % 97 = ((100 % 97) + (200 % 97)) % 97 = 9
example : (addModTemplate 97).lhsEval vocabTestEnv (fun | 0 => 100 | 1 => 200 | _ => 0)
    = 9 := by native_decide

example : (addModTemplate 97).rhsEval vocabTestEnv (fun | 0 => 100 | 1 => 200 | _ => 0)
    = 9 := by native_decide

-- Modular multiplication: (10 * 20) % 97 = ((10 % 97) * (20 % 97)) % 97 = 6
example : (mulModTemplate 97).lhsEval vocabTestEnv (fun | 0 => 10 | 1 => 20 | _ => 0)
    = 6 := by native_decide

-- Mod idempotence: (1000 % 97) % 97 = 1000 % 97 = 30
example : (modIdempotentTemplate 97).lhsEval vocabTestEnv (fun _ => 1000) = 30 := by native_decide

example : (modIdempotentTemplate 97).rhsEval vocabTestEnv (fun _ => 1000) = 30 := by native_decide

-- Vocabulary has 11 rules for BabyBear
example : (generateVocabulary 2013265921 32 0 0).length = 11 := by native_decide

-- Vocabulary has > 0 rules (non-emptiness)
example : (generateVocabulary 2013265921 32 0 0).length > 0 := by native_decide

-- Goldilocks vocabulary also has 11 rules
example : (generateVocabulary (2^64 - 2^32 + 1) 64 0 0).length = 11 := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.Discovery
