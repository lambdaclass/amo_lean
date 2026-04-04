import AmoLean.EGraph.Verified.Bitwise.SolinasRuleGen

/-!
# AmoLean.EGraph.Verified.Bitwise.ReductionComposition

Proves that composing multiple modular reduction steps preserves correctness.

The key mathematical fact: if f(x) % p = x % p and g(x) % p = x % p,
then g(f(x)) % p = x % p. This is the foundation for multi-stage
reduction pipelines used in ZK-friendly field implementations (e.g.,
Goldilocks 128-bit to 64-bit to normalize).

## Key results

- `ReductionStep`: a reduction function bundled with its soundness proof
- `composeTwo`: compose two reduction steps into one
- `composeList`: compose a list of reduction steps
- `compose_sound`: master theorem — composed reductions preserve mod equivalence
- `fromFieldFoldRule`: convert any `FieldFoldRule` to a `ReductionStep`
- `goldilocks_two_stage`: concrete example of a two-stage Goldilocks pipeline

## References

- BitwiseBridge.lean: `fold_reduction_mod`, `mod_from_split`
- FieldFoldRules.lean: `FieldFoldRule`, `goldilocks_fold_rule`
- SolinasRuleGen.lean: `SolinasConfig`, `deriveFieldFoldRule`
-/

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise

/-! ## ReductionStep structure -/

/-- A single modular reduction step: a function with a soundness proof.
    Unlike `FieldFoldRule` (which carries bitwidth, spec, and side conditions),
    `ReductionStep` is minimal: just a function and the proof that it
    preserves the residue modulo `prime`. -/
structure ReductionStep where
  /-- Human-readable name for the reduction step -/
  name : String
  /-- The field prime modulus -/
  prime : Nat
  /-- The reduction function -/
  reduce : Nat → Nat
  /-- Soundness: the reduction preserves the residue modulo `prime` -/
  sound : ∀ (x : Nat), reduce x % prime = x % prime

/-! ## Core lemma: transitivity of mod-preserving functions -/

/-- If f preserves residues mod p and g preserves residues mod p,
    then g . f preserves residues mod p. -/
theorem mod_preserving_comp (f g : Nat → Nat) (p : Nat)
    (hf : ∀ x, f x % p = x % p)
    (hg : ∀ x, g x % p = x % p)
    (x : Nat) : g (f x) % p = x % p := by
  rw [hg (f x), hf x]

/-- Lift a soundness proof from one prime to another via equality. -/
theorem sound_of_prime_eq (s : ReductionStep) (p : Nat) (heq : s.prime = p) (x : Nat) :
    s.reduce x % p = x % p := by
  have := s.sound x; rw [heq] at this; exact this

/-! ## Composition of two steps -/

/-- Compose two reduction steps targeting the same prime.
    The resulting step applies `s1` first, then `s2`.
    Soundness follows by transitivity: s2(s1(x)) % p = s1(x) % p = x % p. -/
def composeTwo (s1 s2 : ReductionStep) (hp : s1.prime = s2.prime) : ReductionStep where
  name := s1.name ++ "+" ++ s2.name
  prime := s1.prime
  reduce := s2.reduce ∘ s1.reduce
  sound := fun x => by
    show (s2.reduce (s1.reduce x)) % s1.prime = x % s1.prime
    exact mod_preserving_comp s1.reduce s2.reduce s1.prime s1.sound
      (fun y => sound_of_prime_eq s2 s1.prime hp.symm y) x

/-- Composing two steps is sound: the result preserves the residue. -/
theorem composeTwo_sound (s1 s2 : ReductionStep) (hp : s1.prime = s2.prime) (x : Nat) :
    (composeTwo s1 s2 hp).reduce x % (composeTwo s1 s2 hp).prime = x % s1.prime :=
  (composeTwo s1 s2 hp).sound x

/-! ## Composition of a list of steps -/

/-- Compose a list of reduction steps all targeting prime `p`.
    The empty list yields the identity reduction.
    A cons applies the head first, then composes the tail.
    Returns a pair: the composed step and a proof its prime equals `p`. -/
def composeListAux (p : Nat) :
    (steps : List ReductionStep) → (∀ s ∈ steps, s.prime = p) →
    { r : ReductionStep // r.prime = p }
  | [], _ => ⟨{
      name := "id"
      prime := p
      reduce := id
      sound := fun _ => rfl
    }, rfl⟩
  | s :: rest, hp =>
    let rest_hp : ∀ r ∈ rest, r.prime = p :=
      fun r hr => hp r (List.mem_cons_of_mem s hr)
    let ⟨composed_rest, hcr_prime⟩ := composeListAux p rest rest_hp
    ⟨{ name := s.name ++ "+" ++ composed_rest.name
       prime := p
       reduce := composed_rest.reduce ∘ s.reduce
       sound := fun x => by
         show composed_rest.reduce (s.reduce x) % p = x % p
         exact mod_preserving_comp s.reduce composed_rest.reduce p
           (fun y => sound_of_prime_eq s p (hp s List.mem_cons_self) y)
           (fun y => sound_of_prime_eq composed_rest p hcr_prime y) x
     }, rfl⟩

/-- Compose a list of reduction steps all targeting prime `p`. -/
def composeList (p : Nat) (steps : List ReductionStep)
    (hp : ∀ s ∈ steps, s.prime = p) : ReductionStep :=
  (composeListAux p steps hp).val

/-- The prime of a composed list is `p`. -/
theorem composeList_prime (p : Nat) (steps : List ReductionStep)
    (hp : ∀ s ∈ steps, s.prime = p) :
    (composeList p steps hp).prime = p :=
  (composeListAux p steps hp).property

/-- **Master theorem**: composing any list of reduction steps targeting `p`
    preserves the residue modulo `p`. -/
theorem compose_sound (steps : List ReductionStep) (p : Nat)
    (hp : ∀ s ∈ steps, s.prime = p) (x : Nat) :
    (composeList p steps hp).reduce x % p = x % p :=
  sound_of_prime_eq (composeList p steps hp) p (composeList_prime p steps hp) x

/-- Composing a single step yields that step's reduction. -/
theorem composeList_singleton (s : ReductionStep) (p : Nat)
    (hp : ∀ r ∈ [s], r.prime = p) (x : Nat) :
    (composeList p [s] hp).reduce x = s.reduce x := rfl

/-- Composing two steps via list equals functional composition. -/
theorem composeList_two (s1 s2 : ReductionStep) (p : Nat)
    (hp : ∀ r ∈ [s1, s2], r.prime = p) (x : Nat) :
    (composeList p [s1, s2] hp).reduce x = s2.reduce (s1.reduce x) := rfl

/-! ## Conversion from FieldFoldRule -/

/-- Convert a `FieldFoldRule` with trivial side condition to a `ReductionStep`.
    Most ZK fold rules (Mersenne31, BabyBear, Goldilocks) have `sideCond = fun _ => True`
    and `specEval = fun x => x`, so this conversion is immediate. -/
def fromFieldFoldRule (rule : FieldFoldRule)
    (hspec : ∀ x, rule.specEval x = x)
    (hcond : ∀ x, rule.sideCond x) : ReductionStep where
  name := rule.name
  prime := rule.prime
  reduce := rule.foldEval
  sound := fun x => by
    have := rule.soundness x (hcond x)
    rw [hspec x] at this
    exact this

/-- Soundness of the conversion: the `ReductionStep` preserves the original guarantee. -/
theorem fromFieldFoldRule_sound (rule : FieldFoldRule)
    (hspec : ∀ x, rule.specEval x = x)
    (hcond : ∀ x, rule.sideCond x) (x : Nat) :
    (fromFieldFoldRule rule hspec hcond).reduce x % rule.prime = x % rule.prime :=
  (fromFieldFoldRule rule hspec hcond).sound x

/-! ## Concrete examples: Goldilocks two-stage pipeline -/

/-- Goldilocks first stage: fold from wide to ~65-bit.
    Uses the Solinas fold: (x >>> 64) * (2^32 - 1) + (x &&& (2^64 - 1)). -/
def goldilocks_stage1 : ReductionStep :=
  fromFieldFoldRule goldilocks_fold_rule (fun _ => rfl) (fun _ => trivial)

/-- Goldilocks second stage: fold again (handles overflow from stage 1).
    Same fold function applied again; still sound since fold % p = x % p. -/
def goldilocks_stage2 : ReductionStep :=
  fromFieldFoldRule goldilocks_fold_rule (fun _ => rfl) (fun _ => trivial)

/-- Goldilocks two-stage pipeline: compose two folds.
    After stage 1, the result may still be slightly above 2^64.
    Stage 2 folds again, bringing it into the normalized range. -/
def goldilocks_two_stage : ReductionStep :=
  composeTwo goldilocks_stage1 goldilocks_stage2 rfl

/-- The two-stage Goldilocks pipeline is sound. -/
theorem goldilocks_two_stage_sound (x : Nat) :
    goldilocks_two_stage.reduce x % goldilocks_two_stage.prime = x % goldilocks_prime :=
  goldilocks_two_stage.sound x

/-! ## BabyBear multi-stage pipeline -/

/-- BabyBear single-stage reduction from Solinas config. -/
def babybear_stage : ReductionStep :=
  fromFieldFoldRule (deriveFieldFoldRule babybear_solinas) (fun _ => rfl) (fun _ => trivial)

/-- BabyBear two-stage pipeline: two folds compose correctly. -/
def babybear_two_stage : ReductionStep :=
  composeTwo babybear_stage babybear_stage rfl

/-- BabyBear two-stage is sound. -/
theorem babybear_two_stage_sound (x : Nat) :
    babybear_two_stage.reduce x % babybear_two_stage.prime = x % babybear_solinas.prime :=
  babybear_two_stage.sound x

/-! ## Heterogeneous pipeline: Solinas + hardcoded compose -/

/-- The Solinas-generated Goldilocks rule produces the same `ReductionStep`
    as the hardcoded one (both use the same fold function). -/
theorem solinas_goldilocks_eq_hardcoded (x : Nat) :
    (fromFieldFoldRule goldilocks_solinas_rule (fun _ => rfl) (fun _ => trivial)).reduce x =
    goldilocks_stage1.reduce x := rfl

/-- A three-stage pipeline using `composeList` is sound. -/
theorem three_stage_sound (s1 s2 s3 : ReductionStep) (p : Nat)
    (hp : ∀ s ∈ [s1, s2, s3], s.prime = p) (x : Nat) :
    (composeList p [s1, s2, s3] hp).reduce x % p = x % p :=
  compose_sound [s1, s2, s3] p hp x

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity: composeTwo with concrete steps produces correct results.
    Uses x = 2^65 + 42 which exercises the Goldilocks fold (hi part nonzero). -/
example : goldilocks_two_stage.reduce (2 ^ 65 + 42) %
    goldilocks_two_stage.prime =
    (2 ^ 65 + 42) % goldilocks_prime :=
  goldilocks_two_stage.sound (2 ^ 65 + 42)

/-- Non-vacuity: BabyBear two-stage with a value exceeding 2^31. -/
example : babybear_two_stage.reduce (2 ^ 32 + 7) %
    babybear_two_stage.prime =
    (2 ^ 32 + 7) % babybear_solinas.prime :=
  babybear_two_stage.sound (2 ^ 32 + 7)

/-- Non-vacuity: composeList with empty list is the identity. -/
example : (composeList goldilocks_prime []
    (fun _ h => nomatch h)).reduce 999 = 999 := rfl

/-- Non-vacuity: compose_sound master theorem with concrete three-step pipeline. -/
example : let steps := [goldilocks_stage1, goldilocks_stage2, goldilocks_stage1]
    let hp : ∀ s ∈ steps, s.prime = goldilocks_prime := by
      intro s hs
      simp only [steps, List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | h
      · rfl
      · rfl
      · rfl
      · exact absurd h (by simp)
    (composeList goldilocks_prime steps hp).reduce (2 ^ 70) % goldilocks_prime =
    (2 ^ 70) % goldilocks_prime :=
  by rfl

/-! ## Smoke tests -/

#eval goldilocks_two_stage.reduce 100  -- small input: fold is basically id
#eval goldilocks_two_stage.reduce (2 ^ 65 + 42)  -- exercises the fold
#eval babybear_two_stage.reduce (2 ^ 32 + 7)

end AmoLean.EGraph.Verified.Bitwise
