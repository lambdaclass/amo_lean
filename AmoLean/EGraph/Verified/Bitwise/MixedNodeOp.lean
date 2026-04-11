import AmoLean.EGraph.VerifiedExtraction.Core
import AmoLean.EGraph.Verified.Core
import AmoLean.EGraph.Verified.SemanticSpec

/-!
# AmoLean.EGraph.Verified.Bitwise.MixedNodeOp

Combined algebraic + bitwise operation type for the E-graph engine.
MixedNodeOp is a SEPARATE inductive from CircuitNodeOp to preserve
all 121 existing theorems.

## Design decisions

- 13 constructors: 7 algebraic (mirror CircuitNodeOp) + 6 bitwise
- Evaluated on Nat (concrete, no typeclass for bitwise)
- Field bridge via toZMod comes AFTER extraction
- Cost model: mul = 1, shift/and/or/xor = 0 (extensible)

## References

- Fase 21 (v3.1.0) in ARCHITECTURE.md
- BitwiseLean library (~/Documents/claudio/bitwiselean/)
- CircuitAdaptor.lean (template pattern)
-/

namespace AmoLean.EGraph.Verified.Bitwise

open AmoLean.EGraph.VerifiedExtraction
open AmoLean.EGraph.Verified (CircuitNodeOp CircuitEnv EClassId)

/-! ## MixedNodeOp: Combined Algebraic + Bitwise Operations -/

/-- Mixed operation type combining algebraic circuit gates with bitwise operations.
    Each algebraic constructor mirrors CircuitNodeOp exactly.
    Bitwise constructors operate at the Nat level (shifts, masks, logical ops). -/
inductive MixedNodeOp where
  /-- Constant gate (algebraic) -/
  | constGate  : Nat → MixedNodeOp
  /-- Witness variable (algebraic) -/
  | witness    : Nat → MixedNodeOp
  /-- Public input (algebraic) -/
  | pubInput   : Nat → MixedNodeOp
  /-- Addition gate (algebraic) -/
  | addGate    : EClassId → EClassId → MixedNodeOp
  /-- Multiplication gate (algebraic) -/
  | mulGate    : EClassId → EClassId → MixedNodeOp
  /-- Negation gate (algebraic, evaluates to 0 on Nat — placeholder for structural compat) -/
  | negGate    : EClassId → MixedNodeOp
  /-- Scalar multiplication gate (algebraic) -/
  | smulGate   : Nat → EClassId → MixedNodeOp
  /-- Left shift: x <<< n = x * 2^n -/
  | shiftLeft  : EClassId → Nat → MixedNodeOp
  /-- Right shift: x >>> n = x / 2^n -/
  | shiftRight : EClassId → Nat → MixedNodeOp
  /-- Bitwise AND: x &&& y -/
  | bitAnd     : EClassId → EClassId → MixedNodeOp
  /-- Bitwise XOR: x ^^^ y -/
  | bitXor     : EClassId → EClassId → MixedNodeOp
  /-- Bitwise OR: x ||| y -/
  | bitOr      : EClassId → EClassId → MixedNodeOp
  /-- Constant mask: 2^n - 1 (no children, used for AND masking) -/
  | constMask  : Nat → MixedNodeOp
  /-- Subtraction gate: a - b (Nat truncated: 0 if a < b) -/
  | subGate    : EClassId → EClassId → MixedNodeOp
  /-- Modular reduction: child % p -/
  | reduceGate : EClassId → Nat → MixedNodeOp
  /-- Kronecker pack: a + b * 2^w (pack two field elements in one word) -/
  | kronPack   : EClassId → EClassId → Nat → MixedNodeOp
  /-- Kronecker unpack low: child % 2^w (extract low element) -/
  | kronUnpackLo : EClassId → Nat → MixedNodeOp
  /-- Kronecker unpack high: child / 2^w (extract high element) -/
  | kronUnpackHi : EClassId → Nat → MixedNodeOp
  -- ═══ Modular reduction alternatives (Fase 22+) ═══
  /-- Montgomery REDC: montyReduce(x, p, mu) where mu = p^{-1} mod 2^32.
      Evaluates to: ((x - (x * mu % 2^32) * p) / 2^32) % p
      Verified: monty_reduce_spec in AmoLean/Field/Montgomery.lean -/
  | montyReduce : EClassId → Nat → Nat → MixedNodeOp
  /-- Barrett reduction: barrettReduce(x, p, m) where m ≈ 2^k / p.
      Evaluates to: x - (x * m / 2^k) * p, then conditional subtract.
      Verified: barrett_reduce_correct in BitwiseLean/Barrett.lean -/
  | barrettReduce : EClassId → Nat → Nat → MixedNodeOp
  /-- Harvey conditional subtraction: harveyReduce(x, p).
      If x >= 2p: x - 2p. If x >= p: x - p. Else: x.
      Output in [0, 2p) for input in [0, 4p).
      Verified: harveyReduce_mod, harveyReduce_bound in LazyReductionSpike_aux.lean -/
  | harveyReduce : EClassId → Nat → MixedNodeOp
  /-- Conditional subtraction: conditionalSub(x, p).
      If x >= p: x - p. Else: x. Output in [0, p) for input in [0, 2p).
      Simpler than harveyReduce (1 branch vs 3), selected by bound-aware
      discovery (F3) when boundK ≤ 2 guarantees input < 2p.
      Semantics: if v a >= p then v a - p else v a -/
  | conditionalSub : EClassId → Nat → MixedNodeOp
  deriving Repr, DecidableEq

instance : BEq MixedNodeOp := instBEqOfDecidableEq

instance : Inhabited MixedNodeOp := ⟨.constGate 0⟩

/-! ## NodeOps helper functions -/

/-- Extract e-class children from a mixed operation. -/
@[simp] def mixedChildren : MixedNodeOp → List EClassId
  | .constGate _    => []
  | .witness _      => []
  | .pubInput _     => []
  | .addGate a b    => [a, b]
  | .mulGate a b    => [a, b]
  | .negGate a      => [a]
  | .smulGate _ a   => [a]
  | .shiftLeft a _  => [a]
  | .shiftRight a _ => [a]
  | .bitAnd a b     => [a, b]
  | .bitXor a b     => [a, b]
  | .bitOr a b      => [a, b]
  | .constMask _    => []
  | .subGate a b       => [a, b]
  | .reduceGate a _    => [a]
  | .kronPack a b _    => [a, b]
  | .kronUnpackLo a _  => [a]
  | .kronUnpackHi a _  => [a]
  | .montyReduce a _ _ => [a]
  | .barrettReduce a _ _ => [a]
  | .harveyReduce a _  => [a]
  | .conditionalSub a _ => [a]

/-- Apply a function to all e-class children. -/
@[simp] def mixedMapChildren (f : EClassId → EClassId) : MixedNodeOp → MixedNodeOp
  | .constGate c    => .constGate c
  | .witness i      => .witness i
  | .pubInput i     => .pubInput i
  | .addGate a b    => .addGate (f a) (f b)
  | .mulGate a b    => .mulGate (f a) (f b)
  | .negGate a      => .negGate (f a)
  | .smulGate c a   => .smulGate c (f a)
  | .shiftLeft a n  => .shiftLeft (f a) n
  | .shiftRight a n => .shiftRight (f a) n
  | .bitAnd a b     => .bitAnd (f a) (f b)
  | .bitXor a b     => .bitXor (f a) (f b)
  | .bitOr a b      => .bitOr (f a) (f b)
  | .constMask n    => .constMask n
  | .subGate a b       => .subGate (f a) (f b)
  | .reduceGate a p    => .reduceGate (f a) p
  | .kronPack a b w    => .kronPack (f a) (f b) w
  | .kronUnpackLo a w  => .kronUnpackLo (f a) w
  | .kronUnpackHi a w  => .kronUnpackHi (f a) w
  | .montyReduce a p mu => .montyReduce (f a) p mu
  | .barrettReduce a p m => .barrettReduce (f a) p m
  | .harveyReduce a p  => .harveyReduce (f a) p
  | .conditionalSub a p => .conditionalSub (f a) p

/-- Positionally replace children with new e-class IDs. -/
@[simp] def mixedReplaceChildren (op : MixedNodeOp) (ids : List EClassId) : MixedNodeOp :=
  match op, ids with
  | .addGate _ _, a :: b :: _    => .addGate a b
  | .mulGate _ _, a :: b :: _    => .mulGate a b
  | .negGate _, a :: _           => .negGate a
  | .smulGate c _, a :: _        => .smulGate c a
  | .shiftLeft _ n, a :: _       => .shiftLeft a n
  | .shiftRight _ n, a :: _      => .shiftRight a n
  | .bitAnd _ _, a :: b :: _     => .bitAnd a b
  | .bitXor _ _, a :: b :: _     => .bitXor a b
  | .bitOr _ _, a :: b :: _      => .bitOr a b
  | .subGate _ _, a :: b :: _        => .subGate a b
  | .reduceGate _ p, a :: _         => .reduceGate a p
  | .kronPack _ _ w, a :: b :: _    => .kronPack a b w
  | .kronUnpackLo _ w, a :: _       => .kronUnpackLo a w
  | .kronUnpackHi _ w, a :: _       => .kronUnpackHi a w
  | .montyReduce _ p mu, a :: _    => .montyReduce a p mu
  | .barrettReduce _ p m, a :: _   => .barrettReduce a p m
  | .harveyReduce _ p, a :: _      => .harveyReduce a p
  | .conditionalSub _ p, a :: _   => .conditionalSub a p
  | op, _                           => op

/-- Cost model: mul = 1, all others = 0. Extensible for hardware-specific models. -/
def mixedLocalCost : MixedNodeOp → Nat
  | .mulGate _ _ => 1
  | _            => 0

/-- Simplicity rank for tiebreaking at equal cost (lower = simpler). -/
def mixedSimplicity : MixedNodeOp → Nat
  | .constGate _   => 0
  | .constMask _   => 1
  | .witness _     => 2
  | .pubInput _    => 3
  | .negGate _     => 4
  | .shiftRight _ _ => 5
  | .shiftLeft _ _  => 6
  | .bitAnd _ _    => 7
  | .bitXor _ _    => 8
  | .bitOr _ _     => 9
  | .addGate _ _   => 10
  | .subGate _ _      => 11
  | .kronUnpackLo _ _ => 12
  | .kronUnpackHi _ _ => 13
  | .reduceGate _ _   => 14
  | .kronPack _ _ _   => 15
  | .smulGate _ _     => 16
  | .mulGate _ _      => 17
  | .conditionalSub _ _ => 18
  | .harveyReduce _ _ => 19
  | .montyReduce _ _ _ => 20
  | .barrettReduce _ _ _ => 21

/-! ## List length helpers -/

private theorem list_length_two {α : Type} {l : List α} (h : l.length = 2) :
    ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

private theorem list_length_one {α : Type} {l : List α} (h : l.length = 1) :
    ∃ x, l = [x] := by
  match l, h with
  | [x], _ => exact ⟨x, rfl⟩

/-! ## NodeOps Instance -/

instance : NodeOps MixedNodeOp where
  children := mixedChildren
  mapChildren := mixedMapChildren
  replaceChildren := mixedReplaceChildren
  localCost := mixedLocalCost
  mapChildren_children f op := by cases op <;> simp
  mapChildren_id op := by cases op <;> simp
  replaceChildren_children op ids hlen := by
    cases op with
    | constGate _ => simp at hlen; subst hlen; rfl
    | witness _ => simp at hlen; subst hlen; rfl
    | pubInput _ => simp at hlen; subst hlen; rfl
    | addGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | mulGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | negGate a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | smulGate c a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | shiftLeft a n => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | shiftRight a n => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | bitAnd a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | bitXor a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | bitOr a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | constMask _ => simp at hlen; subst hlen; rfl
    | subGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | reduceGate a p => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | kronPack a b w => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | kronUnpackLo a w => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | kronUnpackHi a w => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | montyReduce a p mu => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | barrettReduce a p m => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | harveyReduce a p => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | conditionalSub a p => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
  replaceChildren_sameShape op ids hlen := by
    cases op with
    | constGate _ => simp at hlen; subst hlen; rfl
    | witness _ => simp at hlen; subst hlen; rfl
    | pubInput _ => simp at hlen; subst hlen; rfl
    | addGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | mulGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | negGate a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | smulGate c a => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | shiftLeft a n => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | shiftRight a n => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | bitAnd a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | bitXor a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | bitOr a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | constMask _ => simp at hlen; subst hlen; rfl
    | subGate a b => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | reduceGate a p => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | kronPack a b w => simp at hlen; obtain ⟨x, y, rfl⟩ := list_length_two hlen; rfl
    | kronUnpackLo a w => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | kronUnpackHi a w => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | montyReduce a p mu => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | barrettReduce a p m => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | harveyReduce a p => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl
    | conditionalSub a p => simp at hlen; obtain ⟨x, rfl⟩ := list_length_one hlen; rfl

/-! ## Semantics: Evaluation on Nat -/

/-- Environment for mixed operations. Reuses CircuitEnv specialized to Nat.
    constVal maps constant indices to Nat values.
    witnessVal maps witness indices to Nat values.
    pubInputVal maps public input indices to Nat values. -/
abbrev MixedEnv := CircuitEnv Nat

/-- Evaluate a mixed operation on Nat.
    Algebraic ops: standard Nat arithmetic.
    Bitwise ops: Nat.shiftLeft, Nat.shiftRight, Nat.land, Nat.xor, Nat.lor.
    negGate evaluates to 0 (Nat has no meaningful negation; included for embedding compat). -/
@[simp] def evalMixedOp (op : MixedNodeOp) (env : MixedEnv) (v : EClassId → Nat) : Nat :=
  match op with
  -- Algebraic
  | .constGate n    => env.constVal n
  | .witness n      => env.witnessVal n
  | .pubInput n     => env.pubInputVal n
  | .addGate a b    => v a + v b
  | .mulGate a b    => v a * v b
  | .negGate _      => 0  -- Nat: no negation; placeholder for structural compat
  | .smulGate n a   => env.constVal n * v a
  -- Bitwise
  | .shiftLeft a n  => Nat.shiftLeft (v a) n
  | .shiftRight a n => Nat.shiftRight (v a) n
  | .bitAnd a b     => Nat.land (v a) (v b)
  | .bitXor a b     => Nat.xor (v a) (v b)
  | .bitOr a b      => Nat.lor (v a) (v b)
  | .constMask n    => 2 ^ n - 1
  -- Subtraction (Nat truncated: a - b = 0 if a < b)
  | .subGate a b       => v a - v b
  -- Modular reduction: child % p
  | .reduceGate a p    => v a % p
  -- Kronecker: pack two values
  | .kronPack a b w    => v a + v b * 2 ^ w
  -- Kronecker: extract low bits
  | .kronUnpackLo a w  => v a % 2 ^ w
  -- Kronecker: extract high bits
  | .kronUnpackHi a w  => v a / 2 ^ w
  -- Modular reduction alternatives
  | .montyReduce a p _mu =>
    -- Montgomery REDC: semantically equivalent to x % p
    -- The mu parameter is for codegen only (determines the algorithm);
    -- the denotational semantics is simply modular reduction.
    v a % p
  | .barrettReduce a p _m =>
    -- Barrett reduction: semantically equivalent to x % p
    -- The m parameter is for codegen only (precomputed ≈ 2^k/p).
    v a % p
  | .harveyReduce a p =>
    -- Harvey conditional subtraction: semantically equivalent to x % p
    -- Output is in [0, 2p) for input in [0, 4p), but denotationally = x % p.
    v a % p
  | .conditionalSub a p =>
    -- Conditional subtract: if x >= p then x - p else x.
    -- For input in [0, 2p), equivalent to x % p. Simpler than Harvey (1 branch).
    if v a ≥ p then v a - p else v a

/-! ## NodeSemantics Instance -/

instance : NodeSemantics MixedNodeOp MixedEnv Nat where
  evalOp := evalMixedOp
  evalOp_ext op env v v' h := by
    cases op with
    | constGate _ => rfl
    | witness _ => rfl
    | pubInput _ => rfl
    | addGate a b =>
      simp only [evalMixedOp]
      congr 1
      · exact h a (by simp [NodeOps.children, mixedChildren])
      · exact h b (by simp [NodeOps.children, mixedChildren])
    | mulGate a b =>
      simp only [evalMixedOp]
      congr 1
      · exact h a (by simp [NodeOps.children, mixedChildren])
      · exact h b (by simp [NodeOps.children, mixedChildren])
    | negGate _ => rfl
    | smulGate n a =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | shiftLeft a n =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | shiftRight a n =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | bitAnd a b =>
      simp only [evalMixedOp]
      congr 1
      · exact h a (by simp [NodeOps.children, mixedChildren])
      · exact h b (by simp [NodeOps.children, mixedChildren])
    | bitXor a b =>
      simp only [evalMixedOp]
      congr 1
      · exact h a (by simp [NodeOps.children, mixedChildren])
      · exact h b (by simp [NodeOps.children, mixedChildren])
    | bitOr a b =>
      simp only [evalMixedOp]
      congr 1
      · exact h a (by simp [NodeOps.children, mixedChildren])
      · exact h b (by simp [NodeOps.children, mixedChildren])
    | constMask _ => rfl
    | subGate a b =>
      simp only [evalMixedOp]
      congr 1
      · exact h a (by simp [NodeOps.children, mixedChildren])
      · exact h b (by simp [NodeOps.children, mixedChildren])
    | reduceGate a p =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | kronPack a b w =>
      simp only [evalMixedOp]
      congr 1
      · exact h a (by simp [NodeOps.children, mixedChildren])
      · congr 1; exact h b (by simp [NodeOps.children, mixedChildren])
    | kronUnpackLo a w =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | kronUnpackHi a w =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | montyReduce a p mu =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | barrettReduce a p m =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | harveyReduce a p =>
      simp only [evalMixedOp]
      congr 1
      exact h a (by simp [NodeOps.children, mixedChildren])
    | conditionalSub a p =>
      simp only [evalMixedOp]
      have h0 := h a (by simp [NodeOps.children, mixedChildren])
      rw [h0]

/-! ## Embedding: CircuitNodeOp → MixedNodeOp -/

/-- Embed a CircuitNodeOp into MixedNodeOp. Preserves all structure. -/
def toMixed : CircuitNodeOp → MixedNodeOp
  | .constGate n  => .constGate n
  | .witness n    => .witness n
  | .pubInput n   => .pubInput n
  | .addGate a b  => .addGate a b
  | .mulGate a b  => .mulGate a b
  | .negGate a    => .negGate a
  | .smulGate c a => .smulGate c a

/-- The embedding preserves children lists. -/
theorem toMixed_children_eq (op : CircuitNodeOp) :
    mixedChildren (toMixed op) = AmoLean.EGraph.Verified.ENode.children ⟨op⟩ := by
  cases op <;> rfl

/-- Partial inverse: extract the CircuitNodeOp if the MixedNodeOp is algebraic. -/
def fromMixed : MixedNodeOp → Option CircuitNodeOp
  | .constGate n  => some (.constGate n)
  | .witness n    => some (.witness n)
  | .pubInput n   => some (.pubInput n)
  | .addGate a b  => some (.addGate a b)
  | .mulGate a b  => some (.mulGate a b)
  | .negGate a    => some (.negGate a)
  | .smulGate c a => some (.smulGate c a)
  | _             => none

/-- fromMixed is a left inverse of toMixed. -/
theorem fromMixed_toMixed (op : CircuitNodeOp) : fromMixed (toMixed op) = some op := by
  cases op <;> rfl

/-- toMixed is injective. -/
theorem toMixed_injective (a b : CircuitNodeOp) (h : toMixed a = toMixed b) : a = b := by
  cases a <;> cases b <;> simp [toMixed] at h <;> try exact h
  all_goals (try (obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl))
  all_goals (try (subst h; rfl))

/-! ## Convenience constructors -/

def mkShiftLeft (a : EClassId) (n : Nat) : MixedNodeOp := .shiftLeft a n
def mkShiftRight (a : EClassId) (n : Nat) : MixedNodeOp := .shiftRight a n
def mkBitAnd (a b : EClassId) : MixedNodeOp := .bitAnd a b
def mkBitXor (a b : EClassId) : MixedNodeOp := .bitXor a b
def mkBitOr (a b : EClassId) : MixedNodeOp := .bitOr a b
def mkConstMask (n : Nat) : MixedNodeOp := .constMask n

/-! ## Predicate: is this a bitwise operation? -/

/-- Returns true if the operation is bitwise (not algebraic). -/
def isBitwise : MixedNodeOp → Bool
  | .shiftLeft _ _  => true
  | .shiftRight _ _ => true
  | .bitAnd _ _     => true
  | .bitXor _ _     => true
  | .bitOr _ _      => true
  | .constMask _    => true
  | .subGate _ _    => false  -- subtraction is algebraic, not bitwise
  | _               => false

/-- Returns true if the operation is algebraic (mirrors CircuitNodeOp). -/
def isAlgebraic : MixedNodeOp → Bool
  | .constGate _  => true
  | .witness _    => true
  | .pubInput _   => true
  | .addGate _ _  => true
  | .mulGate _ _  => true
  | .negGate _    => true
  | .smulGate _ _ => true
  | .subGate _ _      => true
  | .reduceGate _ _   => true
  | .kronPack _ _ _   => true
  | .kronUnpackLo _ _ => true
  | .kronUnpackHi _ _ => true
  | .montyReduce _ _ _ => true
  | .barrettReduce _ _ _ => true
  | .harveyReduce _ _ => true
  | .conditionalSub _ _ => true
  | _                 => false

/-- Returns true if the operation requires u32→u64 widening in SIMD context.
    Operations that need u64 intermediates (like Solinas fold after multiply)
    don't vectorize well because NEON/AVX2 lack native u64-lane multiply.
    Montgomery REDC stays in u32 lanes (via vqdmulhq_s32) → no widening. -/
def needsWidening : MixedNodeOp → Bool
  | .reduceGate _ _      => true  -- Solinas fold: (x >> 31) * c needs u64 intermediate
  | .barrettReduce _ _ _ => true  -- Barrett: mul64 + shift needs u64
  | .montyReduce _ _ _   => false -- Montgomery: all ops in u32 lanes (vqdmulhq_s32)
  | .harveyReduce _ _    => false -- Harvey: conditional subs, u32 only
  | .conditionalSub _ _  => false -- Conditional sub: compare + sub, no widening
  | .mulGate _ _         => true  -- u32 × u32 = u64 (before reduction)
  | _                    => false

/-- Every MixedNodeOp is either algebraic or bitwise. -/
theorem algebraic_or_bitwise (op : MixedNodeOp) : isAlgebraic op = true ∨ isBitwise op = true := by
  cases op <;> simp [isAlgebraic, isBitwise]

/-- Canonical-node bridge: evaluating a node with mapped children under v
    equals evaluating the original node under v ∘ f.
    This is definitionally true for every MixedNodeOp constructor because
    mixedMapChildren applies f to children and evalMixedOp reads children via v. -/
theorem evalOp_mapChildren (f : EClassId → EClassId) (op : MixedNodeOp)
    (env : MixedEnv) (v : EClassId → Nat) :
    evalMixedOp (mixedMapChildren f op) env v = evalMixedOp op env (fun c => v (f c)) := by
  cases op <;> rfl

end AmoLean.EGraph.Verified.Bitwise
