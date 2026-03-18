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
  | op, _                        => op

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
  | .smulGate _ _  => 11
  | .mulGate _ _   => 12

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
  | _             => false

/-- Every MixedNodeOp is either algebraic or bitwise. -/
theorem algebraic_or_bitwise (op : MixedNodeOp) : isAlgebraic op = true ∨ isBitwise op = true := by
  cases op <;> simp [isAlgebraic, isBitwise]

end AmoLean.EGraph.Verified.Bitwise
