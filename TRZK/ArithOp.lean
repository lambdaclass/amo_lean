import LambdaSat
import TRZK.ArithExpr

open LambdaSat UnionFind

namespace TRZK

/-- E-graph node type. Children are `EClassId`s rather than subterms. -/
inductive ArithOp where
  | const : Int → ArithOp
  | var   : Nat → ArithOp
  | add   : EClassId → EClassId → ArithOp
  | mul   : EClassId → EClassId → ArithOp
  deriving Repr, Inhabited, DecidableEq

instance : BEq ArithOp where
  beq a b := decide (a = b)

instance : Hashable ArithOp where
  hash
    | .const n => mixHash 1 (hash n)
    | .var i   => mixHash 2 (hash i)
    | .add l r => mixHash 3 (mixHash (hash l) (hash r))
    | .mul l r => mixHash 4 (mixHash (hash l) (hash r))

instance : LawfulBEq ArithOp where
  eq_of_beq {a b} h := by simp [BEq.beq] at h; exact h
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable ArithOp where
  hash_eq {a b} h := by
    have := eq_of_beq h; subst this; rfl

instance : NodeOps ArithOp where
  children
    | .const _ => []
    | .var _   => []
    | .add l r => [l, r]
    | .mul l r => [l, r]
  mapChildren f
    | .const n => .const n
    | .var i   => .var i
    | .add l r => .add (f l) (f r)
    | .mul l r => .mul (f l) (f r)
  replaceChildren op cs :=
    match op, cs with
    | .add _ _, [l, r] => .add l r
    | .mul _ _, [l, r] => .mul l r
    | op, _ => op
  localCost _ := 1
  mapChildren_children f op := by cases op <;> simp
  mapChildren_id op := by cases op <;> simp
  replaceChildren_children op ids hlen := by
    cases op with
    | const _ => simp at hlen; simp [hlen]
    | var _   => simp at hlen; simp [hlen]
    | add _ _ =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | mul _ _ =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
  replaceChildren_sameShape op ids hlen := by
    cases op with
    | const _ => simp at hlen; simp
    | var _   => simp at hlen; simp
    | add _ _ =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp
    | mul _ _ =>
      simp at hlen
      match ids, hlen with
      | [_, _], _ => simp

instance : Extractable ArithOp ArithExpr where
  reconstruct op childExprs :=
    match op, childExprs with
    | .const n, []     => some (.const n)
    | .var i,   []     => some (.var i)
    | .add _ _, [l, r] => some (.add l r)
    | .mul _ _, [l, r] => some (.mul l r)
    | _, _             => none

end TRZK
