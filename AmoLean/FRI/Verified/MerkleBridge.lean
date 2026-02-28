/-
  AMO-Lean: Merkle Bridge (N13.5)
  Fase 13 — Connecting operational MerkleProof with verified MerklePath

  This module bridges:
  - Operational: MerkleProof (FRI/Merkle.lean) — separated siblings/pathBits, FRIField
  - Verified: MerklePath (FRI/Verified/MerkleSpec.lean) — zipped (Bool × F), generic

  Strategy (staged per QA recommendation):
  1. Index helpers: conversion between proof formats
  2. Inversion: loop equivalence with foldl
  3. Semantic bridge: verify ↔ merklePathVerify
  4. Hash bridge: connecting CryptoHash.hash2to1 with generic hashFn

  Architecture:
  - MerkleProof stores (siblings : List F, pathBits : List Bool) separately
  - MerklePath stores (List (Bool × F)) zipped
  - The bridge zips them and proves verification equivalence
  - Does NOT bridge FlatMerkle ↔ MerkleTree (array → inductive is complex)
  - Instead focuses on the security-critical path: proof verification equivalence
-/

import AmoLean.FRI.Merkle
import AmoLean.FRI.Verified.MerkleSpec

namespace AmoLean.FRI.Verified

open AmoLean.FRI.Merkle.MerkleProof (verify)

/-! ## Part 1: Path Format Conversion -/

/-- Convert operational MerkleProof path format to verified MerklePath.
    Zips pathBits with siblings to create (isRight, siblingHash) pairs. -/
def toMerklePath {F : Type} (proof : AmoLean.FRI.Merkle.MerkleProof F) :
    MerklePath F :=
  proof.pathBits.zip proof.siblings

/-- Number of elements in the converted path -/
theorem toMerklePath_length {F : Type}
    (proof : AmoLean.FRI.Merkle.MerkleProof F) :
    (toMerklePath proof).length = min proof.pathBits.length proof.siblings.length := by
  simp [toMerklePath, List.length_zip]

/-- When pathBits and siblings have equal length, the converted path
    has exactly that length -/
theorem toMerklePath_length_eq {F : Type}
    (proof : AmoLean.FRI.Merkle.MerkleProof F)
    (h : proof.pathBits.length = proof.siblings.length) :
    (toMerklePath proof).length = proof.siblings.length := by
  simp [toMerklePath, List.length_zip, h]

/-! ## Part 2: Loop Equivalence

The operational verify uses a recursive loop while the verified
merklePathVerify uses List.foldl. We prove they compute the same result
when given the same inputs in corresponding formats. -/

/-- Helper: the verify loop from Merkle.lean computed on zipped inputs
    equals merklePathVerify on the zipped list.

    This is the core inductive lemma connecting the two verification
    algorithms. -/
theorem verify_loop_eq_foldl {F : Type}
    (hashFn : F → F → F) (current : F)
    (siblings : List F) (bits : List Bool)
    (h_len : bits.length = siblings.length) :
    AmoLean.FRI.Merkle.MerkleProof.verify.loop hashFn current siblings bits =
    merklePathVerify hashFn (bits.zip siblings) current := by
  induction siblings generalizing current bits with
  | nil =>
    cases bits with
    | nil => simp [AmoLean.FRI.Merkle.MerkleProof.verify.loop, merklePathVerify]
    | cons _ _ => simp at h_len
  | cons sib rest ih =>
    cases bits with
    | nil => simp at h_len
    | cons bit restBits =>
      simp only [AmoLean.FRI.Merkle.MerkleProof.verify.loop, merklePathVerify,
                  List.zip_cons_cons, List.foldl]
      apply ih
      simpa using h_len

/-! ## Part 3: Verification Equivalence

THE main bridge theorem: operational verify agrees with verified
merklePathVerify under path format conversion. -/

/-- The operational verify computes the path root correctly:
    when verify returns true, the computed root via merklePathVerify
    equals the expected root. -/
theorem merkleBridge_verify_equiv {F : Type} [inst : BEq F]
    (proof : AmoLean.FRI.Merkle.MerkleProof F)
    (leafValue expectedRoot : F)
    (hashFn : F → F → F)
    (h_len : proof.pathBits.length = proof.siblings.length)
    (h_beq : ∀ (a b : F), (a == b) = true → a = b) :
    verify proof leafValue expectedRoot hashFn = true →
    merklePathVerify hashFn (toMerklePath proof) leafValue = expectedRoot := by
  intro h_verify
  simp only [verify] at h_verify
  rw [verify_loop_eq_foldl hashFn leafValue proof.siblings proof.pathBits h_len] at h_verify
  simp only [toMerklePath]
  exact h_beq _ _ h_verify

/-- Converse: if the merklePathVerify result equals expectedRoot
    and BEq is correct, then verify returns true. -/
theorem merkleBridge_verify_converse {F : Type} [inst : BEq F]
    (proof : AmoLean.FRI.Merkle.MerkleProof F)
    (leafValue expectedRoot : F)
    (hashFn : F → F → F)
    (h_len : proof.pathBits.length = proof.siblings.length)
    (h_beq_iff : ∀ (a b : F), (a == b) = true ↔ a = b) :
    merklePathVerify hashFn (toMerklePath proof) leafValue = expectedRoot →
    verify proof leafValue expectedRoot hashFn = true := by
  intro h_verify
  simp only [verify, toMerklePath] at *
  rw [verify_loop_eq_foldl hashFn leafValue proof.siblings proof.pathBits h_len]
  rw [h_verify]
  exact (h_beq_iff _ _).mpr rfl

/-- Full equivalence when BEq is lawful -/
theorem merkleBridge_verify_iff {F : Type} [inst : BEq F]
    (proof : AmoLean.FRI.Merkle.MerkleProof F)
    (leafValue expectedRoot : F)
    (hashFn : F → F → F)
    (h_len : proof.pathBits.length = proof.siblings.length)
    (h_beq_iff : ∀ (a b : F), (a == b) = true ↔ a = b) :
    verify proof leafValue expectedRoot hashFn = true ↔
    merklePathVerify hashFn (toMerklePath proof) leafValue = expectedRoot :=
  ⟨merkleBridge_verify_equiv proof leafValue expectedRoot hashFn h_len
     (fun a b h => (h_beq_iff a b).mp h),
   merkleBridge_verify_converse proof leafValue expectedRoot hashFn h_len h_beq_iff⟩

/-! ## Part 4: Hash Function Bridge

Connecting operational CryptoHash.hash2to1 with the generic hashFn
used in verified MerkleSpec theorems. -/

/-- The hash bridge hypothesis: a hash function used in verification
    is the same as CryptoHash.hash2to1. -/
structure HashBridge (F : Type) [AmoLean.FRI.Fold.FRIField F]
    [AmoLean.FRI.Hash.CryptoHash F] (hashFn : F → F → F) : Prop where
  /-- The hash function agrees with CryptoHash.hash2to1 -/
  hash_eq : ∀ (a b : F), hashFn a b = AmoLean.FRI.Hash.CryptoHash.hash2to1 a b

/-- Under hash bridge, operational verification implies verified verification -/
theorem merkleBridge_with_hash {F : Type} [inst : BEq F]
    [AmoLean.FRI.Fold.FRIField F] [AmoLean.FRI.Hash.CryptoHash F]
    (proof : AmoLean.FRI.Merkle.MerkleProof F)
    (leafValue expectedRoot : F)
    (hashFn : F → F → F)
    (hb : HashBridge F hashFn)
    (h_len : proof.pathBits.length = proof.siblings.length)
    (h_beq : ∀ (a b : F), (a == b) = true → a = b) :
    verify proof leafValue expectedRoot hashFn = true →
    merklePathVerify AmoLean.FRI.Hash.CryptoHash.hash2to1
      (toMerklePath proof) leafValue = expectedRoot := by
  intro h_verify
  have h_eq : ∀ (a b : F), AmoLean.FRI.Hash.CryptoHash.hash2to1 a b = hashFn a b :=
    fun a b => (hb.hash_eq a b).symm
  simp only [merklePathVerify, toMerklePath]
  have key := merkleBridge_verify_equiv proof leafValue expectedRoot hashFn h_len h_beq h_verify
  simp only [merklePathVerify, toMerklePath] at key
  suffices h : ∀ (acc : F) (path : List (Bool × F)),
    List.foldl (fun c x => if x.1 = true then AmoLean.FRI.Hash.CryptoHash.hash2to1 x.2 c
                           else AmoLean.FRI.Hash.CryptoHash.hash2to1 c x.2) acc path =
    List.foldl (fun c x => if x.1 = true then hashFn x.2 c else hashFn c x.2) acc path by
    rw [h]; exact key
  intro acc path
  congr 1
  ext c ⟨b, s⟩
  split <;> simp [h_eq]

/-! ## Part 5: Well-Formedness Bridge

Connecting operational tree construction with verified WellFormed predicate. -/

/-- A MerkleTree constructed from a hash function is well-formed. -/
theorem merkleTree_build_wf {F : Type*} (hashFn : F → F → F)
    (l r : MerkleTree F)
    (hwf_l : MerkleTree.WellFormed hashFn l)
    (hwf_r : MerkleTree.WellFormed hashFn r) :
    MerkleTree.WellFormed hashFn
      (MerkleTree.node (hashFn l.root r.root) l r) := by
  exact ⟨rfl, hwf_l, hwf_r⟩

/-- Leaf trees are always well-formed. -/
theorem merkleTree_leaf_wf {F : Type*} (hashFn : F → F → F) (v : F) :
    MerkleTree.WellFormed hashFn (MerkleTree.leaf v) := by
  exact trivial

/-! ## Part 6: MerkleBridgeResult

Proof-carrying structure bundling bridge results for N13.6 integration. -/

/-- A Merkle bridge result bundles:
    - The operational proof
    - The verified path
    - The equivalence proof -/
structure MerkleBridgeResult (F : Type) [BEq F] where
  /-- The operational Merkle proof -/
  opProof : AmoLean.FRI.Merkle.MerkleProof F
  /-- The converted verified path -/
  verifiedPath : MerklePath F
  /-- The path is the conversion of the proof -/
  path_eq : verifiedPath = toMerklePath opProof
  /-- The proof has matching lengths -/
  len_eq : opProof.pathBits.length = opProof.siblings.length

/-- Construct a bridge result from a well-formed proof -/
def mkMerkleBridgeResult {F : Type} [BEq F]
    (proof : AmoLean.FRI.Merkle.MerkleProof F)
    (h_len : proof.pathBits.length = proof.siblings.length) :
    MerkleBridgeResult F :=
  { opProof := proof
    verifiedPath := toMerklePath proof
    path_eq := rfl
    len_eq := h_len }

/-! ## Part 7: Algebraic Properties -/

/-- Empty proof verifies against the leaf value itself -/
theorem merkleBridge_empty_proof {F : Type} [BEq F]
    (leafValue : F) (hashFn : F → F → F) :
    merklePathVerify hashFn (toMerklePath
      { siblings := [], pathBits := [], leafIndex := 0 :
        AmoLean.FRI.Merkle.MerkleProof F }) leafValue = leafValue := by
  simp [toMerklePath, merklePathVerify]

/-- Single-level proof computes one hash step -/
theorem merkleBridge_single_step {F : Type} [BEq F]
    (leafValue sib : F) (isRight : Bool) (hashFn : F → F → F) :
    merklePathVerify hashFn (toMerklePath
      { siblings := [sib], pathBits := [isRight], leafIndex := 0 :
        AmoLean.FRI.Merkle.MerkleProof F }) leafValue =
    if isRight then hashFn sib leafValue else hashFn leafValue sib := by
  simp [toMerklePath, merklePathVerify]

/-! ## Part 8: Bridge Summary

MerkleBridge provides:

1. `toMerklePath`: format conversion (zip pathBits with siblings)
2. `verify_loop_eq_foldl`: core inductive lemma (loop = foldl)
3. `merkleBridge_verify_equiv`: THE main theorem (verify → merklePathVerify eq)
4. `merkleBridge_verify_converse`: reverse direction
5. `merkleBridge_verify_iff`: full equivalence with lawful BEq
6. `HashBridge`: hypothesis connecting hashFn with CryptoHash.hash2to1
7. `merkleBridge_with_hash`: verification with hash bridge
8. `merkleTree_build_wf` / `merkleTree_leaf_wf`: well-formedness construction
9. `MerkleBridgeResult`: proof-carrying structure

Upstream:
- Merkle.lean: MerkleProof, verify
- MerkleSpec.lean: MerklePath, merklePathVerify, MerkleTree.WellFormed

Downstream:
- BridgeIntegration.lean (N13.6): integration theorem
-/

end AmoLean.FRI.Verified
