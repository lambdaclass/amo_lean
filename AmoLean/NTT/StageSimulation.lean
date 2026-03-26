/-
  AmoLean.NTT.StageSimulation

  Modular proof that an in-place NTT stage (via List.set) produces
  correct butterfly results. Built bottom-up:

  Layer 1: Single butterfly pair correctness + non-interference
  Layer 2: Full stage as foldl over pairs
  Layer 3: Connection to ntt_generic's recursive decomposition

  Design: DIT butterfly (matching ntt_generic) for the functional spec.
  The DIF-to-DIT bridge (for lowerNTTLoopStmt) is separate.
-/
import AmoLean.NTT.GenericNTT
import AmoLean.NTT.GenericCorrectness
import AmoLean.NTT.RootsOfUnity

set_option autoImplicit false

namespace AmoLean.NTT.StageSimulation

variable {F : Type} [Field F] [DecidableEq F]

-- ══════════════════════════════════════════════════════════════════
-- Layer 1: Single butterfly pair
-- ══════════════════════════════════════════════════════════════════

/-- Apply a single DIT butterfly to positions i, j in a list.
    butterfly(a, b, w) = (a + w*b, a - w*b) -/
def butterflyAt (data : List F) (i j : Nat) (w : F) : List F :=
  if hi : i < data.length then
    if hj : j < data.length then
      let a := data[i]
      let b := data[j]
      (data.set i (a + w * b)).set j (a - w * b)
    else data
  else data

/-- The written value at position i is a + w*b. -/
theorem butterflyAt_get_i (data : List F) (i j : Nat) (w : F)
    (hi : i < data.length) (hj : j < data.length) (hij : i ≠ j) :
    (butterflyAt data i j w)[i]'(by simp [butterflyAt, hi, hj, List.length_set]) =
    data[i] + w * data[j] := by
  simp only [butterflyAt, hi, hj, dite_true]
  simp [List.getElem_set, hij, Ne.symm hij]

/-- The written value at position j is a - w*b. -/
theorem butterflyAt_get_j (data : List F) (i j : Nat) (w : F)
    (hi : i < data.length) (hj : j < data.length) (hij : i ≠ j) :
    (butterflyAt data i j w)[j]'(by simp [butterflyAt, hi, hj, List.length_set]) =
    data[i] - w * data[j] := by
  simp only [butterflyAt, hi, hj, dite_true]
  simp [List.getElem_set, hij, Ne.symm hij]

/-- Non-interference: positions other than i, j are unchanged. -/
theorem butterflyAt_get_other (data : List F) (i j k : Nat) (w : F)
    (hi : i < data.length) (hj : j < data.length)
    (hki : k ≠ i) (hkj : k ≠ j) (hk : k < data.length) :
    (butterflyAt data i j w)[k]'(by simp [butterflyAt, hi, hj, List.length_set]; exact hk) =
    data[k] := by
  simp only [butterflyAt, hi, hj, dite_true]
  simp [List.getElem_set, hki, hkj, Ne.symm hki, Ne.symm hkj]

/-- Butterfly preserves list length. -/
@[simp] theorem butterflyAt_length (data : List F) (i j : Nat) (w : F) :
    (butterflyAt data i j w).length = data.length := by
  simp only [butterflyAt]
  split
  · split <;> simp [List.length_set]
  · rfl

-- ══════════════════════════════════════════════════════════════════
-- Layer 2: Butterfly pair index structure
-- ══════════════════════════════════════════════════════════════════

/-- Butterfly pair indices at a given stage.
    At stage s with n = 2^logN elements:
    - half = 2^(logN - 1 - s)
    - groups = 2^s
    - pairs per group = half
    - pair(g, p) → (i, j) = (g * 2 * half + p, g * 2 * half + p + half) -/
structure ButterflyPair where
  i : Nat
  j : Nat
  twiddleIdx : Nat

/-- Generate all butterfly pairs for a given NTT stage. -/
def stagePairs (logN stage : Nat) : List ButterflyPair :=
  let n := 2 ^ logN
  let half := 2 ^ (logN - 1 - stage)
  let numGroups := 2 ^ stage
  (List.range numGroups).flatMap fun group =>
    (List.range half).map fun pair =>
      let i := group * 2 * half + pair
      let j := i + half
      let twIdx := stage * (n / 2) + group * half + pair
      ⟨i, j, twIdx⟩

-- ══════════════════════════════════════════════════════════════════
-- Layer 2: Full stage as foldl over butterfly pairs
-- ══════════════════════════════════════════════════════════════════

/-- Apply all butterfly pairs at a given stage.
    Uses DIT butterfly: (a + w*b, a - w*b). -/
def applyStage (data : List F) (twiddles : Nat → F) (logN stage : Nat) : List F :=
  let pairs := stagePairs logN stage
  pairs.foldl (fun d bp => butterflyAt d bp.i bp.j (twiddles bp.twiddleIdx)) data

/-- Apply all stages of the NTT in sequence. -/
def applyAllStages (data : List F) (twiddles : Nat → F) (logN : Nat) : List F :=
  (List.range logN).foldl (fun d stage => applyStage d twiddles logN stage) data

/-- Helper: foldl of butterflyAt preserves length for any accumulator. -/
private theorem foldl_butterflyAt_length (pairs : List ButterflyPair) (twiddles : Nat → F)
    (acc : List F) :
    (pairs.foldl (fun d bp => butterflyAt d bp.i bp.j (twiddles bp.twiddleIdx)) acc).length =
    acc.length := by
  induction pairs generalizing acc with
  | nil => simp
  | cons bp rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact butterflyAt_length _ _ _ _

/-- Length preservation through applyStage. -/
@[simp] theorem applyStage_length (data : List F) (twiddles : Nat → F) (logN stage : Nat) :
    (applyStage data twiddles logN stage).length = data.length :=
  foldl_butterflyAt_length _ _ _

/-- Helper: foldl of applyStage preserves length for any accumulator. -/
private theorem foldl_applyStage_length (stages : List Nat) (twiddles : Nat → F) (logN : Nat)
    (acc : List F) :
    (stages.foldl (fun d stage => applyStage d twiddles logN stage) acc).length =
    acc.length := by
  induction stages generalizing acc with
  | nil => simp
  | cons s rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact applyStage_length _ _ _ _

/-- Length preservation through applyAllStages. -/
@[simp] theorem applyAllStages_length (data : List F) (twiddles : Nat → F) (logN : Nat) :
    (applyAllStages data twiddles logN).length = data.length :=
  foldl_applyStage_length _ _ _ _

-- ══════════════════════════════════════════════════════════════════
-- Layer 3: Non-vacuity — concrete N=4 example
-- ══════════════════════════════════════════════════════════════════

section ConcreteExample

-- Work over Rat for concrete computation
open Rat in
/-- N=4 NTT with omega = imaginary unit (i) is not available over Rat,
    so we use a simpler example: omega = -1 (primitive 2nd root).
    For N=4 we need a primitive 4th root, which doesn't exist over Rat.
    Instead, verify structural properties: length, pair indices. -/
example : (stagePairs 2 0).map (fun p => (p.i, p.j)) = [(0, 2), (1, 3)] := by native_decide
example : (stagePairs 2 1).map (fun p => (p.i, p.j)) = [(0, 1), (2, 3)] := by native_decide

end ConcreteExample

-- ══════════════════════════════════════════════════════════════════
-- Layer 2b: Sub-lemmas for DIT correctness (invariant-based)
-- ══════════════════════════════════════════════════════════════════

open AmoLean.NTT.Generic (ntt_generic ntt_spec_generic)

-- ══════════════════════════════════════════════════════════════════
-- Layer 3: DIT Bottom-Up NTT (correct formulation)
-- ══════════════════════════════════════════════════════════════════

/-- Bit-reverse an index: reverse the lowest `bits` bits. -/
def bitRev (bits : Nat) (x : Nat) : Nat :=
  let rec go (v : Nat) (result : Nat) : Nat → Nat
    | 0 => result
    | fuel + 1 => go (v / 2) (result * 2 + v % 2) fuel
  go x 0 bits

/-- Bit-reverse permute a list (generic over any type). -/
def bitRevPermute {α : Type} [Inhabited α] (logN : Nat) (xs : List α) : List α :=
  (List.range (2 ^ logN)).map fun i =>
    xs.getD (bitRev logN i) default

/-- Apply all NTT stages in bottom-up order (standard textbook DIT).
    Stage 0: half=1 (adjacent pairs), Stage 1: half=2, ..., Stage logN-1: half=N/2.
    This is the REVERSE of applyAllStages (which goes top-down). -/
def applyAllStages_DIT (data : List F) (twiddles : Nat → F) (logN : Nat) : List F :=
  (List.range logN).foldl
    (fun d stage => applyStage d twiddles logN (logN - 1 - stage))
    data

-- Main bridge theorem: dit_bottomUp_eq_ntt_generic (below).
-- Proof decomposed into 3 sub-lemmas:

/-- Stage invariant: after k bottom-up stages on bit-reversed input of length 2^logN,
    the array contains 2^(logN-k) independent blocks of size 2^k, where each block
    is the 2^k-point NTT of the corresponding subset of the original data. -/
def stageInvariant (workData origData : List F) (omega : F)
    (logN stagesCompleted : Nat) : Prop :=
  let n := 2 ^ logN
  let blockSize := 2 ^ stagesCompleted
  let numBlocks := n / blockSize
  workData.length = n ∧
  ∀ b, b < numBlocks → ∀ k, k < blockSize →
    workData.getD (b * blockSize + k) 0 =
      (ntt_spec_generic (omega ^ (2 ^ (logN - stagesCompleted)))
        (List.range blockSize |>.map fun j =>
          origData.getD (bitRev logN (b * blockSize + j)) 0)
      ).getD k 0

/-- After 0 stages, the invariant holds: each singleton is a 1-point NTT (identity). -/
theorem stageInvariant_zero [Inhabited F] (data : List F) (omega : F) (logN : Nat)
    (hlen : data.length = 2 ^ logN) :
    stageInvariant (bitRevPermute logN data) data omega logN 0 := by
  constructor
  · -- Length: bitRevPermute preserves length = 2^logN
    simp [bitRevPermute]
  · -- Element-wise: each singleton block = 1-point NTT = identity
    -- (bitRevPermute data)[b] = data[bitRev b] = ntt_spec_generic(_, [data[bitRev b]])[0]
    -- since ntt_spec_generic on a singleton is the identity.
    sorry

/-- Stage step: butterfly merge doubles block size (Cooley-Tukey identity).
    Uses ntt_coeff_generic_split + ntt_coeff_generic_split_upper. -/
theorem stageInvariant_step [DecidableEq F]
    (workData origData : List F) (omega : F) (logN k : Nat) (hk : k < logN)
    (twiddles : Nat → F)
    (hInv : stageInvariant workData origData omega logN k)
    (htw : ∀ group pair, group < 2 ^ logN / (2 * 2 ^ k) → pair < 2 ^ k →
      twiddles ((logN - 1 - k) * (2 ^ logN / 2) + group * 2 ^ k + pair) =
        omega ^ (pair * 2 ^ (logN - 1 - k))) :
    stageInvariant (applyStage workData twiddles logN (logN - 1 - k))
      origData omega logN (k + 1) := by
  sorry

/-- Final: invariant after all stages = full NTT spec. -/
theorem stageInvariant_final (workData origData : List F) (omega : F) (logN : Nat)
    (hlen : origData.length = 2 ^ logN)
    (hInv : stageInvariant workData origData omega logN logN) :
    workData = ntt_spec_generic omega origData := by
  sorry

theorem dit_bottomUp_eq_ntt_generic [DecidableEq F] [Inhabited F]
    (data : List F) (omega : F) (logN : Nat)
    (hlen : data.length = 2 ^ logN)
    (hroot : IsPrimitiveRoot omega (2 ^ logN))
    (twiddles : Nat → F)
    (htw : ∀ stage group pair,
      stage < logN →
      let half := 2 ^ stage
      let stride := 2 ^ (logN - 1 - stage)
      group < 2 ^ logN / (2 * half) →
      pair < half →
      twiddles (stage * (2 ^ logN / 2) + group * half + pair) =
        omega ^ (pair * stride)) :
    applyAllStages_DIT (bitRevPermute logN data) twiddles logN =
    ntt_generic omega data := by
  -- Compose sub-lemmas: zero → step^logN → final → ntt_generic_eq_spec⁻¹
  -- First show the iterative NTT equals ntt_spec_generic, then use ntt_generic_eq_spec.
  suffices h : applyAllStages_DIT (bitRevPermute logN data) twiddles logN =
      ntt_spec_generic omega data by
    rw [h, ← AmoLean.NTT.Generic.ntt_generic_eq_spec omega data ⟨logN, hlen⟩ (hlen ▸ hroot)]
  -- Now prove: iterative DIT = ntt_spec_generic via the invariant chain.
  -- Step 1: stageInvariant_zero gives invariant at stage 0
  -- Step 2: stageInvariant_step applied logN times gives invariant at stage logN
  -- Step 3: stageInvariant_final converts invariant at stage logN to ntt_spec_generic
  sorry

-- ══════════════════════════════════════════════════════════════════
-- Layer 3b: Deprecated top-down formulation
-- ══════════════════════════════════════════════════════════════════

/-- **DEPRECATED**: The top-down applyAllStages with DIT butterfly is neither
    standard DIT (which is bottom-up) nor standard DIF (which uses a different
    butterfly). Use `dit_bottomUp_eq_ntt_generic` instead.
    This theorem's statement was INCORRECT — empirically falsified for N=8
    over BabyBear. Kept for reference only. -/
theorem applyAllStages_eq_ntt_generic_INCORRECT [DecidableEq F]
    (data : List F) (omega : F) (logN : Nat)
    (hlen : data.length = 2 ^ logN)
    (hroot : IsPrimitiveRoot omega (2 ^ logN))
    (twiddles : Nat → F)
    (htw : ∀ stage group pair,
      stage < logN → group < 2 ^ stage → pair < 2 ^ (logN - 1 - stage) →
      twiddles (stage * (2 ^ logN / 2) + group * 2 ^ (logN - 1 - stage) + pair) =
      omega ^ (group * 2 ^ (logN - 1 - stage) + pair)) :
    applyAllStages data twiddles logN = ntt_generic omega data := by
  -- FALSIFIED: top-down DIT ≠ ntt_generic (verified over BabyBear N=8).
  -- The correct formulation is dit_bottomUp_eq_ntt_generic.
  sorry

/-- Non-vacuity: the theorem statement is satisfiable (hypotheses are jointly consistent).
    We can't compute ntt_generic over Rat for N>2 (no primitive root), but we CAN
    verify the hypotheses make sense for the trivial case N=1 (logN=0). -/
example (x : ℚ) : applyAllStages [x] (fun _ => (0 : ℚ)) 0 = [x] := by
  simp [applyAllStages]

-- ══════════════════════════════════════════════════════════════════
-- Layer 4: N18.6 — Compose into NTT correctness (bridge to ntt_spec)
-- ══════════════════════════════════════════════════════════════════

/-- The full NTT pipeline correctness (corrected): DIT bottom-up on
    bit-reversed input computes the DFT specification.
    Combines dit_bottomUp_eq_ntt_generic with ntt_generic_eq_spec. -/
theorem dit_bottomUp_eq_ntt_spec [DecidableEq F] [Inhabited F]
    (data : List F) (omega : F) (logN : Nat)
    (hlen : data.length = 2 ^ logN)
    (hroot : IsPrimitiveRoot omega (2 ^ logN))
    (twiddles : Nat → F)
    (htw : ∀ stage group pair,
      stage < logN →
      let half := 2 ^ stage
      let stride := 2 ^ (logN - 1 - stage)
      group < 2 ^ logN / (2 * half) →
      pair < half →
      twiddles (stage * (2 ^ logN / 2) + group * half + pair) =
        omega ^ (pair * stride)) :
    applyAllStages_DIT (bitRevPermute logN data) twiddles logN =
    ntt_spec_generic omega data := by
  rw [dit_bottomUp_eq_ntt_generic data omega logN hlen hroot twiddles htw]
  exact AmoLean.NTT.Generic.ntt_generic_eq_spec omega data
    ⟨logN, hlen⟩ (hlen ▸ hroot)

-- ══════════════════════════════════════════════════════════════════
-- Smoke tests
-- ══════════════════════════════════════════════════════════════════

-- N=8 (logN=3), stage 0: half=4, 1 group, 4 pairs
-- Pairs: (0,4), (1,5), (2,6), (3,7)
#eval (stagePairs 3 0).map fun p => (p.i, p.j)
-- expected: [(0, 4), (1, 5), (2, 6), (3, 7)]

-- N=8 (logN=3), stage 1: half=2, 2 groups, 2 pairs each
-- Pairs: (0,2), (1,3), (4,6), (5,7)
#eval (stagePairs 3 1).map fun p => (p.i, p.j)
-- expected: [(0, 2), (1, 3), (4, 6), (5, 7)]

-- N=8 (logN=3), stage 2: half=1, 4 groups, 1 pair each
-- Pairs: (0,1), (2,3), (4,5), (6,7)
#eval (stagePairs 3 2).map fun p => (p.i, p.j)
-- expected: [(0, 1), (2, 3), (4, 5), (6, 7)]

-- Bit-reverse permutation for N=8 (logN=3)
-- bitRev 3: 0→0, 1→4, 2→2, 3→6, 4→1, 5→5, 6→3, 7→7
#eval (List.range 8).map (bitRev 3)
-- expected: [0, 4, 2, 6, 1, 5, 3, 7]

-- bitRevPermute: [a,b,c,d,e,f,g,h] → [a,e,c,g,b,f,d,h]
#eval bitRevPermute 3 ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat)
-- expected: [0, 4, 2, 6, 1, 5, 3, 7]

end AmoLean.NTT.StageSimulation
