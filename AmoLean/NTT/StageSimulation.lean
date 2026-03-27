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

/-- Length preservation through DIT stages. -/
@[simp] theorem applyAllStages_DIT_length (data : List F) (twiddles : Nat → F) (logN : Nat) :
    (applyAllStages_DIT data twiddles logN).length = data.length := by
  unfold applyAllStages_DIT
  induction (List.range logN) generalizing data with
  | nil => simp
  | cons s rest ih => simp only [List.foldl_cons]; rw [ih]; exact applyStage_length _ _ _ _

/-- bitRevPermute output has length 2^logN. -/
@[simp] theorem bitRevPermute_length [Inhabited F] (logN : Nat) (xs : List F) :
    (bitRevPermute logN xs).length = 2 ^ logN := by
  simp [bitRevPermute]

-- ══════════════════════════════════════════════════════════════════
-- bitRev structural lemmas for the DIT correctness proof
-- ══════════════════════════════════════════════════════════════════

/-- bitRev.go with nonzero initial result = shift + bitRev.go with zero. -/
private lemma bitRev_go_shift (v result fuel : Nat) :
    bitRev.go v result fuel = result * 2 ^ fuel + bitRev.go v 0 fuel := by
  induction fuel generalizing v result with
  | zero => simp [bitRev.go]
  | succ n ih =>
    simp only [bitRev.go, Nat.zero_mul, Nat.zero_add]
    rw [ih (v / 2) (result * 2 + v % 2), ih (v / 2) (v % 2)]
    ring

/-- Expanding bitRev (n+1) i via LSB extraction. -/
private lemma bitRev_succ (n i : Nat) :
    bitRev (n + 1) i = (i % 2) * 2 ^ n + bitRev n (i / 2) := by
  simp only [bitRev, bitRev.go]
  rw [bitRev_go_shift]
  ring

/-- Key identity: for i < 2^n, bitRev (n+1) i = 2 * bitRev n i.
    (The extra bit position adds a trailing 0 in the reversed form.) -/
theorem bitRev_succ_lt (n i : Nat) (hi : i < 2 ^ n) :
    bitRev (n + 1) i = 2 * bitRev n i := by
  induction n generalizing i with
  | zero =>
    interval_cases i
    simp [bitRev, bitRev.go]
  | succ k ih =>
    rw [bitRev_succ (k + 1) i]
    have hi2 : i / 2 < 2 ^ k := by omega
    rw [ih (i / 2) hi2]
    rw [bitRev_succ k i]
    ring

/-- Key identity: for j < 2^n, bitRev (n+1) (2^n + j) = 2 * bitRev n j + 1.
    (The MSB=1 becomes the trailing 1 in the reversed form.) -/
theorem bitRev_succ_ge (n j : Nat) (hj : j < 2 ^ n) :
    bitRev (n + 1) (2 ^ n + j) = 2 * bitRev n j + 1 := by
  induction n generalizing j with
  | zero =>
    interval_cases j
    simp [bitRev, bitRev.go]
  | succ k ih =>
    rw [bitRev_succ (k + 1) (2 ^ (k + 1) + j)]
    rw [show (2 ^ (k + 1) + j) % 2 = j % 2 from by omega]
    rw [show (2 ^ (k + 1) + j) / 2 = 2 ^ k + j / 2 from by omega]
    have hj2 : j / 2 < 2 ^ k := by omega
    rw [ih (j / 2) hj2, bitRev_succ k j]
    ring

/-- bitRev maps [0, 2^n) to [0, 2^n). -/
private lemma bitRev_lt (n i : Nat) (hi : i < 2 ^ n) : bitRev n i < 2 ^ n := by
  induction n generalizing i with
  | zero => interval_cases i; simp [bitRev, bitRev.go]
  | succ k ih =>
    rw [bitRev_succ]
    have hi2 : i / 2 < 2 ^ k := by omega
    have hbr : bitRev k (i / 2) < 2 ^ k := ih (i / 2) hi2
    have hmod : i % 2 ≤ 1 := by omega
    have h1 : (i % 2) * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ hmod
    have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
    omega

/-- Element access for bitRevPermute via getD. -/
private lemma bitRevPermute_getD [Inhabited F] (logN : Nat) (xs : List F)
    (i : Nat) (hi : i < 2 ^ logN) :
    (bitRevPermute logN xs).getD i default = xs.getD (bitRev logN i) default := by
  simp only [bitRevPermute, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_range hi]
  simp

/-- bitRevPermute (n+1) splits into evens/odds halves:
    first 2^n elements = bitRevPermute n (evens data),
    second 2^n elements = bitRevPermute n (odds data). -/
theorem bitRevPermute_split [Inhabited F] (n : Nat) (data : List F)
    (hlen : data.length = 2 ^ (n + 1)) :
    bitRevPermute (n + 1) data =
    bitRevPermute n (evens data) ++ bitRevPermute n (odds data) := by
  apply List.ext_getElem
  · simp [bitRevPermute_length]; omega
  · intro i h1 h2
    have hi_bound : i < 2 ^ (n + 1) := by rwa [bitRevPermute_length] at h1
    -- Use getD-based reasoning: convert getElem to getD
    rw [show (bitRevPermute (n + 1) data)[i] =
           (bitRevPermute (n + 1) data).getD i default from by
         simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]]
    rw [show (bitRevPermute n (evens data) ++ bitRevPermute n (odds data))[i] =
           (bitRevPermute n (evens data) ++ bitRevPermute n (odds data)).getD i default from by
         simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]]
    -- Goal: data.getD (bitRev (n+1) i) default = (A ++ B).getD i default
    -- where A = bitRevPermute n (evens data), B = bitRevPermute n (odds data)
    rw [bitRevPermute_getD (n + 1) data i hi_bound]
    have hlen_left : (bitRevPermute n (evens data)).length = 2 ^ n := bitRevPermute_length n _
    by_cases hi : i < 2 ^ n
    · -- First half → evens
      rw [bitRev_succ_lt n i hi]
      conv_rhs => rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [← List.getD_eq_getElem?_getD, bitRevPermute_getD n (evens data) i hi]
      have hbr := bitRev_lt n i hi
      have hbr_ev : bitRev n i < (evens data).length := by
        rw [evens_length_pow2 data (n + 1) (by omega) hlen]; exact hbr
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          evens_get data (bitRev n i) hbr_ev]
    · -- Second half → odds
      push_neg at hi
      have hi2 : i - 2 ^ n < 2 ^ n := by omega
      rw [show i = 2 ^ n + (i - 2 ^ n) from by omega, bitRev_succ_ge n (i - 2 ^ n) hi2]
      conv_rhs => rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      rw [show 2 ^ n + (i - 2 ^ n) - (bitRevPermute n (evens data)).length = i - 2 ^ n from by
            rw [hlen_left]; omega]
      rw [← List.getD_eq_getElem?_getD, bitRevPermute_getD n (odds data) (i - 2 ^ n) hi2]
      have hbr := bitRev_lt n (i - 2 ^ n) hi2
      have hbr_od : bitRev n (i - 2 ^ n) < (odds data).length := by
        rw [odds_length_pow2 data (n + 1) (by omega) hlen]; exact hbr
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          odds_get data (bitRev n (i - 2 ^ n)) hbr_od]

-- ══════════════════════════════════════════════════════════════════
-- Proof roadmap for dit_bottomUp_eq_ntt_generic
--
-- FINDING: A naive "blocks contain sub-NTTs" invariant is INCORRECT.
-- At intermediate stages, the working array is in a mixed state that
-- does NOT correspond to independent sub-DFTs. The contiguous-half
-- butterfly merge does NOT produce sub-DFTs because the DFT sum
-- uses ω^{mj} but sub-NTTs use (ω²)^{mj} = ω^{2mj} — different
-- exponents. Correctness only holds after ALL stages complete.
--
-- CORRECT PROOF APPROACHES (each ~500 LOC of dedicated formalization):
--
-- Approach A (Coefficient tracking):
--   Define coeff_matrix[stage][i][j] tracking the linear combination
--   work[i] = Σ coeff[i][j] * data[j]. Prove butterfly updates the
--   coefficients correctly, and at the end coeff[k][j] = ω^{jk}.
--
-- Approach B (Polynomial factorization, SPIRAL/Thery-style):
--   DFT_N = Π_{s} (I_{2^s} ⊗ DFT_2) · Diag(twiddles_s) · Perm_s
--   Each factor is a simple butterfly matrix. The product telescopes.
--   Requires matrix formalization infrastructure.
--
-- Approach C (Direct DFT sum, element-wise):
--   For each output index k, expand the butterfly operations to show
--   output[k] = Σ_{j} data[j] * ω^{jk}. Uses induction on logN
--   with the CT splitting formula (ntt_coeff_generic_split).
--
-- The existing infrastructure (butterflyAt lemmas, length preservation,
-- stagePairs, ntt_coeff_generic_split) supports all three approaches.
-- ══════════════════════════════════════════════════════════════════

/-- Sub-lemma 1: The first n DIT stages on bitRevPermute (n+1) data produce
    ntt_generic (ω²) (evens data) ++ ntt_generic (ω²) (odds data).
    Butterflies at stageIdx ≥ 1 have distance < 2^n, so they don't cross the
    midpoint of the concatenated list. Each half independently computes a
    sub-DFT via twiddle-value correspondence + IH. -/
private lemma dit_first_n_stages_independent [DecidableEq F] [Inhabited F]
    (n : Nat) (data : List F) (omega : F) (twiddles : Nat → F)
    (hlen : data.length = 2 ^ (n + 1))
    (hroot : IsPrimitiveRoot omega (2 ^ (n + 1)))
    (htw : ∀ stageIdx group pair,
      stageIdx < n + 1 →
      let half := 2 ^ (n + 1 - 1 - stageIdx)
      let numGroups := 2 ^ stageIdx
      group < numGroups →
      pair < half →
      twiddles (stageIdx * (2 ^ (n + 1) / 2) + group * half + pair) = omega ^ (pair * numGroups))
    (ih : ∀ (data' : List F) (omega' : F),
      data'.length = 2 ^ n → IsPrimitiveRoot omega' (2 ^ n) →
      ∀ (twiddles' : Nat → F),
        (∀ stageIdx group pair, stageIdx < n →
          let half := 2 ^ (n - 1 - stageIdx); let numGroups := 2 ^ stageIdx
          group < numGroups → pair < half →
          twiddles' (stageIdx * (2 ^ n / 2) + group * half + pair) = omega' ^ (pair * numGroups)) →
        applyAllStages_DIT (bitRevPermute n data') twiddles' n = ntt_generic omega' data') :
    (List.range n).foldl
      (fun d stage => applyStage d twiddles (n + 1) (n + 1 - 1 - stage))
      (bitRevPermute n (evens data) ++ bitRevPermute n (odds data)) =
    ntt_generic (omega * omega) (evens data) ++ ntt_generic (omega * omega) (odds data) := by
  -- The first n stages use stageIdx = n, n-1, ..., 1.
  -- At each stage, half = 2^(n - stageIdx) < 2^n, so butterflies stay within halves.
  -- Each half independently processes a standalone DIT with appropriate twiddles.
  -- By twiddle-value correspondence: big twiddle at index (s, g, p) has value
  --   omega^(p * 2^(n-s)) = (omega²)^(p * 2^(n-1-s)) = sub-DFT twiddle value.
  -- By IH: each half's result = ntt_generic (omega²) (evens/odds data).
  sorry

-- ══════════════════════════════════════════════════════════════════
-- N2: Core lemma — foldl of disjoint butterflies is element-wise predictable
-- ══════════════════════════════════════════════════════════════════

/-- After a foldl of butterflyAt over non-overlapping pairs, position k retains
    its original value if no pair touches k. Generalized over accumulator (L-700). -/
private lemma foldl_butterflyAt_getElem_untouched
    (pairs : List ButterflyPair) (twiddles : Nat → F) (acc : List F)
    (k : Nat) (hk : k < acc.length)
    (hbounds : ∀ bp ∈ pairs, bp.i < acc.length ∧ bp.j < acc.length)
    (hdisjoint : ∀ bp ∈ pairs, bp.i ≠ k ∧ bp.j ≠ k) :
    (pairs.foldl (fun d bp => butterflyAt d bp.i bp.j (twiddles bp.twiddleIdx)) acc)[k]'
      (by rw [foldl_butterflyAt_length]; exact hk) =
    acc[k] := by
  induction pairs generalizing acc with
  | nil => simp [List.foldl]
  | cons bp rest ih =>
    simp only [List.foldl_cons]
    have hbp_disj := hdisjoint bp (List.mem_cons.mpr (Or.inl rfl))
    have hbp_bnd := hbounds bp (List.mem_cons.mpr (Or.inl rfl))
    have hrest_disj : ∀ bp' ∈ rest, bp'.i ≠ k ∧ bp'.j ≠ k :=
      fun bp' h => hdisjoint bp' (List.mem_cons.mpr (Or.inr h))
    have hrest_bnd : ∀ bp' ∈ rest, bp'.i < (butterflyAt acc bp.i bp.j (twiddles bp.twiddleIdx)).length ∧
        bp'.j < (butterflyAt acc bp.i bp.j (twiddles bp.twiddleIdx)).length :=
      fun bp' h => by rw [butterflyAt_length]; exact hbounds bp' (List.mem_cons.mpr (Or.inr h))
    rw [ih (butterflyAt acc bp.i bp.j (twiddles bp.twiddleIdx))
          (by rw [butterflyAt_length]; exact hk) hrest_bnd hrest_disj]
    exact butterflyAt_get_other acc bp.i bp.j k (twiddles bp.twiddleIdx)
      hbp_bnd.1 hbp_bnd.2 hbp_disj.1.symm hbp_disj.2.symm hk

/-- After a foldl of butterflyAt at disjoint pairs (j, j+N) for j=0..N-1,
    position k < N has: acc[k] + tw(k) * acc[k+N]. -/
private lemma foldl_range_butterflyAt_getElem_i
    (acc : List F) (N : Nat) (tw : Nat → F) (k : Nat)
    (hlen : acc.length = 2 * N) (hk : k < N) :
    ((List.range N).foldl (fun d j => butterflyAt d j (j + N) (tw j)) acc)[k]'
      (by rw [show (List.range N).foldl _ acc = _ from rfl]; sorry) =
    acc[k]'(by omega) + tw k * acc[k + N]'(by omega) := by
  sorry

/-- After a foldl of butterflyAt at disjoint pairs (j, j+N) for j=0..N-1,
    position k+N has: acc[k] - tw(k) * acc[k+N]. -/
private lemma foldl_range_butterflyAt_getElem_j
    (acc : List F) (N : Nat) (tw : Nat → F) (k : Nat)
    (hlen : acc.length = 2 * N) (hk : k < N) :
    ((List.range N).foldl (fun d j => butterflyAt d j (j + N) (tw j)) acc)[k + N]'
      (by sorry) =
    acc[k]'(by omega) - tw k * acc[k + N]'(by omega) := by
  sorry

/-- Sub-lemma 2: The last DIT stage (stageIdx = 0, distance = 2^n) applies
    butterfly operations across the two halves, combining E and O into
    the full NTT via the Cooley-Tukey formula. -/
private lemma dit_last_stage_combine [DecidableEq F] [Inhabited F]
    (n : Nat) (data : List F) (omega : F) (twiddles : Nat → F)
    (hlen : data.length = 2 ^ (n + 1))
    (hroot : IsPrimitiveRoot omega (2 ^ (n + 1)))
    (htw : ∀ stageIdx group pair,
      stageIdx < n + 1 →
      let half := 2 ^ (n + 1 - 1 - stageIdx)
      let numGroups := 2 ^ stageIdx
      group < numGroups →
      pair < half →
      twiddles (stageIdx * (2 ^ (n + 1) / 2) + group * half + pair) = omega ^ (pair * numGroups))
    (intermediate : List F)
    (h_int : intermediate =
      ntt_generic (omega * omega) (evens data) ++ ntt_generic (omega * omega) (odds data)) :
    applyStage intermediate twiddles (n + 1) (n + 1 - 1 - n) =
    ntt_generic omega data := by
  -- Rewrite intermediate
  rw [h_int]
  -- Unfold ntt_generic for data.length ≥ 2
  have hlen2 : data.length ≥ 2 := by
    rw [hlen]; calc (2 : Nat) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [AmoLean.NTT.Generic.ntt_generic_unfold omega data hlen2]
  -- Reduce have-bindings on RHS (L-249: simp only [] for zeta-reduction)
  simp only []
  -- Name E and O for clarity
  set E := ntt_generic (omega * omega) (evens data)
  set O := ntt_generic (omega * omega) (odds data)
  -- Simplify data.length / 2 to 2^n
  have hN : data.length / 2 = 2 ^ n := by rw [hlen]; omega
  rw [hN]
  -- The LHS is: applyStage (E ++ O) twiddles (n+1) (n+1-1-n)
  -- We need to show this = upper ++ lower.
  -- Both sides have length 2^(n+1). Use element-wise comparison.
  apply List.ext_getElem
  · -- Length equality
    simp [applyStage_length, List.length_append, List.length_map, List.length_range]
    have hE_ev := evens_length_pow2 data (n+1) (by omega) hlen
    have hO_od := odds_length_pow2 data (n+1) (by omega) hlen
    rw [AmoLean.NTT.Generic.ntt_generic_length _ _ ⟨n, hE_ev⟩,
        AmoLean.NTT.Generic.ntt_generic_length _ _ ⟨n, hO_od⟩,
        hE_ev, hO_od]; congr 1 <;> omega
  · -- Element-wise: show (applyStage (E++O) tw (n+1) 0)[k] = (upper++lower)[k]
    -- This is the core butterfly-foldl argument.
    -- applyStage unfolds to foldl over stagePairs (n+1) 0
    -- = foldl over pairs (j, j+2^n) for j = 0..2^n-1
    -- Each butterfly at (j, j+2^n) only touches positions j and j+2^n.
    -- Non-overlapping: different j have disjoint position sets.
    -- For k < 2^n: butterfly at (k, k+2^n) sets position k to
    --   (E++O)[k] + tw(k) * (E++O)[k+2^n] = E[k] + omega^k * O[k]
    -- For k >= 2^n: butterfly at (k-2^n, k) sets position k to
    --   (E++O)[k-2^n] - tw(k-2^n) * (E++O)[k] = E[k-2^n] - omega^(k-2^n) * O[k-2^n]
    -- These match upper[k] and lower[k-2^n] respectively.
    -- The foldl_butterflyAt_getElem_untouched lemma (PROVEN) handles
    -- the "all other butterflies don't touch k" part.
    -- What remains is connecting the butterfly result to the RHS format.
    intro k hk1 hk2
    -- Need: E.length = 2^n, O.length = 2^n for bounds
    have hE_ev := evens_length_pow2 data (n+1) (by omega) hlen
    have hO_od := odds_length_pow2 data (n+1) (by omega) hlen
    have hElen : E.length = 2 ^ n := by
      show (ntt_generic (omega * omega) (evens data)).length = 2 ^ n
      rw [AmoLean.NTT.Generic.ntt_generic_length _ _ ⟨n, hE_ev⟩, hE_ev]
      show 2 ^ (n + 1 - 1) = 2 ^ n; congr 1
    have hOlen : O.length = 2 ^ n := by
      show (ntt_generic (omega * omega) (odds data)).length = 2 ^ n
      rw [AmoLean.NTT.Generic.ntt_generic_length _ _ ⟨n, hO_od⟩, hO_od]
      show 2 ^ (n + 1 - 1) = 2 ^ n; congr 1
    -- k < 2^(n+1)
    have hk_bound : k < 2 ^ (n + 1) := by
      rw [applyStage_length, List.length_append, hElen, hOlen] at hk1; omega
    -- TODO: connect applyStage to the foldl_range form, then use
    -- foldl_range_butterflyAt_getElem_i/j for the LHS, and
    -- List.getElem_append_left/right + List.getElem_map for the RHS.
    -- htw at stageIdx=0: twiddles(k) = omega^(k * 1) = omega^k.
    sorry

/-- bitRevPermute 0 of a singleton is itself. -/
private lemma bitRevPermute_zero_singleton [Inhabited F] (x : F) :
    bitRevPermute 0 [x] = [x] := by
  simp [bitRevPermute, bitRev, bitRev.go, List.getD]

/-- Base case: logN = 0 means data has one element, DIT is identity. -/
private lemma dit_base_case_zero [Inhabited F]
    (data : List F) (omega : F) (twiddles : Nat → F)
    (hlen : data.length = 2 ^ 0) :
    applyAllStages_DIT (bitRevPermute 0 data) twiddles 0 =
    ntt_generic omega data := by
  have h1 : data.length = 1 := by simpa using hlen
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h1
  rw [bitRevPermute_zero_singleton]
  simp [applyAllStages_DIT, ntt_generic]

theorem dit_bottomUp_eq_ntt_generic [DecidableEq F] [Inhabited F]
    (data : List F) (omega : F) (logN : Nat)
    (hlen : data.length = 2 ^ logN)
    (hroot : IsPrimitiveRoot omega (2 ^ logN))
    (twiddles : Nat → F)
    (htw : ∀ stageIdx group pair,
      stageIdx < logN →
      let half := 2 ^ (logN - 1 - stageIdx)
      let numGroups := 2 ^ stageIdx
      group < numGroups →
      pair < half →
      twiddles (stageIdx * (2 ^ logN / 2) + group * half + pair) =
        omega ^ (pair * numGroups)) :
    applyAllStages_DIT (bitRevPermute logN data) twiddles logN =
    ntt_generic omega data := by
  -- Strategy: both sides equal ntt_spec_generic omega data.
  -- RHS: ntt_generic = ntt_spec_generic (by ntt_generic_eq_spec)
  -- LHS: iterative DIT = ntt_spec_generic (element-wise butterfly expansion)
  induction logN generalizing data omega twiddles with
  | zero => exact dit_base_case_zero data omega twiddles hlen
  | succ n ih =>
    -- Step 1: Decompose input via bitRevPermute_split
    rw [bitRevPermute_split n data hlen]
    -- Goal: applyAllStages_DIT (bRP n (evens data) ++ bRP n (odds data)) twiddles (n+1) =
    --       ntt_generic omega data
    -- Step 2: Unfold applyAllStages_DIT (n+1) = lastStage ∘ firstNStages
    -- The DIT applies n+1 stages to A ++ B where A = bRP n (evens), B = bRP n (odds):
    --   Stages 0..n-1 (stageIdx n..1): butterflies within halves (distance < 2^n)
    --   Stage n (stageIdx 0): butterflies across halves (distance = 2^n)
    -- After first n stages: the halves become independent sub-DFTs E, O
    -- After last stage: butterfly combine E, O → ntt_generic omega data
    --
    -- Key sub-lemma (stage independence + IH application):
    -- The first n DIT stages on A ++ B produce E ++ O where
    --   E = ntt_generic (ω²) (evens data)
    --   O = ntt_generic (ω²) (odds data)
    -- This requires:
    --   (i) Butterflies with stageIdx ≥ 1 don't cross the midpoint (index arithmetic)
    --   (ii) The butterfly operations on each half match a standalone DIT
    --   (iii) Twiddle values match between big and standalone indexing
    --   (iv) IH application on each half
    --
    -- Key sub-lemma (last stage combine):
    -- applyStage (E ++ O) twiddles (n+1) 0 produces the CT butterfly combination
    -- matching ntt_generic omega data's upper ++ lower structure.
    -- Decompose foldl (n+1) = foldl (first n) then one more step
    show (List.range (n + 1)).foldl
      (fun d stage => applyStage d twiddles (n + 1) (n + 1 - 1 - stage))
      (bitRevPermute n (evens data) ++ bitRevPermute n (odds data)) =
      ntt_generic omega data
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- Define intermediate state after first n stages
    set intermediate := (List.range n).foldl
      (fun d stage => applyStage d twiddles (n + 1) (n + 1 - 1 - stage))
      (bitRevPermute n (evens data) ++ bitRevPermute n (odds data))
    -- Sub-lemma 1: first n stages produce E ++ O (sub-DFTs on each half)
    -- Butterflies with stageIdx ≥ 1 have distance < 2^n, so they don't cross halves.
    -- Each half independently computes a sub-DFT via twiddle-value correspondence.
    have h_intermediate :
        intermediate = ntt_generic (omega * omega) (evens data) ++
                       ntt_generic (omega * omega) (odds data) :=
      dit_first_n_stages_independent n data omega twiddles hlen hroot htw ih
    -- Sub-lemma 2: last stage butterfly combines E ++ O into ntt_generic omega data
    exact dit_last_stage_combine n data omega twiddles hlen hroot htw intermediate h_intermediate

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
    (htw : ∀ stageIdx group pair,
      stageIdx < logN →
      let half := 2 ^ (logN - 1 - stageIdx)
      let numGroups := 2 ^ stageIdx
      group < numGroups →
      pair < half →
      twiddles (stageIdx * (2 ^ logN / 2) + group * half + pair) =
        omega ^ (pair * numGroups)) :
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
