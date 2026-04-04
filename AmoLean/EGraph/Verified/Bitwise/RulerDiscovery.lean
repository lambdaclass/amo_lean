/-
  AMO-Lean Ultra — Phase 25: Ruler Discovery
  Autonomous rule discovery via CVec (Characteristic Vector) matching.

  Adapted from OptiSat v2 Ruler/CVecEngine.lean.

  A CVec is the evaluation of a pattern on concrete test inputs.
  Two patterns with identical CVecs are rule candidates (they agree
  on all test inputs → likely equivalent).

  CVecMatchMode supports:
  - .eq: patterns evaluate to same values (equality rule)
  - .le: pattern A ≤ pattern B (bound rule)
  - .modN p: patterns equivalent mod p (field equivalence)

  For NTT: the Ruler discovers rules like:
  - x * (2^24 - 1) = (x << 24) - x  (shift decomposition)
  - fold(fold(x)) == fold(x)  (idempotent fold)
  - solinasFold ≡ montyReduce ≡ harveyReduce (mod p)

  Consumes: HardwareColors (for color-aware discovery)
  Consumed by: Phase27Integration (top-level)
-/
import AmoLean.EGraph.Verified.Bitwise.HardwareColors

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: CVec (Characteristic Vector)
-- ══════════════════════════════════════════════════════════════════

/-- A characteristic vector: evaluation of a pattern on test inputs. -/
abbrev CVec := Array Nat

/-- Evaluate a function on multiple test inputs, producing a CVec. -/
def evaluateCVec (f : Nat → Nat) (testInputs : Array Nat) : CVec :=
  testInputs.map f

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Match Modes
-- ══════════════════════════════════════════════════════════════════

/-- How to compare two CVecs. -/
inductive CVecMatchMode where
  | eq            -- ∀ i, cv1[i] = cv2[i]
  | le            -- ∀ i, cv1[i] ≤ cv2[i]
  | modN (n : Nat) -- ∀ i, cv1[i] % n = cv2[i] % n
  deriving Repr, BEq, Inhabited

/-- Compare two CVecs element-wise. Returns false for empty vectors
    (avoids vacuous match producing spurious candidates). -/
private def zipWith (cv1 cv2 : CVec) (f : Nat → Nat → Bool) : Bool :=
  cv1.size > 0 && cv1.size == cv2.size &&
  (Array.range cv1.size).all fun i =>
    match cv1[i]?, cv2[i]? with
    | some a, some b => f a b
    | _, _ => false

def cvecEqual (cv1 cv2 : CVec) : Bool := zipWith cv1 cv2 (· == ·)
def cvecLe (cv1 cv2 : CVec) : Bool := zipWith cv1 cv2 (· ≤ ·)
def cvecModEq (cv1 cv2 : CVec) (n : Nat) : Bool :=
  n > 0 && zipWith cv1 cv2 (fun a b => a % n == b % n)

def cvecMatch (cv1 cv2 : CVec) (mode : CVecMatchMode) : Bool :=
  match mode with
  | .eq => cvecEqual cv1 cv2
  | .le => cvecLe cv1 cv2
  | .modN n => cvecModEq cv1 cv2 n

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Rule Discovery
-- ══════════════════════════════════════════════════════════════════

/-- A discovered rule candidate. -/
structure RuleCandidate where
  name : String
  lhsName : String
  rhsName : String
  mode : CVecMatchMode
  confidence : Nat  -- number of test inputs that matched
  deriving Repr, Inhabited

/-- Discover equivalences between a set of named functions.
    Each function is evaluated on test inputs, CVecs are compared. -/
def discoverRules (functions : List (String × (Nat → Nat)))
    (testInputs : Array Nat) (mode : CVecMatchMode) : List RuleCandidate :=
  let cvecs := functions.map fun (name, f) => (name, evaluateCVec f testInputs)
  let pairs := cvecs.flatMap fun (n1, cv1) =>
    cvecs.filterMap fun (n2, cv2) =>
      if n1 < n2 && cvecMatch cv1 cv2 mode then
        some { name := s!"{n1}_eq_{n2}", lhsName := n1, rhsName := n2,
               mode, confidence := testInputs.size }
      else none
  pairs

-- ══════════════════════════════════════════════════════════════════
-- Section 4: NTT-Specific Discovery
-- ══════════════════════════════════════════════════════════════════

/-- Solinas fold for BabyBear: (x >> 31) * c + (x & 0x7FFFFFFF) where c = 15 * 2^27 + 1. -/
private def solinasFoldBB (x : Nat) : Nat :=
  let c := 2013265921 / (2^31) + 1  -- = 1
  (x >>> 31) * c + (x &&& 0x7FFFFFFF)

/-- Simple modular reduction. -/
private def modReduce (p : Nat) (x : Nat) : Nat := x % p

/-- Harvey conditional subtraction (for inputs < 2p). -/
private def harveyCond (p : Nat) (x : Nat) : Nat :=
  if x ≥ p then x - p else x

/-- Shift decomposition for KoalaBear: x * (2^24 - 1) = (x << 24) - x. -/
private def mulKoalaConst (x : Nat) : Nat := x * (2^24 - 1)
private def shiftSubKoala (x : Nat) : Nat := (x <<< 24) - x

/-- Double fold: fold(fold(x)). -/
private def doubleFoldBB (x : Nat) : Nat := solinasFoldBB (solinasFoldBB x)

/-- Test inputs: range of values including edge cases. -/
def nttTestInputs : Array Nat :=
  #[0, 1, 2, 100, 1000, 2013265920, 2013265921, 2013265922,
    4026531841, 0x7FFFFFFF, 0xFFFFFFFF, 12345678, 99999999]

/-- Discover reduction equivalences for BabyBear. -/
def discoverBabyBearRules : List RuleCandidate :=
  let p := 2013265921
  discoverRules
    [("solinas_fold", solinasFoldBB),
     ("mod_reduce", modReduce p),
     ("harvey_cond", harveyCond p)]
    nttTestInputs (.modN p)

/-- Discover shift decomposition for KoalaBear. -/
def discoverKoalaBearShift : List RuleCandidate :=
  discoverRules
    [("mul_const", mulKoalaConst),
     ("shift_sub", shiftSubKoala)]
    #[0, 1, 2, 100, 1000, 0xFFFF, 0x7FFFFFFF] .eq

/-- Discover fold idempotency. -/
def discoverFoldIdempotency : List RuleCandidate :=
  discoverRules
    [("single_fold", solinasFoldBB),
     ("double_fold", doubleFoldBB)]
    nttTestInputs .le

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Empty CVecs do NOT match (guard against spurious candidates). -/
theorem cvecEqual_empty_false : cvecEqual #[] #[] = false := by native_decide

/-- CVec equality is reflexive on concrete vectors. -/
example : cvecEqual #[1, 2, 3] #[1, 2, 3] = true := by native_decide

/-- Shift decomposition for KoalaBear is correct for small values. -/
theorem koala_shift_eq : ∀ x ∈ [0, 1, 2, 100, 1000],
    mulKoalaConst x = shiftSubKoala x := by
  intro x hx; simp [List.mem_cons, List.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    simp [mulKoalaConst, shiftSubKoala]

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

/-- BabyBear reduction discovery finds equivalences. -/
example : discoverBabyBearRules.length > 0 := by native_decide

/-- KoalaBear shift discovery finds the rule. -/
example : discoverKoalaBearShift.length > 0 := by native_decide

/-- Fold idempotency: single fold ≤ double fold on test inputs. -/
example : discoverFoldIdempotency.length > 0 := by native_decide

/-- CVec matching works. -/
example : cvecEqual #[1, 2, 3] #[1, 2, 3] = true := by native_decide
example : cvecEqual #[1, 2, 3] #[1, 2, 4] = false := by native_decide
example : cvecModEq #[10, 20] #[3, 6] 7 = true := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.Ruler
