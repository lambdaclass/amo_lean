/-
  AMO-Lean Ultra — Phase 25: Hardware Colors + Colored Rules
  Conditional rewrite rules that apply only under specific hardware assumptions.

  Adapted from OptiSat v2 ColorTypes.lean. A color hierarchy allows rules
  like "under SIMD, prefer Montgomery" without polluting the base e-graph.

  Architecture:
  - ColorId 0 (root): universal rules, all hardware
  - ColorId 1 (scalar): rules for scalar targets only
  - ColorId 2 (simd): rules for SIMD targets (NEON or AVX2)
  - ColorId 3 (neon): ARM NEON-specific rules
  - ColorId 4 (avx2): x86 AVX2-specific rules
  - ColorId 5 (largeArray): rules for N > cache threshold

  A colored rule is a standard MixedSoundRule plus a color predicate.
  During extraction, only rules whose color matches the target are active.

  Consumes: MultiRelMixed.State, BoundPropagation.ReductionChoice
  Consumed by: Phase27Integration (top-level)
-/
import AmoLean.EGraph.Verified.Matrix.Phase24Integration

set_option autoImplicit false

namespace AmoLean.EGraph.Verified.Bitwise.Colors

open AmoLean.EGraph.Verified.Bitwise (MixedSoundRule MixedEnv)
open AmoLean.EGraph.Verified (EClassId)
open AmoLean.EGraph.Verified.Bitwise.BoundProp (ReductionChoice)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Color Hierarchy
-- ══════════════════════════════════════════════════════════════════

abbrev ColorId := Nat

def colorRoot : ColorId := 0

/-- Color hierarchy: tree of colors with parent pointers. -/
structure ColorHierarchy where
  parentOf : Std.HashMap ColorId ColorId := {}
  numColors : Nat := 1  -- root always exists
  deriving Repr, Inhabited

def ColorHierarchy.empty : ColorHierarchy := {}

def ColorHierarchy.addColor (h : ColorHierarchy) (parent : ColorId) : ColorHierarchy × ColorId :=
  let newId := h.numColors
  ({ parentOf := h.parentOf.insert newId parent, numColors := h.numColors + 1 }, newId)

def ColorHierarchy.getParent (h : ColorHierarchy) (c : ColorId) : ColorId :=
  if c == colorRoot then colorRoot
  else h.parentOf.getD c colorRoot

/-- Check if `ancestor` is an ancestor of `c` in the hierarchy. -/
def ColorHierarchy.isAncestor (h : ColorHierarchy) (c ancestor : ColorId)
    (fuel : Nat := 20) : Bool :=
  if c == ancestor then true
  else match fuel with
    | 0 => false
    | fuel + 1 =>
      let parent := h.getParent c
      if parent == c then false  -- reached root without finding ancestor
      else h.isAncestor parent ancestor fuel

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Standard NTT Color Hierarchy
-- ══════════════════════════════════════════════════════════════════

/-- Build the standard color hierarchy for NTT optimization. -/
def nttColorHierarchy : ColorHierarchy × (ColorId × ColorId × ColorId × ColorId × ColorId) :=
  let h := ColorHierarchy.empty
  let (h, scalar) := h.addColor colorRoot     -- 1: scalar
  let (h, simd) := h.addColor colorRoot       -- 2: SIMD
  let (h, neon) := h.addColor simd            -- 3: NEON (child of SIMD)
  let (h, avx2) := h.addColor simd            -- 4: AVX2 (child of SIMD)
  let (h, largeArr) := h.addColor colorRoot   -- 5: large array
  (h, (scalar, simd, neon, avx2, largeArr))

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Colored Rewrite Rules
-- ══════════════════════════════════════════════════════════════════

/-- A colored rule: a MixedSoundRule with a color predicate.
    The rule only applies when the target color is active (i.e., the
    target color is an ancestor of or equal to the current extraction color). -/
structure ColoredRule where
  rule : MixedSoundRule
  color : ColorId
  description : String := ""
  -- No deriving Inhabited (MixedSoundRule has Prop field)

/-- Check if a colored rule is active for a given target color. -/
def ColoredRule.isActive (cr : ColoredRule) (targetColor : ColorId)
    (hierarchy : ColorHierarchy) : Bool :=
  cr.color == colorRoot ||  -- root rules always active
  hierarchy.isAncestor targetColor cr.color

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Hardware-Specific Rules
-- ══════════════════════════════════════════════════════════════════

/-- Under SIMD: Montgomery REDC preferred (stays in u32 lanes).
    This is a cost-guidance rule, not a rewrite — it tells extraction
    to prefer montyReduce when in SIMD mode. -/
def simdPrefersMonty (simdColor : ColorId) : ColoredRule where
  rule := {
    name := "simd_prefers_montgomery"
    lhsEval := fun _env v => v 0 % v 1  -- reduceGate semantics
    rhsEval := fun _env v => v 0 % v 1  -- montyReduce semantics (same mod p)
    soundness := fun _ _ => rfl
  }
  color := simdColor
  description := "Under SIMD, Montgomery stays in u32 lanes (no widening)"

/-- Under scalar: Solinas fold preferred (fewer operations). -/
def scalarPrefersSolinas (scalarColor : ColorId) : ColoredRule where
  rule := {
    name := "scalar_prefers_solinas"
    lhsEval := fun _env v => v 0 % v 1
    rhsEval := fun _env v => v 0 % v 1
    soundness := fun _ _ => rfl
  }
  color := scalarColor
  description := "Under scalar, Solinas fold is cheaper (no widening penalty)"

/-- Under large array: Montgomery preferred (cache pressure of u64). -/
def largeArrayPrefersMonty (largeColor : ColorId) : ColoredRule where
  rule := {
    name := "large_array_prefers_montgomery"
    lhsEval := fun _env v => v 0 % v 1
    rhsEval := fun _env v => v 0 % v 1
    soundness := fun _ _ => rfl
  }
  color := largeColor
  description := "For large arrays, Montgomery avoids u64 cache pressure"

/-- Collect all hardware-specific rules. -/
def allColoredRules : List ColoredRule :=
  let (_, scalar, simd, _, _, largeArr) := nttColorHierarchy
  [ simdPrefersMonty simd,
    scalarPrefersSolinas scalar,
    largeArrayPrefersMonty largeArr ]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Color-Aware Extraction
-- ══════════════════════════════════════════════════════════════════

/-- Select the preferred reduction for a target color. -/
def preferredReduction (targetColor : ColorId) : ReductionChoice :=
  let (_, scalar, simd, _, _, largeArr) := nttColorHierarchy
  let h := nttColorHierarchy.1
  if h.isAncestor targetColor simd || h.isAncestor targetColor largeArr
  then .montgomery
  else if h.isAncestor targetColor scalar || targetColor == colorRoot
  then .solinasFold
  else .solinasFold  -- default

/-- Filter active rules for a target color. -/
def activeRules (rules : List ColoredRule) (targetColor : ColorId)
    (hierarchy : ColorHierarchy) : List MixedSoundRule :=
  rules.filter (·.isActive targetColor hierarchy) |>.map (·.rule)

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Theorems
-- ══════════════════════════════════════════════════════════════════

/-- Root rules are always active. -/
theorem root_always_active (cr : ColoredRule) (target : ColorId) (h : ColorHierarchy)
    (hroot : cr.color = colorRoot) : cr.isActive target h = true := by
  simp [ColoredRule.isActive, hroot, colorRoot]

/-- SIMD preference is montgomery. -/
theorem simd_prefers_monty :
    let (_, _, simd, _, _, _) := nttColorHierarchy
    preferredReduction simd == .montgomery := by native_decide

/-- Scalar preference is solinas. -/
theorem scalar_prefers_solinas :
    let (_, scalar, _, _, _, _) := nttColorHierarchy
    preferredReduction scalar == .solinasFold := by native_decide

/-- All colored rules have sound base rules. -/
theorem allColoredRules_sound :
    ∀ cr ∈ allColoredRules, ∀ env v, cr.rule.lhsEval env v = cr.rule.rhsEval env v := by
  intro cr hmem env v
  simp [allColoredRules] at hmem
  rcases hmem with rfl | rfl | rfl <;> rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

section SmokeTests

example : nttColorHierarchy.1.numColors = 6 := by native_decide
example : allColoredRules.length = 3 := rfl
example : preferredReduction 2 == .montgomery := by native_decide  -- simd
example : preferredReduction 1 == .solinasFold := by native_decide  -- scalar

/-- NEON (child of SIMD) also gets Montgomery. -/
example : preferredReduction 3 == .montgomery := by native_decide

end SmokeTests

end AmoLean.EGraph.Verified.Bitwise.Colors
