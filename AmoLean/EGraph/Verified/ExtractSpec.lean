/-
  AMO-Lean — Extraction Correctness Specification
  Fase 11 N11.4: Formal verification of greedy + ILP extraction

  Key theorems:
  - `extractF_correct`: greedy extraction produces semantically correct expressions
  - `extractILP_correct`: ILP-guided extraction produces correct expressions
  - `validSolution_decompose`: ValidSolution ↔ all 4 checks pass
  - 4 decomposition theorems: checkRootActive_sound, checkExactlyOne_sound,
    checkChildDeps_sound, checkAcyclicity_sound

  Adapted from OptiSat/ExtractSpec + ILPSpec for the AMO circuit domain.
-/
import AmoLean.EGraph.Verified.SaturationSpec
import AmoLean.EGraph.Verified.ILP

namespace AmoLean.EGraph.Verified

open UnionFind ILP

set_option linter.unusedSectionVars false

variable {Val : Type} [Add Val] [Mul Val] [Neg Val]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: mapOption (total helper with spec lemmas)
-- ══════════════════════════════════════════════════════════════════

/-- Apply `f` to each element, collecting results.
    Returns `none` if any application returns `none`. -/
def mapOption (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as =>
    match f a with
    | none => none
    | some b =>
      match mapOption f as with
      | none => none
      | some bs => some (b :: bs)

@[simp] theorem mapOption_nil (f : α → Option β) : mapOption f [] = some [] := rfl

/-- Inversion lemma for cons case. -/
theorem mapOption_cons_inv {f : α → Option β} {a : α} {as : List α} {results : List β}
    (h : mapOption f (a :: as) = some results) :
    ∃ b bs, f a = some b ∧ mapOption f as = some bs ∧ results = b :: bs := by
  simp only [mapOption] at h
  split at h
  · exact absurd h (by simp)
  · rename_i b hb
    split at h
    · exact absurd h (by simp)
    · rename_i bs hbs
      exact ⟨b, bs, hb, hbs, (Option.some.inj h).symm⟩

theorem mapOption_length {f : α → Option β} {l : List α} {results : List β}
    (h : mapOption f l = some results) : results.length = l.length := by
  induction l generalizing results with
  | nil => simp [mapOption] at h; subst h; rfl
  | cons a as ih =>
    obtain ⟨b, bs, _, hrest, hrsl⟩ := mapOption_cons_inv h
    subst hrsl
    simp [ih hrest]

theorem mapOption_get {f : α → Option β} {l : List α} {results : List β}
    (h : mapOption f l = some results)
    (i : Nat) (hil : i < l.length) (hir : i < results.length) :
    f l[i] = some results[i] := by
  induction l generalizing results i with
  | nil => exact absurd hil (Nat.not_lt_zero _)
  | cons a as ih =>
    obtain ⟨b, bs, hfa, hrest, hrsl⟩ := mapOption_cons_inv h
    subst hrsl
    match i with
    | 0 => exact hfa
    | i + 1 =>
      exact ih hrest i (Nat.lt_of_succ_lt_succ hil) (Nat.lt_of_succ_lt_succ hir)

/-- `mapOption` is monotone: if `f` results are preserved by `g`, so is `mapOption`. -/
theorem mapOption_mono {α β : Type _} {f g : α → Option β} {l : List α} {bs : List β}
    (hm : mapOption f l = some bs)
    (hmono : ∀ a ∈ l, ∀ b, f a = some b → g a = some b) :
    mapOption g l = some bs := by
  induction l generalizing bs with
  | nil => simp [mapOption] at hm ⊢; exact hm
  | cons hd tl ih =>
    simp only [mapOption] at hm ⊢
    split at hm
    · exact absurd hm (by simp)
    · rename_i b hfhd
      split at hm
      · exact absurd hm (by simp)
      · rename_i bs' hmf
        have hbs : bs = b :: bs' := by cases hm; rfl
        rw [hmono hd (List.mem_cons.mpr (Or.inl rfl)) b hfhd]
        rw [ih hmf (fun a ha b hfa => hmono a (List.mem_cons.mpr (Or.inr ha)) b hfa)]
        rw [hbs]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Extractable + BestNodeInv
-- ══════════════════════════════════════════════════════════════════

/-- Typeclass for reconstructing expressions from e-graph circuit nodes.
    `Expr` is the target expression language (e.g., symbolic circuit AST). -/
class CircuitExtractable (Expr : Type) where
  reconstruct : CircuitNodeOp → List Expr → Option Expr

/-- Typeclass for evaluating extracted circuit expressions. -/
class CircuitEvalExpr (Expr : Type) (Val : Type) where
  evalExpr : Expr → CircuitEnv Val → Val

/-- Soundness law: if reconstruction succeeds and each child expression evaluates
    to the value of its corresponding child class, then the result evaluates to
    `NodeEval` applied to those child values.
    This is the key bridge: extracted Expr semantics ↔ e-graph NodeEval. -/
def CircuitExtractableSound (Expr Val : Type) [Add Val] [Mul Val] [Neg Val]
    [CircuitExtractable Expr] [CircuitEvalExpr Expr Val] : Prop :=
  ∀ (node : ENode) (childExprs : List Expr) (expr : Expr)
    (env : CircuitEnv Val) (v : EClassId → Val),
  CircuitExtractable.reconstruct node.op childExprs = some expr →
  childExprs.length = node.children.length →
  (∀ (i : Nat) (hi : i < childExprs.length) (hio : i < node.children.length),
    CircuitEvalExpr.evalExpr childExprs[i] env =
      v (node.children[i]'hio)) →
  CircuitEvalExpr.evalExpr expr env = NodeEval node env v

/-- BestNodeInv: every class with a bestNode has that node in its nodes array. -/
def BestNodeInv (classes : Std.HashMap EClassId EClass) : Prop :=
  ∀ classId eclass bestNode,
    classes.get? classId = some eclass →
    eclass.bestNode = some bestNode →
    bestNode ∈ eclass.nodes.toList

-- ══════════════════════════════════════════════════════════════════
-- Section 3: extractF (fuel-based greedy extraction)
-- ══════════════════════════════════════════════════════════════════

variable {Expr : Type} [CircuitExtractable Expr]

/-- Extract an expression from the e-graph starting at class `id`.
    Follows `bestNode` pointers set by `computeCosts`.
    Uses fuel for termination. -/
def extractF (g : EGraph) (id : EClassId) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
    let canonId := root g.unionFind id
    match g.classes.get? canonId with
    | none => none
    | some eclass =>
      match eclass.bestNode with
      | none => none
      | some bestNode =>
        match mapOption (fun c => extractF g c fuel) bestNode.children with
        | none => none
        | some childExprs => CircuitExtractable.reconstruct bestNode.op childExprs

@[simp] theorem extractF_zero (g : EGraph) (id : EClassId) :
    extractF g id 0 = (none : Option Expr) := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 4: extractF_correct
-- ══════════════════════════════════════════════════════════════════

variable [CircuitEvalExpr Expr Val]

/-- Greedy extraction produces semantically correct expressions.

    If ConsistentValuation + BestNodeInv + CircuitExtractableSound,
    then extractF returns an expression that evaluates to the correct value. -/
theorem extractF_correct (g : EGraph) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : CircuitExtractableSound Expr Val) :
    ∀ (fuel : Nat) (classId : EClassId) (expr : Expr),
      extractF g classId fuel = some expr →
      CircuitEvalExpr.evalExpr expr env = v (root g.unionFind classId) := by
  intro fuel
  induction fuel with
  | zero => intro classId expr h; simp [extractF] at h
  | succ n ih =>
    intro classId expr hext
    unfold extractF at hext
    simp only [] at hext
    split at hext
    · exact absurd hext (by simp)
    · rename_i eclass heclass
      split at hext
      · exact absurd hext (by simp)
      · rename_i bestNode hbestNode
        split at hext
        · exact absurd hext (by simp)
        · rename_i childExprs hmapOpt
          have hbn_mem := hbni _ _ _ heclass hbestNode
          have heval := hcv.2 (root g.unionFind classId) eclass heclass bestNode hbn_mem
          have hlen := mapOption_length hmapOpt
          have hchildren : ∀ (i : Nat) (hi : i < childExprs.length)
              (hio : i < bestNode.children.length),
              CircuitEvalExpr.evalExpr childExprs[i] env =
                v (bestNode.children[i]'hio) := by
            intro i hi hio
            have hget := mapOption_get hmapOpt i hio hi
            simp only [] at hget
            rw [ih _ _ hget]
            exact consistent_root_eq' g env v hcv hwf _
          rw [hsound bestNode childExprs expr env v hext hlen hchildren]
          exact heval

-- ══════════════════════════════════════════════════════════════════
-- Section 5: ILP Check Functions
-- ══════════════════════════════════════════════════════════════════

/-- Check that the root class is active. -/
def checkRootActive (rootId : EClassId) (sol : ILPSolution) : Bool :=
  sol.isActive rootId

/-- Check: every active class has exactly one selected node with valid index;
    every inactive class has no selected node. -/
def checkExactlyOne (g : EGraph) (sol : ILPSolution) : Bool :=
  g.classes.fold (init := true) fun acc classId eclass =>
    if sol.isActive classId then
      match sol.selectedNodes.get? classId with
      | some idx => acc && decide (idx < eclass.nodes.size)
      | none => false
    else acc && (sol.selectedNodes.get? classId).isNone

/-- Check: for every class with a selected node, all children are active. -/
def checkChildDeps (g : EGraph) (sol : ILPSolution) : Bool :=
  g.classes.fold (init := true) fun acc classId eclass =>
    match sol.selectedNodes.get? classId with
    | none => acc
    | some nIdx =>
      if h : nIdx < eclass.nodes.size then
        acc && (eclass.nodes[nIdx]).children.all fun child =>
          sol.isActive (root g.unionFind child)
      else acc

/-- Check: DAG property — children have strictly lower levels. -/
def checkAcyclicity (g : EGraph) (sol : ILPSolution) : Bool :=
  g.classes.fold (init := true) fun acc classId eclass =>
    match sol.selectedNodes.get? classId with
    | none => acc
    | some nIdx =>
      if h : nIdx < eclass.nodes.size then
        acc && (eclass.nodes[nIdx]).children.all fun child =>
          let canonChild := root g.unionFind child
          if canonChild == classId then true
          else sol.getLevel classId > sol.getLevel canonChild
      else acc

/-- Combined check: all four conditions. -/
def checkSolution (g : EGraph) (rootId : EClassId) (sol : ILPSolution) : Bool :=
  checkRootActive (root g.unionFind rootId) sol &&
  checkExactlyOne g sol &&
  checkChildDeps g sol &&
  checkAcyclicity g sol

/-- A valid ILP solution: checkSolution passes. -/
def ValidSolution (g : EGraph) (rootId : EClassId) (sol : ILPSolution) : Prop :=
  checkSolution g rootId sol = true

-- ══════════════════════════════════════════════════════════════════
-- Section 6: HashMap.fold decomposition lemmas
-- ══════════════════════════════════════════════════════════════════

/-- A foldl with monotone-false body starting at false stays false. -/
private theorem foldl_false_stays {α : Type _} (f : Bool → α → Bool)
    (hf : ∀ x, f false x = false) (l : List α) :
    List.foldl f false l = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, hf, ih]

/-- If foldl with init := true and monotone-false body returns true,
    then every element satisfies the body with acc = true. -/
private theorem foldl_bool_true {α : Type _} {l : List α} {f : Bool → α → Bool}
    (hf : ∀ x, f false x = false)
    (h : List.foldl f true l = true) :
    ∀ x ∈ l, f true x = true := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons hd tl ih =>
    intro x hx
    simp only [List.foldl_cons] at h
    cases hfhd : f true hd with
    | true =>
      rw [hfhd] at h
      cases List.mem_cons.mp hx with
      | inl heq => rw [heq]; exact hfhd
      | inr hmem => exact ih h x hmem
    | false =>
      rw [hfhd] at h; rw [foldl_false_stays f hf tl] at h
      exact absurd h Bool.false_ne_true

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Check soundness theorems
-- ══════════════════════════════════════════════════════════════════

theorem checkRootActive_sound (rootId : EClassId) (sol : ILPSolution)
    (h : checkRootActive rootId sol = true) :
    sol.isActive rootId = true := h

theorem checkExactlyOne_sound (g : EGraph) (sol : ILPSolution)
    (h : checkExactlyOne g sol = true)
    (classId : EClassId) (eclass : EClass)
    (hget : g.classes.get? classId = some eclass) :
    (sol.isActive classId = true →
      ∃ idx, sol.selectedNodes.get? classId = some idx ∧
             idx < eclass.nodes.size) ∧
    (sol.isActive classId = false →
      (sol.selectedNodes.get? classId).isNone = true) := by
  unfold checkExactlyOne at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  let body : Bool → EClassId × EClass → Bool := fun acc b =>
    if sol.isActive b.1 = true then
      match sol.selectedNodes.get? b.1 with
      | some idx => acc && decide (idx < b.2.nodes.size)
      | none => false
    else acc && (sol.selectedNodes.get? b.1).isNone
  have hf_mono : ∀ x, body false x = false := by
    intro ⟨cid, ecl⟩; simp only [body]
    split
    · split <;> simp [Bool.false_and]
    · simp [Bool.false_and]
  have hall := foldl_bool_true hf_mono (f := body) h
  have hmem : (classId, eclass) ∈ g.classes.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.HashMap.get?_eq_getElem? ▸ hget)
  have hpair := hall (classId, eclass) hmem
  simp only [body] at hpair
  constructor
  · intro hactive
    rw [hactive] at hpair; simp only [↓reduceIte] at hpair
    split at hpair
    · rename_i idx hidx; exact ⟨idx, hidx, by simpa using hpair⟩
    · exact absurd hpair Bool.false_ne_true
  · intro hinactive
    rw [hinactive] at hpair
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and] at hpair
    exact hpair

theorem checkChildDeps_sound (g : EGraph) (sol : ILPSolution)
    (h : checkChildDeps g sol = true)
    (classId : EClassId) (eclass : EClass)
    (hget : g.classes.get? classId = some eclass)
    (idx : Nat) (hsel : sol.selectedNodes.get? classId = some idx)
    (hidx : idx < eclass.nodes.size) :
    ∀ child ∈ (eclass.nodes[idx]).children,
      sol.isActive (root g.unionFind child) = true := by
  unfold checkChildDeps at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  let body : Bool → EClassId × EClass → Bool := fun acc b =>
    match sol.selectedNodes.get? b.1 with
    | none => acc
    | some nIdx =>
      if _hh : nIdx < b.2.nodes.size then
        acc && (b.2.nodes[nIdx]).children.all fun child =>
          sol.isActive (root g.unionFind child)
      else acc
  have hf_mono : ∀ x, body false x = false := by
    intro ⟨cid, ecl⟩; simp only [body]
    split
    · rfl
    · split
      · simp [Bool.false_and]
      · rfl
  have hall := foldl_bool_true hf_mono (f := body) h
  have hmem : (classId, eclass) ∈ g.classes.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.HashMap.get?_eq_getElem? ▸ hget)
  have hpair := hall (classId, eclass) hmem
  simp only [body, hsel, dif_pos hidx, Bool.true_and] at hpair
  exact List.all_eq_true.mp hpair

theorem checkAcyclicity_sound (g : EGraph) (sol : ILPSolution)
    (h : checkAcyclicity g sol = true)
    (classId : EClassId) (eclass : EClass)
    (hget : g.classes.get? classId = some eclass)
    (idx : Nat) (hsel : sol.selectedNodes.get? classId = some idx)
    (hidx : idx < eclass.nodes.size) :
    ∀ child ∈ (eclass.nodes[idx]).children,
      root g.unionFind child ≠ classId →
      sol.getLevel classId > sol.getLevel (root g.unionFind child) := by
  unfold checkAcyclicity at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  let body : Bool → EClassId × EClass → Bool := fun acc b =>
    match sol.selectedNodes.get? b.1 with
    | none => acc
    | some nIdx =>
      if _hh : nIdx < b.2.nodes.size then
        acc && (b.2.nodes[nIdx]).children.all fun child =>
          let canonChild := root g.unionFind child
          if canonChild == b.1 then true
          else sol.getLevel b.1 > sol.getLevel canonChild
      else acc
  have hf_mono : ∀ x, body false x = false := by
    intro ⟨cid, ecl⟩; simp only [body]
    split
    · rfl
    · split
      · simp [Bool.false_and]
      · rfl
  have hall := foldl_bool_true hf_mono (f := body) h
  have hmem : (classId, eclass) ∈ g.classes.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.HashMap.get?_eq_getElem? ▸ hget)
  have hpair := hall (classId, eclass) hmem
  simp only [body, hsel, dif_pos hidx, Bool.true_and] at hpair
  intro child hchild hneq
  have hc := (List.all_eq_true.mp hpair) child hchild
  simp [beq_eq_false_iff_ne.mpr hneq] at hc
  exact hc

-- ══════════════════════════════════════════════════════════════════
-- Section 8: validSolution_decompose
-- ══════════════════════════════════════════════════════════════════

/-- Decompose `ValidSolution` into its four constituent checks. -/
theorem validSolution_decompose (g : EGraph) (rootId : EClassId)
    (sol : ILPSolution) (hv : ValidSolution g rootId sol) :
    sol.isActive (root g.unionFind rootId) = true ∧
    checkExactlyOne g sol = true ∧
    checkChildDeps g sol = true ∧
    checkAcyclicity g sol = true := by
  simp only [ValidSolution, checkSolution, checkRootActive, Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 9: extractILP (ILP-guided extraction)
-- ══════════════════════════════════════════════════════════════════

/-- ILP-guided extraction: follows the ILP solution's selected nodes. -/
def extractILP (g : EGraph) (sol : ILPSolution) (classId : EClassId) :
    Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
    let canonId := root g.unionFind classId
    match sol.selectedNodes.get? canonId with
    | none => none
    | some nodeIdx =>
      match g.classes.get? canonId with
      | none => none
      | some eclass =>
        if h : nodeIdx < eclass.nodes.size then
          match mapOption (fun c => extractILP g sol (root g.unionFind c) fuel)
              (eclass.nodes[nodeIdx]).children with
          | none => none
          | some childExprs =>
            CircuitExtractable.reconstruct (eclass.nodes[nodeIdx]).op childExprs
        else none

-- ══════════════════════════════════════════════════════════════════
-- Section 10: extractILP_correct
-- ══════════════════════════════════════════════════════════════════

/-- ILP-guided extraction produces semantically correct expressions.
    Proof strategy mirrors extractF_correct but uses ILP solution as guide. -/
theorem extractILP_correct (g : EGraph) (rootId : EClassId)
    (sol : ILPSolution) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (_hvalid : ValidSolution g rootId sol)
    (hsound : CircuitExtractableSound Expr Val) :
    ∀ (fuel : Nat) (classId : EClassId) (expr : Expr),
      extractILP g sol classId fuel = some expr →
      CircuitEvalExpr.evalExpr expr env = v (root g.unionFind classId) := by
  intro fuel
  induction fuel with
  | zero => intro classId expr h; simp [extractILP] at h
  | succ n ih =>
    intro classId expr hext
    unfold extractILP at hext
    simp only [] at hext
    split at hext
    · exact absurd hext (by simp)
    · rename_i nodeIdx hselected
      split at hext
      · exact absurd hext (by simp)
      · rename_i eclass heclass
        split at hext
        · rename_i hidx
          split at hext
          · exact absurd hext (by simp)
          · rename_i childExprs hmapOpt
            have hnode_mem : (eclass.nodes[nodeIdx]) ∈ eclass.nodes.toList :=
              Array.getElem_mem_toList hidx
            have heval := hcv.2 (root g.unionFind classId) eclass heclass
              (eclass.nodes[nodeIdx]) hnode_mem
            have hlen := mapOption_length hmapOpt
            have hchildren : ∀ (i : Nat) (hi : i < childExprs.length)
                (hio : i < (eclass.nodes[nodeIdx]).children.length),
                CircuitEvalExpr.evalExpr childExprs[i] env =
                  v ((eclass.nodes[nodeIdx]).children[i]'hio) := by
              intro i hi hio
              have hget := mapOption_get hmapOpt i hio hi
              simp only [] at hget
              rw [ih _ _ hget]
              rw [consistent_root_eq' g env v hcv hwf _]
              exact consistent_root_eq' g env v hcv hwf _
            rw [hsound (eclass.nodes[nodeIdx]) childExprs expr env v hext hlen hchildren]
            exact heval
        · simp at hext

/-- End-to-end ILP extraction soundness. -/
theorem ilp_extraction_soundness (g : EGraph) (rootId : EClassId)
    (sol : ILPSolution) (env : CircuitEnv Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hvalid : ValidSolution g rootId sol)
    (hsound : CircuitExtractableSound Expr Val)
    (fuel : Nat) (expr : Expr)
    (hext : extractILP g sol rootId fuel = some expr) :
    CircuitEvalExpr.evalExpr expr env = v (root g.unionFind rootId) :=
  extractILP_correct g rootId sol env v hcv hwf hvalid hsound fuel rootId expr hext

-- ══════════════════════════════════════════════════════════════════
-- Section 11: Fuel monotonicity
-- ══════════════════════════════════════════════════════════════════

/-- Fuel monotonicity: if extraction succeeds with fuel n, it succeeds with m ≥ n. -/
theorem extractILP_fuel_mono (g : EGraph) (sol : ILPSolution) (id : EClassId) :
    ∀ (n m : Nat) (expr : Expr), n ≤ m →
    extractILP g sol id n = some expr →
    extractILP g sol id m = some expr := by
  intro n
  induction n generalizing id with
  | zero => intro m expr _ h; simp [extractILP] at h
  | succ k ih =>
    intro m expr hle h
    obtain ⟨m', rfl⟩ : ∃ m', m = k + 1 + m' := ⟨m - (k + 1), by omega⟩
    have hm : k + 1 + m' = (k + m') + 1 := by omega
    rw [hm]
    simp only [extractILP] at h ⊢
    split at h
    · exact absurd h (by simp)
    · rename_i nodeIdx hsel
      split at h
      · exact absurd h (by simp)
      · rename_i eclass hcls
        split at h
        · rename_i hidx
          split at h
          · exact absurd h (by simp)
          · rename_i childExprs hmapOpt
            simp only [dif_pos hidx] at ⊢
            have hmono : mapOption (fun c => extractILP g sol (root g.unionFind c) (k + m'))
                (eclass.nodes[nodeIdx]).children = some childExprs :=
              mapOption_mono hmapOpt (fun a _ b hfa =>
                ih (root g.unionFind a) (k + m') b (by omega) hfa)
            rw [hmono]
            exact h
        · simp at h

end AmoLean.EGraph.Verified
