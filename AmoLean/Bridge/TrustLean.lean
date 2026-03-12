/-
  AMO-Lean v2.2.0 — Trust-Lean Bridge
  Bridge/TrustLean.lean: Type conversion between AmoLean and Trust-Lean

  N10.1 (v2.2.0): Lake dependency + import verification.
  N10.2 (v2.2.0): Type conversion functions + roundtrip proofs.
  v3.0 integration: MicroC pipeline (stmtToMicroC + microCToString + roundtrip).

  This is the ONLY module that directly imports Trust-Lean.
  All other AmoLean modules access Trust-Lean types through this bridge.

  Design: convertScalarVar returns Option because AmoLean uses String names
  (infinite domain) but only {"x","y","t"} are valid for ExpandedSigma.
  All other conversions (IdxExpr, Gather, Scatter) are total isomorphisms.

  Two code generation paths:
  - verifiedCodeGen: ExpandedSigma → Stmt → stmtToC (CBackend, industrial C)
  - verifiedCodeGenMicroC: ExpandedSigma → Stmt → MicroCStmt → microCToString
    (formal C semantics + roundtrip guarantee from Trust-Lean v3.0)
-/

import TrustLean.Bridge
import TrustLean.Backend.CBackend
import TrustLean.MicroC.Translation
import TrustLean.MicroC.PrettyPrint
import TrustLean.MicroC.RoundtripMaster
import AmoLean.Sigma.Expand

set_option autoImplicit false

namespace AmoLean.Bridge.TrustLean

open AmoLean.Sigma

/-! ## ScalarVar Conversion (Partial) -/

/-- Convert AmoLean ScalarVar (name, idx) to Trust-Lean ScalarVar (kind, idx).
    Returns `none` for variable names outside {"x", "y", "t"}. -/
def convertScalarVar : ScalarVar → Option _root_.TrustLean.Bridge.ScalarVar
  | ⟨"x", idx⟩ => some ⟨.input, idx⟩
  | ⟨"y", idx⟩ => some ⟨.output, idx⟩
  | ⟨"t", idx⟩ => some ⟨.temp, idx⟩
  | _ => none

/-- Convert Trust-Lean ScalarVar back to AmoLean ScalarVar. Total function. -/
def convertBackScalarVar : _root_.TrustLean.Bridge.ScalarVar → ScalarVar
  | ⟨.input, idx⟩ => ⟨"x", idx⟩
  | ⟨.output, idx⟩ => ⟨"y", idx⟩
  | ⟨.temp, idx⟩ => ⟨"t", idx⟩

/-! ## ScalarVar Roundtrip Proofs -/

/-- Backward roundtrip: TrustLean → AmoLean → TrustLean always succeeds. -/
@[simp] theorem roundtrip_scalarVar_backward (v : _root_.TrustLean.Bridge.ScalarVar) :
    convertScalarVar (convertBackScalarVar v) = some v := by
  match v with
  | ⟨.input, _⟩ => rfl
  | ⟨.output, _⟩ => rfl
  | ⟨.temp, _⟩ => rfl

/-- Forward roundtrip: if conversion succeeds, converting back yields the original. -/
theorem roundtrip_scalarVar_forward (v : ScalarVar)
    (v' : _root_.TrustLean.Bridge.ScalarVar)
    (h : convertScalarVar v = some v') :
    convertBackScalarVar v' = v := by
  revert v'
  obtain ⟨name, idx⟩ := v
  unfold convertScalarVar
  split <;> intro v' h
  all_goals first
    | (next heq =>
        simp only [ScalarVar.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at h
        subst h; rfl)
    | exact absurd h (by simp)

/-- ScalarVar conversion succeeds for input variables. -/
@[simp] theorem convertScalarVar_input (n : Nat) :
    convertScalarVar (ScalarVar.input n) = some ⟨.input, n⟩ := rfl

/-- ScalarVar conversion succeeds for output variables. -/
@[simp] theorem convertScalarVar_output (n : Nat) :
    convertScalarVar (ScalarVar.output n) = some ⟨.output, n⟩ := rfl

/-- ScalarVar conversion succeeds for temp variables. -/
@[simp] theorem convertScalarVar_temp (n : Nat) :
    convertScalarVar (ScalarVar.temp n) = some ⟨.temp, n⟩ := rfl

/-! ## IdxExpr Conversion (Total Isomorphism) -/

/-- Convert AmoLean IdxExpr to Trust-Lean IdxExpr. O(n) in expression size. -/
def convertIdxExpr : IdxExpr → _root_.TrustLean.Bridge.IdxExpr
  | .const n => .const n
  | .var v => .var v
  | .affine b s v => .affine b s v
  | .add e1 e2 => .add (convertIdxExpr e1) (convertIdxExpr e2)
  | .mul c e => .mul c (convertIdxExpr e)

/-- Convert Trust-Lean IdxExpr back to AmoLean IdxExpr. -/
def convertBackIdxExpr : _root_.TrustLean.Bridge.IdxExpr → IdxExpr
  | .const n => .const n
  | .var v => .var v
  | .affine b s v => .affine b s v
  | .add e1 e2 => .add (convertBackIdxExpr e1) (convertBackIdxExpr e2)
  | .mul c e => .mul c (convertBackIdxExpr e)

@[simp] theorem roundtrip_idxExpr_backward (e : _root_.TrustLean.Bridge.IdxExpr) :
    convertIdxExpr (convertBackIdxExpr e) = e := by
  induction e with
  | const | var | affine => rfl
  | add _ _ ih1 ih2 => simp [convertBackIdxExpr, convertIdxExpr, ih1, ih2]
  | mul _ _ ih => simp [convertBackIdxExpr, convertIdxExpr, ih]

@[simp] theorem roundtrip_idxExpr_forward (e : IdxExpr) :
    convertBackIdxExpr (convertIdxExpr e) = e := by
  induction e with
  | const | var | affine => rfl
  | add _ _ ih1 ih2 => simp [convertIdxExpr, convertBackIdxExpr, ih1, ih2]
  | mul _ _ ih => simp [convertIdxExpr, convertBackIdxExpr, ih]

/-! ## Gather/Scatter Conversion (Total Isomorphism) -/

/-- Convert AmoLean Gather to Trust-Lean Gather. -/
def convertGather (g : Gather) : _root_.TrustLean.Bridge.Gather :=
  ⟨g.count, convertIdxExpr g.baseAddr, g.stride⟩

/-- Convert Trust-Lean Gather back to AmoLean Gather. -/
def convertBackGather (g : _root_.TrustLean.Bridge.Gather) : Gather :=
  ⟨g.count, convertBackIdxExpr g.baseAddr, g.stride⟩

/-- Convert AmoLean Scatter to Trust-Lean Scatter. -/
def convertScatter (s : Scatter) : _root_.TrustLean.Bridge.Scatter :=
  ⟨s.count, convertIdxExpr s.baseAddr, s.stride⟩

/-- Convert Trust-Lean Scatter back to AmoLean Scatter. -/
def convertBackScatter (s : _root_.TrustLean.Bridge.Scatter) : Scatter :=
  ⟨s.count, convertBackIdxExpr s.baseAddr, s.stride⟩

@[simp] theorem roundtrip_gather_backward (g : _root_.TrustLean.Bridge.Gather) :
    convertGather (convertBackGather g) = g := by
  simp [convertGather, convertBackGather]

@[simp] theorem roundtrip_gather_forward (g : Gather) :
    convertBackGather (convertGather g) = g := by
  simp [convertGather, convertBackGather]

@[simp] theorem roundtrip_scatter_backward (s : _root_.TrustLean.Bridge.Scatter) :
    convertScatter (convertBackScatter s) = s := by
  simp [convertScatter, convertBackScatter]

@[simp] theorem roundtrip_scatter_forward (s : Scatter) :
    convertBackScatter (convertScatter s) = s := by
  simp [convertScatter, convertBackScatter]

/-! ## ScalarExpr Conversion -/

/-- Convert AmoLean ScalarExpr to Trust-Lean ScalarExpr. O(n) in expression size. -/
def convertScalarExpr : ScalarExpr → Option _root_.TrustLean.Bridge.ScalarExpr
  | .var v => (convertScalarVar v).map .var
  | .const n => some (.const n)
  | .neg e => (convertScalarExpr e).map .neg
  | .add e1 e2 => do
      let e1' ← convertScalarExpr e1
      let e2' ← convertScalarExpr e2
      some (.add e1' e2')
  | .sub e1 e2 => do
      let e1' ← convertScalarExpr e1
      let e2' ← convertScalarExpr e2
      some (.sub e1' e2')
  | .mul e1 e2 => do
      let e1' ← convertScalarExpr e1
      let e2' ← convertScalarExpr e2
      some (.mul e1' e2')

/-- Convert Trust-Lean ScalarExpr back to AmoLean ScalarExpr. Total. -/
def convertBackScalarExpr : _root_.TrustLean.Bridge.ScalarExpr → ScalarExpr
  | .var v => .var (convertBackScalarVar v)
  | .const n => .const n
  | .neg e => .neg (convertBackScalarExpr e)
  | .add e1 e2 => .add (convertBackScalarExpr e1) (convertBackScalarExpr e2)
  | .sub e1 e2 => .sub (convertBackScalarExpr e1) (convertBackScalarExpr e2)
  | .mul e1 e2 => .mul (convertBackScalarExpr e1) (convertBackScalarExpr e2)

@[simp] theorem roundtrip_scalarExpr_backward (e : _root_.TrustLean.Bridge.ScalarExpr) :
    convertScalarExpr (convertBackScalarExpr e) = some e := by
  induction e with
  | var v =>
    simp [convertBackScalarExpr, convertScalarExpr, Option.map]
  | const => rfl
  | neg _ ih =>
    simp [convertBackScalarExpr, convertScalarExpr, Option.map, ih]
  | add _ _ ih1 ih2 =>
    simp [convertBackScalarExpr, convertScalarExpr, bind, Option.bind, ih1, ih2]
  | sub _ _ ih1 ih2 =>
    simp [convertBackScalarExpr, convertScalarExpr, bind, Option.bind, ih1, ih2]
  | mul _ _ ih1 ih2 =>
    simp [convertBackScalarExpr, convertScalarExpr, bind, Option.bind, ih1, ih2]

/-- Forward roundtrip for ScalarExpr: if conversion succeeds, converting back yields the original. -/
theorem roundtrip_scalarExpr_forward (e : ScalarExpr)
    (e' : _root_.TrustLean.Bridge.ScalarExpr)
    (h : convertScalarExpr e = some e') :
    convertBackScalarExpr e' = e := by
  induction e generalizing e' with
  | var v =>
    simp only [convertScalarExpr, Option.map] at h
    split at h <;> simp at h
    rename_i v' hv'
    subst h
    simp [convertBackScalarExpr, roundtrip_scalarVar_forward v v' hv']
  | const n =>
    simp only [convertScalarExpr, Option.some.injEq] at h; subst h; rfl
  | neg e ih =>
    simp only [convertScalarExpr, Option.map] at h
    split at h <;> simp at h
    rename_i e'' he''
    subst h
    simp [convertBackScalarExpr, ih e'' he'']
  | add e1 e2 ih1 ih2 =>
    simp only [convertScalarExpr, bind, Option.bind] at h
    cases he1 : convertScalarExpr e1 with
    | none => simp [he1] at h
    | some e1' =>
      simp [he1] at h
      cases he2 : convertScalarExpr e2 with
      | none => simp [he2] at h
      | some e2' =>
        simp [he2, Option.some.injEq] at h; subst h
        simp [convertBackScalarExpr, ih1 e1' he1, ih2 e2' he2]
  | sub e1 e2 ih1 ih2 =>
    simp only [convertScalarExpr, bind, Option.bind] at h
    cases he1 : convertScalarExpr e1 with
    | none => simp [he1] at h
    | some e1' =>
      simp [he1] at h
      cases he2 : convertScalarExpr e2 with
      | none => simp [he2] at h
      | some e2' =>
        simp [he2, Option.some.injEq] at h; subst h
        simp [convertBackScalarExpr, ih1 e1' he1, ih2 e2' he2]
  | mul e1 e2 ih1 ih2 =>
    simp only [convertScalarExpr, bind, Option.bind] at h
    cases he1 : convertScalarExpr e1 with
    | none => simp [he1] at h
    | some e1' =>
      simp [he1] at h
      cases he2 : convertScalarExpr e2 with
      | none => simp [he2] at h
      | some e2' =>
        simp [he2, Option.some.injEq] at h; subst h
        simp [convertBackScalarExpr, ih1 e1' he1, ih2 e2' he2]

/-! ## ScalarAssign Conversion -/

/-- Convert AmoLean ScalarAssign to Trust-Lean ScalarAssign. -/
def convertScalarAssign (a : ScalarAssign) :
    Option _root_.TrustLean.Bridge.ScalarAssign := do
  let target ← convertScalarVar a.target
  let value ← convertScalarExpr a.value
  some ⟨target, value⟩

/-- Convert Trust-Lean ScalarAssign back to AmoLean ScalarAssign. -/
def convertBackScalarAssign (a : _root_.TrustLean.Bridge.ScalarAssign) :
    ScalarAssign :=
  ⟨convertBackScalarVar a.target, convertBackScalarExpr a.value⟩

@[simp] theorem roundtrip_scalarAssign_backward
    (a : _root_.TrustLean.Bridge.ScalarAssign) :
    convertScalarAssign (convertBackScalarAssign a) = some a := by
  simp [convertBackScalarAssign, convertScalarAssign, bind, Option.bind]

/-- Forward roundtrip for ScalarAssign. -/
theorem roundtrip_scalarAssign_forward (a : ScalarAssign)
    (a' : _root_.TrustLean.Bridge.ScalarAssign)
    (h : convertScalarAssign a = some a') :
    convertBackScalarAssign a' = a := by
  simp only [convertScalarAssign, bind, Option.bind] at h
  cases ht : convertScalarVar a.target with
  | none => simp [ht] at h
  | some t' =>
    simp [ht] at h
    cases hv : convertScalarExpr a.value with
    | none => simp [hv] at h
    | some v' =>
      simp [hv, Option.some.injEq] at h; subst h
      simp [convertBackScalarAssign,
            roundtrip_scalarVar_forward a.target t' ht,
            roundtrip_scalarExpr_forward a.value v' hv]

/-! ## List Conversions (Recursive for clean induction) -/

/-- Convert a list of AmoLean ScalarVars. -/
def convertScalarVarList : List ScalarVar → Option (List _root_.TrustLean.Bridge.ScalarVar)
  | [] => some []
  | v :: rest => do
      let v' ← convertScalarVar v
      let rest' ← convertScalarVarList rest
      some (v' :: rest')

/-- Convert a list of Trust-Lean ScalarVars back. -/
def convertBackScalarVarList : List _root_.TrustLean.Bridge.ScalarVar → List ScalarVar
  | [] => []
  | v :: rest => convertBackScalarVar v :: convertBackScalarVarList rest

@[simp] theorem roundtrip_scalarVarList_backward
    (vs : List _root_.TrustLean.Bridge.ScalarVar) :
    convertScalarVarList (convertBackScalarVarList vs) = some vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
    simp [convertBackScalarVarList, convertScalarVarList, bind, Option.bind, ih]

/-- Forward roundtrip for ScalarVar lists. -/
theorem roundtrip_scalarVarList_forward (vs : List ScalarVar)
    (vs' : List _root_.TrustLean.Bridge.ScalarVar)
    (h : convertScalarVarList vs = some vs') :
    convertBackScalarVarList vs' = vs := by
  induction vs generalizing vs' with
  | nil => simp [convertScalarVarList] at h; subst h; rfl
  | cons v rest ih =>
    simp only [convertScalarVarList, bind, Option.bind] at h
    cases hv : convertScalarVar v with
    | none => simp [hv] at h
    | some v' =>
      simp [hv] at h
      cases hr : convertScalarVarList rest with
      | none => simp [hr] at h
      | some rest' =>
        simp [hr, Option.some.injEq] at h; subst h
        simp [convertBackScalarVarList,
              roundtrip_scalarVar_forward v v' hv, ih rest' hr]

/-- Convert a list of AmoLean ScalarAssigns. -/
def convertScalarAssignList : List ScalarAssign →
    Option (List _root_.TrustLean.Bridge.ScalarAssign)
  | [] => some []
  | a :: rest => do
      let a' ← convertScalarAssign a
      let rest' ← convertScalarAssignList rest
      some (a' :: rest')

/-- Convert a list of Trust-Lean ScalarAssigns back. -/
def convertBackScalarAssignList :
    List _root_.TrustLean.Bridge.ScalarAssign → List ScalarAssign
  | [] => []
  | a :: rest => convertBackScalarAssign a :: convertBackScalarAssignList rest

@[simp] theorem roundtrip_scalarAssignList_backward
    (as_ : List _root_.TrustLean.Bridge.ScalarAssign) :
    convertScalarAssignList (convertBackScalarAssignList as_) = some as_ := by
  induction as_ with
  | nil => rfl
  | cons a rest ih =>
    simp [convertBackScalarAssignList, convertScalarAssignList, bind, Option.bind, ih]

/-- Forward roundtrip for ScalarAssign lists. -/
theorem roundtrip_scalarAssignList_forward (as_ : List ScalarAssign)
    (as' : List _root_.TrustLean.Bridge.ScalarAssign)
    (h : convertScalarAssignList as_ = some as') :
    convertBackScalarAssignList as' = as_ := by
  induction as_ generalizing as' with
  | nil => simp [convertScalarAssignList] at h; subst h; rfl
  | cons a rest ih =>
    simp only [convertScalarAssignList, bind, Option.bind] at h
    cases ha : convertScalarAssign a with
    | none => simp [ha] at h
    | some a' =>
      simp [ha] at h
      cases hr : convertScalarAssignList rest with
      | none => simp [hr] at h
      | some rest' =>
        simp [hr, Option.some.injEq] at h; subst h
        simp [convertBackScalarAssignList,
              roundtrip_scalarAssign_forward a a' ha, ih rest' hr]

/-! ## ExpandedKernel Conversion -/

/-- Convert AmoLean ExpandedKernel to Trust-Lean ExpandedKernel. -/
def convertExpandedKernel (k : ExpandedKernel) :
    Option _root_.TrustLean.Bridge.ExpandedKernel := do
  let ivs ← convertScalarVarList k.inputVars
  let ovs ← convertScalarVarList k.outputVars
  let body ← convertScalarAssignList k.body
  some ⟨ivs, ovs, body⟩

/-- Convert Trust-Lean ExpandedKernel back to AmoLean ExpandedKernel. -/
def convertBackExpandedKernel (k : _root_.TrustLean.Bridge.ExpandedKernel) :
    ExpandedKernel :=
  ⟨convertBackScalarVarList k.inputVars,
   convertBackScalarVarList k.outputVars,
   convertBackScalarAssignList k.body⟩

@[simp] theorem roundtrip_expandedKernel_backward
    (k : _root_.TrustLean.Bridge.ExpandedKernel) :
    convertExpandedKernel (convertBackExpandedKernel k) = some k := by
  simp [convertExpandedKernel, convertBackExpandedKernel, bind, Option.bind]

/-- Forward roundtrip for ExpandedKernel. -/
theorem roundtrip_expandedKernel_forward (k : ExpandedKernel)
    (k' : _root_.TrustLean.Bridge.ExpandedKernel)
    (h : convertExpandedKernel k = some k') :
    convertBackExpandedKernel k' = k := by
  simp only [convertExpandedKernel, bind, Option.bind] at h
  cases hivs : convertScalarVarList k.inputVars with
  | none => simp [hivs] at h
  | some ivs' =>
    simp [hivs] at h
    cases hovs : convertScalarVarList k.outputVars with
    | none => simp [hovs] at h
    | some ovs' =>
      simp [hovs] at h
      cases hbody : convertScalarAssignList k.body with
      | none => simp [hbody] at h
      | some body' =>
        simp [hbody, Option.some.injEq] at h; subst h
        simp [convertBackExpandedKernel,
              roundtrip_scalarVarList_forward k.inputVars ivs' hivs,
              roundtrip_scalarVarList_forward k.outputVars ovs' hovs,
              roundtrip_scalarAssignList_forward k.body body' hbody]

/-! ## ExpandedSigma Conversion -/

/-- Convert AmoLean ExpandedSigma to Trust-Lean ExpandedSigma.
    Returns `none` if any ScalarVar has an unrecognized name. O(n). -/
def convertExpandedSigma : ExpandedSigma → Option _root_.TrustLean.Bridge.ExpandedSigma
  | .scalar k g s => do
      let k' ← convertExpandedKernel k
      some (.scalar k' (convertGather g) (convertScatter s))
  | .loop n v body => do
      let b ← convertExpandedSigma body
      some (.loop n v b)
  | .seq s1 s2 => do
      let s1' ← convertExpandedSigma s1
      let s2' ← convertExpandedSigma s2
      some (.seq s1' s2')
  | .par s1 s2 => do
      let s1' ← convertExpandedSigma s1
      let s2' ← convertExpandedSigma s2
      some (.par s1' s2')
  | .temp size body => do
      let b ← convertExpandedSigma body
      some (.temp size b)
  | .nop => some .nop

/-- Convert Trust-Lean ExpandedSigma back to AmoLean ExpandedSigma. Total. -/
def convertBackExpandedSigma : _root_.TrustLean.Bridge.ExpandedSigma → ExpandedSigma
  | .scalar k g s =>
      .scalar (convertBackExpandedKernel k) (convertBackGather g) (convertBackScatter s)
  | .loop n v body => .loop n v (convertBackExpandedSigma body)
  | .seq s1 s2 => .seq (convertBackExpandedSigma s1) (convertBackExpandedSigma s2)
  | .par s1 s2 => .par (convertBackExpandedSigma s1) (convertBackExpandedSigma s2)
  | .temp size body => .temp size (convertBackExpandedSigma body)
  | .nop => .nop

/-! ## ExpandedSigma Roundtrip -/

/-- Backward roundtrip for ExpandedSigma:
    converting back from Trust-Lean and then forward always recovers the original.
    This is the primary correctness theorem for the bridge. -/
theorem roundtrip_expandedSigma_backward
    (s : _root_.TrustLean.Bridge.ExpandedSigma) :
    convertExpandedSigma (convertBackExpandedSigma s) = some s := by
  induction s with
  | scalar k g sc =>
    simp [convertBackExpandedSigma, convertExpandedSigma, bind, Option.bind]
  | loop _ _ _ ih =>
    simp [convertBackExpandedSigma, convertExpandedSigma, bind, Option.bind, ih]
  | seq _ _ ih1 ih2 =>
    simp [convertBackExpandedSigma, convertExpandedSigma, bind, Option.bind, ih1, ih2]
  | par _ _ ih1 ih2 =>
    simp [convertBackExpandedSigma, convertExpandedSigma, bind, Option.bind, ih1, ih2]
  | temp _ _ ih =>
    simp [convertBackExpandedSigma, convertExpandedSigma, bind, Option.bind, ih]
  | nop => rfl

/-- Forward roundtrip for ExpandedSigma:
    if conversion succeeds, converting back yields the original.
    This completes the bidirectional roundtrip with the backward theorem above. -/
theorem roundtrip_expandedSigma_forward (s : ExpandedSigma)
    (s' : _root_.TrustLean.Bridge.ExpandedSigma)
    (h : convertExpandedSigma s = some s') :
    convertBackExpandedSigma s' = s := by
  induction s generalizing s' with
  | scalar k g sc =>
    simp only [convertExpandedSigma, bind, Option.bind] at h
    cases hk : convertExpandedKernel k with
    | none => simp [hk] at h
    | some k' =>
      simp [hk, Option.some.injEq] at h; subst h
      simp [convertBackExpandedSigma,
            roundtrip_expandedKernel_forward k k' hk,
            roundtrip_gather_forward g, roundtrip_scatter_forward sc]
  | loop n v body ih =>
    simp only [convertExpandedSigma, bind, Option.bind] at h
    cases hb : convertExpandedSigma body with
    | none => simp [hb] at h
    | some b' =>
      simp [hb, Option.some.injEq] at h; subst h
      simp [convertBackExpandedSigma, ih b' hb]
  | seq s1 s2 ih1 ih2 =>
    simp only [convertExpandedSigma, bind, Option.bind] at h
    cases h1 : convertExpandedSigma s1 with
    | none => simp [h1] at h
    | some s1' =>
      simp [h1] at h
      cases h2 : convertExpandedSigma s2 with
      | none => simp [h2] at h
      | some s2' =>
        simp [h2, Option.some.injEq] at h; subst h
        simp [convertBackExpandedSigma, ih1 s1' h1, ih2 s2' h2]
  | par s1 s2 ih1 ih2 =>
    simp only [convertExpandedSigma, bind, Option.bind] at h
    cases h1 : convertExpandedSigma s1 with
    | none => simp [h1] at h
    | some s1' =>
      simp [h1] at h
      cases h2 : convertExpandedSigma s2 with
      | none => simp [h2] at h
      | some s2' =>
        simp [h2, Option.some.injEq] at h; subst h
        simp [convertBackExpandedSigma, ih1 s1' h1, ih2 s2' h2]
  | temp size body ih =>
    simp only [convertExpandedSigma, bind, Option.bind] at h
    cases hb : convertExpandedSigma body with
    | none => simp [hb] at h
    | some b' =>
      simp [hb, Option.some.injEq] at h; subst h
      simp [convertBackExpandedSigma, ih b' hb]
  | nop =>
    simp only [convertExpandedSigma, Option.some.injEq] at h; subst h; rfl

/-- Injectivity: if two ExpandedSigma values convert to the same `some` value,
    they must be equal. Derived from the forward roundtrip.
    Note: for partial functions, injectivity only holds on the domain where
    conversion succeeds (returns `some`). -/
theorem convert_injective (a b : ExpandedSigma)
    (x : _root_.TrustLean.Bridge.ExpandedSigma)
    (ha : convertExpandedSigma a = some x)
    (hb : convertExpandedSigma b = some x) : a = b :=
  (roundtrip_expandedSigma_forward a x ha).symm.trans
  (roundtrip_expandedSigma_forward b x hb)

/-! ## Verified Pipeline -/

/-- Generate verified C code from an AmoLean ExpandedSigma.
    Chains: convertExpandedSigma → expandedSigmaToStmt → stmtToC.
    Returns `none` if conversion fails (non-standard variable names). -/
def verifiedCodeGen (s : ExpandedSigma) : Option String :=
  (convertExpandedSigma s).map fun ts =>
    _root_.TrustLean.stmtToC 0 (_root_.TrustLean.Bridge.expandedSigmaToStmt ts)

/-! ## MicroC Pipeline (Trust-Lean v3.0)

  The MicroC path provides formal C semantics: `stmtToMicroC_correct` proves
  that Core IR evaluation matches MicroC evaluation, and `master_roundtrip`
  proves that `parseMicroC(microCToString s) = some s` for all well-formed
  statements. This gives a stronger guarantee than the CBackend path above.
-/

/-- Convert an AmoLean ExpandedSigma to a Trust-Lean MicroCStmt.
    Chains: convertExpandedSigma → expandedSigmaToStmt → stmtToMicroC.
    Returns `none` if conversion fails (non-standard variable names).
    The intermediate MicroCStmt has formal evaluation semantics
    (`evalMicroC`) and a verified roundtrip with `parseMicroC`. -/
def expandedSigmaToMicroCStmt (s : ExpandedSigma) :
    Option _root_.TrustLean.MicroCStmt :=
  (convertExpandedSigma s).map fun ts =>
    _root_.TrustLean.stmtToMicroC (_root_.TrustLean.Bridge.expandedSigmaToStmt ts)

/-- Generate verified C code from an AmoLean ExpandedSigma via MicroC.
    Chains: convertExpandedSigma → expandedSigmaToStmt → stmtToMicroC → microCToString.
    Returns `none` if conversion fails (non-standard variable names).

    Unlike `verifiedCodeGen` (which uses CBackend's `stmtToC`), this path
    goes through the MicroC AST layer that has:
    - Formal evaluation semantics (`evalMicroC`)
    - Simulation proof (`stmtToMicroC_correct`)
    - Full roundtrip guarantee (`master_roundtrip`)
    - Int64 overflow model (`evalMicroC_int64`)
    - Call semantics (`evalMicroC_withCalls`) -/
def verifiedCodeGenMicroC (s : ExpandedSigma) : Option String :=
  (expandedSigmaToMicroCStmt s).map _root_.TrustLean.microCToString

end AmoLean.Bridge.TrustLean
