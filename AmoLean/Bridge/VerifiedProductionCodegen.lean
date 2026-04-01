/-
  AMO-Lean — Verified Production Codegen (Fase 30)

  Generates verified C + Rust code for ALL production primitives:
  - Field reduction (Solinas fold) for BabyBear, Mersenne31, KoalaBear, Goldilocks
  - DIF Butterfly for all 4 primes
  - NTT loop for all 4 primes
  - FRI fold loop (parametric)
  - Poseidon S-box x^5 (3-mul optimal chain) and x^7 (4-mul chain)

  ALL code flows through the verified Path A:
    MixedExpr/Stmt → lowerMixedExprFull/lowerDIFButterflyStmt/lowerNTTLoopStmt
    → TrustLean.stmtToC / TrustLean.stmtToRust

  0 sorry, 0 new axioms.
-/
import AmoLean.Bridge.VerifiedPipeline
import AmoLean.EGraph.Verified.Bitwise.SynthesisToC
import AmoLean.EGraph.Verified.Bitwise.SolinasRuleGen
import AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen
import TrustLean.Backend.RustBackend

set_option autoImplicit false

namespace AmoLean.Bridge.VerifiedProductionCodegen

open AmoLean.Bridge.VerifiedPipeline (mixedExprToC mixedExprToRust
  mixedExprToCFn mixedExprToRustFn)
open AmoLean.EGraph.Verified.Bitwise.VerifiedCodeGen (emitDIFButterflyC emitDIFButterflyRust
  emitNTTCFn emitNTTRustFn counting_while_evaluates_post for_evaluates_via_while
  solinasFoldLLE)
open AmoLean.EGraph.Verified.Bitwise (solinasFoldMixedExpr mersenneFoldMixedExpr
  babybear_solinas koalabear_solinas goldilocks_solinas)
open AmoLean.EGraph.Verified.Bitwise.MixedExtract (MixedExpr)
open TrustLean (Stmt VarName LowLevelExpr LowLevelEnv Value CodeGenState
  evalExpr evalStmt evalBinOp Outcome getArrayName)

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Prime Constants
-- ══════════════════════════════════════════════════════════════════

/-! ## Solinas parameters: p = 2^a - 2^b + 1

| Prime      | a  | b  | c = 2^b - 1       | p                    |
|------------|----|----|--------------------|-----------------------|
| BabyBear   | 31 | 27 | 134217727          | 2013265921            |
| KoalaBear  | 31 | 24 | 16777215           | 2130706433            |
| Mersenne31 | 31 |  — | 1 (pure Mersenne)  | 2147483647            |
| Goldilocks | 64 | 32 | 4294967295         | 18446744069414584321  |
-/

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Field Reduction C + Rust (all 4 primes)
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear Solinas reduction → C function. Path A verified. -/
def babybear_reduce_c : String :=
  mixedExprToCFn (solinasFoldMixedExpr babybear_solinas) "babybear_reduce" [("x", "int64_t")]

/-- BabyBear Solinas reduction → Rust function. Path A verified. -/
def babybear_reduce_rust : String :=
  mixedExprToRustFn (solinasFoldMixedExpr babybear_solinas) "babybear_reduce" [("x", "i64")]

/-- Mersenne31 pure-Mersenne reduction → C function. No multiplication needed. -/
def mersenne31_reduce_c : String :=
  mixedExprToCFn (mersenneFoldMixedExpr 31) "mersenne31_reduce" [("x", "int64_t")]

/-- Mersenne31 pure-Mersenne reduction → Rust function. -/
def mersenne31_reduce_rust : String :=
  mixedExprToRustFn (mersenneFoldMixedExpr 31) "mersenne31_reduce" [("x", "i64")]

/-- KoalaBear Solinas reduction → C function. Path A verified. -/
def koalabear_reduce_c : String :=
  mixedExprToCFn (solinasFoldMixedExpr koalabear_solinas) "koalabear_reduce" [("x", "int64_t")]

/-- KoalaBear Solinas reduction → Rust function. -/
def koalabear_reduce_rust : String :=
  mixedExprToRustFn (solinasFoldMixedExpr koalabear_solinas) "koalabear_reduce" [("x", "i64")]

/-- Goldilocks Solinas reduction → C function. Path A verified. -/
def goldilocks_reduce_c : String :=
  mixedExprToCFn (solinasFoldMixedExpr goldilocks_solinas) "goldilocks_reduce" [("x", "int64_t")]

/-- Goldilocks Solinas reduction → Rust function. -/
def goldilocks_reduce_rust : String :=
  mixedExprToRustFn (solinasFoldMixedExpr goldilocks_solinas) "goldilocks_reduce" [("x", "i64")]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: DIF Butterfly C + Rust (all 4 primes)
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear DIF butterfly → C. p=2013265921, k=31, c=134217727. -/
def babybear_butterfly_c : String :=
  emitDIFButterflyC "a" "b" "w" 2013265921 31 134217727

/-- BabyBear DIF butterfly → Rust. -/
def babybear_butterfly_rust : String :=
  emitDIFButterflyRust "a" "b" "w" 2013265921 31 134217727

/-- Mersenne31 DIF butterfly → C. p=2147483647, k=31, c=1. -/
def mersenne31_butterfly_c : String :=
  emitDIFButterflyC "a" "b" "w" 2147483647 31 1

/-- Mersenne31 DIF butterfly → Rust. -/
def mersenne31_butterfly_rust : String :=
  emitDIFButterflyRust "a" "b" "w" 2147483647 31 1

/-- KoalaBear DIF butterfly → C. p=2130706433, k=31, c=16777215. -/
def koalabear_butterfly_c : String :=
  emitDIFButterflyC "a" "b" "w" 2130706433 31 16777215

/-- KoalaBear DIF butterfly → Rust. -/
def koalabear_butterfly_rust : String :=
  emitDIFButterflyRust "a" "b" "w" 2130706433 31 16777215

/-- Goldilocks DIF butterfly → C. p=18446744069414584321, k=64, c=4294967295. -/
def goldilocks_butterfly_c : String :=
  emitDIFButterflyC "a" "b" "w" 18446744069414584321 64 4294967295

/-- Goldilocks DIF butterfly → Rust. -/
def goldilocks_butterfly_rust : String :=
  emitDIFButterflyRust "a" "b" "w" 18446744069414584321 64 4294967295

-- ══════════════════════════════════════════════════════════════════
-- Section 4: NTT Complete Functions C + Rust (all 4 primes)
-- ══════════════════════════════════════════════════════════════════

/-- BabyBear NTT (logN-point) → complete C function. -/
def babybear_ntt_c (logN : Nat) : String :=
  emitNTTCFn logN 2013265921 31 134217727 "babybear_ntt"

/-- BabyBear NTT (logN-point) → complete Rust function. -/
def babybear_ntt_rust (logN : Nat) : String :=
  emitNTTRustFn logN 2013265921 31 134217727 "babybear_ntt"

/-- Mersenne31 NTT → complete C function. -/
def mersenne31_ntt_c (logN : Nat) : String :=
  emitNTTCFn logN 2147483647 31 1 "mersenne31_ntt"

/-- Mersenne31 NTT → complete Rust function. -/
def mersenne31_ntt_rust (logN : Nat) : String :=
  emitNTTRustFn logN 2147483647 31 1 "mersenne31_ntt"

/-- KoalaBear NTT → complete C function. -/
def koalabear_ntt_c (logN : Nat) : String :=
  emitNTTCFn logN 2130706433 31 16777215 "koalabear_ntt"

/-- KoalaBear NTT → complete Rust function. -/
def koalabear_ntt_rust (logN : Nat) : String :=
  emitNTTRustFn logN 2130706433 31 16777215 "koalabear_ntt"

/-- Goldilocks NTT → complete C function. -/
def goldilocks_ntt_c (logN : Nat) : String :=
  emitNTTCFn logN 18446744069414584321 64 4294967295 "goldilocks_ntt"

/-- Goldilocks NTT → complete Rust function. -/
def goldilocks_ntt_rust (logN : Nat) : String :=
  emitNTTRustFn logN 18446744069414584321 64 4294967295 "goldilocks_ntt"

-- ══════════════════════════════════════════════════════════════════
-- Section 5: FRI Fold Loop C + Rust
-- ══════════════════════════════════════════════════════════════════

/-- FRI fold inner loop as Trust-Lean Stmt.
    Computes: output[i] = input[2*i] + alpha * input[2*i + 1] for i in 0..n. -/
def friFoldLoopStmt (n : Nat) : Stmt :=
  let iVar := VarName.user "i"
  let body := Stmt.seq
    -- a = input[2*i]
    (Stmt.load (.user "a") (.varRef (.user "input"))
      (.binOp .mul (.varRef iVar) (.litInt 2)))
    (Stmt.seq
      -- b = input[2*i + 1]
      (Stmt.load (.user "b") (.varRef (.user "input"))
        (.binOp .add (.binOp .mul (.varRef iVar) (.litInt 2)) (.litInt 1)))
      (Stmt.seq
        -- result = a + alpha * b
        (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a"))
          (.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b")))))
        -- output[i] = result
        (Stmt.store (.varRef (.user "output")) (.varRef iVar) (.varRef (.user "result")))))
  Stmt.for_
    (Stmt.assign iVar (.litInt 0))
    (.binOp .ltOp (.varRef iVar) (.litInt ↑n))
    (Stmt.assign iVar (.binOp .add (.varRef iVar) (.litInt 1)))
    body

/-- FRI fold with intermediate reduction for fields where p*(1+p) > 2^64.
    For Goldilocks, adds a Solinas fold after alpha * b to prevent overflow. -/
def friFoldLoopStmtWithReduce (n : Nat) (needsReduce : Bool) (k c : Nat) : Stmt :=
  let iVar := VarName.user "i"
  let mulExpr := LowLevelExpr.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b"))
  let body := Stmt.seq
    (Stmt.load (.user "a") (.varRef (.user "input"))
      (.binOp .mul (.varRef iVar) (.litInt 2)))
    (Stmt.seq
      (Stmt.load (.user "b") (.varRef (.user "input"))
        (.binOp .add (.binOp .mul (.varRef iVar) (.litInt 2)) (.litInt 1)))
      (if needsReduce then
        -- Goldilocks: reduce alpha*b before adding to a
        Stmt.seq
          (Stmt.assign (.user "ab") mulExpr)
          (Stmt.seq (Stmt.assign (.user "ab_r") (solinasFoldLLE (.varRef (.user "ab")) k c))
          (Stmt.seq
            (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a")) (.varRef (.user "ab_r"))))
            (Stmt.store (.varRef (.user "output")) (.varRef iVar) (.varRef (.user "result")))))
      else
        -- 31-bit primes: no intermediate reduce needed
        Stmt.seq
          (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a")) mulExpr))
          (Stmt.store (.varRef (.user "output")) (.varRef iVar) (.varRef (.user "result")))))
  Stmt.for_
    (Stmt.assign iVar (.litInt 0))
    (.binOp .ltOp (.varRef iVar) (.litInt ↑n))
    (Stmt.assign iVar (.binOp .add (.varRef iVar) (.litInt 1)))
    body

/-- FRI fold loop → complete C function. -/
def friFold_c (n : Nat) : String :=
  TrustLean.generateCFunction {} "fri_fold"
    [("input", "const int64_t*"), ("output", "int64_t*"), ("alpha", "int64_t")]
    (friFoldLoopStmt n) (.litInt 0)

/-- FRI fold loop → complete Rust function. -/
def friFold_rust (n : Nat) : String :=
  TrustLean.generateRustFunction {} "fri_fold"
    [("input", "&[i64]"), ("output", "&mut [i64]"), ("alpha", "i64")]
    (friFoldLoopStmt n) (.litInt 0)

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Poseidon S-box x^5 and x^7 as Verified Stmt
-- ══════════════════════════════════════════════════════════════════

/-- Poseidon S-box: x^5 via optimal 3-multiplication chain.
    x2 = x * x, x4 = x2 * x2, x5 = x4 * x. -/
def genSbox5Stmt (xVar : VarName) (cgs : CodeGenState) :
    Stmt × VarName × CodeGenState :=
  let (x2Var, cgs1) := cgs.freshVar
  let s1 := Stmt.assign x2Var (.binOp .mul (.varRef xVar) (.varRef xVar))
  let (x4Var, cgs2) := cgs1.freshVar
  let s2 := Stmt.assign x4Var (.binOp .mul (.varRef x2Var) (.varRef x2Var))
  let (x5Var, cgs3) := cgs2.freshVar
  let s3 := Stmt.assign x5Var (.binOp .mul (.varRef x4Var) (.varRef xVar))
  (Stmt.seq s1 (Stmt.seq s2 s3), x5Var, cgs3)

/-- Poseidon S-box: x^5 with intermediate Solinas fold after squarings.
    For 31-bit primes: x^2 < p² < 2^62 → fold produces < 2p < 2^32.
    For Goldilocks: x^2 < p² < 2^128 → MUST fold before next multiply.
    Parameters: k = shift bits, c = Solinas constant for the field. -/
def genSbox5StmtWithReduce (xVar : VarName) (p k c : Nat) (cgs : CodeGenState) :
    Stmt × VarName × CodeGenState :=
  let (x2Var, cgs1) := cgs.freshVar
  let s1 := Stmt.assign x2Var (.binOp .mul (.varRef xVar) (.varRef xVar))
  -- Reduce x2 via Solinas fold: [0, 2p)
  let (x2rVar, cgs2) := cgs1.freshVar
  let s1r := Stmt.seq s1 (Stmt.assign x2rVar (solinasFoldLLE (.varRef x2Var) k c))
  -- x4 = x2r * x2r (bounded: < (2p)^2 = 4p^2, fits in u64 for 31-bit primes)
  let (x4Var, cgs3) := cgs2.freshVar
  let s2 := Stmt.assign x4Var (.binOp .mul (.varRef x2rVar) (.varRef x2rVar))
  -- x5 = x4 * x
  let (x5Var, cgs4) := cgs3.freshVar
  let s3 := Stmt.assign x5Var (.binOp .mul (.varRef x4Var) (.varRef xVar))
  (Stmt.seq s1r (Stmt.seq s2 s3), x5Var, cgs4)

/-- Poseidon S-box x^5 → complete C function. -/
def poseidon_sbox5_c : String :=
  let (stmt, resultVar, _) := genSbox5Stmt (.user "x") {}
  TrustLean.generateCFunction {} "poseidon_sbox5" [("x", "int64_t")] stmt (.varRef resultVar)

/-- Poseidon S-box x^5 → complete Rust function. -/
def poseidon_sbox5_rust : String :=
  let (stmt, resultVar, _) := genSbox5Stmt (.user "x") {}
  TrustLean.generateRustFunction {} "poseidon_sbox5" [("x", "i64")] stmt (.varRef resultVar)

/-- Poseidon S-box: x^7 via 4-multiplication chain (for Goldilocks).
    x2 = x * x, x3 = x2 * x, x4 = x3 * x, x7 = x4 * x3. -/
def genSbox7Stmt (xVar : VarName) (cgs : CodeGenState) :
    Stmt × VarName × CodeGenState :=
  let (x2Var, cgs1) := cgs.freshVar
  let s1 := Stmt.assign x2Var (.binOp .mul (.varRef xVar) (.varRef xVar))
  let (x3Var, cgs2) := cgs1.freshVar
  let s2 := Stmt.assign x3Var (.binOp .mul (.varRef x2Var) (.varRef xVar))
  let (x4Var, cgs3) := cgs2.freshVar
  let s3 := Stmt.assign x4Var (.binOp .mul (.varRef x3Var) (.varRef xVar))
  let (x7Var, cgs4) := cgs3.freshVar
  let s4 := Stmt.assign x7Var (.binOp .mul (.varRef x4Var) (.varRef x3Var))
  (Stmt.seq s1 (Stmt.seq s2 (Stmt.seq s3 s4)), x7Var, cgs4)

/-- Poseidon S-box x^7 → complete C function. -/
def poseidon_sbox7_c : String :=
  let (stmt, resultVar, _) := genSbox7Stmt (.user "x") {}
  TrustLean.generateCFunction {} "poseidon_sbox7" [("x", "int64_t")] stmt (.varRef resultVar)

/-- Poseidon S-box x^7 → complete Rust function. -/
def poseidon_sbox7_rust : String :=
  let (stmt, resultVar, _) := genSbox7Stmt (.user "x") {}
  TrustLean.generateRustFunction {} "poseidon_sbox7" [("x", "i64")] stmt (.varRef resultVar)

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Soundness for genSbox5Stmt
-- ══════════════════════════════════════════════════════════════════

/-- genSbox5Stmt evaluates to x^5 = x * x * (x * x) * x.
    The statement assigns three temporaries:
      temp(N)   = x * x
      temp(N+1) = temp(N) * temp(N)
      temp(N+2) = temp(N+1) * x
    Result variable is temp(N+2) holding v * v * (v * v) * v. -/
theorem genSbox5Stmt_evaluates (xVar : VarName) (v : Int)
    (llEnv : LowLevelEnv) (hx : llEnv xVar = .int v)
    (cgs : CodeGenState)
    (hnt0 : xVar ≠ .temp cgs.nextVar)
    (hnt1 : xVar ≠ .temp (cgs.nextVar + 1))
    (_hnt2 : xVar ≠ .temp (cgs.nextVar + 2)) :
    let (stmt, resultVar, _) := genSbox5Stmt xVar cgs
    ∃ env', evalStmt 1 llEnv stmt = some (.normal, env') ∧
      env' resultVar = .int (v * v * (v * v) * v) := by
  simp only [genSbox5Stmt, CodeGenState.freshVar]
  set t0 := VarName.temp cgs.nextVar
  set t1 := VarName.temp (cgs.nextVar + 1)
  set t2 := VarName.temp (cgs.nextVar + 2)
  -- Step through: seq(assign t0 = x*x, seq(assign t1 = t0*t0, assign t2 = t1*x))
  -- Each .assign evaluates its RHS in the current env, then updates the env.
  -- update_other handles cross-variable lookups (xVar ≠ t0, xVar ≠ t1).
  simp only [TrustLean.evalStmt_seq, TrustLean.evalStmt_assign,
    TrustLean.evalExpr_binOp, TrustLean.evalExpr_varRef,
    hx, TrustLean.evalBinOp_mul,
    TrustLean.LowLevelEnv.update_same,
    TrustLean.LowLevelEnv.update_other _ _ _ _ hnt0,
    TrustLean.LowLevelEnv.update_other _ _ _ _ hnt1]
  exact ⟨_, rfl, TrustLean.LowLevelEnv.update_same _ _ _⟩

/-- genSbox7Stmt evaluates to x^7 = (x^4) * (x^3).
    Chain: x2 = x*x, x3 = x2*x, x4 = x3*x, x7 = x4*x3.
    Result: (v * v * v * v) * (v * v * v) i.e. v^7. -/
theorem genSbox7Stmt_evaluates (xVar : VarName) (v : Int)
    (llEnv : LowLevelEnv) (hx : llEnv xVar = .int v)
    (cgs : CodeGenState)
    (hnt0 : xVar ≠ .temp cgs.nextVar)
    (hnt1 : xVar ≠ .temp (cgs.nextVar + 1))
    (_hnt2 : xVar ≠ .temp (cgs.nextVar + 2))
    (_hnt3 : xVar ≠ .temp (cgs.nextVar + 3)) :
    let (stmt, resultVar, _) := genSbox7Stmt xVar cgs
    ∃ env', evalStmt 1 llEnv stmt = some (.normal, env') ∧
      env' resultVar = .int ((v * v * v * v) * (v * v * v)) := by
  simp only [genSbox7Stmt, CodeGenState.freshVar]
  -- x2 = v*v at temp N, x3 = x2*v at temp N+1, x4 = x3*v at temp N+2, x7 = x4*x3 at temp N+3
  -- Need: xVar accessible after each update (hnt0, hnt1)
  -- Need: temp N+1 accessible after temp N+2 update (different temps)
  have htt : VarName.temp (cgs.nextVar + 1) ≠ VarName.temp (cgs.nextVar + 2) := by
    simp [VarName.temp.injEq]
  simp only [TrustLean.evalStmt_seq, TrustLean.evalStmt_assign,
    TrustLean.evalExpr_binOp, TrustLean.evalExpr_varRef,
    hx, TrustLean.evalBinOp_mul,
    TrustLean.LowLevelEnv.update_same,
    TrustLean.LowLevelEnv.update_other _ _ _ _ hnt0,
    TrustLean.LowLevelEnv.update_other _ _ _ _ hnt1,
    TrustLean.LowLevelEnv.update_other _ _ _ _ htt]
  exact ⟨_, rfl, TrustLean.LowLevelEnv.update_same _ _ _⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 8: FRI Fold Loop Soundness (general for ALL n)
-- ══════════════════════════════════════════════════════════════════

/-- Environment invariant for the FRI fold loop:
    input/output arrays are Int-valued, user vars are Int-valued, temps are Int-valued. -/
def FRIInv (env : LowLevelEnv) : Prop :=
  (∀ i : Int, ∃ v : Int, env (.array "input" i) = .int v) ∧
  (∀ i : Int, ∃ v : Int, env (.array "output" i) = .int v) ∧
  (∀ s : String, ∃ v : Int, env (.user s) = .int v) ∧
  (∀ n : Nat, ∃ v : Int, env (.temp n) = .int v)

/-- Updating a user variable with an Int value preserves FRIInv. -/
theorem FRIInv_update_user (env : LowLevelEnv) (s : String) (val : Int)
    (h : FRIInv env) : FRIInv (env.update (.user s) (.int val)) := by
  refine ⟨fun i => ?_, fun i => ?_, fun s' => ?_, fun n => ?_⟩
  · obtain ⟨v, hv⟩ := h.1 i; exact ⟨v, by simp [LowLevelEnv.update, hv]⟩
  · obtain ⟨v, hv⟩ := h.2.1 i; exact ⟨v, by simp [LowLevelEnv.update, hv]⟩
  · by_cases heq : s' = s
    · exact ⟨val, by simp [LowLevelEnv.update, heq]⟩
    · obtain ⟨v, hv⟩ := h.2.2.1 s'
      exact ⟨v, by simp [LowLevelEnv.update, VarName.user.injEq, heq, hv]⟩
  · obtain ⟨v, hv⟩ := h.2.2.2 n; exact ⟨v, by simp [LowLevelEnv.update, hv]⟩

/-- Updating an output array element with an Int value preserves FRIInv. -/
private theorem FRIInv_update_output (env : LowLevelEnv) (idx : Int) (val : Int)
    (h : FRIInv env) : FRIInv (env.update (.array "output" idx) (.int val)) := by
  refine ⟨fun i => ?_, fun i => ?_, fun s => ?_, fun n => ?_⟩
  · obtain ⟨v, hv⟩ := h.1 i
    exact ⟨v, by simp [LowLevelEnv.update, VarName.array.injEq, hv]⟩
  · by_cases heq : i = idx
    · exact ⟨val, by simp [LowLevelEnv.update, heq]⟩
    · obtain ⟨v, hv⟩ := h.2.1 i
      exact ⟨v, by simp [LowLevelEnv.update, VarName.array.injEq, heq, hv]⟩
  · obtain ⟨v, hv⟩ := h.2.2.1 s; exact ⟨v, by simp [LowLevelEnv.update, hv]⟩
  · obtain ⟨v, hv⟩ := h.2.2.2 n; exact ⟨v, by simp [LowLevelEnv.update, hv]⟩

/-- A load from the input array evaluates and preserves FRIInv. -/
private theorem load_input_FRI_evaluates (env : LowLevelEnv) (target : String)
    (idxExpr : LowLevelExpr) (hInv : FRIInv env)
    (hIdx : ∃ idx : Int, evalExpr env idxExpr = some (.int idx)) :
    ∃ fuel env',
      evalStmt fuel env (.load (.user target) (.varRef (.user "input")) idxExpr) =
        some (.normal, env') ∧ FRIInv env' := by
  obtain ⟨idx, hidx⟩ := hIdx
  obtain ⟨dval, hdval⟩ := hInv.1 idx
  refine ⟨0, env.update (.user target) (env (.array "input" idx)), ?_, ?_⟩
  · simp [getArrayName, hidx]
  · rw [hdval]; exact FRIInv_update_user env target dval hInv

/-- A store to the output array evaluates and preserves FRIInv. -/
private theorem store_output_FRI_evaluates (env : LowLevelEnv)
    (idxVar valVar : VarName)
    (hInv : FRIInv env)
    (hIdx : ∃ idx : Int, env idxVar = .int idx)
    (hVal : ∃ v : Int, env valVar = .int v) :
    ∃ fuel env',
      evalStmt fuel env (.store (.varRef (.user "output")) (.varRef idxVar) (.varRef valVar)) =
        some (.normal, env') ∧ FRIInv env' := by
  obtain ⟨idx, hidx⟩ := hIdx
  obtain ⟨v, hv⟩ := hVal
  refine ⟨0, env.update (.array "output" idx) (env valVar), ?_, ?_⟩
  · simp [getArrayName, hidx, hv]
  · rw [hv]; exact FRIInv_update_output env idx v hInv

/-- An assign of an arithmetic expression over Int-valued variables evaluates
    and preserves FRIInv. -/
private theorem assign_arith_FRI_evaluates (env : LowLevelEnv) (s : String)
    (expr : LowLevelExpr) (hInv : FRIInv env)
    (hExpr : ∃ val : Int, evalExpr env expr = some (.int val)) :
    ∃ fuel env',
      evalStmt fuel env (.assign (.user s) expr) = some (.normal, env') ∧
      FRIInv env' := by
  obtain ⟨val, hval⟩ := hExpr
  exact ⟨0, env.update (.user s) (.int val),
    by simp [hval], FRIInv_update_user env s val hInv⟩

/-- Sequencing: if s1 evaluates preserving FRIInv, and s2 evaluates given FRIInv,
    then (seq s1 s2) evaluates preserving FRIInv. -/
private theorem seq_FRIInv_evaluates (s1 s2 : Stmt) (env : LowLevelEnv)
    (h1 : ∃ fuel1 env1, evalStmt fuel1 env s1 = some (.normal, env1) ∧ FRIInv env1)
    (h2 : ∀ env1, FRIInv env1 → ∃ fuel2 env2, evalStmt fuel2 env1 s2 = some (.normal, env2) ∧ FRIInv env2) :
    ∃ fuel env', evalStmt fuel env (.seq s1 s2) = some (.normal, env') ∧ FRIInv env' := by
  obtain ⟨fuel1, env1, heval1, hinv1⟩ := h1
  obtain ⟨fuel2, env2, heval2, hinv2⟩ := h2 env1 hinv1
  refine ⟨max fuel1 fuel2, env2, ?_, hinv2⟩
  rw [TrustLean.evalStmt_seq]
  rw [TrustLean.evalStmt_fuel_mono heval1 (le_max_left fuel1 fuel2)]
  simp only []
  exact TrustLean.evalStmt_fuel_mono heval2 (le_max_right fuel1 fuel2)

/-- evalExpr for a user variable reference under FRIInv. -/
private theorem evalExpr_user_int_FRI (env : LowLevelEnv) (hInv : FRIInv env) (s : String) :
    ∃ v : Int, evalExpr env (.varRef (.user s)) = some (.int v) := by
  obtain ⟨v, hv⟩ := hInv.2.2.1 s; exact ⟨v, by simp [evalExpr, hv]⟩

/-- Helper: evalExpr for an Int-valued index expression under FRIInv.
    Any expression built from user vars and literals evaluates to Int. -/
private theorem evalExpr_mul_user_lit_FRI (env : LowLevelEnv) (hInv : FRIInv env) (s : String) (n : Int) :
    ∃ v : Int, evalExpr env (.binOp .mul (.varRef (.user s)) (.litInt n)) = some (.int v) := by
  obtain ⟨vi, hvi⟩ := hInv.2.2.1 s
  exact ⟨vi * n, by simp [evalExpr, hvi, evalBinOp]⟩

/-- Helper: evalExpr for 2*i + 1 under FRIInv. -/
private theorem evalExpr_2i_plus_1_FRI (env : LowLevelEnv) (hInv : FRIInv env) :
    ∃ v : Int, evalExpr env (.binOp .add (.binOp .mul (.varRef (.user "i")) (.litInt 2)) (.litInt 1)) = some (.int v) := by
  obtain ⟨vi, hvi⟩ := hInv.2.2.1 "i"
  exact ⟨vi * 2 + 1, by simp [evalExpr, hvi, evalBinOp]⟩

/-- The FRI fold body (load a, load b, assign result, store output)
    evaluates and preserves FRIInv.
    Uses seq chaining: each operation preserves FRIInv, passing it to the next. -/
private theorem friFoldBody_evaluates (env : LowLevelEnv) (hInv : FRIInv env) :
    ∃ fuel env',
      evalStmt fuel env
        (Stmt.seq
          (Stmt.load (.user "a") (.varRef (.user "input"))
            (.binOp .mul (.varRef (.user "i")) (.litInt 2)))
          (Stmt.seq
            (Stmt.load (.user "b") (.varRef (.user "input"))
              (.binOp .add (.binOp .mul (.varRef (.user "i")) (.litInt 2)) (.litInt 1)))
            (Stmt.seq
              (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a"))
                (.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b")))))
              (Stmt.store (.varRef (.user "output")) (.varRef (.user "i")) (.varRef (.user "result")))))) =
        some (.normal, env') ∧ FRIInv env' :=
  -- Chain 4 operations via seq, each preserving FRIInv
  seq_FRIInv_evaluates _ _ env
    (load_input_FRI_evaluates env "a" _ hInv (evalExpr_mul_user_lit_FRI env hInv "i" 2))
    (fun e1 hI1 => seq_FRIInv_evaluates _ _ e1
      (load_input_FRI_evaluates e1 "b" _ hI1 (evalExpr_2i_plus_1_FRI e1 hI1))
      (fun e2 hI2 => seq_FRIInv_evaluates _ _ e2
        (assign_arith_FRI_evaluates e2 "result" _ hI2
          (by obtain ⟨va, hva⟩ := hI2.2.2.1 "a"
              obtain ⟨valpha, halpha⟩ := hI2.2.2.1 "alpha"
              obtain ⟨vb, hvb⟩ := hI2.2.2.1 "b"
              exact ⟨va + valpha * vb, by simp [evalExpr, hva, halpha, hvb, evalBinOp]⟩))
        (fun e3 hI3 => store_output_FRI_evaluates e3 (.user "i") (.user "result") hI3
          (hI3.2.2.1 "i") (hI3.2.2.1 "result"))))


/-- Sequencing of two statements preserving an invariant + counter tracking. -/
private theorem seq_tracked_evaluates (s1 s2 : Stmt) (env : LowLevelEnv) (j : Int)
    (h1 : ∃ fuel1 env1, evalStmt fuel1 env s1 = some (.normal, env1) ∧ FRIInv env1 ∧
      env1 (.user "i") = .int j)
    (h2 : ∀ env1, FRIInv env1 → env1 (.user "i") = .int j →
      ∃ fuel2 env2, evalStmt fuel2 env1 s2 = some (.normal, env2) ∧ FRIInv env2 ∧
        env2 (.user "i") = .int j) :
    ∃ fuel env', evalStmt fuel env (.seq s1 s2) = some (.normal, env') ∧ FRIInv env' ∧
      env' (.user "i") = .int j := by
  obtain ⟨fuel1, env1, heval1, hinv1, hi1⟩ := h1
  obtain ⟨fuel2, env2, heval2, hinv2, hi2⟩ := h2 env1 hinv1 hi1
  refine ⟨max fuel1 fuel2, env2, ?_, hinv2, hi2⟩
  rw [TrustLean.evalStmt_seq]
  rw [TrustLean.evalStmt_fuel_mono heval1 (le_max_left fuel1 fuel2)]
  simp only []
  exact TrustLean.evalStmt_fuel_mono heval2 (le_max_right fuel1 fuel2)

/-- A load from input array preserves FRIInv and preserves the i counter. -/
private theorem load_input_tracked (env : LowLevelEnv) (target : String)
    (idxExpr : LowLevelExpr) (j : Int) (hInv : FRIInv env)
    (hi : env (.user "i") = .int j) (hne : target ≠ "i")
    (hIdx : ∃ idx : Int, evalExpr env idxExpr = some (.int idx)) :
    ∃ fuel env',
      evalStmt fuel env (.load (.user target) (.varRef (.user "input")) idxExpr) =
        some (.normal, env') ∧ FRIInv env' ∧ env' (.user "i") = .int j := by
  obtain ⟨idx, hidx⟩ := hIdx
  obtain ⟨dval, hdval⟩ := hInv.1 idx
  refine ⟨0, env.update (.user target) (env (.array "input" idx)), ?_, ?_, ?_⟩
  · simp [getArrayName, hidx]
  · rw [hdval]; exact FRIInv_update_user env target dval hInv
  · have hne' : VarName.user "i" ≠ VarName.user target := by simp [VarName.user.injEq, Ne.symm hne]
    rw [LowLevelEnv.update_other _ _ _ _ hne']; exact hi

/-- An assign to a user var (not "i") preserves FRIInv and preserves the i counter. -/
private theorem assign_tracked (env : LowLevelEnv) (s : String) (expr : LowLevelExpr)
    (j : Int) (hInv : FRIInv env) (hi : env (.user "i") = .int j) (hne : s ≠ "i")
    (hExpr : ∃ val : Int, evalExpr env expr = some (.int val)) :
    ∃ fuel env',
      evalStmt fuel env (.assign (.user s) expr) = some (.normal, env') ∧
      FRIInv env' ∧ env' (.user "i") = .int j := by
  obtain ⟨val, hval⟩ := hExpr
  refine ⟨0, env.update (.user s) (.int val),
    by simp [hval], FRIInv_update_user env s val hInv, ?_⟩
  have hne' : VarName.user "i" ≠ VarName.user s := by simp [VarName.user.injEq, Ne.symm hne]
  rw [LowLevelEnv.update_other _ _ _ _ hne']; exact hi

/-- A store to output array preserves FRIInv and preserves the i counter. -/
private theorem store_output_tracked (env : LowLevelEnv) (idxVar valVar : VarName)
    (j : Int) (hInv : FRIInv env) (hi : env (.user "i") = .int j)
    (hIdx : ∃ idx : Int, env idxVar = .int idx)
    (hVal : ∃ v : Int, env valVar = .int v) :
    ∃ fuel env',
      evalStmt fuel env (.store (.varRef (.user "output")) (.varRef idxVar) (.varRef valVar)) =
        some (.normal, env') ∧ FRIInv env' ∧ env' (.user "i") = .int j := by
  obtain ⟨idx, hidx⟩ := hIdx
  obtain ⟨v, hv⟩ := hVal
  refine ⟨0, env.update (.array "output" idx) (env valVar), ?_, ?_, ?_⟩
  · simp [getArrayName, hidx, hv]
  · rw [hv]; exact FRIInv_update_output env idx v hInv
  · simp [LowLevelEnv.update, hi]

/-- The FRI fold body + step (i++) evaluates and preserves the loop invariant. -/
private theorem friFoldBodyStep_evaluates (n : Nat) (env : LowLevelEnv)
    (j : Int) (hP : FRIInv env ∧ env (.user "i") = .int j) (hjlt : j < ↑n) :
    evalExpr env (.binOp .ltOp (.varRef (.user "i")) (.litInt ↑n)) = some (.bool true) ∧
    ∃ fuelB env',
      evalStmt fuelB env
        (Stmt.seq
          (Stmt.seq
            (Stmt.load (.user "a") (.varRef (.user "input"))
              (.binOp .mul (.varRef (.user "i")) (.litInt 2)))
            (Stmt.seq
              (Stmt.load (.user "b") (.varRef (.user "input"))
                (.binOp .add (.binOp .mul (.varRef (.user "i")) (.litInt 2)) (.litInt 1)))
              (Stmt.seq
                (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a"))
                  (.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b")))))
                (Stmt.store (.varRef (.user "output")) (.varRef (.user "i")) (.varRef (.user "result"))))))
          (Stmt.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1)))) =
        some (.normal, env') ∧ FRIInv env' ∧ env' (.user "i") = .int (j + 1) := by
  obtain ⟨hInv, hi⟩ := hP
  constructor
  · -- Condition is true: j < n
    simp [evalExpr, hi, evalBinOp, hjlt]
  · -- Body (4 operations preserving FRIInv + i = j) then step (i := i + 1)
    have hBody : ∃ fuel env', evalStmt fuel env
        (Stmt.seq
          (Stmt.load (.user "a") (.varRef (.user "input"))
            (.binOp .mul (.varRef (.user "i")) (.litInt 2)))
          (Stmt.seq
            (Stmt.load (.user "b") (.varRef (.user "input"))
              (.binOp .add (.binOp .mul (.varRef (.user "i")) (.litInt 2)) (.litInt 1)))
            (Stmt.seq
              (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a"))
                (.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b")))))
              (Stmt.store (.varRef (.user "output")) (.varRef (.user "i")) (.varRef (.user "result")))))) =
        some (.normal, env') ∧ FRIInv env' ∧ env' (.user "i") = .int j :=
      seq_tracked_evaluates _ _ env j
        (load_input_tracked env "a" _ j hInv hi (by decide)
          (evalExpr_mul_user_lit_FRI env hInv "i" 2))
        (fun e1 hI1 hi1 => seq_tracked_evaluates _ _ e1 j
          (load_input_tracked e1 "b" _ j hI1 hi1 (by decide)
            (evalExpr_2i_plus_1_FRI e1 hI1))
          (fun e2 hI2 hi2 => seq_tracked_evaluates _ _ e2 j
            (assign_tracked e2 "result" _ j hI2 hi2 (by decide)
              (by obtain ⟨va, hva⟩ := hI2.2.2.1 "a"
                  obtain ⟨valpha, halpha⟩ := hI2.2.2.1 "alpha"
                  obtain ⟨vb, hvb⟩ := hI2.2.2.1 "b"
                  exact ⟨va + valpha * vb, by simp [evalExpr, hva, halpha, hvb, evalBinOp]⟩))
            (fun e3 hI3 hi3 => store_output_tracked e3 (.user "i") (.user "result") j hI3 hi3
              (hI3.2.2.1 "i") (hI3.2.2.1 "result"))))
    -- Now chain body with step (i := i + 1)
    obtain ⟨fBody, envBody, hEvalBody, hInvBody, hiBody⟩ := hBody
    refine ⟨max fBody 0, envBody.update (.user "i") (.int (j + 1)), ?_, ?_, ?_⟩
    · rw [TrustLean.evalStmt_seq]
      rw [TrustLean.evalStmt_fuel_mono hEvalBody (le_max_left fBody 0)]
      simp only []
      simp [evalExpr, hiBody, evalBinOp]
    · exact FRIInv_update_user envBody "i" (j + 1) hInvBody
    · simp [LowLevelEnv.update]

set_option maxHeartbeats 400000 in
/-- The FRI fold loop evaluates successfully for any n, given Int-valued arrays and variables.
    Uses counting_while_evaluates_post for the single for_ loop. -/
theorem friFoldLoopStmt_evaluates (n : Nat) (llEnv : LowLevelEnv)
    (hInv : FRIInv llEnv) :
    ∃ fuel env', evalStmt fuel llEnv (friFoldLoopStmt n) = some (.normal, env') := by
  unfold friFoldLoopStmt
  -- Use for_evaluates_via_while: init + while
  apply for_evaluates_via_while
  -- Init: assign i := 0
  refine ⟨0, llEnv.update (.user "i") (.int 0), by simp [evalExpr], ?_⟩
  -- While: use counting_while_evaluates_post
  set envI := llEnv.update (.user "i") (.int 0) with hEnvI_def
  have hPI : FRIInv envI ∧ envI (.user "i") = .int 0 :=
    ⟨FRIInv_update_user llEnv "i" 0 hInv, by simp [envI]⟩
  obtain ⟨fW, envW, hW, _⟩ := counting_while_evaluates_post
    (.binOp .ltOp (.varRef (.user "i")) (.litInt ↑n))
    (Stmt.seq
      (Stmt.seq
        (Stmt.load (.user "a") (.varRef (.user "input"))
          (.binOp .mul (.varRef (.user "i")) (.litInt 2)))
        (Stmt.seq
          (Stmt.load (.user "b") (.varRef (.user "input"))
            (.binOp .add (.binOp .mul (.varRef (.user "i")) (.litInt 2)) (.litInt 1)))
          (Stmt.seq
            (Stmt.assign (.user "result") (.binOp .add (.varRef (.user "a"))
              (.binOp .mul (.varRef (.user "alpha")) (.varRef (.user "b")))))
            (Stmt.store (.varRef (.user "output")) (.varRef (.user "i")) (.varRef (.user "result"))))))
      (Stmt.assign (.user "i") (.binOp .add (.varRef (.user "i")) (.litInt 1))))
    (↑n)
    (fun j env => FRIInv env ∧ env (.user "i") = .int j)
    -- hCondFalse: when j = n, condition is false
    (fun env ⟨_, hi⟩ => by simp [evalExpr, hi, evalBinOp])
    -- hStep: body + step evaluates and preserves invariant
    (fun env j hP hjlt => friFoldBodyStep_evaluates n env j hP hjlt)
    n 0 (by simp) (by omega) envI hPI
  exact ⟨fW, envW, hW⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Smoke Tests
-- ══════════════════════════════════════════════════════════════════

#eval IO.println babybear_reduce_c
#eval IO.println babybear_reduce_rust
#eval IO.println mersenne31_reduce_c
#eval IO.println koalabear_reduce_c
#eval IO.println goldilocks_reduce_c

#eval IO.println babybear_butterfly_c
#eval IO.println mersenne31_butterfly_rust

#eval IO.println (babybear_ntt_c 4)

#eval IO.println poseidon_sbox5_c
#eval IO.println poseidon_sbox5_rust
#eval IO.println poseidon_sbox7_c

#eval IO.println (friFold_c 8)
#eval IO.println (friFold_rust 8)

end AmoLean.Bridge.VerifiedProductionCodegen
